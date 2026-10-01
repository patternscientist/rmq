/* LIFE-NATIVE-P0: measurements outside the Lean kernel and production ABI.
 * Only live owned roots are traversed. Snapshots retain numbers, never Lean
 * references. Capacity is read from lean_array_capacity, not logical size.
 * External payloads are static test tokens; their finalizers count destruction
 * of Lean external objects. These counts do not measure allocator RSS.
 */
#include <lean/lean.h>
#include <lean/version.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#if LEAN_VERSION_MAJOR != 4 || LEAN_VERSION_MINOR != 22 || LEAN_VERSION_PATCH != 0
#error This probe requires the pinned Lean 4.22.0 runtime headers
#endif

extern void lean_initialize_runtime_module(void);
enum { N = 6, ROOTS = 3, MAX_SNAPSHOTS = 9 };
typedef struct { unsigned id; int value; } Token;
static Token tokens[N];
static unsigned destroyed[N];
static lean_external_class *token_class;
static const int specification[N] = {101, -7, 303, 303, 505, -19};

static void internal(const char *message) {
    fprintf(stderr, "INTERNAL: %s\n", message);
    exit(4);
}
static void finalize_token(void *data) {
    Token *t = (Token *)data;
    if (t->id >= N || ++destroyed[t->id] != 1) internal("double destruction");
}
static void foreach_token(void *data, b_lean_obj_arg visitor) {
    (void)data; (void)visitor; /* No hidden Lean references in the payload. */
}
static lean_object *make_input(size_t n) {
    lean_object *a = lean_alloc_array(0, 32);
    for (size_t i = 0; i < n; ++i) {
        tokens[i].id = (unsigned)i;
        tokens[i].value = specification[i];
        a = lean_array_push(a, lean_alloc_external(token_class, &tokens[i]));
    }
    return a;
}
static lean_object *shrink(lean_object *a, size_t target) {
    /* Init/Data/Array/Basic.lean shrink: size-target repeated pops. */
    size_t pops = lean_array_size(a) > target ? lean_array_size(a) - target : 0;
    while (pops-- != 0) a = lean_array_pop(a);
    return a;
}
static void release(lean_object **p) {
    if (*p) { lean_dec(*p); *p = NULL; }
}

typedef struct {
    int present, old, rc;
    size_t size, capacity, bytes;
    int values[N];
    unsigned ids[N];
} RootView;
typedef struct {
    const char *phase;
    RootView roots[ROOTS]; /* source owner, alias owner, output owner */
    unsigned destroyed[N];
    int element_rc[N];
    size_t live_elements, element_references, unique_arrays, container_bytes;
    int old_reachable, external_element;
} Snapshot;
static Snapshot snapshots[MAX_SNAPSHOTS];
static size_t snapshot_count;
static uintptr_t old_identity;

static void observe_element(Snapshot *s, lean_object *e) {
    if (lean_is_scalar(e) || lean_obj_tag(e) != LeanExternal ||
        lean_get_external_class(e) != token_class || e->m_rc <= 0)
        internal("unexpected element representation");
    Token *t = (Token *)lean_get_external_data(e);
    if (t->id >= N || destroyed[t->id]) internal("dead element reached");
    if (s->element_rc[t->id] && s->element_rc[t->id] != e->m_rc)
        internal("inconsistent element references");
    s->element_rc[t->id] = e->m_rc;
}
static Snapshot *observe(const char *phase, lean_object *source,
                         lean_object *alias, lean_object *out,
                         lean_object *element_alias) {
    if (snapshot_count == MAX_SNAPSHOTS) internal("snapshot bound");
    Snapshot *s = &snapshots[snapshot_count++];
    s->phase = phase;
    s->external_element = -1;
    lean_object *roots[ROOTS] = {source, alias, out};
    for (size_t r = 0; r < ROOTS; ++r) {
        lean_object *a = roots[r];
        if (!a) continue;
        RootView *v = &s->roots[r];
        v->present = 1;
        v->old = (uintptr_t)a == old_identity;
        v->rc = a->m_rc;
        v->size = lean_array_size(a);
        v->capacity = lean_array_capacity(a);
        v->bytes = lean_array_byte_size(a);
        if (v->size > N || v->size > v->capacity || v->rc <= 0)
            internal("unexpected array shape");
        s->old_reachable |= v->old;
        int duplicate = 0;
        for (size_t j = 0; j < r; ++j) if (roots[j] == a) duplicate = 1;
        if (!duplicate) { ++s->unique_arrays; s->container_bytes += v->bytes; }
        for (size_t i = 0; i < v->size; ++i) {
            lean_object *e = lean_array_get_core(a, i); /* borrowed while a lives */
            observe_element(s, e);
            Token *t = (Token *)lean_get_external_data(e);
            v->values[i] = t->value;
            v->ids[i] = t->id;
        }
    }
    if (element_alias) {
        observe_element(s, element_alias);
        s->external_element = (int)((Token *)lean_get_external_data(element_alias))->id;
    }
    for (size_t i = 0; i < N; ++i) {
        s->destroyed[i] = destroyed[i];
        if (s->element_rc[i]) {
            ++s->live_elements;
            s->element_references += (size_t)s->element_rc[i];
        }
    }
    return s;
}

typedef struct {
    const char *id;
    int operation; /* 0 pop, 1 shrink, 2 replacement, 3 controlled failure */
    size_t n, start, count;
    int alias, element_alias, fail_stage, mutation;
} Case;
static const Case registry[] = {
    {"pop-unique",0,6,0,5,0,0,0,0},
    {"shrink-unique",1,6,0,2,0,0,0,0},
    {"pop-shared",0,6,0,5,1,0,0,0},
    {"shrink-shared",1,6,0,2,1,0,0,0},
    {"pop-empty-unique",0,0,0,0,0,0,0,0},
    {"pop-empty-shared",0,0,0,0,1,0,0,0},
    {"shrink-noop",1,6,0,6,0,0,0,0},
    {"replace-prefix",2,6,0,2,0,0,0,0},
    {"replace-overlap",2,6,1,4,0,0,0,0},
    {"replace-tail",2,6,4,2,0,0,0,0},
    {"replace-empty",2,6,0,0,0,0,0,0},
    {"replace-alias",2,6,1,4,1,0,0,0},
    {"replace-element-alias",2,6,4,2,0,1,0,0},
    {"fail-alloc",3,6,1,4,0,0,1,0},
    {"fail-after-alloc",3,6,1,4,0,0,2,0},
    {"fail-mid-copy",3,6,1,4,0,0,3,0},
    {"fail-handoff",3,6,1,4,0,0,4,0},
    {"fail-after-consume",3,6,1,4,0,0,5,0},
    {"fail-alias",3,6,1,4,1,0,3,0},
    {"negative-shrink",2,6,0,2,0,0,0,1},
    {"negative-alias",2,6,1,4,1,0,0,2},
    {"negative-cleanup",3,6,1,4,0,0,4,3},
    {"negative-value",2,6,1,4,0,0,0,4}
};
static const size_t registry_size = sizeof(registry) / sizeof(registry[0]);

/* These checks inspect recorded projections, never the case's expected verdict.
 * The same strict transfer predicate is used for successful exclusive transfers
 * and all three challenged transfers. Alias-aware cases use an explicit weaker
 * observation contract and do not advertise exclusive consumption.
 */
static int values_match(const RootView *v, size_t start, size_t count) {
    if (!v->present || v->size != count) return 0;
    for (size_t i = 0; i < count; ++i)
        if (v->values[i] != specification[start+i] || v->ids[i] != start+i) return 0;
    return 1;
}
static int references_match(const Snapshot *s, size_t n, size_t start,
                            size_t count, int alias, int element_alias) {
    for (size_t i = 0; i < N; ++i) {
        int expected = (i < n && alias ? 1 : 0) +
            (i >= start && i < start+count ? 1 : 0) +
            (i == 0 && element_alias ? 1 : 0);
        if (s->element_rc[i] != expected ||
            s->destroyed[i] != (unsigned)(i < n && expected == 0)) return 0;
    }
    return 1;
}
static const char *transfer_predicate(const Snapshot *s, const Case *c,
                                      int allowed_alias, int allowed_element_alias) {
    const RootView *v = &s->roots[2];
    if (!values_match(v, c->start, c->count)) return "values";
    if (v->capacity > c->count ||
        v->bytes > sizeof(lean_array_object) + sizeof(void *)*c->count) return "capacity";
    if (s->roots[0].present || v->old || v->rc != 1 ||
        s->roots[1].present != allowed_alias ||
        s->old_reachable != allowed_alias ||
        s->external_element != (allowed_element_alias ? 0 : -1)) return "ownership";
    if (allowed_alias && (!s->roots[1].old || s->roots[1].rc != 1 ||
                          !values_match(&s->roots[1], 0, c->n))) return "ownership";
    if (!references_match(s,c->n,c->start,c->count,allowed_alias,allowed_element_alias))
        return "references";
    return "none";
}
static const char *failure_predicate(const Snapshot *s, const Case *c) {
    if (s->roots[0].present || s->roots[2].present ||
        s->roots[1].present != c->alias || s->old_reachable != c->alias)
        return "cleanup";
    if (c->alias && (!values_match(&s->roots[1],0,c->n) || s->roots[1].rc != 1))
        return "cleanup";
    return references_match(s,c->n,0,0,c->alias,0) ? "none" : "cleanup";
}
static const char *shrink_predicate(const Snapshot *s, const Case *c) {
    const RootView *v = &s->roots[2];
    if (!values_match(v,0,c->count)) return "values";
    if (v->capacity != 32) return "capacity";
    if (!c->alias && (!v->old || v->rc != 1)) return "capacity";
    if (c->alias && (!s->roots[1].old || !values_match(&s->roots[1],0,c->n) ||
                     v->old || v->rc != 1 || s->roots[1].rc != 1)) return "ownership";
    if (v->capacity < v->size) return "capacity";
    return references_match(s,c->n,0,c->count,c->alias,0) ? "none" : "references";
}

/* Consumes source on success AND injected error. Only initialized destination
 * entries enter its logical size, so lean_dec safely cleans a partial copy.
 * fail_stage 1 is a deterministic pre-allocation error, not real Lean OOM.
 */
static void replacement(const Case *c, lean_object **source, lean_object *alias,
                        lean_object **out, lean_object *element_alias) {
    if (c->fail_stage == 1) goto failed;
    *out = lean_alloc_array(0,c->count);
    observe("allocated",*source,alias,*out,element_alias);
    if (c->fail_stage == 2) goto failed;
    for (size_t i = 0; i < c->count; ++i) {
        size_t position = c->start+i;
        if (c->mutation == 4 && i == 0) position = 0;
        *out = lean_array_push(*out,lean_array_uget(*source,position));
        if (c->fail_stage == 3 && i == 1) goto failed;
    }
    observe("copied",*source,alias,*out,element_alias);
    if (c->fail_stage == 4) goto failed;
    release(source);
    if (c->fail_stage == 5) goto failed;
    return;
failed:
    observe("failure-before-cleanup",*source,alias,*out,element_alias);
    if (c->mutation != 3) release(out); /* Omitted cleanup is the actual mutant. */
    release(source);
}

static void print_ints(const int *a,size_t n) {
    putchar('['); for(size_t i=0;i<n;++i) printf("%s%d",i?",":"",a[i]); putchar(']');
}
static void print_unsigneds(const unsigned *a,size_t n) {
    putchar('['); for(size_t i=0;i<n;++i) printf("%s%u",i?",":"",a[i]); putchar(']');
}
static void print_snapshot(const Snapshot *s) {
    printf("{\"phase\":\"%s\",\"roots\":[",s->phase);
    for(size_t r=0;r<ROOTS;++r) {
        const RootView *v=&s->roots[r];
        printf("%s{\"present\":%d,\"old\":%d,\"rc\":%d,\"size\":%zu,\"capacity\":%zu,\"bytes\":%zu,\"values\":",
               r?",":"",v->present,v->old,v->rc,v->size,v->capacity,v->bytes);
        print_ints(v->values,v->size); printf(",\"ids\":"); print_unsigneds(v->ids,v->size); putchar('}');
    }
    printf("],\"destroyed\":"); print_unsigneds(s->destroyed,N);
    printf(",\"elementRC\":"); print_ints(s->element_rc,N);
    printf(",\"liveElements\":%zu,\"elementReferences\":%zu,\"uniqueArrays\":%zu,\"containerBytes\":%zu,\"oldReachable\":%d,\"externalElement\":%d}",
           s->live_elements,s->element_references,s->unique_arrays,s->container_bytes,
           s->old_reachable,s->external_element);
}
static int execute(const Case *c) {
    lean_object *source=make_input(c->n), *alias=NULL, *out=NULL, *element_alias=NULL;
    old_identity=(uintptr_t)source;
    if(c->alias) { alias=source; lean_inc(alias); }
    if(c->element_alias) element_alias=lean_array_uget(source,0);
    observe("before",source,alias,out,element_alias);
    if(c->operation<2 || c->mutation==1) {
        out = c->operation==0 ? lean_array_pop(source) :
            shrink(source,strcmp(c->id,"shrink-noop")==0?8:c->count);
        source=NULL;
    } else replacement(c,&source,alias,&out,element_alias);
    Snapshot *handoff=observe("handoff",source,alias,out,element_alias);
    const char *failure;
    if(c->operation<2) failure=shrink_predicate(handoff,c);
    else if(c->operation==3) failure=failure_predicate(handoff,c);
    else failure=transfer_predicate(handoff,c,c->mutation==2?0:c->alias,c->element_alias);
    /* Restore omitted cleanup and release legitimate aliases after the measured
       verdict. Never silently repair before evaluating its acceptance predicate. */
    release(&source); release(&alias); release(&out); release(&element_alias);
    Snapshot *final=observe("restored",source,alias,out,element_alias);
    int clean=final->unique_arrays==0 && final->live_elements==0;
    for(size_t i=0;i<N;++i) if(destroyed[i]!=(unsigned)(i<c->n)) clean=0;
    if(!clean) internal("final cleanup incomplete");
    printf("{\"schema\":1,\"case\":\"%s\",\"n\":%zu,\"start\":%zu,\"count\":%zu,\"operation\":%d,\"alias\":%d,\"elementAlias\":%d,\"failStage\":%d,\"mutation\":%d,\"expectedValues\":",
           c->id,c->n,c->start,c->count,c->operation,c->alias,c->element_alias,c->fail_stage,c->mutation);
    print_ints(specification+c->start,c->count);
    printf(",\"snapshots\":[");
    for(size_t i=0;i<snapshot_count;++i) { if(i) putchar(','); print_snapshot(&snapshots[i]); }
    printf("],\"verdict\":\"%s\",\"failure\":\"%s\",\"cleanupComplete\":true}\n",
           strcmp(failure,"none")==0?"ACCEPT":"REJECT",failure);
    return strcmp(failure,"none")==0?0:3;
}
int main(int argc,char **argv) {
    if(argc==2 && strcmp(argv[1],"--list")==0) {
        putchar('['); for(size_t i=0;i<registry_size;++i) printf("%s\"%s\"",i?",":"",registry[i].id);
        puts("]"); return 0;
    }
    if(argc==2 && strcmp(argv[1],"--startup")==0) {
        printf("{\"schema\":1,\"runtime\":\"%s\",\"pointerBytes\":%zu,\"arrayHeaderBytes\":%zu}\n",
               LEAN_VERSION_STRING,sizeof(void*),sizeof(lean_array_object));
        return 0;
    }
    if(argc==2 && strcmp(argv[1],"--fatal-oom")==0) {
        lean_initialize_runtime_module();
        lean_internal_panic_out_of_memory(); /* Explicit fatal-handler control. */
    }
    if(argc!=3 || strcmp(argv[1],"--case")!=0 || argv[2][0]=='\0') {
        fputs("SELECTOR: invalid invocation\n",stderr); return 2;
    }
    const Case *selected=NULL;
    for(size_t i=0;i<registry_size;++i) if(strcmp(argv[2],registry[i].id)==0) selected=&registry[i];
    if(!selected) { fputs("SELECTOR: unknown case\n",stderr); return 2; }
    lean_initialize_runtime_module();
    token_class=lean_register_external_class(finalize_token,foreach_token);
    lean_io_mark_end_initialization();
    return execute(selected);
}
