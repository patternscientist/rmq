/* The executable semantics are compiled Lean. This file owns foreign buffers,
 * measures live runtime objects and implements one consuming publication step.
 * Requested bytes are not allocator usable bytes or process RSS. */
#include <lean/lean.h>
#include <lean/version.h>
#include <stdint.h>
#include <stddef.h>
#include <limits.h>
#include "include/packed_rmq_lifecycle.h"

/* leanc supplies minimal C headers. These declarations match Windows SDK
 * 10.0.22621.0 corecrt_malloc.h, processthreadsapi.h and processenv.h, plus
 * MSVC 14.44.35207 vcruntime_string.h. malloc/free come from lean.h. Keep the
 * same compiler/runtime rather than mixing a second compiler's header model. */
extern void *__cdecl calloc(size_t count,size_t size);
extern void *__cdecl realloc(void *block,size_t size);
extern void *__cdecl memcpy(void *destination,const void *source,size_t size);
extern void *__cdecl memset(void *destination,int value,size_t size);
extern int __cdecl memcmp(const void *left,const void *right,size_t size);
__declspec(dllimport) unsigned long __stdcall GetCurrentThreadId(void);
__declspec(dllimport) unsigned long __stdcall GetEnvironmentVariableA(const char *,char *,unsigned long);

#if LEAN_VERSION_MAJOR != 4 || LEAN_VERSION_MINOR != 22 || LEAN_VERSION_PATCH != 0
#error The lifecycle ABI requires Lean 4.22.0
#endif
#if !defined(_WIN64)
#error This certification is Windows x64 only
#endif

extern void lean_initialize_runtime_module(void);
extern lean_object *initialize_RMQ_Core_WordRAM_Native_Lifecycle_Entry(uint8_t, lean_object *);
extern lean_object *rmq_lifecycle_decode_signed(uint8_t, lean_object *);
extern uint8_t rmq_lifecycle_signed_format(uint8_t, lean_object *);
extern lean_object *rmq_lifecycle_profile(lean_object *);
extern uint8_t rmq_lifecycle_admit(uint8_t, lean_object *, lean_object *, lean_object *, lean_object *);
extern lean_object *rmq_lifecycle_initial(uint8_t, lean_object *, lean_object *, lean_object *);
extern lean_object *rmq_lifecycle_run_first(uint8_t, lean_object *, lean_object *);
extern lean_object *rmq_lifecycle_run_fuel(uint8_t, lean_object *, lean_object *);
extern lean_object *rmq_lifecycle_run_first_observed(uint8_t, lean_object *, lean_object *);
extern uint8_t rmq_lifecycle_query_admit(lean_object *, lean_object *, lean_object *);
extern lean_object *rmq_lifecycle_query(uint8_t, lean_object *, lean_object *, lean_object *);
extern lean_object *rmq_lifecycle_query_observed(uint8_t, lean_object *, lean_object *, lean_object *);
extern lean_object *rmq_lifecycle_metadata(lean_object *, lean_object *);
extern uint8_t rmq_lifecycle_status(lean_object *);
extern lean_object *rmq_lifecycle_packet(lean_object *);
extern lean_object *rmq_lifecycle_observation_counter(lean_object *, uint8_t);
extern lean_object *rmq_lifecycle_observation_reads(lean_object *);
extern lean_object *rmq_lifecycle_observation_route(lean_object *, uint8_t);
extern lean_object *rmq_lifecycle_signature_count(uint8_t, uint8_t);
extern lean_object *rmq_lifecycle_encode_natural(lean_object *);
extern lean_object *rmq_lifecycle_program(uint8_t);
extern void ln1_visit_fixed_globals(void (*visit)(lean_object *, void *), void *);

_Static_assert(sizeof(void *) == 8, "Windows x64 pointers");
_Static_assert(sizeof(unsigned long) == 4, "Windows DWORD width");
_Static_assert(sizeof(lean_object) == 8, "Pinned Lean object header");
_Static_assert(sizeof(packed_lifecycle_info) == 216, "C/Rust info layout");

struct packed_lifecycle_owner {
    lean_object *state;
    uint64_t generation;
    size_t repacked_arrays, copied_entries;
    uint8_t model;
};
struct packed_lifecycle_result { uint64_t generation; size_t size; uint8_t data[]; };
struct packed_lifecycle_observation {
    lean_object *stats, *reads;
    uint64_t generation;
};

/* Exact pinned GMP mpz_object layout, verified at runtime before traversal.
 * GMP allocates _mp_alloc limbs, independently of signed used size _mp_size.
 * The separate requested backing is allocated * sizeof(uint64_t). */
typedef struct {
    lean_object header;
    int32_t allocated;
    int32_t used;
    uint64_t *digits;
} ln1_mpz;
_Static_assert(sizeof(ln1_mpz) == 24, "Pinned GMP MPZ size");
_Static_assert(offsetof(ln1_mpz, allocated) == 8, "GMP allocated limb count offset");
_Static_assert(offsetof(ln1_mpz, used) == 12, "GMP signed used limb count offset");
_Static_assert(offsetof(ln1_mpz, digits) == 16, "GMP limb pointer offset");

typedef struct { uint64_t calls, cells, capacity, expanded, maximum; uint8_t overflow; } copy_counts;
static copy_counts current_copies, initialization_copies;
static _Atomic(int) initialization_state;
static unsigned long initializing_thread;
static uint8_t layout_verified;
static uint64_t generation;

#ifdef PACKED_LIFECYCLE_TESTING
static uint32_t test_mode;
static size_t test_argument;
static packed_lifecycle_test_info receipt;
#define RECORD(field, value) (receipt.field = (value))
#define INCREMENT(field, value) (receipt.field += (value))
#else
#define RECORD(field, value) ((void)0)
#define INCREMENT(field, value) ((void)0)
#endif

static int test_is(uint32_t mode) {
#ifdef PACKED_LIFECYCLE_TESTING
    return test_mode == mode;
#else
    (void)mode; return 0;
#endif
}
/* Numeric mode values are frozen in the public testing enum. Keeping them
 * local also permits building ordinary code without test declarations. */
enum { T_SKIP=1, T_ALIAS=2, T_INPUT=3, T_ARENA=4, T_KEYS=5, T_HISTORY=6,
    T_VALUE=7, T_OFFSET=8, T_PARTIAL=9, T_TAKE=10, T_FAULT=11, T_FUEL=12,
    T_ALLOC=13, T_PUBLISH=14, T_SCALAR=15 };

static int test_environment(const char *name) {
#ifdef PACKED_LIFECYCLE_TESTING
    char value[4] = {0};
    return GetEnvironmentVariableA(name, value, sizeof(value)) == 1 && value[0] == '1';
#else
    (void)name; return 0;
#endif
}
static void add_copy_count(uint64_t *counter, uint64_t amount) {
    if (UINT64_MAX - *counter < amount) { current_copies.overflow = 1; *counter = UINT64_MAX; }
    else *counter += amount;
}

/* Generated C alone renames its call to this symbol. This translation unit
 * includes the normal runtime declaration and delegates without a new evaluator. */
LEAN_EXPORT lean_object *ln1_counted_copy_expand_array(lean_object *array, bool expand) {
    size_t size = lean_array_size(array), capacity = lean_array_capacity(array);
    add_copy_count(&current_copies.calls, 1);
    add_copy_count(&current_copies.cells, (uint64_t)size);
    add_copy_count(&current_copies.capacity, (uint64_t)capacity);
    add_copy_count(&current_copies.expanded, expand ? 1 : 0);
    if (capacity > current_copies.maximum) current_copies.maximum = (uint64_t)capacity;
    return lean_copy_expand_array(array, expand);
}

static int active_thread(void) {
    if (initialization_state != 2) return PACKED_LIFECYCLE_INITIALIZATION;
    if (GetCurrentThreadId() != initializing_thread) return PACKED_LIFECYCLE_THREAD;
    return 0;
}
static void release_lean(lean_object **slot) {
    if (*slot) { lean_dec(*slot); *slot = NULL; }
}
static lean_object *copy_bytes(packed_lifecycle_bytes bytes) {
    lean_object *array = lean_alloc_sarray(1, bytes.size, bytes.size);
    if (bytes.size) memcpy(lean_sarray_cptr(array), bytes.data, bytes.size);
    return array;
}
static int view_valid(packed_lifecycle_bytes bytes) { return bytes.data != NULL || bytes.size == 0; }
static int array_view(lean_object *array, packed_lifecycle_array_info *out) {
    if (!array || lean_is_scalar(array) || !lean_is_array(array)) return PACKED_LIFECYCLE_STATE;
    out->initialized = lean_array_size(array);
    out->capacity = lean_array_capacity(array);
    if (out->initialized > out->capacity || out->capacity > (SIZE_MAX-sizeof(lean_array_object))/sizeof(void *))
        return PACKED_LIFECYCLE_STATE;
    out->requested_bytes = sizeof(lean_array_object) + out->capacity * sizeof(void *);
    out->identity = (uintptr_t)array;
    return 0;
}
static int owner_shape(lean_object *owner) {
    if (!owner || lean_is_scalar(owner) || !lean_is_ctor(owner) || lean_obj_tag(owner) != 0 ||
        lean_ctor_num_objs(owner) != 6) return 0;
    for (unsigned i=0; i<4; ++i) {
        lean_object *array = lean_ctor_get(owner, i);
        if (lean_is_scalar(array) || !lean_is_array(array) || lean_array_size(array)>lean_array_capacity(array)) return 0;
    }
    return 1;
}
static int natural_shape(lean_object *value) {
    return lean_is_scalar(value) || (lean_is_mpz(value) && layout_verified && ((ln1_mpz *)value)->used>=0);
}
static int option_natural_shape(lean_object *value) {
    return (lean_is_scalar(value) && lean_unbox(value)==0) ||
        (!lean_is_scalar(value) && lean_is_ctor(value) && lean_obj_tag(value)==1 &&
         lean_ctor_num_objs(value)==1 && natural_shape(lean_ctor_get(value,0)));
}
static int ready_shape(lean_object *owner) {
    if (!owner_shape(owner) || lean_array_size(lean_ctor_get(owner,0))!=8273 ||
        lean_array_size(lean_ctor_get(owner,2))!=0 || lean_array_size(lean_ctor_get(owner,3))!=0 ||
        !natural_shape(lean_ctor_get(owner,4))) return 0;
    lean_object *status=lean_ctor_get(owner,5);
    if (lean_is_scalar(status) || !lean_is_ctor(status) || lean_obj_tag(status)!=1 ||
        lean_ctor_num_objs(status)!=1 || !natural_shape(lean_ctor_get(status,0))) return 0;
    for (unsigned bank=0; bank<2; ++bank) {
        lean_object *array=lean_ctor_get(owner,bank);
        for (size_t i=0; i<lean_array_size(array); ++i) {
            lean_object *value=lean_array_get_core(array,i);
            if (!(bank==0 ? natural_shape(value) : option_natural_shape(value))) return 0;
        }
    }
    return 1;
}
static int exact_arrays(lean_object *owner) {
    if (!owner_shape(owner)) return 0;
    for (unsigned i=0;i<4;++i) {
        lean_object *array=lean_ctor_get(owner,i);
        if (lean_array_size(array)!=lean_array_capacity(array)) return 0;
    }
    return 1;
}
static int exclusive_owner(lean_object *owner) {
    if (!owner_shape(owner) || !lean_is_exclusive(owner)) return 0;
    for (unsigned i=0;i<4;++i) if (!lean_is_exclusive(lean_ctor_get(owner,i))) return 0;
    return 1;
}
static int profile_of_count(size_t count, size_t *bits, size_t *bytes) {
    if (count>4096) return PACKED_LIFECYCLE_LIMIT;
    lean_object *width=rmq_lifecycle_profile(lean_usize_to_nat(count));
    if (!lean_is_scalar(width)) { lean_dec(width); return PACKED_LIFECYCLE_LIMIT; }
    *bits=lean_unbox(width); lean_dec(width);
    if (*bits==0 || *bits>SIZE_MAX-7) return PACKED_LIFECYCLE_STATE;
    *bytes=(*bits+7)/8;
    return 0;
}
static int produced_metadata(lean_object *owner, size_t *count, size_t *extent, size_t *width) {
    if (!owner_shape(owner)) return PACKED_LIFECYCLE_STATE;
    lean_inc(owner);
    lean_object *n=rmq_lifecycle_metadata(owner,lean_box(0));
    if (lean_is_scalar(n) || lean_obj_tag(n)!=1 || lean_ctor_num_objs(n)!=1 ||
        !lean_is_scalar(lean_ctor_get(n,0))) { lean_dec(n); return PACKED_LIFECYCLE_STATE; }
    *count=lean_unbox(lean_ctor_get(n,0)); lean_dec(n);
    if (*count>4096) return PACKED_LIFECYCLE_LIMIT;
    *extent=lean_array_size(lean_ctor_get(owner,1));
    lean_inc(owner);
    lean_object *m=rmq_lifecycle_metadata(owner,lean_box(7));
    lean_object *expected=lean_usize_to_nat(*extent);
    int valid=!lean_is_scalar(m) && lean_obj_tag(m)==1 && lean_ctor_num_objs(m)==1 &&
        lean_nat_dec_eq(lean_ctor_get(m,0),expected);
    lean_dec(expected); lean_dec(m);
    if (!valid) return PACKED_LIFECYCLE_STATE;
    size_t bytes=0; return profile_of_count(*count,width,&bytes);
}

/* A pointer set and explicit worklist deduplicate live objects. Scalar values
 * are occurrences; immutable scalar/constructor sharing is permitted. */
typedef struct {
    lean_object **set, **work;
    size_t set_capacity, used, work_count, work_capacity;
    size_t objects, scalars, boxed, object_bytes, digit_bytes, roots;
    int error;
} graph;
static size_t pointer_hash(lean_object *pointer) {
    uintptr_t p=(uintptr_t)pointer;
    p ^= p>>33; p *= UINT64_C(0xff51afd7ed558ccd); p ^= p>>33;
    return (size_t)p;
}
static int size_add(size_t *out,size_t n) {
    if (SIZE_MAX-*out<n) return 0;
    *out+=n; return 1;
}
static int graph_rehash(graph *g,size_t capacity) {
    if (capacity>SIZE_MAX/sizeof(lean_object *)) return 0;
    lean_object **next=(lean_object **)calloc(capacity,sizeof(lean_object *));
    if (!next) return 0;
    for(size_t i=0;i<g->set_capacity;++i) if(g->set[i]) {
        size_t j=pointer_hash(g->set[i])&(capacity-1);
        while(next[j]) j=(j+1)&(capacity-1);
        next[j]=g->set[i];
    }
    free(g->set);g->set=next;g->set_capacity=capacity;return 1;
}
static void graph_push(lean_object *object,void *context) {
    graph *g=(graph *)context;
    if (g->error || !object) return;
    if (lean_is_scalar(object)) { if(!size_add(&g->scalars,1)) g->error=PACKED_LIFECYCLE_LIMIT; return; }
    if (g->set_capacity==0 || g->used>=g->set_capacity/2) {
        size_t next=g->set_capacity ? g->set_capacity*2 : 256;
        if(next<g->set_capacity || !graph_rehash(g,next)) {g->error=PACKED_LIFECYCLE_ALLOCATION;return;}
    }
    size_t slot=pointer_hash(object)&(g->set_capacity-1);
    while(g->set[slot]) {if(g->set[slot]==object)return;slot=(slot+1)&(g->set_capacity-1);}
    if(g->work_count==g->work_capacity) {
        size_t next=g->work_capacity ? g->work_capacity*2 : 256;
        if(next<g->work_capacity || next>SIZE_MAX/sizeof(lean_object *)) {g->error=PACKED_LIFECYCLE_LIMIT;return;}
        lean_object **work=(lean_object **)realloc(g->work,next*sizeof(lean_object *));
        if(!work){g->error=PACKED_LIFECYCLE_ALLOCATION;return;}
        g->work=work;g->work_capacity=next;
    }
    g->set[slot]=object;++g->used;g->work[g->work_count++]=object;
}
static int graph_finish(graph *g) {
    for(size_t index=0;index<g->work_count && !g->error;++index) {
        lean_object *object=g->work[index];
        if(!size_add(&g->objects,1) || !size_add(&g->object_bytes,lean_object_byte_size(object))) {
            g->error=PACKED_LIFECYCLE_LIMIT;break;
        }
        if(lean_is_ctor(object)) {
            for(unsigned i=0;i<lean_ctor_num_objs(object);++i) graph_push(lean_ctor_get(object,i),g);
        } else if(lean_is_array(object)) {
            for(size_t i=0;i<lean_array_size(object);++i) graph_push(lean_array_get_core(object,i),g);
        } else if(lean_is_closure(object)) {
            /* Count only captured Lean roots; the function address is code. */
            for(unsigned i=0;i<lean_closure_num_fixed(object);++i) graph_push(lean_closure_get(object,i),g);
        } else if(lean_is_ref(object)) {
            graph_push(lean_to_ref(object)->m_value,g);
        } else if(lean_is_thunk(object)) {
            /* Observe initialized roots without forcing or mutating a thunk. */
            graph_push(lean_to_thunk(object)->m_value,g);
            graph_push(lean_to_thunk(object)->m_closure,g);
        } else if(lean_is_mpz(object)) {
            ln1_mpz *value=(ln1_mpz *)object;
            uint64_t used=value->used<0 ? (uint64_t)(-(int64_t)value->used) : (uint64_t)value->used;
            if(!layout_verified || value->allocated<0 || used>(uint64_t)value->allocated ||
                (value->allocated>0 && !value->digits) || (uint64_t)value->allocated>SIZE_MAX/8 ||
                !size_add(&g->boxed,1) || !size_add(&g->digit_bytes,(size_t)value->allocated*8))
                g->error=PACKED_LIFECYCLE_STATE;
        } else if(lean_is_sarray(object) || lean_is_string(object)) {
            /* Scalar storage contains no Lean object pointers. */
        } else {
            /* Task/external roots require a separately specified traversal.
             * Global visitors may encounter them; extending that inventory
             * requires explicit traversal, never silent omission. */
            g->error=PACKED_LIFECYCLE_STATE;
        }
    }
    return g->error;
}
static void graph_clear(graph *g) {free(g->set);free(g->work);g->set=NULL;g->work=NULL;}
static void graph_global_root(lean_object *object,void *context) {
    graph *g=(graph *)context;
    if(object && !size_add(&g->roots,1)){g->error=PACKED_LIFECYCLE_LIMIT;return;}
    graph_push(object,context);
}

static int verify_layout(void) {
    uint8_t magnitude[17]={7}; magnitude[16]=4;
    packed_lifecycle_bytes bytes={magnitude,sizeof(magnitude)};
    lean_object *positive=rmq_lifecycle_decode_signed(0,copy_bytes(bytes));
    lean_object *negative=rmq_lifecycle_decode_signed(1,copy_bytes(bytes));
    int good=!lean_is_scalar(positive) && lean_is_mpz(positive) &&
        !lean_is_scalar(negative) && lean_is_mpz(negative) &&
        lean_object_byte_size(positive)==24 && lean_object_byte_size(negative)==24;
    if(good) {
        ln1_mpz *p=(ln1_mpz *)positive,*n=(ln1_mpz *)negative;
        good=p->allocated>=3 && n->allocated>=3 && p->used==3 && n->used==-3 && p->digits && n->digits;
        if(good) for(size_t i=0;i<3;++i) {
            uint64_t expected=i==0 ? 7 : i==2 ? 4 : 0;
            if(p->digits[i]!=expected || n->digits[i]!=expected) good=0;
        }
    }
    if(good) {
        lean_inc(positive);
        lean_object *encoded=rmq_lifecycle_encode_natural(positive);
        good=lean_sarray_size(encoded)==17 && memcmp(lean_sarray_cptr(encoded),magnitude,17)==0;
        lean_dec(encoded);
    }
    lean_dec(positive);lean_dec(negative);
    layout_verified=(uint8_t)good;return good;
}

int packed_lifecycle_init(void) {
    int unclaimed=0;
    if(!atomic_compare_exchange_strong(&initialization_state,&unclaimed,1)) return PACKED_LIFECYCLE_INITIALIZATION;
    initializing_thread=GetCurrentThreadId();
    if(test_environment("PACKED_LIFECYCLE_FAIL_INIT")){initialization_state=-1;return PACKED_LIFECYCLE_INITIALIZATION;}
    lean_initialize_runtime_module();
    lean_object *result=initialize_RMQ_Core_WordRAM_Native_Lifecycle_Entry(1,lean_io_mk_world());
    lean_io_mark_end_initialization();
    int failed=lean_io_result_is_error(result);lean_dec(result);
    if(failed){initialization_state=-1;return PACKED_LIFECYCLE_INITIALIZATION;}
    lean_init_task_manager_using(1);
    if(!verify_layout()){initialization_state=-1;return PACKED_LIFECYCLE_INITIALIZATION;}
    initialization_copies=current_copies;memset(&current_copies,0,sizeof(current_copies));
    initialization_state=2;return 0;
}
int packed_lifecycle_profile(size_t count,size_t *bits,size_t *bytes) {
    int error=active_thread();if(error)return error;
    if(!bits || !bytes)return PACKED_LIFECYCLE_FORMAT;
    return profile_of_count(count,bits,bytes);
}

static void begin_operation(void) {
    ++generation;memset(&current_copies,0,sizeof(current_copies));
#ifdef PACKED_LIFECYCLE_TESTING
    memset(&receipt,0,sizeof(receipt));
    receipt.first_mismatch_array=SIZE_MAX;receipt.first_mismatch_index=SIZE_MAX;
#endif
}
static void handle_created(void) {INCREMENT(native_handles_created,1);INCREMENT(native_handles_live,1);}
static void handle_released(uint64_t old_generation) {
    if(old_generation==generation){INCREMENT(native_handles_released,1);
#ifdef PACKED_LIFECYCLE_TESTING
        if(receipt.native_handles_live) --receipt.native_handles_live;
#endif
    }
}
static packed_lifecycle_owner *allocate_owner(void) {
    if(test_is(T_ALLOC))return NULL;
    packed_lifecycle_owner *owner=(packed_lifecycle_owner *)calloc(1,sizeof(*owner));
    if(owner){owner->generation=generation;handle_created();}return owner;
}
static int result_from_bytes(lean_object *bytes,packed_lifecycle_result **output) {
    size_t size=lean_sarray_size(bytes);
    if(size==0 || size>SIZE_MAX-sizeof(packed_lifecycle_result)){lean_dec(bytes);return PACKED_LIFECYCLE_STATE;}
    packed_lifecycle_result *result=(packed_lifecycle_result *)malloc(sizeof(*result)+size);
    if(!result){lean_dec(bytes);return PACKED_LIFECYCLE_ALLOCATION;}
    result->generation=generation;result->size=size;memcpy(result->data,lean_sarray_cptr(bytes),size);
    lean_dec(bytes);handle_created();*output=result;return 0;
}
static int result_from_nat(lean_object *value,packed_lifecycle_result **output) {
    return result_from_bytes(rmq_lifecycle_encode_natural(value),output);
}
packed_lifecycle_bytes packed_lifecycle_result_bytes(const packed_lifecycle_result *answer) {
    packed_lifecycle_bytes result={NULL,0};
    if(!active_thread() && answer){result.data=answer->data;result.size=answer->size;}return result;
}
void packed_lifecycle_result_free(packed_lifecycle_result *answer) {
    if(answer && !active_thread()){handle_released(answer->generation);free(answer);}
}
void packed_lifecycle_owner_free(packed_lifecycle_owner **slot) {
    if(slot && *slot && !active_thread()) {
        packed_lifecycle_owner *owner=*slot;*slot=NULL;
        if(owner->generation==generation) {
            /* Former temporary arrays were transferred to this published
             * handle. Their final release remains part of this receipt. */
            INCREMENT(temporary_arrays_released,owner->repacked_arrays);
            INCREMENT(released_entries,owner->copied_entries);
        }
        release_lean(&owner->state);handle_released(owner->generation);free(owner);
    }
}
void packed_lifecycle_observation_free(packed_lifecycle_observation *diagnostics) {
    if(diagnostics && !active_thread()) {
        release_lean(&diagnostics->stats);release_lean(&diagnostics->reads);
        handle_released(diagnostics->generation);free(diagnostics);
    }
}

typedef struct {
    lean_object *input,*source,*replacement,*stats;
    lean_object *retained_owner,*retained_input,*retained_arena,*retained_keys,*retained_history,*shared_scalar;
    packed_lifecycle_owner *handle;
    packed_lifecycle_result *answer;
    packed_lifecycle_observation *diagnostics;
    size_t replacement_arrays,initialized_entries,copied_entries;
    int values_equal;
} transfer;
static int hidden_roots(transfer *t) {
    RECORD(retained_owner_roots,t->retained_owner!=NULL);
    RECORD(retained_input_roots,t->retained_input!=NULL);
    RECORD(retained_arena_roots,t->retained_arena!=NULL);
    RECORD(retained_key_roots,t->retained_keys!=NULL);
    RECORD(retained_history_roots,t->retained_history!=NULL);
    RECORD(retained_scalar_roots,t->shared_scalar!=NULL);
    return t->input || t->source || t->retained_owner || t->retained_input || t->retained_arena ||
        t->retained_keys || t->retained_history;
}
static void cleanup_transfer(transfer *t,int success) {
    release_lean(&t->input);release_lean(&t->source);
    if(t->replacement) {
        release_lean(&t->replacement);
        INCREMENT(temporary_arrays_released,t->replacement_arrays);
        INCREMENT(released_entries,t->initialized_entries);
    }
    RECORD(temporary_arrays_live,0);
    release_lean(&t->stats);release_lean(&t->retained_owner);release_lean(&t->retained_input);
    release_lean(&t->retained_arena);release_lean(&t->retained_keys);release_lean(&t->retained_history);
    release_lean(&t->shared_scalar);
    if(!success) {
        packed_lifecycle_owner_free(&t->handle);
        packed_lifecycle_result_free(t->answer);t->answer=NULL;
        packed_lifecycle_observation_free(t->diagnostics);t->diagnostics=NULL;
    }
    RECORD(source_copy_calls,current_copies.calls);RECORD(source_copy_cells,current_copies.cells);
    RECORD(source_copy_capacity_total,current_copies.capacity);
    RECORD(source_copy_capacity_max,current_copies.maximum);
    RECORD(source_copy_expands,current_copies.expanded);
    RECORD(copy_counter_overflow,current_copies.overflow);
    RECORD(cleanup_complete,!t->input && !t->source && !t->replacement && !t->stats &&
        !t->retained_owner && !t->retained_input && !t->retained_arena && !t->retained_keys &&
        !t->retained_history && !t->shared_scalar && (success || (!t->handle && !t->answer && !t->diagnostics)));
}
static int arrays_equal(lean_object *left,lean_object *right,unsigned bank) {
    size_t n=lean_array_size(left);if(n!=lean_array_size(right))return 0;
    for(size_t i=0;i<n;++i) {
        lean_object *a=lean_array_get_core(left,i),*b=lean_array_get_core(right,i);
        int same;
        if(bank==1) {
            if(!option_natural_shape(a)||!option_natural_shape(b))return 0;
            same=lean_obj_tag(a)==lean_obj_tag(b) && (lean_obj_tag(a)==0 ||
                lean_nat_dec_eq(lean_ctor_get(a,0),lean_ctor_get(b,0)));
        } else same=lean_nat_dec_eq(a,b);
        if(!same){RECORD(first_mismatch_array,bank);RECORD(first_mismatch_index,i);return 0;}
    }
    return 1;
}
static int repack(transfer *t) {
    if(!owner_shape(t->source))return PACKED_LIFECYCLE_STATE;
#ifdef PACKED_LIFECYCLE_TESTING
    for(unsigned b=0;b<4;++b)array_view(lean_ctor_get(t->source,b),&receipt.source[b]);
#endif
    if(test_is(T_ARENA)){t->retained_arena=lean_ctor_get(t->source,1);lean_inc(t->retained_arena);}
    if(test_is(T_SKIP)){t->replacement=t->source;t->source=NULL;t->values_equal=1;return 0;}
    lean_object *arrays[4]={NULL,NULL,NULL,NULL};
    int error=0;
    for(unsigned bank=0;bank<4 && !error;++bank) {
        lean_object *source=lean_ctor_get(t->source,bank);
        size_t size=lean_array_size(source);
        arrays[bank]=lean_alloc_array(0,size);++t->replacement_arrays;
        INCREMENT(temporary_arrays_created,1);INCREMENT(temporary_arrays_live,1);
        for(size_t i=0;i<size;++i) {
#ifdef PACKED_LIFECYCLE_TESTING
            if(test_is(T_PARTIAL) && t->copied_entries==test_argument){error=PACKED_LIFECYCLE_CONTROLLED_FAILURE;break;}
#endif
            size_t source_index=i;
#ifdef PACKED_LIFECYCLE_TESTING
            if(bank==1 && test_is(T_OFFSET) && i==test_argument && size>1)source_index=(i+1)%size;
#endif
            lean_object *value=lean_array_get_core(source,source_index);lean_inc(value);
#ifdef PACKED_LIFECYCLE_TESTING
            if(bank==1 && test_is(T_VALUE) && i==test_argument && lean_obj_tag(value)==1) {
                lean_object *next=lean_nat_add(lean_ctor_get(value,0),lean_box(1));
                lean_dec(value);value=lean_alloc_ctor(1,1,0);lean_ctor_set(value,0,next);
            }
#endif
            lean_array_cptr(arrays[bank])[i]=value;
            lean_array_set_size(arrays[bank],i+1);
            ++t->copied_entries;++t->initialized_entries;
            INCREMENT(copied_entries,1);INCREMENT(initialized_entries,1);
        }
    }
    if(error) {
        for(unsigned bank=0;bank<4;++bank)if(arrays[bank]) {
            INCREMENT(released_entries,lean_array_size(arrays[bank]));lean_dec(arrays[bank]);
            INCREMENT(temporary_arrays_released,1);
        }
        t->replacement_arrays=0;t->initialized_entries=0;RECORD(temporary_arrays_live,0);return error;
    }
    t->values_equal=1;
    for(unsigned bank=0;bank<4;++bank)if(!arrays_equal(lean_ctor_get(t->source,bank),arrays[bank],bank))t->values_equal=0;
    t->replacement=lean_alloc_ctor(0,6,0);
    for(unsigned bank=0;bank<4;++bank)lean_ctor_set(t->replacement,bank,arrays[bank]);
    for(unsigned field=4;field<6;++field){lean_object *value=lean_ctor_get(t->source,field);lean_inc(value);lean_ctor_set(t->replacement,field,value);}
    release_lean(&t->source);
    return 0;
}
static void retain_shared_scalar(transfer *t) {
    if(!test_is(T_SCALAR))return;
    for(unsigned bank=0;bank<2;++bank) {
        lean_object *array=lean_ctor_get(t->replacement,bank);
        for(size_t i=0;i<lean_array_size(array);++i) {
            lean_object *value=lean_array_get_core(array,i);
            if(bank==1){if(lean_obj_tag(value)!=1)continue;value=lean_ctor_get(value,0);}
            if(!lean_is_scalar(value) && lean_is_mpz(value)){t->shared_scalar=value;lean_inc(value);return;}
        }
    }
}
static int prepare_publication(transfer *t,uint8_t model,uint8_t observe) {
    int error=repack(t);if(error)return error;
    if(test_is(T_ALIAS)){t->retained_owner=t->replacement;lean_inc(t->retained_owner);}
    retain_shared_scalar(t);
    int exclusive=exclusive_owner(t->replacement),exact=exact_arrays(t->replacement),hidden=hidden_roots(t);
    int strict=exclusive && exact && t->values_equal && !hidden && ready_shape(t->replacement) && !current_copies.overflow;
    RECORD(owner_exclusive,exclusive);RECORD(arrays_exact,exact);RECORD(values_equal,t->values_equal);
    RECORD(strict_publication,strict);
#ifdef PACKED_LIFECYCLE_TESTING
    for(unsigned bank=0;bank<4;++bank)array_view(lean_ctor_get(t->replacement,bank),&receipt.replacement[bank]);
#endif
    if(!strict)return PACKED_LIFECYCLE_CONTROLLED_FAILURE;
    size_t count,extent,width;
    error=produced_metadata(t->replacement,&count,&extent,&width);if(error)return error;
    lean_inc(t->replacement);
    error=result_from_bytes(rmq_lifecycle_packet(t->replacement),&t->answer);if(error)return error;
    if(t->answer->size!=(width+7)/8)return PACKED_LIFECYCLE_STATE;
    if(observe) {
        if(!t->stats)return PACKED_LIFECYCLE_STATE;
        t->diagnostics=(packed_lifecycle_observation *)calloc(1,sizeof(*t->diagnostics));
        if(!t->diagnostics)return PACKED_LIFECYCLE_ALLOCATION;
        t->diagnostics->generation=generation;handle_created();
        t->diagnostics->stats=t->stats;t->stats=NULL;
        lean_inc(t->diagnostics->stats);
        t->diagnostics->reads=rmq_lifecycle_observation_reads(t->diagnostics->stats);
    }
    if(test_is(T_PUBLISH))return PACKED_LIFECYCLE_CONTROLLED_FAILURE;
    t->handle->state=t->replacement;t->replacement=NULL;
    t->handle->model=model;t->handle->repacked_arrays=t->replacement_arrays;t->handle->copied_entries=t->copied_entries;
    RECORD(temporary_arrays_live,0);
    return 0;
}
static void receive_observed(transfer *t,lean_object *pair) {
    t->source=lean_ctor_get(pair,0);lean_inc(t->source);
    t->stats=lean_ctor_get(pair,1);lean_inc(t->stats);lean_dec(pair);
    if(test_is(T_HISTORY)){t->retained_history=t->stats;lean_inc(t->retained_history);}
}
static int status_result(transfer *t) {
    if(!owner_shape(t->source))return PACKED_LIFECYCLE_STATE;
#ifdef PACKED_LIFECYCLE_TESTING
    for(unsigned bank=0;bank<4;++bank)array_view(lean_ctor_get(t->source,bank),&receipt.source[bank]);
#endif
    lean_inc(t->source);uint8_t status=rmq_lifecycle_status(t->source);
    return status==1 ? 0 : status==2 ? PACKED_LIFECYCLE_MODEL_FAULT : PACKED_LIFECYCLE_FUEL_EXHAUSTED;
}
static int endpoints_shape(size_t width,size_t bytes,packed_lifecycle_bytes left,packed_lifecycle_bytes right) {
    if(!view_valid(left)||!view_valid(right)||left.size!=bytes||right.size!=bytes)return PACKED_LIFECYCLE_FORMAT;
    unsigned bits=(unsigned)(width%8);
    if(bits && ((left.data[bytes-1]>>bits)||(right.data[bytes-1]>>bits)))return PACKED_LIFECYCLE_FORMAT;
    return 0;
}

int packed_lifecycle_build_first(uint8_t model,const packed_lifecycle_int *input,size_t count,
    packed_lifecycle_bytes left,packed_lifecycle_bytes right,uint8_t observe,
    packed_lifecycle_owner **owner,packed_lifecycle_result **answer,packed_lifecycle_observation **diagnostics) {
    int error=active_thread();if(error)return error;
    if(!owner||!answer||!diagnostics||*owner||*answer||*diagnostics||model>1||observe>1||(!input&&count))return PACKED_LIFECYCLE_FORMAT;
    begin_operation();transfer t={0};lean_object *l=NULL,*r=NULL,*initial=NULL;
    if(count>4096){error=PACKED_LIFECYCLE_LIMIT;goto done;}
    size_t width=0,bytes=0,total=0;
    error=profile_of_count(count,&width,&bytes);if(error)goto done;
    error=endpoints_shape(width,bytes,left,right);if(error)goto done;
    for(size_t i=0;i<count;++i) {
        if(input[i].negative>1||!view_valid(input[i].magnitude)||input[i].magnitude.size==0){error=PACKED_LIFECYCLE_FORMAT;goto done;}
        if(input[i].magnitude.size>4096||total>16777216-input[i].magnitude.size){error=PACKED_LIFECYCLE_LIMIT;goto done;}
        total+=input[i].magnitude.size;
    }
    t.input=lean_box(0);
    for(size_t i=count;i>0;--i) {
        lean_object *magnitude=copy_bytes(input[i-1].magnitude);lean_inc(magnitude);
        if(!rmq_lifecycle_signed_format(input[i-1].negative,magnitude)) {
            lean_dec(magnitude);error=PACKED_LIFECYCLE_FORMAT;goto done;
        }
        lean_object *value=rmq_lifecycle_decode_signed(input[i-1].negative,magnitude);
        lean_object *node=lean_alloc_ctor(1,2,0);lean_ctor_set(node,0,value);lean_ctor_set(node,1,t.input);t.input=node;
    }
    l=copy_bytes(left);r=copy_bytes(right);
    lean_inc(t.input);lean_inc(l);lean_inc(r);
    if(!rmq_lifecycle_admit(model,t.input,lean_usize_to_nat(count),l,r)){error=PACKED_LIFECYCLE_INPUT_DOMAIN;goto done;}
    t.handle=allocate_owner();if(!t.handle){error=PACKED_LIFECYCLE_ALLOCATION;goto done;}
    if(test_is(T_INPUT)){t.retained_input=t.input;lean_inc(t.retained_input);}
    initial=rmq_lifecycle_initial(model,t.input,l,r);t.input=NULL;l=NULL;r=NULL;
    if(test_is(T_KEYS)){t.retained_keys=lean_ctor_get(initial,2);lean_inc(t.retained_keys);}
    if(test_is(T_FAULT)) {
        lean_object *old_status=lean_ctor_get(initial,5);lean_ctor_set(initial,5,lean_box(2));lean_dec(old_status);
    }
    if(test_is(T_FUEL)||test_is(T_FAULT)) {
        size_t fuel=0;
#ifdef PACKED_LIFECYCLE_TESTING
        fuel=test_argument;
#endif
        t.source=rmq_lifecycle_run_fuel(model,lean_usize_to_nat(fuel),initial);initial=NULL;
    } else if(observe||test_is(T_HISTORY)) {
        receive_observed(&t,rmq_lifecycle_run_first_observed(model,lean_usize_to_nat(count),initial));initial=NULL;
    } else {t.source=rmq_lifecycle_run_first(model,lean_usize_to_nat(count),initial);initial=NULL;}
    error=status_result(&t);if(error)goto done;
    error=prepare_publication(&t,model,observe);if(error)goto done;
    *owner=t.handle;*answer=t.answer;*diagnostics=t.diagnostics;
done:
    release_lean(&l);release_lean(&r);release_lean(&initial);cleanup_transfer(&t,error==0);return error;
}

int packed_lifecycle_query(packed_lifecycle_owner **slot,packed_lifecycle_bytes left,packed_lifecycle_bytes right,
    uint8_t observe,packed_lifecycle_result **answer,packed_lifecycle_observation **diagnostics) {
    int error=active_thread();if(error)return error;
    if(!slot||!*slot||!answer||!diagnostics||*answer||*diagnostics||observe>1)return PACKED_LIFECYCLE_FORMAT;
    begin_operation();transfer t={0};lean_object *l=NULL,*r=NULL,*taken=NULL;
    packed_lifecycle_owner *old=*slot;uint8_t model=old->model;
    size_t count=0,extent=0,width=0;
    error=produced_metadata(old->state,&count,&extent,&width);if(error)goto done;
    error=endpoints_shape(width,(width+7)/8,left,right);if(error)goto done;
    l=copy_bytes(left);r=copy_bytes(right);lean_inc(old->state);lean_inc(l);lean_inc(r);
    if(!rmq_lifecycle_query_admit(old->state,l,r)){error=PACKED_LIFECYCLE_FORMAT;goto done;}
    if(test_is(T_FUEL)){error=PACKED_LIFECYCLE_STATE;goto done;}
    t.handle=allocate_owner();if(!t.handle){error=PACKED_LIFECYCLE_ALLOCATION;goto done;}
    /* Irrevocable take. No increment of the operational owner spans execution. */
    *slot=NULL;taken=old->state;old->state=NULL;handle_released(old->generation);free(old);old=NULL;
    if(test_is(T_TAKE)||test_environment("PACKED_LIFECYCLE_FAIL_AFTER_TAKE")){error=PACKED_LIFECYCLE_CONTROLLED_FAILURE;goto done;}
    if(test_is(T_FAULT)) {lean_object *status=lean_ctor_get(taken,5);lean_ctor_set(taken,5,lean_box(2));lean_dec(status);}
    if(observe||test_is(T_HISTORY)){receive_observed(&t,rmq_lifecycle_query_observed(model,l,r,taken));}
    else t.source=rmq_lifecycle_query(model,l,r,taken);
    l=NULL;r=NULL;taken=NULL;
    error=status_result(&t);if(error)goto done;
    error=prepare_publication(&t,model,observe);if(error)goto done;
    *slot=t.handle;*answer=t.answer;*diagnostics=t.diagnostics;
done:
    release_lean(&l);release_lean(&r);release_lean(&taken);cleanup_transfer(&t,error==0);return error;
}

int packed_lifecycle_inspect(const packed_lifecycle_owner *owner,packed_lifecycle_info *info) {
    int error=active_thread();if(error)return error;
    if(!owner||!owner->state||!info)return PACKED_LIFECYCLE_FORMAT;
    memset(info,0,sizeof(*info));
    error=produced_metadata(owner->state,&info->count,&info->memory_extent,&info->width_bits);if(error)return error;
    for(unsigned bank=0;bank<4;++bank){error=array_view(lean_ctor_get(owner->state,bank),&info->arrays[bank]);if(error)return error;}
    graph g={0};graph_push(owner->state,&g);error=graph_finish(&g);
    if(!error){info->reachable_objects=g.objects;info->scalar_occurrences=g.scalars;info->boxed_integers=g.boxed;
        info->runtime_reported_object_bytes=g.object_bytes;info->boxed_digit_requested_bytes=g.digit_bytes;}
    graph_clear(&g);if(error)return error;
    info->repacked_arrays=owner->repacked_arrays;info->copied_entries=owner->copied_entries;
    info->exclusive_owner=(uint8_t)exclusive_owner(owner->state);
    info->exact_capacities=(uint8_t)exact_arrays(owner->state);
    /* The native owner layout stores no other Lean root; the schema checks all
     * reachable operational fields and publication discharges temporary roots. */
    info->no_retained_operational_roots=(uint8_t)ready_shape(owner->state);
    return 0;
}
int packed_lifecycle_memory_cell(const packed_lifecycle_owner *owner,size_t index,uint8_t *present,packed_lifecycle_result **value) {
    int error=active_thread();if(error)return error;
    if(!owner||!owner->state||!present||!value||*value)return PACKED_LIFECYCLE_FORMAT;
    lean_object *memory=lean_ctor_get(owner->state,1);
    if(index>=lean_array_size(memory))return PACKED_LIFECYCLE_LIMIT;
    lean_object *cell=lean_array_get_core(memory,index);
    *present=(uint8_t)(lean_obj_tag(cell)==1);
    if(!*present)return 0;
    lean_object *nat=lean_ctor_get(cell,0);lean_inc(nat);return result_from_nat(nat,value);
}
int packed_lifecycle_inspect_code(packed_lifecycle_code_info *info) {
    int error=active_thread();if(error)return error;
    if(!info)return PACKED_LIFECYCLE_FORMAT;memset(info,0,sizeof(*info));
    lean_object *programs[2]={rmq_lifecycle_program(0),rmq_lifecycle_program(1)};
    graph g={0};
    for(unsigned i=0;i<2;++i){error=array_view(programs[i],&info->programs[i]);if(error)break;graph_push(programs[i],&g);}
    if(!error)error=graph_finish(&g);
    if(!error){info->reachable_objects=g.objects;info->scalar_occurrences=g.scalars;info->boxed_integers=g.boxed;
        info->runtime_reported_object_bytes=g.object_bytes;info->boxed_digit_requested_bytes=g.digit_bytes;}
    graph_clear(&g);lean_dec(programs[0]);lean_dec(programs[1]);
    if(error)return error;
    /* A fresh set measures the full fixed graph independently. Its overlap
     * with the two program roots must never be added as disjoint storage. */
    graph fixed={0};ln1_visit_fixed_globals(graph_global_root,&fixed);
    error=graph_finish(&fixed);
    if(!error){info->fixed_global_roots=fixed.roots;info->fixed_reachable_objects=fixed.objects;
        info->fixed_runtime_reported_object_bytes=fixed.object_bytes;
        info->fixed_boxed_digit_requested_bytes=fixed.digit_bytes;}
    graph_clear(&fixed);return error;
}
int packed_lifecycle_observation_counter(const packed_lifecycle_observation *observation,uint8_t category,packed_lifecycle_result **value) {
    int error=active_thread();if(error)return error;
    if(!observation||!value||*value||category>15)return PACKED_LIFECYCLE_FORMAT;
    lean_inc(observation->stats);return result_from_nat(rmq_lifecycle_observation_counter(observation->stats,category),value);
}
int packed_lifecycle_observation_route(const packed_lifecycle_observation *observation,uint8_t route,packed_lifecycle_result **value) {
    int error=active_thread();if(error)return error;
    if(!observation||!value||*value||route>12)return PACKED_LIFECYCLE_FORMAT;
    lean_inc(observation->stats);return result_from_nat(rmq_lifecycle_observation_route(observation->stats,route),value);
}
int packed_lifecycle_signature_count(uint8_t model,uint8_t route,packed_lifecycle_result **value) {
    int error=active_thread();if(error)return error;
    if(model>1||route>12||!value||*value)return PACKED_LIFECYCLE_FORMAT;
    return result_from_nat(rmq_lifecycle_signature_count(model,route),value);
}
int packed_lifecycle_observation_read_count(const packed_lifecycle_observation *observation,size_t *count) {
    int error=active_thread();if(error)return error;
    if(!observation||!count)return PACKED_LIFECYCLE_FORMAT;*count=lean_array_size(observation->reads);return 0;
}
int packed_lifecycle_observation_read(const packed_lifecycle_observation *observation,size_t index,
    packed_lifecycle_result **address,uint8_t *present,packed_lifecycle_result **reply) {
    int error=active_thread();if(error)return error;
    if(!observation||!address||*address||!present||!reply||*reply)return PACKED_LIFECYCLE_FORMAT;
    if(index>=lean_array_size(observation->reads))return PACKED_LIFECYCLE_LIMIT;
    lean_object *pair=lean_array_get_core(observation->reads,index);
    lean_object *a=lean_ctor_get(pair,0),*r=lean_ctor_get(pair,1);lean_inc(a);
    error=result_from_nat(a,address);if(error)return error;
    *present=(uint8_t)(lean_obj_tag(r)==1);
    if(*present){lean_object *v=lean_ctor_get(r,0);lean_inc(v);error=result_from_nat(v,reply);
        if(error){packed_lifecycle_result_free(*address);*address=NULL;*present=0;}}
    return error;
}
#ifdef PACKED_LIFECYCLE_TESTING
int packed_lifecycle_test_configure(uint32_t mode,size_t argument) {
    int error=active_thread();if(error)return error;
    if(mode>15)return PACKED_LIFECYCLE_FORMAT;
    test_mode=mode;test_argument=argument;begin_operation();return 0;
}
int packed_lifecycle_test_receipt(packed_lifecycle_test_info *info) {
    int error=active_thread();if(error)return error;
    if(!info)return PACKED_LIFECYCLE_FORMAT;*info=receipt;return 0;
}
#endif
