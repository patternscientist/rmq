#include "packed_rmq_lifecycle.h"

#include <errno.h>
#include <inttypes.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#if defined(_WIN32)
#include <fcntl.h>
#include <io.h>
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#endif

/* This client is an ABI consumer. Expected packets arrive in an independently
   frozen fixture; it has no RMQ implementation or payload constructor. */
typedef struct { uint8_t *data; size_t size; } blob;
typedef struct { blob left, right, expected; } request;
typedef struct {
    uint8_t model;
    size_t count, query_count;
    char id[129];
    packed_lifecycle_int *input;
    request *queries;
} fixture;
typedef struct { const uint8_t *data; size_t size, offset; } parser;
typedef struct { size_t count; blob *cells; } snapshot;

static char error_text[1024];

static int fail(const char *format, ...) {
    va_list args;
    va_start(args, format);
    vsnprintf(error_text, sizeof(error_text), format, args);
    va_end(args);
    return 0;
}

static int status_ok(int status, const char *operation) {
    return status == PACKED_LIFECYCLE_OK || fail("%s status=%d", operation, status);
}

static void blob_free(blob *b) {
    free(b->data);
    b->data = NULL;
    b->size = 0;
}

static packed_lifecycle_bytes bytes(const blob *b) {
    packed_lifecycle_bytes out = {b->data, b->size};
    return out;
}

static int blob_copy(blob *out, packed_lifecycle_bytes in) {
    if (!in.data || !in.size || in.size > 4096) return fail("result magnitude shape");
    out->data = (uint8_t *)malloc(in.size);
    if (!out->data) return fail("client allocation bytes=%zu", in.size);
    out->size = in.size;
    memcpy(out->data, in.data, in.size);
    return 1;
}

static int need(parser *p, size_t count) {
    return count <= p->size - p->offset || fail("fixture truncated offset=%zu need=%zu", p->offset, count);
}

static int read_u32(parser *p, uint32_t *value) {
    const uint8_t *b;
    if (!need(p, 4)) return 0;
    b = p->data + p->offset;
    *value = (uint32_t)b[0] | ((uint32_t)b[1] << 8) |
             ((uint32_t)b[2] << 16) | ((uint32_t)b[3] << 24);
    p->offset += 4;
    return 1;
}

static int read_blob(parser *p, blob *out) {
    uint32_t size;
    packed_lifecycle_bytes b;
    if (!read_u32(p, &size)) return 0;
    if (!size || size > 4096) return fail("fixture blob length=%" PRIu32, size);
    if (!need(p, size)) return 0;
    b.data = p->data + p->offset;
    b.size = size;
    if (!blob_copy(out, b)) return 0;
    p->offset += size;
    return 1;
}

static void free_inputs(fixture *f) {
    size_t i;
    if (f->input) {
        for (i = 0; i < f->count; ++i) free((void *)f->input[i].magnitude.data);
        free(f->input);
        f->input = NULL;
    }
}

static void fixture_free(fixture *f) {
    size_t i;
    free_inputs(f);
    if (f->queries) {
        for (i = 0; i < f->query_count; ++i) {
            blob_free(&f->queries[i].left);
            blob_free(&f->queries[i].right);
            blob_free(&f->queries[i].expected);
        }
        free(f->queries);
        f->queries = NULL;
    }
}

static int fixture_load(const char *path, fixture *out) {
    FILE *file = NULL;
    uint8_t *raw = NULL;
    long length;
    uint32_t count, queries, id_size;
    size_t i, total = 0;
    parser p;
    int ok = 0;
    file = fopen(path, "rb");
    if (!file) return fail("fixture open errno=%d", errno);
    if (fseek(file, 0, SEEK_END) || (length = ftell(file)) < 0 || length > 33554432L ||
        fseek(file, 0, SEEK_SET)) { fail("fixture file size"); goto done; }
    raw = (uint8_t *)malloc((size_t)length + 1);
    if (!raw) { fail("fixture file allocation"); goto done; }
    if (fread(raw, 1, (size_t)length, file) != (size_t)length) { fail("fixture file read"); goto done; }
    p.data = raw; p.size = (size_t)length; p.offset = 0;
    if (!need(&p, 7)) goto done;
    if (memcmp(raw, "LN1F1", 6) != 0) { fail("fixture magic"); goto done; }
    p.offset = 6;
    out->model = raw[p.offset++];
    if (out->model > 1) { fail("fixture model=%u", out->model); goto done; }
    if (!read_u32(&p, &count) || !read_u32(&p, &queries) || !read_u32(&p, &id_size)) goto done;
    if (count > 4096 || queries == 0 || queries > 4096 || id_size == 0 || id_size > 128) {
        fail("fixture header bounds"); goto done;
    }
    out->count = count; out->query_count = queries;
    if (!need(&p, id_size)) goto done;
    for (i = 0; i < id_size; ++i) {
        uint8_t c = raw[p.offset++];
        if (!((c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') ||
              (c >= '0' && c <= '9') || c == '-' || c == '_')) {
            fail("fixture ID character offset=%zu", i); goto done;
        }
        out->id[i] = (char)c;
    }
    out->id[id_size] = 0;
    out->input = (packed_lifecycle_int *)calloc(count ? count : 1, sizeof(*out->input));
    out->queries = (request *)calloc(queries, sizeof(*out->queries));
    if (!out->input || !out->queries) { fail("fixture arrays allocation"); goto done; }
    for (i = 0; i < count; ++i) {
        blob magnitude = {0};
        if (!need(&p, 1)) goto done;
        out->input[i].negative = raw[p.offset++];
        if (!read_blob(&p, &magnitude)) goto done;
        out->input[i].magnitude = bytes(&magnitude);
        total += magnitude.size;
    }
    if (total > 16777216) { fail("fixture total magnitude bytes"); goto done; }
    for (i = 0; i < queries; ++i) {
        if (!read_blob(&p, &out->queries[i].left) || !read_blob(&p, &out->queries[i].right) ||
            !read_blob(&p, &out->queries[i].expected)) goto done;
    }
    if (p.offset != p.size) { fail("fixture trailing bytes=%zu", p.size - p.offset); goto done; }
    ok = 1;
done:
    if (file) fclose(file);
    free(raw);
    if (!ok) fixture_free(out);
    return ok;
}

/* Only explicitly bounded index/count comparisons use size_t. Answer values
   and memory words stay byte strings throughout. */
static int equal_small(packed_lifecycle_bytes actual, size_t value) {
    size_t i;
    if (!actual.data || !actual.size) return 0;
    for (i = 0; i < actual.size; ++i) {
        if (actual.data[i] != (uint8_t)(value & 255)) return 0;
        value >>= 8;
    }
    return value == 0;
}

static int to_size_bounded(packed_lifecycle_bytes actual, size_t bound, size_t *value) {
    size_t i, result = 0;
    if (!actual.data || !actual.size) return fail("index magnitude shape");
    for (i = actual.size; i != 0; --i) {
        if (result > (SIZE_MAX - actual.data[i - 1]) / 256) return fail("index magnitude overflow");
        result = result * 256 + actual.data[i - 1];
    }
    if (result >= bound) return fail("index outside actual memory");
    *value = result;
    return 1;
}

static int at_most(packed_lifecycle_bytes actual, size_t maximum) {
    size_t i = actual.size;
    uint8_t expected[sizeof(size_t)];
    size_t j;
    if (!actual.data || !actual.size) return 0;
    for (j = 0; j < sizeof(expected); ++j) { expected[j] = (uint8_t)(maximum & 255); maximum >>= 8; }
    while (i > sizeof(expected)) if (actual.data[--i] != 0) return 0;
    for (j = sizeof(expected); j != 0; --j) {
        uint8_t a = j <= actual.size ? actual.data[j - 1] : 0;
        if (a != expected[j - 1]) return a < expected[j - 1];
    }
    return 1;
}

static int canonical_magnitude(packed_lifecycle_bytes b) {
    return b.data && b.size && (b.size == 1 || b.data[b.size - 1] != 0);
}

static int pad_word(const blob *input, size_t width_bits, size_t width_bytes, blob *output) {
    size_t i;
    if (!width_bytes || width_bytes > 4096) return fail("profile byte width");
    for (i = width_bytes; i < input->size; ++i)
        if (input->data[i] != 0) return fail("fixture endpoint width overflow");
    output->data = (uint8_t *)calloc(width_bytes, 1);
    if (!output->data) return fail("endpoint padding allocation");
    output->size = width_bytes;
    memcpy(output->data, input->data, input->size < width_bytes ? input->size : width_bytes);
    if (width_bits % 8 && (output->data[width_bytes - 1] >> (width_bits % 8))) {
        blob_free(output);
        return fail("fixture endpoint unused high bits");
    }
    return 1;
}

static void json_bytes(FILE *report, packed_lifecycle_bytes b) {
    size_t i;
    static const char digits[] = "0123456789abcdef";
    fputc('"', report);
    for (i = 0; i < b.size; ++i) {
        fputc(digits[b.data[i] >> 4], report);
        fputc(digits[b.data[i] & 15], report);
    }
    fputc('"', report);
}

static void json_array_info(FILE *report, const packed_lifecycle_array_info *a) {
    fprintf(report, "{\"initialized\":%zu,\"capacity\":%zu,\"requestedBytes\":%zu,\"identity\":\"0x%" PRIxPTR "\"}",
            a->initialized, a->capacity, a->requested_bytes, a->identity);
}

static void json_code(FILE *report, const packed_lifecycle_code_info *info) {
    fputs("{\"programs\":[", report);
    json_array_info(report, &info->programs[0]); fputc(',', report);
    json_array_info(report, &info->programs[1]);
    fprintf(report, "],\"reachableObjects\":%zu,\"scalarOccurrences\":%zu,\"boxedIntegers\":%zu,"
            "\"runtimeReportedObjectBytes\":%zu,\"boxedDigitRequestedBytes\":%zu,"
            "\"fixedGlobalRoots\":%zu,\"fixedReachableObjects\":%zu,"
            "\"fixedRuntimeReportedObjectBytes\":%zu,\"fixedBoxedDigitRequestedBytes\":%zu}",
            info->reachable_objects, info->scalar_occurrences, info->boxed_integers,
            info->runtime_reported_object_bytes, info->boxed_digit_requested_bytes,
            info->fixed_global_roots, info->fixed_reachable_objects,
            info->fixed_runtime_reported_object_bytes, info->fixed_boxed_digit_requested_bytes);
}

static int inspect_code(packed_lifecycle_code_info *info) {
    if (!status_ok(packed_lifecycle_inspect_code(info), "inspect-code")) return 0;
    if (info->programs[0].initialized != 223371 || info->programs[1].initialized != 223379)
        return fail("fixed code lengths");
    if (!info->programs[0].identity || !info->programs[1].identity ||
        info->programs[0].capacity < info->programs[0].initialized ||
        info->programs[1].capacity < info->programs[1].initialized)
        return fail("fixed code containers");
    return 1;
}

static int strict_info(packed_lifecycle_owner *owner, size_t count, size_t width_bits,
                       packed_lifecycle_info *info) {
    size_t i, header;
    if (!owner) return fail("publication missing owner");
    if (!status_ok(packed_lifecycle_inspect(owner, info), "inspect-owner")) return 0;
    if (info->count != count || info->width_bits != width_bits || !info->memory_extent ||
        info->arrays[1].initialized != info->memory_extent) return fail("publication metadata");
    if (info->arrays[0].initialized != 8273 || info->arrays[2].initialized || info->arrays[3].initialized)
        return fail("publication finite banks");
    if (info->exclusive_owner != 1 || info->exact_capacities != 1 || info->no_retained_operational_roots != 1)
        return fail("publication strict ownership/capacity predicate");
    header = info->arrays[2].requested_bytes;
    if (!header || info->arrays[3].requested_bytes != header) return fail("publication empty container storage");
    for (i = 0; i < 4; ++i) {
        packed_lifecycle_array_info *a = &info->arrays[i];
        if (a->initialized != a->capacity || !a->identity) return fail("publication exact capacity array=%zu", i);
        if (a->capacity > (SIZE_MAX - header) / sizeof(void *) ||
            a->requested_bytes != header + a->capacity * sizeof(void *))
            return fail("publication requested storage array=%zu", i);
    }
    return 1;
}

static void json_info(FILE *report, const packed_lifecycle_info *info) {
    size_t i;
    fprintf(report, "{\"count\":%zu,\"memoryExtent\":%zu,\"widthBits\":%zu,\"arrays\":[",
            info->count, info->memory_extent, info->width_bits);
    for (i = 0; i < 4; ++i) { if (i) fputc(',', report); json_array_info(report, &info->arrays[i]); }
    fprintf(report, "],\"reachableObjects\":%zu,\"scalarOccurrences\":%zu,\"boxedIntegers\":%zu,"
            "\"runtimeReportedObjectBytes\":%zu,\"boxedDigitRequestedBytes\":%zu,"
            "\"repackedArrays\":%zu,\"copiedEntries\":%zu,\"exclusiveOwner\":%u,"
            "\"exactCapacities\":%u,\"noRetainedOperationalRoots\":%u}",
            info->reachable_objects, info->scalar_occurrences, info->boxed_integers,
            info->runtime_reported_object_bytes, info->boxed_digit_requested_bytes,
            info->repacked_arrays, info->copied_entries, info->exclusive_owner,
            info->exact_capacities, info->no_retained_operational_roots);
}

static void snapshot_free(snapshot *s) {
    size_t i;
    for (i = 0; i < s->count; ++i) blob_free(&s->cells[i]);
    free(s->cells); s->cells = NULL; s->count = 0;
}

static int snapshot_take(packed_lifecycle_owner *owner, size_t count, snapshot *out) {
    size_t i;
    packed_lifecycle_result *value = NULL;
    uint8_t present = 0;
    if (count > 1000000) return fail("diagnostic memory snapshot ceiling");
    out->cells = (blob *)calloc(count ? count : 1, sizeof(blob));
    if (!out->cells) return fail("memory snapshot allocation");
    out->count = count;
    for (i = 0; i < count; ++i) {
        if (!status_ok(packed_lifecycle_memory_cell(owner, i, &present, &value), "memory-cell")) goto bad;
        if (present != 1 || !value) { fail("canonical memory missing cell=%zu", i); goto bad; }
        if (!blob_copy(&out->cells[i], packed_lifecycle_result_bytes(value))) goto bad;
        packed_lifecycle_result_free(value); value = NULL;
    }
    return 1;
bad:
    packed_lifecycle_result_free(value);
    snapshot_free(out);
    return 0;
}

static int snapshot_equal(const snapshot *a, const snapshot *b) {
    size_t i;
    if (a->count != b->count) return fail("query memory extent changed");
    for (i = 0; i < a->count; ++i)
        if (a->cells[i].size != b->cells[i].size ||
            memcmp(a->cells[i].data, b->cells[i].data, a->cells[i].size))
            return fail("query memory value changed cell=%zu", i);
    return 1;
}

static void json_snapshot(FILE *report, const snapshot *s) {
    size_t i;
    fputc('[', report);
    for (i = 0; i < s->count; ++i) { if (i) fputc(',', report); json_bytes(report, bytes(&s->cells[i])); }
    fputc(']', report);
}

static int signatures(FILE *report, uint8_t model) {
    uint8_t route;
    packed_lifecycle_result *value = NULL;
    fputc('{', report);
    for (route = 7; route <= 12; ++route) {
        packed_lifecycle_bytes b;
        if (!status_ok(packed_lifecycle_signature_count(model, route, &value), "signature-count")) goto bad;
        b = packed_lifecycle_result_bytes(value);
        if (!canonical_magnitude(b)) { fail("signature magnitude route=%u", route); goto bad; }
        if (route <= 10 && !equal_small(b, 1)) { fail("signature uniqueness route=%u", route); goto bad; }
        if (route >= 11 && equal_small(b, 0)) { fail("signature absence route=%u", route); goto bad; }
        if (route != 7) fputc(',', report);
        fprintf(report, "\"%u\":", route); json_bytes(report, b);
        packed_lifecycle_result_free(value); value = NULL;
    }
    fputc('}', report);
    return 1;
bad:
    packed_lifecycle_result_free(value);
    return 0;
}

static int observation_report(FILE *report, packed_lifecycle_observation *observation,
                              size_t query_index, const snapshot *memory) {
    uint8_t category, route, present = 0;
    size_t count = 0, i, address_index;
    packed_lifecycle_result *value = NULL, *address = NULL, *reply = NULL;
    packed_lifecycle_bytes b;
    if (!observation) return fail("observed mode missing diagnostic object");
    fputs("{\"countersLE\":[", report);
    for (category = 0; category <= 15; ++category) {
        if (!status_ok(packed_lifecycle_observation_counter(observation, category, &value), "observation-counter")) goto bad;
        b = packed_lifecycle_result_bytes(value);
        if (!canonical_magnitude(b)) { fail("counter magnitude category=%u", category); goto bad; }
        if ((category == 13 || category == 14) && !equal_small(b, query_index ? 2 : 0)) {
            fail("charged boundary counter query=%zu category=%u", query_index, category); goto bad;
        }
        if (category == 15 && query_index && !at_most(b, 160257)) {
            fail("query modeled step bound"); goto bad;
        }
        if (category) fputc(',', report);
        json_bytes(report, b);
        packed_lifecycle_result_free(value); value = NULL;
    }
    fputs("],\"routesLE\":[", report);
    for (route = 0; route <= 12; ++route) {
        if (!status_ok(packed_lifecycle_observation_route(observation, route, &value), "observation-route")) goto bad;
        b = packed_lifecycle_result_bytes(value);
        if (!canonical_magnitude(b)) { fail("route magnitude route=%u", route); goto bad; }
        if (query_index && route >= 3 && route <= 6 && !equal_small(b, 0)) {
            fail("query reentered construction route=%u", route); goto bad;
        }
        if (route) fputc(',', report);
        json_bytes(report, b);
        packed_lifecycle_result_free(value); value = NULL;
    }
    if (!status_ok(packed_lifecycle_observation_read_count(observation, &count), "observation-read-count")) goto bad;
    if (count > 10000000) { fail("diagnostic read-count ceiling"); goto bad; }
    if (!status_ok(packed_lifecycle_observation_counter(observation, 0, &value), "read-category-count")) goto bad;
    if (!equal_small(packed_lifecycle_result_bytes(value), count)) { fail("read count/category mismatch"); goto bad; }
    packed_lifecycle_result_free(value); value = NULL;
    fprintf(report, "],\"readCount\":%zu,\"readsLE\":[", count);
    for (i = 0; i < count; ++i) {
        packed_lifecycle_bytes a, r;
        if (!status_ok(packed_lifecycle_observation_read(observation, i, &address, &present, &reply), "observation-read")) goto bad;
        a = packed_lifecycle_result_bytes(address);
        if (!canonical_magnitude(a) || present > 1 || (present && !reply) || (!present && reply)) {
            fail("read representation index=%zu", i); goto bad;
        }
        r.data = NULL; r.size = 0;
        if (present) r = packed_lifecycle_result_bytes(reply);
        if (present && !canonical_magnitude(r)) { fail("reply magnitude index=%zu", i); goto bad; }
        if (query_index) {
            if (!present) { fail("canonical query failed read index=%zu", i); goto bad; }
            if (!to_size_bounded(a, memory->count, &address_index)) goto bad;
            if (r.size != memory->cells[address_index].size ||
                memcmp(r.data, memory->cells[address_index].data, r.size)) {
                fail("query read backing index=%zu", i); goto bad;
            }
        }
        if (i) fputc(',', report);
        fputs("{\"address\":", report); json_bytes(report, a); fputs(",\"reply\":", report);
        if (present) json_bytes(report, r); else fputs("null", report);
        fputc('}', report);
        packed_lifecycle_result_free(address); address = NULL;
        packed_lifecycle_result_free(reply); reply = NULL;
    }
    fputs("]}", report);
    return 1;
bad:
    packed_lifecycle_result_free(value);
    packed_lifecycle_result_free(address);
    packed_lifecycle_result_free(reply);
    return 0;
}

static int exercise(fixture *f, int observed, FILE *report) {
    size_t width_bits = 0, width_bytes = 0, q;
    packed_lifecycle_owner *owner = NULL;
    packed_lifecycle_result *answer = NULL;
    packed_lifecycle_observation *observation = NULL;
    packed_lifecycle_info info;
    packed_lifecycle_code_info code, final_code;
    blob left = {0}, right = {0}, expected = {0};
    snapshot original = {0}, current = {0};
    int ok = 0;
    if (!status_ok(packed_lifecycle_init(), "initialize")) goto done;
    if (!status_ok(packed_lifecycle_profile(f->count, &width_bits, &width_bytes), "profile")) goto done;
    if (!width_bits || width_bytes != (width_bits + 7) / 8) { fail("profile relation"); goto done; }
    if (!inspect_code(&code)) goto done;
    fprintf(report, "{\"schema\":\"lifecycle-native1-actual-v1\",\"id\":\"%s\",\"model\":%u,"
            "\"observed\":%s,\"widthBits\":%zu,\"widthBytes\":%zu,\"code\":",
            f->id, f->model, observed ? "true" : "false", width_bits, width_bytes);
    json_code(report, &code); fputs(",\"signatureCountsLE\":", report);
    if (!signatures(report, f->model)) goto done;
    fputs(",\"requests\":[", report);
    for (q = 0; q < f->query_count; ++q) {
        packed_lifecycle_bytes actual;
        if (!pad_word(&f->queries[q].left, width_bits, width_bytes, &left) ||
            !pad_word(&f->queries[q].right, width_bits, width_bytes, &right) ||
            !pad_word(&f->queries[q].expected, width_bits, width_bytes, &expected)) goto done;
        if (q == 0) {
            if (!status_ok(packed_lifecycle_build_first(f->model, f->input, f->count,
                bytes(&left), bytes(&right), (uint8_t)observed, &owner, &answer, &observation), "build-first")) goto done;
            /* Input buffers die at transfer, before any subsequent request. */
            free_inputs(f);
        } else if (!status_ok(packed_lifecycle_query(&owner, bytes(&left), bytes(&right),
                    (uint8_t)observed, &answer, &observation), "query")) goto done;
        actual = packed_lifecycle_result_bytes(answer);
        if (!actual.data || actual.size != width_bytes || memcmp(actual.data, expected.data, width_bytes)) {
            fail("expected packet mismatch query=%zu", q); goto done;
        }
        if (!!observation != !!observed) { fail("diagnostic ownership mode query=%zu", q); goto done; }
        if (!strict_info(owner, f->count, width_bits, &info)) goto done;
        if (!snapshot_take(owner, info.memory_extent, &current)) goto done;
        if (q && !snapshot_equal(&original, &current)) goto done;
        if (q) fputc(',', report);
        fprintf(report, "{\"index\":%zu,\"answerLE\":", q); json_bytes(report, actual);
        fputs(",\"owner\":", report); json_info(report, &info);
        fputs(",\"memoryLE\":", report); json_snapshot(report, &current);
        fputs(",\"observations\":", report);
        if (observed) {
            if (!observation_report(report, observation, q, &current)) goto done;
        } else fputs("null", report);
        fputc('}', report);
        packed_lifecycle_result_free(answer); answer = NULL;
        packed_lifecycle_observation_free(observation); observation = NULL;
        if (q == 0) { original = current; current.cells = NULL; current.count = 0; }
        else snapshot_free(&current);
        blob_free(&left); blob_free(&right); blob_free(&expected);
    }
    if (!inspect_code(&final_code)) goto done;
    for (q = 0; q < 2; ++q)
        if (final_code.programs[q].identity != code.programs[q].identity ||
            final_code.programs[q].capacity != code.programs[q].capacity)
            { fail("fixed code replaced model=%zu", q); goto done; }
    fputs("]}\n", report);
    if (ferror(report)) { fail("report write"); goto done; }
    ok = 1;
done:
    packed_lifecycle_result_free(answer);
    packed_lifecycle_observation_free(observation);
    packed_lifecycle_owner_free(&owner);
    snapshot_free(&original); snapshot_free(&current);
    blob_free(&left); blob_free(&right); blob_free(&expected);
    return ok;
}

static int startup(FILE *report) {
    packed_lifecycle_code_info info;
    if (!status_ok(packed_lifecycle_init(), "initialize") || !inspect_code(&info)) return 0;
    fputs("{\"schema\":\"lifecycle-native1-startup-v1\",\"code\":", report);
    json_code(report, &info);
    fputs(",\"wordSignaturesLE\":", report);
    if (!signatures(report, PACKED_LIFECYCLE_WORD)) return 0;
    fputs(",\"comparisonSignaturesLE\":", report);
    if (!signatures(report, PACKED_LIFECYCLE_COMPARISON)) return 0;
    fputs("}\n", report);
    return !ferror(report) || fail("startup report write");
}

static int abi_case(FILE *report, size_t *count, const char *id,
                    int expected, int actual, int handles_empty) {
    if ((*count)++) fputc(',', report);
    fprintf(report, "{\"id\":\"%s\",\"expectedStatus\":%d,\"actualStatus\":%d,"
            "\"handleOutputsEmpty\":%s}", id, expected, actual,
            handles_empty < 0 ? "null" : handles_empty ? "true" : "false");
    if (actual != expected) return fail("ABI boundary %s expected=%d actual=%d", id, expected, actual);
    if (handles_empty == 0) return fail("ABI boundary %s published rejected outputs", id);
    return 1;
}

static int abi_build_reject(FILE *report, size_t *cases, const char *id, int expected,
                            uint8_t model, const packed_lifecycle_int *input, size_t count,
                            packed_lifecycle_bytes left, packed_lifecycle_bytes right,
                            uint8_t observe, unsigned missing_output) {
    packed_lifecycle_owner *owner = NULL;
    packed_lifecycle_result *answer = NULL;
    packed_lifecycle_observation *observation = NULL;
    int status = packed_lifecycle_build_first(model, input, count, left, right, observe,
        missing_output == 1 ? NULL : &owner, missing_output == 2 ? NULL : &answer,
        missing_output == 3 ? NULL : &observation);
    int empty = owner == NULL && answer == NULL && observation == NULL;
    int ok = abi_case(report, cases, id, expected, status, empty);
    /* Cleanup is still required if a future implementation violates rejection. */
    packed_lifecycle_result_free(answer);
    packed_lifecycle_observation_free(observation);
    packed_lifecycle_owner_free(&owner);
    return ok;
}

#if defined(_WIN32)
typedef struct { int status; size_t bits, bytes; } abi_thread_profile;
static DWORD WINAPI abi_profile_thread(LPVOID argument) {
    abi_thread_profile *result = (abi_thread_profile *)argument;
    result->status = packed_lifecycle_profile(4096, &result->bits, &result->bytes);
    return 0;
}
#endif

/* Admission-only calls. Every build request below rejects before initialOwner;
   no healthy build or lifecycle evaluator is used as a hidden baseline. */
static int abi_boundaries(FILE *report) {
#if !defined(_WIN32)
    (void)report;
    return fail("ABI boundary controls require Windows");
#else
    uint8_t zero = 0;
    packed_lifecycle_int input = {0, {&zero, 1}};
    packed_lifecycle_int *many = NULL;
    blob left = {0}, right = {0}, oversized = {0};
    packed_lifecycle_bytes changed;
    size_t cases = 0, bits = 0, width = 0, max_bits = 0, max_bytes = 0, i;
    abi_thread_profile secondary = {-1, 1, 1};
    HANDLE thread = NULL;
    int status, ok = 0;
    fputs("{\"schema\":\"lifecycle-native1-abi-boundaries-v1\",\"cases\":[", report);
    if (!abi_case(report, &cases, "ABI-INIT", PACKED_LIFECYCLE_OK, packed_lifecycle_init(), -1)) goto done;
    status = packed_lifecycle_profile(4096, &max_bits, &max_bytes);
    if (!abi_case(report, &cases, "PROFILE-4096", PACKED_LIFECYCLE_OK, status, -1)) goto done;
    if (!max_bits || max_bits > SIZE_MAX - 7 || max_bytes != (max_bits + 7) / 8) {
        fail("ABI maximum-count profile relation"); goto done;
    }
    if (!abi_case(report, &cases, "PROFILE-4097", PACKED_LIFECYCLE_LIMIT,
                  packed_lifecycle_profile(4097, &bits, &width), -1) ||
        !abi_case(report, &cases, "PROFILE-SIZE-MAX", PACKED_LIFECYCLE_LIMIT,
                  packed_lifecycle_profile(SIZE_MAX, &bits, &width), -1) ||
        !abi_case(report, &cases, "PROFILE-NULL-BITS", PACKED_LIFECYCLE_FORMAT,
                  packed_lifecycle_profile(1, NULL, &width), -1) ||
        !abi_case(report, &cases, "PROFILE-NULL-BYTES", PACKED_LIFECYCLE_FORMAT,
                  packed_lifecycle_profile(1, &bits, NULL), -1) ||
        !abi_case(report, &cases, "PROFILE-ONE", PACKED_LIFECYCLE_OK,
                  packed_lifecycle_profile(1, &bits, &width), -1)) goto done;
    if (!bits || bits > SIZE_MAX - 7 || width != (bits + 7) / 8 || !width || width > 4096) {
        fail("ABI one-element profile relation"); goto done;
    }
    left.data = (uint8_t *)calloc(width + 1, 1);
    right.data = (uint8_t *)calloc(width + 1, 1);
    oversized.data = (uint8_t *)calloc(4097, 1);
    many = (packed_lifecycle_int *)calloc(4097, sizeof(*many));
    if (!left.data || !right.data || !oversized.data || !many) {
        fail("ABI boundary valid-buffer allocation"); goto done;
    }
    left.size = right.size = width; right.data[0] = 1; oversized.size = 4097;
    for (i = 0; i < 4097; ++i) many[i] = input;
    if (!abi_build_reject(report, &cases, "BUILD-NULL-OWNER", PACKED_LIFECYCLE_FORMAT,
            PACKED_LIFECYCLE_COMPARISON, &input, 1, bytes(&left), bytes(&right), 0, 1) ||
        !abi_build_reject(report, &cases, "BUILD-NULL-ANSWER", PACKED_LIFECYCLE_FORMAT,
            PACKED_LIFECYCLE_COMPARISON, &input, 1, bytes(&left), bytes(&right), 0, 2) ||
        !abi_build_reject(report, &cases, "BUILD-NULL-DIAGNOSTICS", PACKED_LIFECYCLE_FORMAT,
            PACKED_LIFECYCLE_COMPARISON, &input, 1, bytes(&left), bytes(&right), 0, 3) ||
        !abi_build_reject(report, &cases, "BUILD-COUNT-4097", PACKED_LIFECYCLE_LIMIT,
            PACKED_LIFECYCLE_COMPARISON, many, 4097, bytes(&left), bytes(&right), 0, 0)) goto done;
    input.magnitude = bytes(&oversized);
    if (!abi_build_reject(report, &cases, "BUILD-MAGNITUDE-4097", PACKED_LIFECYCLE_LIMIT,
            PACKED_LIFECYCLE_COMPARISON, &input, 1, bytes(&left), bytes(&right), 0, 0)) goto done;
    input.magnitude.data = &zero; input.magnitude.size = 1; input.negative = 2;
    if (!abi_build_reject(report, &cases, "BUILD-SIGN-2", PACKED_LIFECYCLE_FORMAT,
            PACKED_LIFECYCLE_COMPARISON, &input, 1, bytes(&left), bytes(&right), 0, 0)) goto done;
    input.negative = 1;
    if (!abi_build_reject(report, &cases, "BUILD-NEGATIVE-ZERO", PACKED_LIFECYCLE_FORMAT,
            PACKED_LIFECYCLE_COMPARISON, &input, 1, bytes(&left), bytes(&right), 0, 0)) goto done;
    input.negative = 0; input.magnitude.size = 0;
    if (!abi_build_reject(report, &cases, "BUILD-EMPTY-MAGNITUDE", PACKED_LIFECYCLE_FORMAT,
            PACKED_LIFECYCLE_COMPARISON, &input, 1, bytes(&left), bytes(&right), 0, 0)) goto done;
    input.magnitude.size = 1;
    changed = bytes(&left); changed.size = width - 1;
    if (!abi_build_reject(report, &cases, "BUILD-LEFT-SHORT", PACKED_LIFECYCLE_FORMAT,
            PACKED_LIFECYCLE_COMPARISON, &input, 1, changed, bytes(&right), 0, 0)) goto done;
    changed.size = width + 1;
    if (!abi_build_reject(report, &cases, "BUILD-LEFT-LONG", PACKED_LIFECYCLE_FORMAT,
            PACKED_LIFECYCLE_COMPARISON, &input, 1, changed, bytes(&right), 0, 0)) goto done;
    changed = bytes(&right); changed.size = width - 1;
    if (!abi_build_reject(report, &cases, "BUILD-RIGHT-SHORT", PACKED_LIFECYCLE_FORMAT,
            PACKED_LIFECYCLE_COMPARISON, &input, 1, bytes(&left), changed, 0, 0)) goto done;
    changed.size = width + 1;
    if (!abi_build_reject(report, &cases, "BUILD-RIGHT-LONG", PACKED_LIFECYCLE_FORMAT,
            PACKED_LIFECYCLE_COMPARISON, &input, 1, bytes(&left), changed, 0, 0) ||
        !abi_build_reject(report, &cases, "BUILD-MODEL-2", PACKED_LIFECYCLE_FORMAT,
            2, &input, 1, bytes(&left), bytes(&right), 0, 0) ||
        !abi_build_reject(report, &cases, "BUILD-OBSERVE-2", PACKED_LIFECYCLE_FORMAT,
            PACKED_LIFECYCLE_COMPARISON, &input, 1, bytes(&left), bytes(&right), 2, 0)) goto done;
    thread = CreateThread(NULL, 0, abi_profile_thread, &secondary, 0, NULL);
    if (!thread) { fail("ABI secondary thread creation error=%lu", (unsigned long)GetLastError()); goto done; }
    /* The external owned-process stage bounds this join. The worker only calls
       the documented thread-rejection path, and no owner crosses the thread. */
    if (WaitForSingleObject(thread, INFINITE) != WAIT_OBJECT_0) {
        fail("ABI secondary thread join error=%lu", (unsigned long)GetLastError()); goto done;
    }
    CloseHandle(thread); thread = NULL;
    if (!abi_case(report, &cases, "THREAD-SECONDARY-PROFILE", PACKED_LIFECYCLE_THREAD, secondary.status, -1)) goto done;
    if (secondary.bits != 1 || secondary.bytes != 1) { fail("ABI rejected thread modified profile outputs"); goto done; }
    status = packed_lifecycle_profile(4096, &bits, &width);
    if (!abi_case(report, &cases, "THREAD-INITIALIZING-PROFILE", PACKED_LIFECYCLE_OK, status, -1)) goto done;
    if (bits != max_bits || width != max_bytes) { fail("ABI initializing-thread profile changed"); goto done; }
    if (cases != 23) { fail("ABI boundary case roster count=%zu", cases); goto done; }
    /* After both individual bounds hold, count*magnitude <=4096*4096 equals
       the total cap. A larger admitted total is mathematically unreachable. */
    fprintf(report, "],\"caseCount\":%zu,\"profile4096\":{\"widthBits\":%zu,\"widthBytes\":%zu},"
            "\"secondaryProfileOutputsUnchanged\":true,\"totalMagnitudeOverflow\":{"
            "\"reachableAfterIndividualBounds\":false,\"countLimit\":4096,"
            "\"magnitudeLimit\":4096,\"maximumProduct\":16777216,\"totalLimit\":16777216}}\n",
            cases, max_bits, max_bytes);
    if (ferror(report)) { fail("ABI boundary report write"); goto done; }
    ok = 1;
done:
    if (thread) { WaitForSingleObject(thread, INFINITE); CloseHandle(thread); }
    free(many); blob_free(&left); blob_free(&right); blob_free(&oversized);
    return ok;
#endif
}

#ifdef PACKED_LIFECYCLE_TESTING
static const char *const control_names[] = {
    "none", "skip-repack", "extra-owner-alias", "retain-input", "retain-old-arena",
    "retain-keys", "retain-history", "wrong-copy-value", "wrong-copy-offset", "partial-copy",
    "fail-after-take", "model-fault", "exhausted", "fail-before-take-alloc",
    "fail-before-publish", "shared-scalar-accept", "endpoint-short", "endpoint-long",
    "negative-zero", "bad-sign", "word-inputfits"
};

static int control_number(const char *name, uint32_t *mode) {
    size_t i;
    for (i = 0; i < sizeof(control_names) / sizeof(control_names[0]); ++i)
        if (!strcmp(name, control_names[i])) { *mode = (uint32_t)i; return 1; }
    return fail("unknown control=%s", name);
}

static int decimal_size(const char *text, size_t *out) {
    size_t n = 0, i;
    if (!*text) return fail("empty argument");
    for (i = 0; text[i]; ++i) {
        unsigned digit;
        if (text[i] < '0' || text[i] > '9') return fail("argument must be unsigned decimal");
        digit = (unsigned)(text[i] - '0');
        if (n > (SIZE_MAX - digit) / 10) return fail("argument overflow");
        n = n * 10 + digit;
    }
    *out = n;
    return 1;
}

static void json_test_info(FILE *report, const packed_lifecycle_test_info *info) {
    size_t i;
    /* Retained-root fields preserve observations at the publication predicate.
       They are historical after cleanup; cleanupComplete and live resource
       counts describe the completed release, without erasing that evidence. */
    fputs("{\"source\":[", report);
    for (i = 0; i < 4; ++i) { if (i) fputc(',', report); json_array_info(report, &info->source[i]); }
    fputs("],\"replacement\":[", report);
    for (i = 0; i < 4; ++i) { if (i) fputc(',', report); json_array_info(report, &info->replacement[i]); }
    fprintf(report, "],\"copiedEntries\":%zu,\"initializedEntries\":%zu,\"releasedEntries\":%zu,"
            "\"temporaryArraysCreated\":%zu,\"temporaryArraysReleased\":%zu,\"temporaryArraysLive\":%zu,"
            "\"nativeHandlesCreated\":%zu,\"nativeHandlesReleased\":%zu,\"nativeHandlesLive\":%zu,"
            "\"retainedOwnerRoots\":%zu,\"retainedInputRoots\":%zu,\"retainedArenaRoots\":%zu,"
            "\"retainedKeyRoots\":%zu,\"retainedHistoryRoots\":%zu,\"retainedScalarRoots\":%zu,"
            "\"firstMismatchArray\":%zu,\"firstMismatchIndex\":%zu,"
            "\"sourceCopyCalls\":%" PRIu64 ",\"sourceCopyCells\":%" PRIu64 ","
            "\"sourceCopyCapacityTotal\":%" PRIu64 ",\"sourceCopyCapacityMax\":%" PRIu64 ","
            "\"sourceCopyExpands\":%" PRIu64 ","
            "\"ownerExclusive\":%u,\"arraysExact\":%u,\"valuesEqual\":%u,"
            "\"strictPublication\":%u,\"cleanupComplete\":%u,\"copyCounterOverflow\":%u}",
            info->copied_entries, info->initialized_entries, info->released_entries,
            info->temporary_arrays_created, info->temporary_arrays_released, info->temporary_arrays_live,
            info->native_handles_created, info->native_handles_released, info->native_handles_live,
            info->retained_owner_roots, info->retained_input_roots, info->retained_arena_roots,
            info->retained_key_roots, info->retained_history_roots, info->retained_scalar_roots,
            info->first_mismatch_array, info->first_mismatch_index,
            info->source_copy_calls, info->source_copy_cells,
            info->source_copy_capacity_total, info->source_copy_capacity_max, info->source_copy_expands,
            info->owner_exclusive, info->arrays_exact, info->values_equal,
            info->strict_publication, info->cleanup_complete, info->copy_counter_overflow);
}

/* Discovery records observations only. Ordinary exit zero here does not mean
   that a mutation was rejected or any acceptance row was discharged. */
static int control_discover(FILE *report, uint32_t mode, int query_phase, size_t argument) {
    uint8_t three = 3, one = 1, seven = 7, zero = 0;
    uint8_t wide[4096];
    uint8_t model = mode == 20 ? PACKED_LIFECYCLE_WORD : PACKED_LIFECYCLE_COMPARISON;
    packed_lifecycle_int input[4] = {{0,{&three,1}},{1,{&one,1}},{1,{&one,1}},{0,{&seven,1}}};
    packed_lifecycle_owner *owner = NULL;
    packed_lifecycle_result *answer = NULL;
    packed_lifecycle_observation *observation = NULL;
    packed_lifecycle_info baseline_info = {0}, live_info = {0};
    packed_lifecycle_test_info before_cleanup = {0}, after_cleanup = {0};
    packed_lifecycle_bytes left_view, right_view;
    blob left = {0}, right = {0};
    snapshot baseline = {0}, current = {0};
    size_t width_bits = 0, width_bytes = 0;
    uintptr_t original_identity = 0, actual_identity = 0;
    int actual_status = -1, live_predicate = 0, memory_equal = 0, ok = 0;
    int baseline_built = 0;
    const int baseline_needed = query_phase ||
        (mode != PACKED_LIFECYCLE_TEST_EXHAUSTED && mode != PACKED_LIFECYCLE_TEST_MODEL_FAULT);
    char predicate_diagnostic[1024] = "";
    if (!status_ok(packed_lifecycle_init(), "control-initialize") ||
        !status_ok(packed_lifecycle_profile(4, &width_bits, &width_bytes), "control-profile")) goto done;
    if (!width_bytes || width_bytes >= 4096) { fail("control profile width"); goto done; }
    left.data = (uint8_t *)calloc(width_bytes + 1, 1);
    right.data = (uint8_t *)calloc(width_bytes + 1, 1);
    if (!left.data || !right.data) { fail("control endpoint allocation"); goto done; }
    left.size = right.size = width_bytes; right.data[0] = 4;
    /* Bounded initial-owner/fuel probes must not hide a full healthy run. */
    if (baseline_needed) {
        if (!status_ok(packed_lifecycle_test_configure(PACKED_LIFECYCLE_TEST_NONE, 0), "baseline-configure")) goto done;
        if (!status_ok(packed_lifecycle_build_first(model, input, 4, bytes(&left), bytes(&right), 1,
                         &owner, &answer, &observation), "baseline-build")) goto done;
        if (!equal_small(packed_lifecycle_result_bytes(answer), 2)) { fail("control baseline packet"); goto done; }
        if (!strict_info(owner, 4, width_bits, &baseline_info) ||
            !snapshot_take(owner, baseline_info.memory_extent, &baseline)) goto done;
        baseline_built = 1;
        packed_lifecycle_result_free(answer); answer = NULL;
        packed_lifecycle_observation_free(observation); observation = NULL;
        original_identity = (uintptr_t)owner;
        if (!query_phase) packed_lifecycle_owner_free(&owner);
    }
    if (!status_ok(packed_lifecycle_test_configure(mode <= 15 ? mode : PACKED_LIFECYCLE_TEST_NONE,
                                                  argument), "control-configure")) goto done;
    left_view = bytes(&left); right_view = bytes(&right);
    if (mode == 16) left_view.size = width_bytes - 1;
    if (mode == 17) left_view.size = width_bytes + 1;
    if (mode == 18) { input[0].negative = 1; input[0].magnitude.data = &zero; }
    if (mode == 19) input[0].negative = 2;
    if (mode == 20) {
        memset(wide, 255, sizeof(wide));
        input[0].magnitude.data = wide; input[0].magnitude.size = sizeof(wide);
    }
    if (query_phase)
        actual_status = packed_lifecycle_query(&owner, left_view, right_view, 1, &answer, &observation);
    else
        actual_status = packed_lifecycle_build_first(model, input, 4, left_view, right_view, 1,
                                                     &owner, &answer, &observation);
    actual_identity = (uintptr_t)owner;
    if (!status_ok(packed_lifecycle_test_receipt(&before_cleanup), "control-receipt-before")) goto done;
    if (owner) {
        live_predicate = strict_info(owner, 4, width_bits, &live_info);
        if (!live_predicate) { snprintf(predicate_diagnostic, sizeof(predicate_diagnostic), "%s", error_text); error_text[0] = 0; }
        if (!snapshot_take(owner, live_info.arrays[1].initialized, &current)) goto done;
        if (baseline_built) {
            memory_equal = snapshot_equal(&baseline, &current);
            if (!memory_equal) error_text[0] = 0;
        }
    }
    fprintf(report, "{\"schema\":\"lifecycle-native1-control-discovery-v1\",\"control\":\"%s\","
            "\"phase\":\"%s\",\"argument\":%zu,\"actualStatus\":%d,"
            "\"baselineBuilt\":%s,\"baselineOwnerIdentity\":",
            control_names[mode], query_phase ? "query" : "build", argument, actual_status,
            baseline_built ? "true" : "false");
    if (baseline_built) fprintf(report, "\"0x%" PRIxPTR "\"", original_identity);
    else fputs("null", report);
    fprintf(report, ",\"returnedOwnerIdentity\":\"0x%" PRIxPTR "\","
            "\"ownerPresent\":%s,\"sameOwnerIdentity\":%s,\"answerPresent\":%s,\"observationPresent\":%s,"
            "\"liveStrictPredicate\":%s,\"livePredicateDiagnostic\":\"%s\",\"memoryEqual\":%s,"
            "\"baselineInfo\":",
            actual_identity, owner ? "true" : "false",
            query_phase && owner && original_identity == actual_identity ? "true" : "false",
            answer ? "true" : "false", observation ? "true" : "false",
            live_predicate ? "true" : "false", predicate_diagnostic,
            baseline_built ? (memory_equal ? "true" : "false") : "null");
    if (baseline_built) json_info(report, &baseline_info); else fputs("null", report);
    fputs(",\"baselineMemoryLE\":", report);
    if (baseline_built) json_snapshot(report, &baseline); else fputs("null", report);
    fputs(",\"returnedInfo\":", report); if (owner) json_info(report, &live_info); else fputs("null", report);
    fputs(",\"returnedMemoryLE\":", report); if (owner) json_snapshot(report, &current); else fputs("null", report);
    fputs(",\"answerLE\":", report);
    if (answer) json_bytes(report, packed_lifecycle_result_bytes(answer)); else fputs("null", report);
    fputs(",\"beforeCleanup\":", report); json_test_info(report, &before_cleanup);
    packed_lifecycle_result_free(answer); answer = NULL;
    packed_lifecycle_observation_free(observation); observation = NULL;
    packed_lifecycle_owner_free(&owner);
    if (!status_ok(packed_lifecycle_test_receipt(&after_cleanup), "control-receipt-after")) goto done;
    fputs(",\"afterCleanup\":", report); json_test_info(report, &after_cleanup);
    fputs(",\"acceptanceVerdict\":\"not-assigned-discovery-only\"}\n", report);
    if (ferror(report)) { fail("control report write"); goto done; }
    ok = 1;
done:
    packed_lifecycle_result_free(answer);
    packed_lifecycle_observation_free(observation);
    packed_lifecycle_owner_free(&owner);
    snapshot_free(&baseline); snapshot_free(&current);
    blob_free(&left); blob_free(&right);
    return ok;
}
#endif

int main(int argc, char **argv) {
    const char *fixture_path = NULL, *report_path = NULL;
    const char *control_name = NULL, *phase_name = NULL, *argument_text = NULL;
    int observed = -1, startup_mode = 0, abi_mode = 0, i, ok = 0;
#ifdef PACKED_LIFECYCLE_TESTING
    uint32_t control_mode = 0;
    size_t control_argument = 0;
#endif
    FILE *report = NULL;
    fixture f = {0};
#if defined(_WIN32)
    _setmode(_fileno(stdout), _O_BINARY);
    _setmode(_fileno(stderr), _O_BINARY);
#endif
    for (i = 1; i < argc; ++i) {
        if (!strcmp(argv[i], "--startup") && !startup_mode) startup_mode = 1;
        else if (!strcmp(argv[i], "--abi-boundaries") && !abi_mode) abi_mode = 1;
        else if (!strcmp(argv[i], "--fixture") && !fixture_path && i + 1 < argc) fixture_path = argv[++i];
        else if (!strcmp(argv[i], "--report") && !report_path && i + 1 < argc) report_path = argv[++i];
        else if (!strcmp(argv[i], "--control") && !control_name && i + 1 < argc) control_name = argv[++i];
        else if (!strcmp(argv[i], "--phase") && !phase_name && i + 1 < argc) phase_name = argv[++i];
        else if (!strcmp(argv[i], "--argument") && !argument_text && i + 1 < argc) argument_text = argv[++i];
        else if (!strcmp(argv[i], "--observed") && observed == -1 && i + 1 < argc) {
            const char *value = argv[++i];
            if (!strcmp(value, "0")) observed = 0;
            else if (!strcmp(value, "1")) observed = 1;
            else { fail("observed must be 0 or 1"); goto done; }
        } else { fail("unknown/duplicate/missing argument=%s", argv[i]); goto done; }
    }
    if (control_name) {
#ifdef PACKED_LIFECYCLE_TESTING
        if (!report_path || !*report_path || startup_mode || abi_mode || fixture_path || observed != -1 ||
            !phase_name || (strcmp(phase_name, "build") && strcmp(phase_name, "query")) || !argument_text) {
            fail("control requires --phase build|query --argument decimal --report path"); goto done;
        }
        if (!control_number(control_name, &control_mode) || !decimal_size(argument_text, &control_argument)) goto done;
        if (!strcmp(phase_name, "query") && ((control_mode >= 11 && control_mode <= 12) || control_mode >= 18)) {
            fail("control requires build phase"); goto done;
        }
#else
        fail("control requires testing ABI"); goto done;
#endif
    } else if (phase_name || argument_text || !report_path || !*report_path ||
        (abi_mode ? (startup_mode || fixture_path || observed != -1) :
         startup_mode ? (fixture_path || observed != -1) : (!fixture_path || !*fixture_path || observed == -1))) {
        fail("usage: --startup OR --abi-boundaries with --report path; OR --fixture path --report path --observed 0|1"); goto done;
    }
    /* Validate the entire fixture before runtime acquisition or report writes. */
    if (!startup_mode && !abi_mode && !control_name && !fixture_load(fixture_path, &f)) goto done;
    report = fopen(report_path, "wb");
    if (!report) { fail("report open errno=%d", errno); goto done; }
    if (control_name) {
#ifdef PACKED_LIFECYCLE_TESTING
        ok = control_discover(report, control_mode, !strcmp(phase_name, "query"), control_argument);
#endif
    } else if (abi_mode) ok = abi_boundaries(report);
    else ok = startup_mode ? startup(report) : exercise(&f, observed, report);
    if (fclose(report) != 0) { ok = fail("report close"); }
    report = NULL;
done:
    if (report) fclose(report);
    fixture_free(&f);
    if (!ok) {
        fprintf(stderr, "LIFE-NATIVE1 FAIL %s\n", *error_text ? error_text : "unspecified client failure");
        return 1;
    }
    if (control_name) printf("LIFE-NATIVE1 CONTROL %s %s OBSERVED\n", control_name, phase_name);
    else if (abi_mode) fputs("LIFE-NATIVE1 ABI-BOUNDARIES PASS\n", stdout);
    else if (startup_mode) fputs("LIFE-NATIVE1 STARTUP PASS\n", stdout);
    else printf("LIFE-NATIVE1 PASS %s\n", f.id);
    return 0;
}
