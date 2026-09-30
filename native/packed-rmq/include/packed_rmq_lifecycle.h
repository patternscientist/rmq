#ifndef PACKED_RMQ_LIFECYCLE_H
#define PACKED_RMQ_LIFECYCLE_H
#include <stddef.h>
#include <stdint.h>
#if defined(_WIN32)
# if defined(PACKED_LIFECYCLE_BUILD)
#  define PACKED_LIFECYCLE_API __declspec(dllexport)
# else
#  define PACKED_LIFECYCLE_API __declspec(dllimport)
# endif
#else
# define PACKED_LIFECYCLE_API
#endif
#ifdef __cplusplus
extern "C" {
#endif

/* Windows x64, pinned Lean 4.22. All operations, accessors and destruction run
   on the successful initializing thread. Foreign callers provide valid live
   pointers, only live handles returned by this ABI, and exclusive mutable access.
   The ABI cannot enforce those preconditions against arbitrary C misuse. */
typedef struct packed_lifecycle_owner packed_lifecycle_owner;
typedef struct packed_lifecycle_result packed_lifecycle_result;
typedef struct packed_lifecycle_observation packed_lifecycle_observation;

typedef struct packed_lifecycle_bytes {
    const uint8_t *data;
    size_t size;
} packed_lifecycle_bytes;

/* Little-endian unsigned magnitude, 1..4096 bytes; high zero padding allowed.
   negative is exactly 0 or 1, and negative zero is malformed. */
typedef struct packed_lifecycle_int {
    uint8_t negative;
    packed_lifecycle_bytes magnitude;
} packed_lifecycle_int;

enum packed_lifecycle_model {
    PACKED_LIFECYCLE_WORD = 0,
    PACKED_LIFECYCLE_COMPARISON = 1
};
enum packed_lifecycle_error {
    PACKED_LIFECYCLE_OK = 0,
    PACKED_LIFECYCLE_FORMAT = 1,
    PACKED_LIFECYCLE_INPUT_DOMAIN = 2,
    PACKED_LIFECYCLE_LIMIT = 3,
    PACKED_LIFECYCLE_THREAD = 4,
    PACKED_LIFECYCLE_INITIALIZATION = 5,
    PACKED_LIFECYCLE_STATE = 6,
    PACKED_LIFECYCLE_MODEL_FAULT = 7,
    PACKED_LIFECYCLE_FUEL_EXHAUSTED = 8,
    PACKED_LIFECYCLE_ALLOCATION = 9,
    PACKED_LIFECYCLE_CONTROLLED_FAILURE = 10
};

/* One initialization attempt per DLL. The safe Rust facade additionally shares
   its sticky process-level acquisition guard with the older crate runtimes. */
PACKED_LIFECYCLE_API int packed_lifecycle_init(void);

/* Count is checked <=4096. Query-independent bit width comes from Lean's
   wordWidth count; endpoint and answer bytes have exactly ceil(width/8) bytes.
   Unused high bits must be zero. No endpoint is converted through u64/u128. */
PACKED_LIFECYCLE_API int packed_lifecycle_profile(size_t count,
    size_t *width_bits, size_t *width_bytes);

/* Build executes the actual constructor/finalizer AND first query. The input
   buffers are borrowed only for this call; no input/list root is retained.
   total magnitude bytes <=16777216. Word-model InputFits failure rejects;
   comparison model accepts either sign and every finite format-admitted key.

   All three output slots must be nonnull and initially empty. observe is 0/1.
   Success publishes one halted, repacked owner, one independent answer buffer,
   and (only if requested) one separately owned diagnostic object. Represented
   invalid ranges succeed with the ordinary zero/None packet. Failure leaves
   all outputs empty. Lean runtime allocation failure is not recoverable here;
   it may terminate the process. ALLOCATION covers checked native malloc failures. */
PACKED_LIFECYCLE_API int packed_lifecycle_build_first(uint8_t model,
    const packed_lifecycle_int *input, size_t count,
    packed_lifecycle_bytes left, packed_lifecycle_bytes right, uint8_t observe,
    packed_lifecycle_owner **owner, packed_lifecycle_result **answer,
    packed_lifecycle_observation **diagnostics);

/* Query requires unique access to *owner and initially empty result slots.
   Format/resource/admission rejection before transfer preserves *owner.
   After irrevocable take, *owner is cleared. Success publishes exactly one
   replacement through the same value-preserving repacking helper; failure
   leaves *owner empty and releases all initialized temporary resources.
   This executes the existing four charged request/control events plus service.
   A valid later request remains possible after an admitted invalid range. */
PACKED_LIFECYCLE_API int packed_lifecycle_query(packed_lifecycle_owner **owner,
    packed_lifecycle_bytes left, packed_lifecycle_bytes right, uint8_t observe,
    packed_lifecycle_result **answer, packed_lifecycle_observation **diagnostics);

/* The answer is the actual halted Nat packet encoded without narrowing:
   zero means None; nonzero is the leftmost minimum index plus one. The view
   borrows its result object (not the owner) and expires on result_free. */
PACKED_LIFECYCLE_API packed_lifecycle_bytes packed_lifecycle_result_bytes(
    const packed_lifecycle_result *answer);
PACKED_LIFECYCLE_API void packed_lifecycle_result_free(packed_lifecycle_result *answer);
PACKED_LIFECYCLE_API void packed_lifecycle_owner_free(packed_lifecycle_owner **owner);
PACKED_LIFECYCLE_API void packed_lifecycle_observation_free(packed_lifecycle_observation *diagnostics);

/* Snapshot scalars describe actual native representation; requested array
   storage is sizeof(array header)+capacity*sizeof(pointer). It is neither
   allocator usable size nor RSS. Array order: regs, memory, keys, keyRegs.
   n and memory extent are read from produced metadata, never caller copies.
   Numeric addresses are opaque identity receipts only; callers must not
   dereference them or turn them into aliases. */
typedef struct packed_lifecycle_array_info {
    size_t initialized, capacity, requested_bytes;
    uintptr_t identity;
} packed_lifecycle_array_info;
typedef struct packed_lifecycle_info {
    size_t count, memory_extent, width_bits;
    packed_lifecycle_array_info arrays[4];
    size_t reachable_objects, scalar_occurrences, boxed_integers;
    size_t runtime_reported_object_bytes;
    size_t repacked_arrays, copied_entries;
    uint8_t exclusive_owner, exact_capacities, no_retained_operational_roots;
    size_t boxed_digit_requested_bytes;
} packed_lifecycle_info;
PACKED_LIFECYCLE_API int packed_lifecycle_inspect(const packed_lifecycle_owner *owner,
    packed_lifecycle_info *info);
/* Copies one actual modeled memory cell into an independent arbitrary-width
   result. A missing cell has has_value=0 and value=NULL. This read-only
   diagnostic operation does not retain an owner or reset machine state. */
PACKED_LIFECYCLE_API int packed_lifecycle_memory_cell(const packed_lifecycle_owner *owner,
    size_t index, uint8_t *has_value, packed_lifecycle_result **value);

/* The two fixed program graphs are deduplicated together. A second traversal
   deduplicates all initialized RMQ globals from the compiled Entry closure,
   including persistent source-list spines outside those two array roots.
   Compiler-generated read-only visitors expose these roots without retaining
   new references. Standard-library/runtime infrastructure is outside this RMQ
   global graph. The two traversals overlap; do not add them. Boxed digit storage
   uses the verified pinned GMP runtime layout and allocated limb capacity.
   These numbers are not RSS. */
typedef struct packed_lifecycle_code_info {
    packed_lifecycle_array_info programs[2];
    size_t reachable_objects, scalar_occurrences, boxed_integers;
    size_t runtime_reported_object_bytes, boxed_digit_requested_bytes;
    size_t fixed_global_roots, fixed_reachable_objects;
    size_t fixed_runtime_reported_object_bytes, fixed_boxed_digit_requested_bytes;
} packed_lifecycle_code_info;
PACKED_LIFECYCLE_API int packed_lifecycle_inspect_code(packed_lifecycle_code_info *info);

/* Diagnostic values are encoded as canonical little-endian magnitudes with
   at least one byte. The returned buffer belongs to a new independent result.
   Counter IDs 0..14 are read/register/arithmetic/comparison/branch/control/
   write/allocation/keyRead/oracleComparison/numericRelease/keyRelease/
   keyRegisterRelease/requestAdmission/controlEntry. ID15 is total steps.
   A missing read reply is explicit, never confused with the numeric value0. */
PACKED_LIFECYCLE_API int packed_lifecycle_observation_counter(
    const packed_lifecycle_observation *diagnostics, uint8_t category,
    packed_lifecycle_result **value);
PACKED_LIFECYCLE_API int packed_lifecycle_observation_read_count(
    const packed_lifecycle_observation *diagnostics, size_t *count);
PACKED_LIFECYCLE_API int packed_lifecycle_observation_read(
    const packed_lifecycle_observation *diagnostics, size_t index,
    packed_lifecycle_result **address, uint8_t *has_reply,
    packed_lifecycle_result **reply);

/* Route IDs0..12: compact query, service prepare, service setup, builder,
   descriptor, finalizer, retirement, same-block discriminator, cross-block
   discriminator, interior-nonempty discriminator, interior-empty discriminator,
   interior-reader marker, crossing second load. These count actual matching
   transition instructions/prestates. Decision labels require the corresponding
   signature count to be one; a decision alone does not assert a later read. */
PACKED_LIFECYCLE_API int packed_lifecycle_observation_route(
    const packed_lifecycle_observation *diagnostics, uint8_t route,
    packed_lifecycle_result **value);
PACKED_LIFECYCLE_API int packed_lifecycle_signature_count(uint8_t model,
    uint8_t route, packed_lifecycle_result **value);

#ifdef PACKED_LIFECYCLE_TESTING
/* Validation-only controls operate inside the same transfer/copy/publish
   helpers. A mutation is rejected by the ordinary publication predicate, not
   merely because a control mode is nonzero. Foreign misuse is not simulated by
   dereferencing released objects. Configure only on the initializing thread. */
enum packed_lifecycle_test_mode {
    PACKED_LIFECYCLE_TEST_NONE = 0,
    PACKED_LIFECYCLE_TEST_SKIP_REPACK = 1,
    PACKED_LIFECYCLE_TEST_EXTRA_OWNER_ALIAS = 2,
    PACKED_LIFECYCLE_TEST_RETAIN_INPUT = 3,
    PACKED_LIFECYCLE_TEST_RETAIN_OLD_ARENA = 4,
    PACKED_LIFECYCLE_TEST_RETAIN_KEYS = 5,
    PACKED_LIFECYCLE_TEST_RETAIN_HISTORY = 6,
    PACKED_LIFECYCLE_TEST_WRONG_COPY_VALUE = 7,
    PACKED_LIFECYCLE_TEST_WRONG_COPY_OFFSET = 8,
    PACKED_LIFECYCLE_TEST_PARTIAL_COPY = 9,
    PACKED_LIFECYCLE_TEST_FAIL_AFTER_TAKE = 10,
    PACKED_LIFECYCLE_TEST_MODEL_FAULT = 11,
    PACKED_LIFECYCLE_TEST_EXHAUSTED = 12,
    PACKED_LIFECYCLE_TEST_FAIL_BEFORE_TAKE_ALLOC = 13,
    PACKED_LIFECYCLE_TEST_FAIL_BEFORE_PUBLISH = 14,
    PACKED_LIFECYCLE_TEST_SHARED_SCALAR_ACCEPT = 15
};
typedef struct packed_lifecycle_test_info {
    packed_lifecycle_array_info source[4], replacement[4];
    size_t copied_entries, initialized_entries, released_entries;
    size_t temporary_arrays_created, temporary_arrays_released, temporary_arrays_live;
    size_t native_handles_created, native_handles_released, native_handles_live;
    size_t retained_owner_roots, retained_input_roots, retained_arena_roots;
    size_t retained_key_roots, retained_history_roots;
    size_t first_mismatch_array, first_mismatch_index;
    uint64_t source_copy_calls, source_copy_cells;
    uint8_t owner_exclusive, arrays_exact, values_equal, strict_publication;
    uint8_t cleanup_complete, copy_counter_overflow;
    size_t retained_scalar_roots;
    uint64_t source_copy_capacity_total, source_copy_capacity_max, source_copy_expands;
} packed_lifecycle_test_info;
PACKED_LIFECYCLE_API int packed_lifecycle_test_configure(uint32_t mode, size_t argument);
PACKED_LIFECYCLE_API int packed_lifecycle_test_receipt(packed_lifecycle_test_info *info);
#endif

#ifdef __cplusplus
}
#endif
#endif
