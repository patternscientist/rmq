#include <lean/lean.h>
#include <stdint.h>
#include "include/packed_rmq.h"

/* Build validation checks these exact exported prototypes against emitted C. */
extern void lean_initialize_runtime_module(void);
extern lean_obj_res initialize_RMQ_Core_WordRAM_Native_Entry(uint8_t, lean_obj_arg);
extern lean_obj_res rmq_native_load(lean_obj_arg);
extern lean_obj_res rmq_native_query(lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg, uint8_t);
extern size_t rmq_native_word_bytes(lean_obj_arg);

static int native_init_state = 0;

int packed_rmq_init(void) {
    if (native_init_state != 0) return native_init_state == 1 ? 0 : 1;
    native_init_state = -1;
    lean_initialize_runtime_module();
    lean_object *result = initialize_RMQ_Core_WordRAM_Native_Entry(1, lean_io_mk_world());
    lean_io_mark_end_initialization();
    if (lean_io_result_is_error(result)) {
        lean_dec_ref(result);
        return 1;
    }
    lean_dec_ref(result);
    lean_init_task_manager_using(1);
    native_init_state = 1;
    return 0;
}

static lean_object *copy_bytes(const uint8_t *bytes, size_t length) {
    lean_object *result = lean_alloc_sarray(1, length, length);
    uint8_t *target = lean_sarray_cptr(result);
    for (size_t index = 0; index < length; ++index) target[index] = bytes[index];
    return result;
}

packed_rmq_load_result *packed_rmq_load(const uint8_t *bytes, size_t length) {
    if (native_init_state != 1 || (!bytes && length != 0) || length > 134217728) return NULL;
    return (packed_rmq_load_result *)rmq_native_load(copy_bytes(bytes, length));
}

int packed_rmq_load_status(const packed_rmq_load_result *result) {
    if (!result) return 2;
    return lean_obj_tag((lean_object *)result) == 1 ? 0 : 1;
}

const char *packed_rmq_load_error(const packed_rmq_load_result *result) {
    return packed_rmq_load_status(result) == 1
        ? lean_string_cstr(lean_ctor_get((lean_object *)result, 0)) : NULL;
}

const packed_rmq_image *packed_rmq_loaded_image(const packed_rmq_load_result *result) {
    return packed_rmq_load_status(result) == 0
        ? (const packed_rmq_image *)lean_ctor_get((lean_object *)result, 0) : NULL;
}

void packed_rmq_load_free(packed_rmq_load_result *result) {
    if (result) lean_dec((lean_object *)result);
}

size_t packed_rmq_word_bytes(const packed_rmq_image *image) {
    if (native_init_state != 1 || !image) return 0;
    lean_inc((lean_object *)image);
    return rmq_native_word_bytes((lean_object *)image);
}

packed_rmq_query_result *packed_rmq_query(const packed_rmq_image *image,
    const uint8_t *left, size_t left_length, const uint8_t *right, size_t right_length,
    size_t fuel, uint8_t reads) {
    if (native_init_state != 1 || !image || (!left && left_length != 0) ||
        (!right && right_length != 0) || left_length > 512 || right_length > 512 ||
        fuel > 1000000 || reads > 1) return NULL;
    /* The load result retains its image; the pure Lean call receives a new
       owned reference and may release it without invalidating the handle. */
    lean_inc((lean_object *)image);
    return (packed_rmq_query_result *)rmq_native_query((lean_object *)image,
        copy_bytes(left, left_length), copy_bytes(right, right_length), lean_usize_to_nat(fuel), reads);
}

int packed_rmq_query_status(const packed_rmq_query_result *result) {
    if (!result) return 2;
    return lean_obj_tag((lean_object *)result) == 1 ? 0 : 1;
}

const char *packed_rmq_query_text(const packed_rmq_query_result *result) {
    return result ? lean_string_cstr(lean_ctor_get((lean_object *)result, 0)) : NULL;
}

void packed_rmq_query_free(packed_rmq_query_result *result) {
    if (result) lean_dec((lean_object *)result);
}
