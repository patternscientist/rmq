#include <lean/lean.h>
#include <stdint.h>
#include "include/packed_rmq_route.h"

/* The initializer and pure entry prototypes are checked against emitted C. */
extern void lean_initialize_runtime_module(void);
extern lean_obj_res initialize_RMQ_Core_WordRAM_Native_Route(uint8_t, lean_obj_arg);
extern lean_obj_res rmq_native_route(lean_obj_arg, lean_obj_arg, uint8_t);

/* Experiment contract: one calling OS thread; retain runtime until process exit. */
static int init_state = 0;

int packed_route_init(void) {
    if (init_state != 0) return init_state == 1 ? 0 : 1;
    init_state = -1;
    lean_initialize_runtime_module();
    lean_object *r = initialize_RMQ_Core_WordRAM_Native_Route(1, lean_io_mk_world());
    lean_io_mark_end_initialization();
    if (lean_io_result_is_error(r)) {
        lean_dec_ref(r);
        return 1;
    }
    lean_dec_ref(r);
    lean_init_task_manager_using(1);
    init_state = 1;
    return 0;
}

void *packed_route_eval(const char *program, size_t p_len,
                      const char *fixture, size_t f_len, uint8_t reads) {
    if (init_state != 1 || !program || !fixture || reads > 1) return NULL;
    if (p_len > 50000000 || f_len > 1000000) return NULL;
    lean_object *p = lean_mk_string_from_bytes(program, p_len);
    lean_object *f = lean_mk_string_from_bytes(fixture, f_len);
    return rmq_native_route(p, f, reads);
}

const char *packed_route_text(void *result) {
    return result ? lean_string_cstr((lean_object *)result) : NULL;
}

void packed_route_free(void *result) { if (result) lean_dec((lean_object *)result); }
