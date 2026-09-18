#ifndef PACKED_RMQ_ROUTE_H
#define PACKED_RMQ_ROUTE_H
#include <stdint.h>
#include <stddef.h>
#ifdef _WIN32
#ifdef PACKED_ROUTE_BUILD
#define PACKED_ROUTE_API __declspec(dllexport)
#else
#define PACKED_ROUTE_API __declspec(dllimport)
#endif
#else
#define PACKED_ROUTE_API
#endif
#ifdef __cplusplus
extern "C" {
#endif
/* Experimental text route, one OS thread only. Initialize once per process.
   No pointers retained from input. Returned result handle must be released once
   with packed_route_free from this DLL. NULL reports bridge/domain failure.
   ERROR-prefixed text reports a Lean parser rejection. This is not binary ABI v1. */
PACKED_ROUTE_API int packed_route_init(void);
PACKED_ROUTE_API void *packed_route_eval(const char *program, size_t program_len,
    const char *fixture, size_t fixture_len, uint8_t reads);
/* Borrowed NUL-terminated UTF-8 remains valid until this handle is released. */
PACKED_ROUTE_API const char *packed_route_text(void *result);
PACKED_ROUTE_API void packed_route_free(void *result);
#ifdef __cplusplus
}
#endif
#endif
