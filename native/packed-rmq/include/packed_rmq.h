#ifndef PACKED_RMQ_H
#define PACKED_RMQ_H
#include <stdint.h>
#include <stddef.h>
#ifdef _WIN32
#ifdef PACKED_RMQ_BUILD
#define PACKED_RMQ_API __declspec(dllexport)
#else
#define PACKED_RMQ_API __declspec(dllimport)
#endif
#else
#define PACKED_RMQ_API
#endif
#ifdef __cplusplus
extern "C" {
#endif

typedef struct packed_rmq_load_result packed_rmq_load_result;
typedef struct packed_rmq_query_result packed_rmq_query_result;
typedef struct packed_rmq_image packed_rmq_image;

/* ABI 1: initialize once; all calls and destruction must occur on that same OS
   thread. This C interface is not thread-safe. Input spans must point to readable
   bytes for their stated lengths; no input pointer is retained. Allocation
   availability and Lean/C compiler/runtime correctness are explicit assumptions.
   NULL is a bridge/domain failure. Non-NULL result handles are owned by caller,
   must be released exactly once with the matching function from this DLL, and
   must never be used after release. */
PACKED_RMQ_API int packed_rmq_init(void);
PACKED_RMQ_API packed_rmq_load_result *packed_rmq_load(const uint8_t *bytes, size_t length);
/* 0: successful image, 1: rejected image, 2: NULL handle. */
PACKED_RMQ_API int packed_rmq_load_status(const packed_rmq_load_result *result);
/* Borrowed UTF-8 error, valid until load-result release; NULL on success. */
PACKED_RMQ_API const char *packed_rmq_load_error(const packed_rmq_load_result *result);
/* Borrowed image, valid until its load result is released. */
PACKED_RMQ_API const packed_rmq_image *packed_rmq_loaded_image(const packed_rmq_load_result *result);
/* Required canonical endpoint byte length; zero for a NULL handle. */
PACKED_RMQ_API size_t packed_rmq_word_bytes(const packed_rmq_image *image);
PACKED_RMQ_API void packed_rmq_load_free(packed_rmq_load_result *result);

/* Endpoints are canonical little-endian width-sized byte strings, not usize
   endpoint values. Each length is at most 512, image width at most 4096, and
   fuel at most 1,000,000. Reads is exactly 0 or 1. Queries never modify image.
   A rejected endpoint/domain returns status 1. An executed machine fault is
   status 0 with a "fault" observation, distinct from a bridge/parser error.
   The default reads=0 does not retain transition states or read receipts. */
PACKED_RMQ_API packed_rmq_query_result *packed_rmq_query(const packed_rmq_image *image,
    const uint8_t *left, size_t left_length, const uint8_t *right, size_t right_length,
    size_t fuel, uint8_t reads);
/* 0: execution observation, 1: query rejected, 2: NULL handle. */
PACKED_RMQ_API int packed_rmq_query_status(const packed_rmq_query_result *result);
/* Borrowed UTF-8 observation or rejection reason; valid until query release. */
PACKED_RMQ_API const char *packed_rmq_query_text(const packed_rmq_query_result *result);
PACKED_RMQ_API void packed_rmq_query_free(packed_rmq_query_result *result);

#ifdef __cplusplus
}
#endif
#endif
