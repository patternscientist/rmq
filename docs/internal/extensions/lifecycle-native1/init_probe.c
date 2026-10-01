/* Supplement linked with the exact verified generated objects and original
 * production shim. Only the augmented diagnostic DLL exports this extra entry.
 * No private pointer from a raw object dump is dereferenced. */
#include <lean/lean.h>
#include <stdint.h>
#include <stddef.h>
extern int __cdecl printf(const char *,...);
extern int packed_lifecycle_init(void);
extern lean_object *rmq_lifecycle_decode_signed(uint8_t,lean_object *);
extern lean_object *rmq_lifecycle_encode_natural(lean_object *);
extern lean_object *l_RMQ_SuccinctFinal_PackedNative_Lifecycle_maxMagnitudeBytes;
static lean_object *magnitude(void) {
    lean_object *bytes=lean_alloc_sarray(1,17,17);
    for(size_t i=0;i<17;++i)lean_sarray_cptr(bytes)[i]=i==0?7:i==16?4:0;
    return bytes;
}
static void hex(const uint8_t *bytes,size_t count) {
    for(size_t i=0;i<count;++i)printf("%02x",(unsigned)bytes[i]);
}
static int inspect(const char *name,lean_object *object) {
    if(lean_is_scalar(object)){printf("\"%s\":{\"scalar\":true}",name);return 0;}
    size_t bytes=lean_object_byte_size(object);
    printf("\"%s\":{\"tag\":%u,\"runtimeBytes\":%zu,\"rawWithinBound\":\"",
        name,(unsigned)lean_obj_tag(object),bytes);
    hex((const uint8_t *)object,bytes<64?bytes:64);
    printf("\",\"natAbsLE\":\"");
    lean_object *encoded=rmq_lifecycle_encode_natural(lean_nat_abs(object));
    hex(lean_sarray_cptr(encoded),lean_sarray_size(encoded));
    int exact=lean_sarray_size(encoded)==17;
    if(exact)for(size_t i=0;i<17;++i)
        if(lean_sarray_cptr(encoded)[i]!=(i==0?7:i==16?4:0))exact=0;
    printf("\",\"exactMagnitude\":%s}",exact?"true":"false");
    lean_dec(encoded);return exact;
}
__declspec(dllexport) int ln1_init_probe_main(void) {
    int status=packed_lifecycle_init();
    lean_object *marker=l_RMQ_SuccinctFinal_PackedNative_Lifecycle_maxMagnitudeBytes;
    if(!lean_is_scalar(marker)||lean_unbox(marker)!=4096){
        printf("{\"initializationStatus\":%d,\"codecInitialized\":false}\n",status);return 6;
    }
    printf("{\"schema\":\"life-native1-init-probe-v1\",\"initializationStatus\":%d,",status);
    lean_object *positive=rmq_lifecycle_decode_signed(0,magnitude());
    lean_object *negative=rmq_lifecycle_decode_signed(1,magnitude());
    int p=inspect("positive",positive);printf(",");
    int n=inspect("negative",negative);printf("}\n");
    lean_dec(positive);lean_dec(negative);
    return p&&n?0:5;
}
