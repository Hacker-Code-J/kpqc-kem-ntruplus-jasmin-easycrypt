#include "decap_complete.h"
#include "decap_message.h"
#include "fips202/fips202.h"
#include <stddef.h>

/* Fixed-size, disjoint storage for the existing and new Jasmin exports.
 * The static assertions bind the native layout to the clear procedure.
 */
struct decap_workspace {
    uint16_t c[768], f[768], h[768], m[768], r[768], r1[768], n1[768];
    uint8_t msg[96];
    uint8_t serialized[1152];
    uint8_t regenerated[1152];
    uint8_t hash_input[129];
    uint8_t hash_output[224];
};

_Static_assert(sizeof(struct decap_workspace) == 13506, "workspace size");
_Static_assert(_Alignof(struct decap_workspace) == 2, "workspace alignment");
_Static_assert(offsetof(struct decap_workspace, c) == 0, "c offset");
_Static_assert(offsetof(struct decap_workspace, f) == 1536, "f offset");
_Static_assert(offsetof(struct decap_workspace, h) == 3072, "h offset");
_Static_assert(offsetof(struct decap_workspace, m) == 4608, "m offset");
_Static_assert(offsetof(struct decap_workspace, r) == 6144, "r offset");
_Static_assert(offsetof(struct decap_workspace, r1) == 7680, "r1 offset");
_Static_assert(offsetof(struct decap_workspace, n1) == 9216, "n1 offset");
_Static_assert(offsetof(struct decap_workspace, msg) == 10752, "msg offset");
_Static_assert(offsetof(struct decap_workspace, serialized) == 10848, "serialized offset");
_Static_assert(offsetof(struct decap_workspace, regenerated) == 12000, "regenerated offset");
_Static_assert(offsetof(struct decap_workspace, hash_input) == 13152, "hash input offset");
_Static_assert(offsetof(struct decap_workspace, hash_output) == 13281, "hash output offset");

extern uint32_t jade_ntruplus_ntruplus768_amd64_ref_decap_guard(
    uint16_t c[768], uint16_t f[768], uint16_t h[768], uint8_t ss[32],
    const uint8_t ct[1152], const uint8_t skpoly[2304]);
extern void jade_ntruplus_ntruplus768_amd64_ref_decap_candidate(
    uint16_t m[768], const uint16_t c[768], const uint16_t f[768]);
extern void jade_ntruplus_ntruplus768_amd64_ref_decap_r2(
    uint16_t r[768], const uint16_t c[768], const uint16_t m[768],
    const uint16_t h[768]);
extern void jade_ntruplus_ntruplus768_amd64_ref_decap_hash_h_prepare(
    uint8_t input[129], const uint8_t msg[96], const uint8_t suffix[32]);
extern void jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(
    uint16_t r[768], const uint8_t buf[192]);
extern void jade_ntruplus_ntruplus768_amd64_ref_ntt(
    uint16_t output[768], const uint16_t input[768]);
extern void jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes(
    uint8_t output[1152], const uint16_t input[768]);
extern uint32_t jade_ntruplus_ntruplus768_amd64_ref_decap_finish(
    uint8_t ss[32], const uint8_t hash_output[224],
    const uint8_t recovered[1152], const uint8_t regenerated[1152],
    uint32_t decode_fail);
extern void jade_ntruplus_ntruplus768_amd64_ref_decap_clear(
    uint8_t workspace[13506]);

int ntruplus768_decaps(uint8_t ss[32], const uint8_t ct[1152],
                      const uint8_t sk[2336])
{
    struct decap_workspace w = {0};
    uint32_t fail;

    fail = jade_ntruplus_ntruplus768_amd64_ref_decap_guard(
        w.c, w.f, w.h, ss, ct, sk);
    if (fail != 0)
        goto cleanup;

    jade_ntruplus_ntruplus768_amd64_ref_decap_candidate(w.m, w.c, w.f);
    jade_ntruplus_ntruplus768_amd64_ref_decap_r2(w.r, w.c, w.m, w.h);
    fail = ntruplus768_decap_message(w.msg, w.serialized, w.m, w.r);
    jade_ntruplus_ntruplus768_amd64_ref_decap_hash_h_prepare(
        w.hash_input, w.msg, sk + 2304);
    shake256(w.hash_output, sizeof w.hash_output,
             w.hash_input, sizeof w.hash_input);
    jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(w.r1, w.hash_output + 32);
    jade_ntruplus_ntruplus768_amd64_ref_ntt(w.n1, w.r1);
    jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes(w.regenerated, w.n1);
    fail = jade_ntruplus_ntruplus768_amd64_ref_decap_finish(
        ss, w.hash_output, w.serialized, w.regenerated, fail);

cleanup:
    jade_ntruplus_ntruplus768_amd64_ref_decap_clear((uint8_t *)&w);
    return (int)fail;
}
