#include "keygen_complete.h"
#include "fips202/fips202.h"
#include "randombytes.h"
#include <stddef.h>

struct keygen_workspace {
    uint16_t f[768], finv[768], g[768], ginv[768], h[768], hinv[768], pre[768];
    uint8_t seed[32];
    uint8_t buf[192];
    uint8_t hash_input[1153];
    uint8_t hash_f[32];
    uint8_t fbytes[1152];
    uint8_t hinvbytes[1152];
    uint8_t reserved[1];
};

_Static_assert(sizeof(struct keygen_workspace) == 14466, "workspace size");
_Static_assert(_Alignof(struct keygen_workspace) == 2, "workspace alignment");
_Static_assert(offsetof(struct keygen_workspace, f) == 0, "f offset");
_Static_assert(offsetof(struct keygen_workspace, finv) == 1536, "finv offset");
_Static_assert(offsetof(struct keygen_workspace, g) == 3072, "g offset");
_Static_assert(offsetof(struct keygen_workspace, ginv) == 4608, "ginv offset");
_Static_assert(offsetof(struct keygen_workspace, h) == 6144, "h offset");
_Static_assert(offsetof(struct keygen_workspace, hinv) == 7680, "hinv offset");
_Static_assert(offsetof(struct keygen_workspace, pre) == 9216, "pre offset");
_Static_assert(offsetof(struct keygen_workspace, seed) == 10752, "seed offset");
_Static_assert(offsetof(struct keygen_workspace, buf) == 10784, "buf offset");
_Static_assert(offsetof(struct keygen_workspace, hash_input) == 10976, "hash_input offset");
_Static_assert(offsetof(struct keygen_workspace, hash_f) == 12129, "hash_f offset");
_Static_assert(offsetof(struct keygen_workspace, fbytes) == 12161, "fbytes offset");
_Static_assert(offsetof(struct keygen_workspace, hinvbytes) == 13313, "hinvbytes offset");
_Static_assert(offsetof(struct keygen_workspace, reserved) == 14465, "reserved offset");

extern void jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(
    uint16_t r[768], const uint8_t buf[192]);
extern void jade_ntruplus_ntruplus768_amd64_ref_keygen_shape_f(uint16_t r[768]);
extern void jade_ntruplus_ntruplus768_amd64_ref_keygen_shape_g(uint16_t r[768]);
extern void jade_ntruplus_ntruplus768_amd64_ref_ntt(
    uint16_t output[768], const uint16_t input[768]);
extern uint64_t jade_ntruplus_ntruplus768_amd64_ref_poly_baseinv(
    uint16_t output[768], const uint16_t input[768]);
extern void jade_ntruplus_ntruplus768_amd64_ref_poly_basemul(
    uint16_t output[768], const uint16_t a[768], const uint16_t b[768]);
extern void jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes(
    uint8_t output[1152], const uint16_t input[768]);
extern void jade_ntruplus_ntruplus768_amd64_ref_encap_hash_f_prepare(
    uint8_t input[1153], const uint8_t pk[1152]);
extern void jade_ntruplus_ntruplus768_amd64_ref_keygen_pack_sk(
    uint8_t sk[2336], const uint8_t fbytes[1152],
    const uint8_t hinvbytes[1152], const uint8_t hash_f[32]);
extern void jade_ntruplus_ntruplus768_amd64_ref_keygen_clear(
    uint8_t workspace[14466]);

int ntruplus768_keypair(uint8_t pk[1152], uint8_t sk[2336])
{
    struct keygen_workspace w = {0};
    uint64_t status;

    do {
        randombytes(w.seed, sizeof w.seed);
        shake256(w.buf, sizeof w.buf, w.seed, sizeof w.seed);
        jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(w.pre, w.buf);
        jade_ntruplus_ntruplus768_amd64_ref_keygen_shape_f(w.pre);
        jade_ntruplus_ntruplus768_amd64_ref_ntt(w.f, w.pre);
        status = jade_ntruplus_ntruplus768_amd64_ref_poly_baseinv(w.finv, w.f);
    } while (status != 0);

    do {
        randombytes(w.seed, sizeof w.seed);
        shake256(w.buf, sizeof w.buf, w.seed, sizeof w.seed);
        jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(w.pre, w.buf);
        jade_ntruplus_ntruplus768_amd64_ref_keygen_shape_g(w.pre);
        jade_ntruplus_ntruplus768_amd64_ref_ntt(w.g, w.pre);
        status = jade_ntruplus_ntruplus768_amd64_ref_poly_baseinv(w.ginv, w.g);
    } while (status != 0);

    jade_ntruplus_ntruplus768_amd64_ref_poly_basemul(w.h, w.g, w.finv);
    jade_ntruplus_ntruplus768_amd64_ref_poly_basemul(w.hinv, w.f, w.ginv);
    jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes(pk, w.h);
    jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes(w.fbytes, w.f);
    jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes(w.hinvbytes, w.hinv);
    jade_ntruplus_ntruplus768_amd64_ref_encap_hash_f_prepare(w.hash_input, pk);
    shake256(w.hash_f, sizeof w.hash_f, w.hash_input, sizeof w.hash_input);
    jade_ntruplus_ntruplus768_amd64_ref_keygen_pack_sk(
        sk, w.fbytes, w.hinvbytes, w.hash_f);
    jade_ntruplus_ntruplus768_amd64_ref_keygen_clear((uint8_t *)&w);
    return 0;
}
