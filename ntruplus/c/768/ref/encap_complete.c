#include "encap_complete.h"
#include "fips202/fips202.h"
#include "randombytes.h"
#include <stddef.h>

struct encap_workspace {
    uint16_t h[768], r[768], r_ntt[768], m[768], m_ntt[768], product[768], c[768];
    uint8_t input[1153];
    uint8_t hash_f[32];
    uint8_t hash_h_input[129];
    uint8_t hash_output[224];
    uint8_t serialized_r[1152];
    uint8_t pad[192];
};

_Static_assert(sizeof(struct encap_workspace) == 13634, "workspace size");
_Static_assert(_Alignof(struct encap_workspace) == 2, "workspace alignment");
_Static_assert(offsetof(struct encap_workspace, h) == 0, "h offset");
_Static_assert(offsetof(struct encap_workspace, r) == 1536, "r offset");
_Static_assert(offsetof(struct encap_workspace, r_ntt) == 3072, "r_ntt offset");
_Static_assert(offsetof(struct encap_workspace, m) == 4608, "m offset");
_Static_assert(offsetof(struct encap_workspace, m_ntt) == 6144, "m_ntt offset");
_Static_assert(offsetof(struct encap_workspace, product) == 7680, "product offset");
_Static_assert(offsetof(struct encap_workspace, c) == 9216, "c offset");
_Static_assert(offsetof(struct encap_workspace, input) == 10752, "input offset");
_Static_assert(offsetof(struct encap_workspace, hash_f) == 11905, "hash_f offset");
_Static_assert(offsetof(struct encap_workspace, hash_h_input) == 11937, "hash_h_input offset");
_Static_assert(offsetof(struct encap_workspace, hash_output) == 12066, "hash_output offset");
_Static_assert(offsetof(struct encap_workspace, serialized_r) == 12290, "serialized_r offset");
_Static_assert(offsetof(struct encap_workspace, pad) == 13442, "pad offset");

extern uint32_t jade_ntruplus_ntruplus768_amd64_ref_encap_guard(
    uint16_t h[768], uint8_t ct[1152], uint8_t ss[32], const uint8_t pk[1152]);
extern void jade_ntruplus_ntruplus768_amd64_ref_encap_hash_f_prepare(
    uint8_t input[1153], const uint8_t pk[1152]);
extern void jade_ntruplus_ntruplus768_amd64_ref_decap_hash_h_prepare(
    uint8_t input[129], const uint8_t msg[96], const uint8_t suffix[32]);
extern void jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(
    uint16_t r[768], const uint8_t buf[192]);
extern void jade_ntruplus_ntruplus768_amd64_ref_ntt(
    uint16_t output[768], const uint16_t input[768]);
extern void jade_ntruplus_ntruplus768_amd64_ref_decap_message_prepare(
    uint8_t serialized[1152], uint8_t input[1153], const uint16_t r[768]);
extern void jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_encode(
    uint16_t m[768], const uint8_t msg[96], const uint8_t pad[192]);
extern void jade_ntruplus_ntruplus768_amd64_ref_poly_basemul(
    uint16_t output[768], const uint16_t a[768], const uint16_t b[768]);
extern void jade_ntruplus_ntruplus768_amd64_ref_poly_centered_add(
    uint16_t output[768], const uint16_t a[768], const uint16_t b[768]);
extern void jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes(
    uint8_t output[1152], const uint16_t input[768]);
extern void jade_ntruplus_ntruplus768_amd64_ref_encap_copy_key(
    uint8_t ss[32], const uint8_t hash_output[224]);
extern void jade_ntruplus_ntruplus768_amd64_ref_encap_clear(
    uint8_t workspace[13634]);
extern void jade_ntruplus_ntruplus768_amd64_ref_encap_clear_coins(
    uint8_t coins[96]);

int ntruplus768_encaps_derand(uint8_t ct[1152], uint8_t ss[32],
                             const uint8_t pk[1152], const uint8_t coins[96])
{
    struct encap_workspace w = {0};
    uint32_t status;

    status = jade_ntruplus_ntruplus768_amd64_ref_encap_guard(w.h, ct, ss, pk);
    if (status != 0)
        goto cleanup;

    jade_ntruplus_ntruplus768_amd64_ref_encap_hash_f_prepare(w.input, pk);
    shake256(w.hash_f, sizeof w.hash_f, w.input, sizeof w.input);
    jade_ntruplus_ntruplus768_amd64_ref_decap_hash_h_prepare(
        w.hash_h_input, coins, w.hash_f);
    shake256(w.hash_output, sizeof w.hash_output,
             w.hash_h_input, sizeof w.hash_h_input);
    jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(w.r, w.hash_output + 32);
    jade_ntruplus_ntruplus768_amd64_ref_ntt(w.r_ntt, w.r);
    jade_ntruplus_ntruplus768_amd64_ref_decap_message_prepare(
        w.serialized_r, w.input, w.r_ntt);
    shake256(w.pad, sizeof w.pad, w.input, sizeof w.input);
    jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_encode(w.m, coins, w.pad);
    jade_ntruplus_ntruplus768_amd64_ref_ntt(w.m_ntt, w.m);
    jade_ntruplus_ntruplus768_amd64_ref_poly_basemul(w.product, w.h, w.r_ntt);
    jade_ntruplus_ntruplus768_amd64_ref_poly_centered_add(w.c, w.product, w.m_ntt);
    jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes(ct, w.c);
    jade_ntruplus_ntruplus768_amd64_ref_encap_copy_key(ss, w.hash_output);

cleanup:
    jade_ntruplus_ntruplus768_amd64_ref_encap_clear((uint8_t *)&w);
    return (int)status;
}

int ntruplus768_encaps(uint8_t ct[1152], uint8_t ss[32], const uint8_t pk[1152])
{
    uint8_t coins[96] = {0};
    int status;

    randombytes(coins, sizeof coins);
    status = ntruplus768_encaps_derand(ct, ss, pk, coins);
    jade_ntruplus_ntruplus768_amd64_ref_encap_clear_coins(coins);
    return status;
}
