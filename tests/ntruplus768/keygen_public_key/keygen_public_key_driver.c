#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../../../NTRU+/NTRU+768/params.h"
#include "../../../NTRU+/NTRU+768/ntt.h"
#include "../../../NTRU+/NTRU+768/poly.h"

#define NTRUPLUS_RINV_MOD_Q 2775
#define TARGET_SUCCESS_PAIRS 31u
#define MAX_ATTEMPTS 512u

extern uint64_t jade_ntruplus_ntruplus768_amd64_ref_poly_baseinv(
    poly *r, const poly *a);
extern void jade_ntruplus_ntruplus768_amd64_ref_poly_basemul(
    int16_t r[NTRUPLUS_N], const int16_t a[NTRUPLUS_N], const int16_t b[NTRUPLUS_N]);
extern void jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes(
    uint8_t out[NTRUPLUS_POLYBYTES], const int16_t in[NTRUPLUS_N]);

_Static_assert(CHAR_BIT == 8, "keygen_public_key test requires 8-bit bytes");
_Static_assert(sizeof(int16_t) * CHAR_BIT == 16,
               "keygen_public_key test requires 16-bit int16_t");
_Static_assert(NTRUPLUS_N == 768, "keygen_public_key test requires N=768");
_Static_assert(NTRUPLUS_Q == 3457, "keygen_public_key test requires q=3457");
_Static_assert(NTRUPLUS_POLYBYTES == 1152,
               "keygen_public_key test requires 1152 serialized bytes");
_Static_assert(sizeof(((poly *)0)->coeffs) / sizeof(int16_t) == NTRUPLUS_N,
               "poly ABI must expose exactly N coefficients");

static uint32_t next_u32(uint32_t *state)
{
    uint32_t x = *state;

    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    *state = x;
    return x;
}

static void fill_sampler_buf(uint8_t buf[NTRUPLUS_N / 4], uint32_t seed)
{
    uint32_t state = seed;
    size_t i;

    for (i = 0; i < NTRUPLUS_N / 4; ++i) {
        buf[i] = (uint8_t)next_u32(&state);
    }
}

static int32_t mod_q(int64_t value)
{
    int64_t reduced = value % NTRUPLUS_Q;

    if (reduced < 0) {
        reduced += NTRUPLUS_Q;
    }
    return (int32_t)reduced;
}

static uint16_t canonical_coeff(int16_t value)
{
    return (uint16_t)(value < 0 ? value + NTRUPLUS_Q : value);
}

static void fill_poly_constant(poly *dst, int16_t value)
{
    size_t i;

    for (i = 0; i < NTRUPLUS_N; ++i) {
        dst->coeffs[i] = value;
    }
}

static int poly_equal(const poly *left, const poly *right)
{
    return memcmp(left, right, sizeof(*left)) == 0;
}

static int poly_qrange(const poly *value)
{
    size_t i;

    for (i = 0; i < NTRUPLUS_N; ++i) {
        if (value->coeffs[i] < -NTRUPLUS_Q || value->coeffs[i] >= NTRUPLUS_Q) {
            return 0;
        }
    }
    return 1;
}

static void require_poly_equal(
    const poly *left, const poly *right, const char *label, size_t index)
{
    if (!poly_equal(left, right)) {
        fprintf(stderr, "%s mismatch at pair %zu\n", label, index);
        exit(1);
    }
}

static void require_poly_qrange(const poly *value, const char *label, size_t index)
{
    if (!poly_qrange(value)) {
        fprintf(stderr, "%s escaped centered q-range at pair %zu\n", label, index);
        exit(1);
    }
}

static void require_bytes_equal(
    const uint8_t *left,
    const uint8_t *right,
    size_t length,
    const char *label,
    size_t pair_index)
{
    size_t i;

    for (i = 0; i < length; ++i) {
        if (left[i] != right[i]) {
            fprintf(stderr,
                    "%s mismatch at pair %zu byte %zu: %02x != %02x\n",
                    label,
                    pair_index,
                    i,
                    left[i],
                    right[i]);
            exit(1);
        }
    }
}

static void require_bytes_unchanged(
    const uint8_t *before,
    const uint8_t *after,
    size_t length,
    const char *label,
    size_t pair_index)
{
    if (memcmp(before, after, length) != 0) {
        fprintf(stderr, "%s mutated bytes at pair %zu\n", label, pair_index);
        exit(1);
    }
}

static void make_keygen_ntt(poly *dst, size_t pair_index, int is_f_case)
{
    uint8_t buf[NTRUPLUS_N / 4];
    poly sample;

    fill_sampler_buf(
        buf,
        (uint32_t)(0x6A09E667u + 0x01000193u * (uint32_t)pair_index +
                   (is_f_case ? 7u : 13u)));
    poly_cbd1(&sample, buf);
    poly_triple(dst, &sample);
    if (is_f_case) {
        dst->coeffs[0] += 1;
    }
    poly_ntt(dst, dst);
}

static int block_inverse_ok(
    const int16_t input[4], const int16_t inverse[4], int16_t zeta_word)
{
    const int32_t zeta = mod_q((int64_t)zeta_word * NTRUPLUS_RINV_MOD_Q);
    const int64_t c0 =
        (int64_t)input[0] * inverse[0] +
        (int64_t)zeta *
            ((int64_t)input[1] * inverse[3] +
             (int64_t)input[2] * inverse[2] +
             (int64_t)input[3] * inverse[1]);
    const int64_t c1 =
        (int64_t)input[0] * inverse[1] +
        (int64_t)input[1] * inverse[0] +
        (int64_t)zeta *
            ((int64_t)input[2] * inverse[3] +
             (int64_t)input[3] * inverse[2]);
    const int64_t c2 =
        (int64_t)input[0] * inverse[2] +
        (int64_t)input[1] * inverse[1] +
        (int64_t)input[2] * inverse[0] +
        (int64_t)zeta * (int64_t)input[3] * inverse[3];
    const int64_t c3 =
        (int64_t)input[0] * inverse[3] +
        (int64_t)input[1] * inverse[2] +
        (int64_t)input[2] * inverse[1] +
        (int64_t)input[3] * inverse[0];

    return mod_q(c0) == 1 && mod_q(c1) == 0 &&
           mod_q(c2) == 0 && mod_q(c3) == 0;
}

static int poly_inverse_ok(const poly *input, const poly *inverse)
{
    size_t block;

    for (block = 0; block < NTRUPLUS_N / 4; ++block) {
        const int16_t zeta =
            (block & 1u) == 0u ? zetas[96u + block / 2u]
                               : (int16_t)-zetas[96u + block / 2u];

        if (!block_inverse_ok(
                input->coeffs + 4 * block, inverse->coeffs + 4 * block, zeta)) {
            return 0;
        }
    }
    return 1;
}

static void compute_poly_baseinv_checked(
    const char *label,
    size_t pair_index,
    const poly *input,
    poly *inverse_out)
{
    poly c_input = *input;
    poly j_input = *input;
    poly c_output;
    poly j_output;
    int c_status;
    uint64_t j_status;

    fill_poly_constant(&c_output, (int16_t)0x4444);
    fill_poly_constant(&j_output, (int16_t)0x7777);
    c_status = poly_baseinv(&c_output, &c_input);
    j_status = jade_ntruplus_ntruplus768_amd64_ref_poly_baseinv(&j_output, &j_input);

    if (c_status < 0 || c_status > 1 || j_status != (uint64_t)c_status) {
        fprintf(stderr, "%s inverse status mismatch at pair %zu\n", label, pair_index);
        exit(1);
    }
    require_poly_equal(&c_input, input, "C poly_baseinv input mutation", pair_index);
    require_poly_equal(&j_input, input, "Jasmin poly_baseinv input mutation", pair_index);
    require_poly_equal(&c_output, &j_output, "C/Jasmin poly_baseinv output", pair_index);
    if (c_status != 0) {
        fprintf(stderr, "%s inverse failed at accepted pair %zu\n", label, pair_index);
        exit(1);
    }
    require_poly_qrange(&c_output, "poly_baseinv output", pair_index);
    if (!poly_inverse_ok(input, &c_output)) {
        fprintf(stderr, "%s inverse contract failure at pair %zu\n", label, pair_index);
        exit(1);
    }
    *inverse_out = c_output;
}

static void poly_basemul_jasmin(poly *dst, const poly *left, const poly *right)
{
    int16_t out[NTRUPLUS_N];
    size_t i;

    jade_ntruplus_ntruplus768_amd64_ref_poly_basemul(
        out, left->coeffs, right->coeffs);
    for (i = 0; i < NTRUPLUS_N; ++i) {
        dst->coeffs[i] = out[i];
    }
}

static void compute_poly_basemul_checked(
    const char *label,
    size_t pair_index,
    const poly *left,
    const poly *right,
    poly *out)
{
    poly c_left = *left;
    poly c_right = *right;
    poly j_left = *left;
    poly j_right = *right;
    poly c_out;
    poly j_out;

    fill_poly_constant(&c_out, (int16_t)0x2222);
    fill_poly_constant(&j_out, (int16_t)0x3333);
    poly_basemul(&c_out, &c_left, &c_right);
    poly_basemul_jasmin(&j_out, &j_left, &j_right);

    require_poly_equal(&c_left, left, "C poly_basemul left input mutation", pair_index);
    require_poly_equal(&c_right, right, "C poly_basemul right input mutation", pair_index);
    require_poly_equal(&j_left, left, "Jasmin poly_basemul left input mutation", pair_index);
    require_poly_equal(&j_right, right, "Jasmin poly_basemul right input mutation", pair_index);
    require_poly_equal(&c_out, &j_out, "C/Jasmin poly_basemul output", pair_index);
    require_poly_qrange(&c_out, label, pair_index);
    *out = c_out;
}

static void check_product_mod_q(
    const poly *product,
    const poly *left,
    const poly *right,
    const poly *target,
    const char *label,
    size_t pair_index)
{
    size_t block;

    for (block = 0; block < NTRUPLUS_N / 4; ++block) {
        const size_t off = 4 * block;
        const int32_t zeta_math = mod_q(
            (int64_t)((block & 1u) == 0u ? zetas[96u + block / 2u]
                                         : (int16_t)-zetas[96u + block / 2u]) *
            NTRUPLUS_RINV_MOD_Q);
        const int64_t expected[4] = {
            (int64_t)left->coeffs[off] * right->coeffs[off] +
                (int64_t)zeta_math *
                    ((int64_t)left->coeffs[off + 1] * right->coeffs[off + 3] +
                     (int64_t)left->coeffs[off + 2] * right->coeffs[off + 2] +
                     (int64_t)left->coeffs[off + 3] * right->coeffs[off + 1]),
            (int64_t)left->coeffs[off] * right->coeffs[off + 1] +
                (int64_t)left->coeffs[off + 1] * right->coeffs[off] +
                (int64_t)zeta_math *
                    ((int64_t)left->coeffs[off + 2] * right->coeffs[off + 3] +
                     (int64_t)left->coeffs[off + 3] * right->coeffs[off + 2]),
            (int64_t)left->coeffs[off] * right->coeffs[off + 2] +
                (int64_t)left->coeffs[off + 1] * right->coeffs[off + 1] +
                (int64_t)left->coeffs[off + 2] * right->coeffs[off] +
                (int64_t)zeta_math *
                    (int64_t)left->coeffs[off + 3] * right->coeffs[off + 3],
            (int64_t)left->coeffs[off] * right->coeffs[off + 3] +
                (int64_t)left->coeffs[off + 1] * right->coeffs[off + 2] +
                (int64_t)left->coeffs[off + 2] * right->coeffs[off + 1] +
                (int64_t)left->coeffs[off + 3] * right->coeffs[off],
        };
        size_t lane;

        for (lane = 0; lane < 4; ++lane) {
            if (mod_q(product->coeffs[off + lane]) != mod_q(expected[lane]) ||
                mod_q(product->coeffs[off + lane]) != mod_q(target->coeffs[off + lane])) {
                fprintf(stderr,
                        "%s modular mismatch at pair %zu block %zu lane %zu\n",
                        label,
                        pair_index,
                        block,
                        lane);
                exit(1);
            }
        }
    }
}

static void poly_tobytes_oracle(
    uint8_t out[NTRUPLUS_POLYBYTES], const int16_t in[NTRUPLUS_N])
{
    size_t i;

    for (i = 0; i < NTRUPLUS_N / 2; ++i) {
        const uint16_t t0 = canonical_coeff(in[2 * i]);
        const uint16_t t1 = canonical_coeff(in[2 * i + 1]);
        const size_t j = 3 * i;

        out[j + 0] = (uint8_t)t0;
        out[j + 1] = (uint8_t)((t0 >> 8) | (t1 << 4));
        out[j + 2] = (uint8_t)(t1 >> 4);
    }
}

static void poly_frombytes_oracle(
    poly *out, const uint8_t in[NTRUPLUS_POLYBYTES])
{
    size_t i;

    for (i = 0; i < NTRUPLUS_N / 2; ++i) {
        const size_t j = 3 * i;
        const uint16_t a0 = in[j + 0];
        const uint16_t a1 = in[j + 1];
        const uint16_t a2 = in[j + 2];
        const uint16_t lo = a0 + ((a1 & 0x0fu) << 8);
        const uint16_t hi = (a1 >> 4) + (a2 << 4);

        out->coeffs[2 * i] = (int16_t)(lo & 0x0fffu);
        out->coeffs[2 * i + 1] = (int16_t)(hi & 0x0fffu);
    }
}

static void check_decoded_matches_canonical(
    const poly *decoded, const poly *source, size_t pair_index)
{
    size_t i;

    for (i = 0; i < NTRUPLUS_N; ++i) {
        const int16_t expected = (int16_t)canonical_coeff(source->coeffs[i]);

        if (decoded->coeffs[i] != expected) {
            fprintf(stderr,
                    "decoded canonical mismatch at pair %zu coeff %zu: %d != %d\n",
                    pair_index,
                    i,
                    decoded->coeffs[i],
                    expected);
            exit(1);
        }
        if (decoded->coeffs[i] < 0 || decoded->coeffs[i] >= NTRUPLUS_Q) {
            fprintf(stderr,
                    "decoded coefficient escaped [0,q) at pair %zu coeff %zu: %d\n",
                    pair_index,
                    i,
                    decoded->coeffs[i]);
            exit(1);
        }
        if (mod_q(decoded->coeffs[i]) != mod_q(source->coeffs[i])) {
            fprintf(stderr,
                    "decoded mod-q mismatch at pair %zu coeff %zu: %d vs %d\n",
                    pair_index,
                    i,
                    decoded->coeffs[i],
                    source->coeffs[i]);
            exit(1);
        }
    }
}

static void compute_public_key_checked(
    size_t pair_index,
    const poly *h,
    uint8_t pk_out[NTRUPLUS_POLYBYTES])
{
    poly c_input = *h;
    poly j_input = *h;
    uint8_t oracle[NTRUPLUS_POLYBYTES];
    uint8_t c_pk[NTRUPLUS_POLYBYTES];
    uint8_t j_pk[NTRUPLUS_POLYBYTES];

    memset(c_pk, 0x11, sizeof(c_pk));
    memset(j_pk, 0x22, sizeof(j_pk));
    poly_tobytes_oracle(oracle, h->coeffs);
    poly_tobytes(c_pk, &c_input);
    jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes(j_pk, j_input.coeffs);

    require_poly_equal(&c_input, h, "C poly_tobytes input mutation", pair_index);
    require_poly_equal(&j_input, h, "Jasmin poly_tobytes input mutation", pair_index);
    require_bytes_equal(oracle, c_pk, sizeof(c_pk), "oracle/C pk", pair_index);
    require_bytes_equal(oracle, j_pk, sizeof(j_pk), "oracle/Jasmin pk", pair_index);
    memcpy(pk_out, c_pk, sizeof(c_pk));
}

static void decode_public_key_checked(
    size_t pair_index,
    const uint8_t pk[NTRUPLUS_POLYBYTES],
    const poly *h,
    poly *decoded_out)
{
    uint8_t pk_before[NTRUPLUS_POLYBYTES];
    poly c_decoded;
    poly oracle_decoded;

    memcpy(pk_before, pk, sizeof(pk_before));
    poly_frombytes(&c_decoded, pk);
    require_bytes_unchanged(pk_before, pk, sizeof(pk_before), "poly_frombytes", pair_index);
    poly_frombytes_oracle(&oracle_decoded, pk);
    require_poly_equal(&c_decoded, &oracle_decoded, "C/oracle decoded public key", pair_index);
    check_decoded_matches_canonical(&c_decoded, h, pair_index);
    *decoded_out = c_decoded;
}

static void check_pair(size_t pair_index)
{
    poly f;
    poly g;
    poly finv;
    poly ginv;
    poly h;
    poly hinv;
    poly decoded_h;
    poly decoded_hf;
    uint8_t pk[NTRUPLUS_POLYBYTES];

    make_keygen_ntt(&f, pair_index, 1);
    make_keygen_ntt(&g, pair_index, 0);
    require_poly_qrange(&f, "f pre-baseinv", pair_index);
    require_poly_qrange(&g, "g pre-baseinv", pair_index);

    compute_poly_baseinv_checked("f", pair_index, &f, &finv);
    compute_poly_baseinv_checked("g", pair_index, &g, &ginv);
    compute_poly_basemul_checked("h", pair_index, &g, &finv, &h);
    compute_poly_basemul_checked("hinv", pair_index, &f, &ginv, &hinv);
    check_product_mod_q(&h, &g, &finv, &h, "h = g * finv", pair_index);
    check_product_mod_q(&hinv, &f, &ginv, &hinv, "hinv = f * ginv", pair_index);

    compute_public_key_checked(pair_index, &h, pk);
    decode_public_key_checked(pair_index, pk, &h, &decoded_h);
    compute_poly_basemul_checked("decoded_h * f", pair_index, &decoded_h, &f, &decoded_hf);
    check_product_mod_q(&decoded_hf, &decoded_h, &f, &g, "decoded_h * f = g", pair_index);
}

static int pair_is_successful(size_t pair_index)
{
    poly f;
    poly g;
    poly finv;
    poly ginv;

    make_keygen_ntt(&f, pair_index, 1);
    make_keygen_ntt(&g, pair_index, 0);
    if (poly_baseinv(&finv, &f) != 0) {
        return 0;
    }
    if (poly_baseinv(&ginv, &g) != 0) {
        return 0;
    }
    return 1;
}

int main(void)
{
    size_t attempt;
    size_t successes = 0;

    for (attempt = 0; attempt < MAX_ATTEMPTS && successes < TARGET_SUCCESS_PAIRS; ++attempt) {
        if (!pair_is_successful(attempt)) {
            continue;
        }
        check_pair(attempt);
        ++successes;
    }

    if (successes != TARGET_SUCCESS_PAIRS) {
        fprintf(stderr,
                "insufficient successful keygen pairs: got %zu need %u within %u attempts\n",
                successes,
                TARGET_SUCCESS_PAIRS,
                MAX_ATTEMPTS);
        return 1;
    }

    printf("keygen_public_key differential passed: %u successful deterministic pairs\n",
           TARGET_SUCCESS_PAIRS);
    return 0;
}
