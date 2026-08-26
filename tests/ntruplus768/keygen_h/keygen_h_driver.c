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

_Static_assert(CHAR_BIT == 8, "keygen_h test requires 8-bit bytes");
_Static_assert(sizeof(int16_t) * CHAR_BIT == 16,
               "keygen_h test requires 16-bit int16_t");
_Static_assert(NTRUPLUS_N == 768, "keygen_h test requires N=768");
_Static_assert(NTRUPLUS_Q == 3457, "keygen_h test requires q=3457");
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

static void poly_basemul_jasmin(
    poly *dst, const poly *left, const poly *right)
{
    int16_t out[NTRUPLUS_N];
    size_t i;

    jade_ntruplus_ntruplus768_amd64_ref_poly_basemul(
        out, left->coeffs, right->coeffs);
    for (i = 0; i < NTRUPLUS_N; ++i) {
        dst->coeffs[i] = out[i];
    }
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

static void check_pair(size_t pair_index)
{
    poly f;
    poly g;
    poly finv;
    poly ginv;
    poly h;
    poly hinv;
    poly hf;
    poly hinvg;

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

    compute_poly_basemul_checked("h*f", pair_index, &h, &f, &hf);
    compute_poly_basemul_checked("hinv*g", pair_index, &hinv, &g, &hinvg);
    check_product_mod_q(&hf, &h, &f, &g, "h*f = g", pair_index);
    check_product_mod_q(&hinvg, &hinv, &g, &f, "hinv*g = f", pair_index);
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

    printf("keygen_h differential passed: %u successful deterministic pairs\n",
           TARGET_SUCCESS_PAIRS);
    return 0;
}
