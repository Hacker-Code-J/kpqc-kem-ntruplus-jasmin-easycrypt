#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../../../NTRU+/NTRU+768/params.h"
#include "../../../NTRU+/NTRU+768/ntt.h"
#include "../../../NTRU+/NTRU+768/poly.h"

#define NTRUPLUS_RINV_MOD_Q 2775
#define FIXED_CASES 17u
#define RANDOM_CASES 32u

extern uint64_t jade_ntruplus_ntruplus768_amd64_ref_poly_baseinv(
    poly *r, const poly *a);

_Static_assert(CHAR_BIT == 8, "poly_baseinv test requires 8-bit bytes");
_Static_assert(sizeof(int16_t) * CHAR_BIT == 16,
               "poly_baseinv test requires 16-bit int16_t");
_Static_assert(NTRUPLUS_N == 768, "poly_baseinv test requires N=768");
_Static_assert(NTRUPLUS_Q == 3457, "poly_baseinv test requires q=3457");

static int32_t mod_q(int64_t value)
{
    int64_t reduced = value % NTRUPLUS_Q;

    if (reduced < 0) {
        reduced += NTRUPLUS_Q;
    }
    return (int32_t)reduced;
}

static uint32_t next_u32(uint32_t *state)
{
    uint32_t value = *state;

    value ^= value << 13;
    value ^= value >> 17;
    value ^= value << 5;
    *state = value;
    return value;
}

static int16_t sample_qrange(uint32_t *state)
{
    return (int16_t)((int32_t)(next_u32(state) % (2u * NTRUPLUS_Q)) -
                     NTRUPLUS_Q);
}

static void fill_identity_block(int16_t dst[4])
{
    dst[0] = 1;
    dst[1] = 0;
    dst[2] = 0;
    dst[3] = 0;
}

static void fill_monomial_block(int16_t dst[4], size_t monomial, int16_t scale)
{
    dst[0] = 0;
    dst[1] = 0;
    dst[2] = 0;
    dst[3] = 0;
    dst[monomial & 3u] = scale;
}

static void fill_poly_constant(poly *dst, int16_t value)
{
    size_t i;

    for (i = 0; i < NTRUPLUS_N; ++i) {
        dst->coeffs[i] = value;
    }
}

static void fill_poly_identity(poly *dst)
{
    size_t block;

    for (block = 0; block < NTRUPLUS_N / 4; ++block) {
        fill_identity_block(dst->coeffs + 4 * block);
    }
}

static void fill_poly_monomials(poly *dst)
{
    size_t block;

    for (block = 0; block < NTRUPLUS_N / 4; ++block) {
        const size_t monomial = block & 3u;
        const int16_t scale = (int16_t)((block % 5u) + 1u);

        fill_monomial_block(dst->coeffs + 4 * block, monomial, scale);
    }
}

static void fill_poly_scaled_identity(poly *dst)
{
    size_t block;

    for (block = 0; block < NTRUPLUS_N / 4; ++block) {
        const int16_t scale =
            (int16_t)((3u * block) % (NTRUPLUS_Q - 1u) + 1u);

        fill_monomial_block(dst->coeffs + 4 * block, 0u, scale);
    }
}

static void fill_poly_failure(poly *dst, size_t zero_block)
{
    size_t lane;

    fill_poly_identity(dst);
    for (lane = 0; lane < 4; ++lane) {
        dst->coeffs[4 * zero_block + lane] = 0;
    }
}

static void fill_poly_random(poly *dst, uint32_t *state)
{
    size_t i;

    for (i = 0; i < NTRUPLUS_N; ++i) {
        dst->coeffs[i] = sample_qrange(state);
    }
}

static void fill_sampler_buf(uint8_t buf[NTRUPLUS_N / 4], uint32_t seed)
{
    uint32_t state = seed;
    size_t i;

    for (i = 0; i < NTRUPLUS_N / 4; ++i) {
        buf[i] = (uint8_t)next_u32(&state);
    }
}

static void fill_poly_keygen_shaped(poly *dst, size_t case_index, int is_f_case)
{
    uint8_t buf[NTRUPLUS_N / 4];
    poly sample;

    fill_sampler_buf(
        buf,
        (uint32_t)(0x6A09E667u + 0x01000193u * (uint32_t)case_index +
                   (is_f_case ? 7u : 13u)));
    poly_cbd1(&sample, buf);
    poly_triple(dst, &sample);
    if (is_f_case) {
        dst->coeffs[0] += 1;
    }
    poly_ntt(dst, dst);
}

static void init_poly_case(size_t case_index, poly *a)
{
    uint32_t state = (uint32_t)(0x243f6a88u ^ (0x9e3779b9u * (uint32_t)case_index));

    if (case_index == 0u) {
        fill_poly_identity(a);
        return;
    }
    if (case_index == 1u) {
        fill_poly_monomials(a);
        return;
    }
    if (case_index == 2u) {
        fill_poly_scaled_identity(a);
        return;
    }
    if (case_index == 3u) {
        fill_poly_failure(a, 0u);
        return;
    }
    if (case_index == 4u) {
        fill_poly_failure(a, 96u);
        return;
    }
    if (case_index == 5u) {
        fill_poly_failure(a, 191u);
        return;
    }
    if (case_index < FIXED_CASES) {
        fill_poly_keygen_shaped(a, case_index - 6u, (case_index & 1u) == 0u);
        return;
    }
    fill_poly_random(a, &state);
}

static int strict_qrange_poly(const poly *value)
{
    size_t i;

    for (i = 0; i < NTRUPLUS_N; ++i) {
        if (!(-NTRUPLUS_Q < value->coeffs[i] && value->coeffs[i] < NTRUPLUS_Q)) {
            return 0;
        }
    }
    return 1;
}

static int poly_all_zero(const poly *value)
{
    size_t i;

    for (i = 0; i < NTRUPLUS_N; ++i) {
        if (value->coeffs[i] != 0) {
            return 0;
        }
    }
    return 1;
}

static int block_inverse_ok(const int16_t a[4], const int16_t inverse[4], int16_t zeta_word)
{
    const int32_t zeta =
        mod_q((int64_t)zeta_word * NTRUPLUS_RINV_MOD_Q);
    const int64_t c0 =
        (int64_t)a[0] * inverse[0] +
        (int64_t)zeta *
            ((int64_t)a[1] * inverse[3] +
             (int64_t)a[2] * inverse[2] +
             (int64_t)a[3] * inverse[1]);
    const int64_t c1 =
        (int64_t)a[0] * inverse[1] +
        (int64_t)a[1] * inverse[0] +
        (int64_t)zeta *
            ((int64_t)a[2] * inverse[3] +
             (int64_t)a[3] * inverse[2]);
    const int64_t c2 =
        (int64_t)a[0] * inverse[2] +
        (int64_t)a[1] * inverse[1] +
        (int64_t)a[2] * inverse[0] +
        (int64_t)zeta * (int64_t)a[3] * inverse[3];
    const int64_t c3 =
        (int64_t)a[0] * inverse[3] +
        (int64_t)a[1] * inverse[2] +
        (int64_t)a[2] * inverse[1] +
        (int64_t)a[3] * inverse[0];

    return mod_q(c0) == 1 && mod_q(c1) == 0 &&
           mod_q(c2) == 0 && mod_q(c3) == 0;
}

static int poly_inverse_ok(const poly *a, const poly *inverse)
{
    size_t block;

    for (block = 0; block < NTRUPLUS_N / 4; ++block) {
        const int16_t zeta =
            (block & 1u) == 0u ? zetas[96u + block / 2u]
                               : (int16_t)-zetas[96u + block / 2u];

        if (!block_inverse_ok(a->coeffs + 4 * block,
                              inverse->coeffs + 4 * block,
                              zeta)) {
            return 0;
        }
    }
    return 1;
}

static void require_poly_equal(const poly *left, const poly *right,
                               const char *label, size_t case_index)
{
    if (memcmp(left, right, sizeof(*left)) != 0) {
        fprintf(stderr, "%s mismatch in case %zu\n", label, case_index);
        exit(1);
    }
}

static void check_case(const char *tag, size_t case_index, const poly *input,
                       size_t *successes, size_t *failures)
{
    poly c_input;
    poly j_input;
    poly j_alias;
    poly c_output;
    poly j_output;
    poly input_before;
    int c_status;
    uint64_t j_status;
    uint64_t j_alias_status;

    c_input = *input;
    j_input = *input;
    j_alias = *input;
    input_before = *input;
    fill_poly_constant(&c_output, (int16_t)0x4444);
    fill_poly_constant(&j_output, (int16_t)0x7777);

    c_status = poly_baseinv(&c_output, &c_input);
    j_status = jade_ntruplus_ntruplus768_amd64_ref_poly_baseinv(&j_output, &j_input);
    j_alias_status = jade_ntruplus_ntruplus768_amd64_ref_poly_baseinv(&j_alias, &j_alias);

    if (c_status < 0 || c_status > 1 ||
        j_status != (uint64_t)c_status || j_alias_status != j_status) {
        fprintf(stderr,
                "%s[%zu] status mismatch: C=%d Jasmin=%llu alias=%llu\n",
                tag,
                case_index,
                c_status,
                (unsigned long long)j_status,
                (unsigned long long)j_alias_status);
        exit(1);
    }

    require_poly_equal(&c_input, &input_before, "C input mutation", case_index);
    require_poly_equal(&j_input, &input_before, "Jasmin disjoint input mutation", case_index);
    require_poly_equal(&c_output, &j_output, "C/Jasmin output", case_index);

    if (c_status == 0) {
        ++*successes;
        require_poly_equal(&j_alias, &j_output, "Jasmin alias success", case_index);
        if (!strict_qrange_poly(&c_output)) {
            fprintf(stderr, "%s[%zu] success output is out of range\n", tag, case_index);
            exit(1);
        }
        if (!poly_inverse_ok(&input_before, &c_output)) {
            fprintf(stderr, "%s[%zu] success output is not a block inverse\n",
                    tag, case_index);
            exit(1);
        }
    } else {
        ++*failures;
        if (!poly_all_zero(&c_output) || !poly_all_zero(&j_output) ||
            !poly_all_zero(&j_alias)) {
            fprintf(stderr, "%s[%zu] failure did not zero all outputs\n",
                    tag, case_index);
            exit(1);
        }
    }
}

int main(void)
{
    size_t successes = 0;
    size_t failures = 0;
    size_t case_index;

    for (case_index = 0; case_index < FIXED_CASES; ++case_index) {
        poly input;

        init_poly_case(case_index, &input);
        check_case("fixed", case_index, &input, &successes, &failures);
    }

    for (case_index = 0; case_index < RANDOM_CASES; ++case_index) {
        poly input;

        init_poly_case(FIXED_CASES + case_index, &input);
        check_case("random", case_index, &input, &successes, &failures);
    }

    if (successes == 0 || failures == 0) {
        fprintf(stderr,
                "branch coverage missing: successes=%zu failures=%zu\n",
                successes,
                failures);
        return 1;
    }

    printf("poly_baseinv differential passed: %u fixed + %u random cases; "
           "%zu success, %zu failure\n",
           FIXED_CASES,
           RANDOM_CASES,
           successes,
           failures);
    return 0;
}
