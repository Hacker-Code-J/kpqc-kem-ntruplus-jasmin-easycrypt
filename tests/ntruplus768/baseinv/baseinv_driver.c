#include <limits.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "../../../NTRU+/NTRU+768/params.h"
#include "../../../NTRU+/NTRU+768/ntt.h"
#include "../../../NTRU+/NTRU+768/poly.h"

#define SCALAR_FIXED_CASES 12u
#define SCALAR_RANDOM_CASES 12u
#define SCALAR_CASES (SCALAR_FIXED_CASES + SCALAR_RANDOM_CASES)
#define POLY_SUCCESS_CASES 3u
#define POLY_FAILURE_CASES 3u
#define POLY_RANDOM_CASES 5u
#define POLY_KEYGEN_CASES 6u
#define POLY_CASES (POLY_SUCCESS_CASES + POLY_FAILURE_CASES + POLY_RANDOM_CASES + POLY_KEYGEN_CASES)

extern int16_t test_only_fqinv(int16_t a);

_Static_assert(CHAR_BIT == 8, "baseinv test requires 8-bit bytes");
_Static_assert(sizeof(int16_t) * CHAR_BIT == 16, "baseinv test requires 16-bit int16_t");
_Static_assert(NTRUPLUS_N == 768, "baseinv test requires N=768");
_Static_assert(NTRUPLUS_Q == 3457, "baseinv test requires q=3457");
_Static_assert(sizeof(((poly *)0)->coeffs) / sizeof(int16_t) == NTRUPLUS_N,
               "poly ABI must expose exactly 768 coefficients");

static uint32_t next_u32(uint32_t *state)
{
    uint32_t x = *state;

    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    *state = x;
    return x;
}

static int16_t sample_qrange(uint32_t *state)
{
    return (int16_t)((int32_t)(next_u32(state) % (2 * NTRUPLUS_Q)) - NTRUPLUS_Q);
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

static void copy_scalar4(int16_t dst[4], const int16_t src[4])
{
    for (size_t i = 0; i < 4; ++i) {
        dst[i] = src[i];
    }
}

static void fill_poly_constant(poly *dst, int16_t value)
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        dst->coeffs[i] = value;
    }
}

static void init_scalar_case(size_t case_index, int16_t a[4], int16_t *zeta)
{
    uint32_t state = (uint32_t)(0x9E3779B9u ^ (0x45d9f3bu * (uint32_t)case_index));
    static const int16_t fixed_cases[SCALAR_FIXED_CASES][4] = {
        {0, 0, 0, 0},
        {1, 0, 0, 0},
        {0, 1, 0, 0},
        {0, 0, 1, 0},
        {0, 0, 0, 1},
        {2, 0, 0, 0},
        {-1, 0, 0, 0},
        {0, -1, 0, 0},
        {1, 1, 0, 0},
        {1, 0, 1, 0},
        {1, 0, 0, 1},
        {NTRUPLUS_Q - 1, 0, 0, 0},
    };
    static const size_t zeta_indices[SCALAR_FIXED_CASES] = {
        96, 96, 96, 96, 96, 97, 97, 97, 98, 98, 99, 99,
    };
    static const int zeta_negate[SCALAR_FIXED_CASES] = {
        0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1,
    };

    if (case_index < SCALAR_FIXED_CASES) {
        copy_scalar4(a, fixed_cases[case_index]);
        *zeta = zeta_negate[case_index] ? (int16_t)-zetas[zeta_indices[case_index]] : zetas[zeta_indices[case_index]];
        return;
    }

    for (size_t i = 0; i < 4; ++i) {
        a[i] = sample_qrange(&state);
    }
    {
        const size_t idx = 96u + (case_index % (NTRUPLUS_N / 8u));
        const int negate = (case_index & 1u) != 0u;
        *zeta = negate ? (int16_t)-zetas[idx] : zetas[idx];
    }
}

static void fill_poly_identity(poly *dst)
{
    for (size_t block = 0; block < NTRUPLUS_N / 4; ++block) {
        fill_identity_block(dst->coeffs + 4 * block);
    }
}

static void fill_poly_monomials(poly *dst)
{
    for (size_t block = 0; block < NTRUPLUS_N / 4; ++block) {
        const size_t monomial = block & 3u;
        const int16_t scale = (int16_t)((block % 5u) + 1u);
        fill_monomial_block(dst->coeffs + 4 * block, monomial, scale);
    }
}

static void fill_poly_scaled_identity(poly *dst)
{
    for (size_t block = 0; block < NTRUPLUS_N / 4; ++block) {
        const int16_t scale = (int16_t)((3u * block) % (NTRUPLUS_Q - 1u) + 1u);
        fill_monomial_block(dst->coeffs + 4 * block, 0u, scale);
    }
}

static void fill_poly_failure(poly *dst, size_t zero_block)
{
    fill_poly_identity(dst);
    for (size_t lane = 0; lane < 4; ++lane) {
        dst->coeffs[4 * zero_block + lane] = 0;
    }
}

static void fill_poly_random(poly *dst, uint32_t *state)
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        dst->coeffs[i] = sample_qrange(state);
    }
}

static void fill_sampler_buf(uint8_t buf[NTRUPLUS_N / 4], uint32_t seed)
{
    uint32_t state = seed;

    for (size_t i = 0; i < NTRUPLUS_N / 4; ++i) {
        buf[i] = (uint8_t)next_u32(&state);
    }
}

static void fill_poly_keygen_shaped(poly *dst, size_t case_index, int is_f_case)
{
    uint8_t buf[NTRUPLUS_N / 4];
    poly sample;

    fill_sampler_buf(buf, (uint32_t)(0x6A09E667u + 0x01000193u * (uint32_t)case_index + (is_f_case ? 7u : 13u)));
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
    if (case_index < 11u) {
        fill_poly_random(a, &state);
        return;
    }
    fill_poly_keygen_shaped(a, case_index - 11u, (case_index & 1u) == 0u);
}

static int poly_all_zero(const poly *value)
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        if (value->coeffs[i] != 0) {
            return 0;
        }
    }
    return 1;
}

static int poly_qrange(const poly *value)
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        if (value->coeffs[i] < -NTRUPLUS_Q || value->coeffs[i] >= NTRUPLUS_Q) {
            return 0;
        }
    }
    return 1;
}

static int scalar_qrange(const int16_t value[4])
{
    for (size_t i = 0; i < 4; ++i) {
        if (value[i] < -NTRUPLUS_Q || value[i] >= NTRUPLUS_Q) {
            return 0;
        }
    }
    return 1;
}

static void require_poly_equal(const poly *left, const poly *right, const char *label, size_t case_index)
{
    if (memcmp(left, right, sizeof(*left)) != 0) {
        fprintf(stderr, "%s mismatch in case %zu\n", label, case_index);
        (void)fflush(stderr);
        _Exit(1);
    }
}

static void require_scalar_equal(const int16_t left[4], const int16_t right[4], const char *label, size_t case_index)
{
    if (memcmp(left, right, 4u * sizeof(int16_t)) != 0) {
        fprintf(stderr, "%s mismatch in scalar case %zu\n", label, case_index);
        (void)fflush(stderr);
        _Exit(1);
    }
}

static void print_scalar_case(size_t case_index)
{
    int16_t a[4];
    int16_t a_before[4];
    int16_t out1[4] = {111, 111, 111, 111};
    int16_t out2[4] = {222, 222, 222, 222};
    int16_t zeta;
    int status1;
    int status2;

    init_scalar_case(case_index, a, &zeta);
    copy_scalar4(a_before, a);
    status1 = baseinv(out1, a, zeta);
    status2 = baseinv(out2, a, zeta);
    require_scalar_equal(a, a_before, "baseinv input mutation", case_index);
    if (status1 != status2) {
        fprintf(stderr, "baseinv status nondeterminism in scalar case %zu\n", case_index);
        _Exit(1);
    }
    if (status1 == 0) {
        require_scalar_equal(out1, out2, "baseinv determinism", case_index);
        if (!scalar_qrange(out1)) {
            fprintf(stderr, "baseinv success out-of-range in scalar case %zu\n", case_index);
            _Exit(1);
        }
    }

    printf("SCALAR %zu %d %d", case_index, zeta, status1);
    for (size_t i = 0; i < 4; ++i) {
        printf(" %d", a[i]);
    }
    for (size_t i = 0; i < 4; ++i) {
        printf(" %d", out1[i]);
    }
    printf("\n");
}

static void print_poly_case(size_t case_index)
{
    poly a;
    poly a_before;
    poly out1;
    poly out2;
    int status1;
    int status2;

    init_poly_case(case_index, &a);
    a_before = a;
    fill_poly_constant(&out1, 0x4444);
    fill_poly_constant(&out2, 0x7777);
    status1 = poly_baseinv(&out1, &a);
    status2 = poly_baseinv(&out2, &a);
    require_poly_equal(&a, &a_before, "poly_baseinv input mutation", case_index);
    if (status1 != status2) {
        fprintf(stderr, "poly_baseinv status nondeterminism in case %zu\n", case_index);
        _Exit(1);
    }
    require_poly_equal(&out1, &out2, "poly_baseinv determinism", case_index);
    if (status1 == 0) {
        if (!poly_qrange(&out1)) {
            fprintf(stderr, "poly_baseinv success out-of-range in case %zu\n", case_index);
            _Exit(1);
        }
    } else if (!poly_all_zero(&out1)) {
        fprintf(stderr, "poly_baseinv failure did not zero output in case %zu\n", case_index);
        _Exit(1);
    }

    printf("POLY %zu %d", case_index, status1);
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        printf(" %d", a.coeffs[i]);
    }
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        printf(" %d", out1.coeffs[i]);
    }
    printf("\n");
}

static void print_fqinv_table(void)
{
    for (int a = 0; a < NTRUPLUS_Q; ++a) {
        printf("FQINV %d %d\n", a, test_only_fqinv((int16_t)a));
    }
}

int main(void)
{
    for (size_t case_index = 0; case_index < SCALAR_CASES; ++case_index) {
        print_scalar_case(case_index);
    }
    for (size_t case_index = 0; case_index < POLY_CASES; ++case_index) {
        print_poly_case(case_index);
    }
    print_fqinv_table();
    return 0;
}
