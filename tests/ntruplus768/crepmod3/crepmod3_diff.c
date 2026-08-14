#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../../../NTRU+/NTRU+768/poly.h"

#define RANDOM_CASES 4096

_Static_assert(NTRUPLUS_N == 768, "unexpected NTRUPLUS_N");
_Static_assert(NTRUPLUS_Q == 3457, "unexpected NTRUPLUS_Q");

extern void jade_ntruplus_ntruplus768_amd64_ref_poly_crepmod3(
    int16_t r[NTRUPLUS_N], const int16_t a[NTRUPLUS_N]);

static void poly_crepmod3_ref(int16_t r[NTRUPLUS_N], const int16_t a[NTRUPLUS_N])
{
    poly pa;
    poly pr;

    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        pa.coeffs[i] = a[i];
    }

    poly_crepmod3(&pr, &pa);

    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        r[i] = pr.coeffs[i];
    }
}

static void poly_crepmod3_ref_alias(int16_t r[NTRUPLUS_N], const int16_t a[NTRUPLUS_N])
{
    poly p;

    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        p.coeffs[i] = a[i];
    }

    poly_crepmod3(&p, &p);

    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        r[i] = p.coeffs[i];
    }
}

static void fill_constant(int16_t dst[NTRUPLUS_N], int16_t value)
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        dst[i] = value;
    }
}

static void fill_alternating(int16_t dst[NTRUPLUS_N], int16_t even_value, int16_t odd_value)
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        dst[i] = (i & 1u) == 0 ? even_value : odd_value;
    }
}

static void fill_staircase(int16_t dst[NTRUPLUS_N], int16_t start, int16_t step)
{
    int32_t value = start;

    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        dst[i] = (int16_t)value;
        value += step;
        if (value > NTRUPLUS_Q) {
            value = -NTRUPLUS_Q;
        } else if (value < -NTRUPLUS_Q) {
            value = NTRUPLUS_Q;
        }
    }
}

static uint32_t next_u32(uint32_t *state)
{
    uint32_t x = *state;

    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    *state = x;
    return x;
}

static int16_t sample_mod_q(uint32_t *state)
{
    return (int16_t)((int32_t)(next_u32(state) % (2u * NTRUPLUS_Q)) - NTRUPLUS_Q);
}

static void require_trit(const char *impl,
                         const char *tag,
                         size_t case_index,
                         size_t coeff_index,
                         int16_t value,
                         int16_t input)
{
    if (!(value == -1 || value == 0 || value == 1)) {
        fprintf(stderr,
                "%s produced non-trit output in %s[%zu] at coeff %zu: output=%d input=%d\n",
                impl,
                tag,
                case_index,
                coeff_index,
                value,
                input);
        exit(1);
    }
}

static int32_t center_mod_q(int16_t input)
{
    int32_t centered = input;

    centered += (centered >> 31) & NTRUPLUS_Q;
    centered -= (NTRUPLUS_Q + 1) / 2;
    centered += (centered >> 31) & NTRUPLUS_Q;
    centered -= (NTRUPLUS_Q - 1) / 2;
    return centered;
}

static void require_mod3_congruence(const char *impl,
                                    const char *tag,
                                    size_t case_index,
                                    size_t coeff_index,
                                    int16_t input,
                                    int16_t output)
{
    int32_t centered = center_mod_q(input);
    int32_t delta = centered - output;

    if (delta % 3 != 0) {
        fprintf(stderr,
                "%s broke centered mod-3 congruence in %s[%zu] at coeff %zu: centered=%d output=%d input=%d delta=%d\n",
                impl,
                tag,
                case_index,
                coeff_index,
                centered,
                output,
                input,
                delta);
        exit(1);
    }
}

static void compare_vector(const char *mode,
                           const char *tag,
                           size_t case_index,
                           const int16_t input[NTRUPLUS_N],
                           const int16_t expected[NTRUPLUS_N],
                           const int16_t actual[NTRUPLUS_N])
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        if (input[i] >= -NTRUPLUS_Q && input[i] < NTRUPLUS_Q) {
            require_trit("ref", tag, case_index, i, expected[i], input[i]);
            require_trit("jasmin", tag, case_index, i, actual[i], input[i]);
            require_mod3_congruence("ref", tag, case_index, i, input[i], expected[i]);
            require_mod3_congruence("jasmin", tag, case_index, i, input[i], actual[i]);
        }
        if (expected[i] != actual[i]) {
            fprintf(stderr,
                    "mismatch in %s %s[%zu] at coeff %zu: ref=%d jasmin=%d input=%d\n",
                    mode,
                    tag,
                    case_index,
                    i,
                    expected[i],
                    actual[i],
                    input[i]);
            exit(1);
        }
    }
}

static void require_unchanged(const char *who,
                              const char *tag,
                              size_t case_index,
                              const int16_t before[NTRUPLUS_N],
                              const int16_t after[NTRUPLUS_N])
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        if (before[i] != after[i]) {
            fprintf(stderr,
                    "%s mutated input in %s[%zu] at coeff %zu: before=%d after=%d\n",
                    who,
                    tag,
                    case_index,
                    i,
                    before[i],
                    after[i]);
            exit(1);
        }
    }
}

static void check_disjoint_case(const char *tag, size_t case_index, const int16_t input[NTRUPLUS_N])
{
    int16_t c_input[NTRUPLUS_N];
    int16_t jasmin_input[NTRUPLUS_N];
    int16_t expected[NTRUPLUS_N];
    int16_t actual[NTRUPLUS_N];

    memcpy(c_input, input, sizeof(c_input));
    memcpy(jasmin_input, input, sizeof(jasmin_input));

    poly_crepmod3_ref(expected, c_input);
    jade_ntruplus_ntruplus768_amd64_ref_poly_crepmod3(actual, jasmin_input);

    compare_vector("disjoint", tag, case_index, input, expected, actual);
    require_unchanged("C poly_crepmod3()", tag, case_index, input, c_input);
    require_unchanged("Jasmin poly_crepmod3()", tag, case_index, input, jasmin_input);
}

static void check_alias_case(const char *tag, size_t case_index, const int16_t input[NTRUPLUS_N])
{
    int16_t disjoint[NTRUPLUS_N];
    int16_t expected_alias[NTRUPLUS_N];
    int16_t actual_alias[NTRUPLUS_N];

    poly_crepmod3_ref(disjoint, input);

    memcpy(expected_alias, input, sizeof(expected_alias));
    poly_crepmod3_ref_alias(expected_alias, expected_alias);
    compare_vector("c-alias-vs-disjoint", tag, case_index, input, disjoint, expected_alias);

    memcpy(actual_alias, input, sizeof(actual_alias));
    jade_ntruplus_ntruplus768_amd64_ref_poly_crepmod3(actual_alias, actual_alias);
    compare_vector("alias", tag, case_index, input, expected_alias, actual_alias);
}

static void check_case(const char *tag, size_t case_index, const int16_t input[NTRUPLUS_N])
{
    check_disjoint_case(tag, case_index, input);
    check_alias_case(tag, case_index, input);
}

static void run_boundary_cases(void)
{
    int16_t input[NTRUPLUS_N];
    const size_t sparse_indices[] = {0, 1, 2, 383, 384, 385, 766, 767};

    fill_constant(input, 0);
    check_case("boundary", 0, input);

    fill_constant(input, NTRUPLUS_Q - 1);
    check_case("boundary", 1, input);

    fill_constant(input, 1 - NTRUPLUS_Q);
    check_case("boundary", 2, input);

    fill_constant(input, NTRUPLUS_Q);
    check_case("boundary", 3, input);

    fill_constant(input, -NTRUPLUS_Q);
    check_case("boundary", 4, input);

    fill_alternating(input, NTRUPLUS_Q - 1, 1 - NTRUPLUS_Q);
    check_case("boundary", 5, input);

    fill_staircase(input, -NTRUPLUS_Q, 17);
    check_case("boundary", 6, input);

    fill_constant(input, 0);
    for (size_t i = 0; i < sizeof(sparse_indices) / sizeof(sparse_indices[0]); ++i) {
        input[sparse_indices[i]] = (int16_t)((i & 1u) == 0 ? NTRUPLUS_Q : -NTRUPLUS_Q);
    }
    check_case("boundary", 7, input);
}

static void run_random_cases(void)
{
    uint32_t state = 0x63f19a4du;

    for (size_t case_index = 0; case_index < RANDOM_CASES; ++case_index) {
        int16_t input[NTRUPLUS_N];

        for (size_t i = 0; i < NTRUPLUS_N; ++i) {
            input[i] = sample_mod_q(&state);
        }
        check_case("random", case_index, input);
    }
}

static void run_exhaustive_int16_cases(void)
{
    uint32_t next_value = (uint32_t)(uint16_t)INT16_MIN;
    size_t case_index = 0;

    while (1) {
        int16_t input[NTRUPLUS_N];

        for (size_t i = 0; i < NTRUPLUS_N; ++i) {
            input[i] = (int16_t)(uint16_t)next_value;
            if (next_value == (uint32_t)(uint16_t)INT16_MAX) {
                next_value = 0;
                i += 1;
                for (; i < NTRUPLUS_N; ++i) {
                    input[i] = INT16_MIN;
                }
                check_case("int16-exhaustive", case_index, input);
                return;
            }
            next_value = (next_value + 1u) & 0xffffu;
        }

        check_case("int16-exhaustive", case_index, input);
        case_index += 1;
    }
}

int main(void)
{
    run_boundary_cases();
    run_random_cases();
    run_exhaustive_int16_cases();

    printf("crepmod3 differential passed: 8 boundary + %d random + full int16 exhaustive, "
           "disjoint/input-immutable/exact-alias\n",
           RANDOM_CASES);
    return 0;
}
