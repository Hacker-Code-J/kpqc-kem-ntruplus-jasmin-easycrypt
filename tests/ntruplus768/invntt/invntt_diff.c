#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define NTRUPLUS_N 768
#define NTRUPLUS_Q 3457
#define RANDOM_CASES 4096

extern void invntt(int16_t r[NTRUPLUS_N], const int16_t a[NTRUPLUS_N]);
extern void jade_ntruplus_ntruplus768_amd64_ref_invntt(
    int16_t r[NTRUPLUS_N], const int16_t a[NTRUPLUS_N]);

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
    return (int16_t)((int32_t)(next_u32(state) % (2 * NTRUPLUS_Q)) - NTRUPLUS_Q);
}

static void compare_vector(const char *mode,
                           const char *tag,
                           size_t case_index,
                           const int16_t input[NTRUPLUS_N],
                           const int16_t expected[NTRUPLUS_N],
                           const int16_t actual[NTRUPLUS_N])
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        if (expected[i] != actual[i]) {
            fprintf(stderr,
                    "mismatch in %s %s[%zu] at coeff %zu: c=%d jasmin=%d input=%d\n",
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
                              const int16_t original[NTRUPLUS_N],
                              const int16_t after[NTRUPLUS_N])
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        if (original[i] != after[i]) {
            fprintf(stderr,
                    "%s mutated input in %s[%zu] at coeff %zu: before=%d after=%d\n",
                    who,
                    tag,
                    case_index,
                    i,
                    original[i],
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

    invntt(expected, c_input);
    jade_ntruplus_ntruplus768_amd64_ref_invntt(actual, jasmin_input);

    compare_vector("disjoint", tag, case_index, input, expected, actual);
    require_unchanged("C invntt()", tag, case_index, input, c_input);
    require_unchanged("Jasmin invntt()", tag, case_index, input, jasmin_input);
}

static void check_alias_case(const char *tag, size_t case_index, const int16_t input[NTRUPLUS_N])
{
    int16_t expected_alias[NTRUPLUS_N];
    int16_t actual_alias[NTRUPLUS_N];
    int16_t disjoint[NTRUPLUS_N];

    memcpy(expected_alias, input, sizeof(expected_alias));
    memcpy(actual_alias, input, sizeof(actual_alias));

    invntt(disjoint, input);
    invntt(expected_alias, expected_alias);
    compare_vector("c-alias-vs-disjoint", tag, case_index, input, disjoint, expected_alias);

    jade_ntruplus_ntruplus768_amd64_ref_invntt(actual_alias, actual_alias);
    compare_vector("alias", tag, case_index, input, expected_alias, actual_alias);
}

static void check_case(const char *tag,
                       size_t case_index,
                       const int16_t input[NTRUPLUS_N])
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

    fill_constant(input, NTRUPLUS_Q);
    check_case("boundary", 1, input);

    fill_constant(input, -NTRUPLUS_Q);
    check_case("boundary", 2, input);

    fill_alternating(input, NTRUPLUS_Q, -NTRUPLUS_Q);
    check_case("boundary", 3, input);

    fill_staircase(input, -NTRUPLUS_Q, 17);
    check_case("boundary", 4, input);

    fill_staircase(input, NTRUPLUS_Q, -29);
    check_case("boundary", 5, input);

    fill_constant(input, 0);
    for (size_t i = 0; i < sizeof(sparse_indices) / sizeof(sparse_indices[0]); ++i) {
        input[sparse_indices[i]] = (int16_t)((i & 1u) == 0 ? NTRUPLUS_Q : -NTRUPLUS_Q);
    }
    check_case("boundary", 6, input);

    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        input[i] = (int16_t)((i < NTRUPLUS_N / 2) ? (NTRUPLUS_Q - 1) : (1 - NTRUPLUS_Q));
    }
    check_case("boundary", 7, input);
}

static void run_random_cases(void)
{
    uint32_t state = 0x8c13d52au;

    for (size_t case_index = 0; case_index < RANDOM_CASES; ++case_index) {
        int16_t input[NTRUPLUS_N];

        for (size_t i = 0; i < NTRUPLUS_N; ++i) {
            input[i] = sample_mod_q(&state);
        }
        check_case("random", case_index, input);
    }
}

int main(void)
{
    run_boundary_cases();
    run_random_cases();

    printf("invntt differential passed: 8 boundary + %d random vectors, disjoint/input-immutable/exact-alias\n",
           RANDOM_CASES);

    return 0;
}
