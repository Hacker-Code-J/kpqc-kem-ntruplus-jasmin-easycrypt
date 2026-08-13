#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define NTRUPLUS_N 768
#define NTRUPLUS_Q 3457

extern void ntt(int16_t r[NTRUPLUS_N], const int16_t a[NTRUPLUS_N]);
extern void jade_ntruplus_ntruplus768_amd64_ref_ntt(
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
    return (int16_t)((int32_t)(next_u32(state) % (2 * NTRUPLUS_Q + 1u)) - NTRUPLUS_Q);
}

static void compare_output(const char *mode,
                           const char *tag,
                           size_t case_index,
                           const int16_t input[NTRUPLUS_N],
                           const int16_t expected[NTRUPLUS_N],
                           const int16_t actual[NTRUPLUS_N])
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
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

static void check_case(const char *tag, size_t case_index, const int16_t input[NTRUPLUS_N])
{
    int16_t expected_disjoint[NTRUPLUS_N];
    int16_t actual_disjoint[NTRUPLUS_N];
    int16_t expected_inplace[NTRUPLUS_N];
    int16_t actual_inplace[NTRUPLUS_N];

    ntt(expected_disjoint, input);
    jade_ntruplus_ntruplus768_amd64_ref_ntt(actual_disjoint, input);
    compare_output("disjoint", tag, case_index, input, expected_disjoint, actual_disjoint);

    memcpy(expected_inplace, input, sizeof(expected_inplace));
    memcpy(actual_inplace, input, sizeof(actual_inplace));
    ntt(expected_inplace, expected_inplace);
    jade_ntruplus_ntruplus768_amd64_ref_ntt(actual_inplace, actual_inplace);
    compare_output("in-place", tag, case_index, input, expected_inplace, actual_inplace);
}

static void run_boundary_cases(void)
{
    int16_t input[NTRUPLUS_N];
    const size_t sparse_indices[] = {0, 1, 383, 384, 385, 767};

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

    fill_constant(input, 0);
    for (size_t i = 0; i < NTRUPLUS_N / 2; ++i) {
        input[i] = NTRUPLUS_Q;
        input[i + NTRUPLUS_N / 2] = -NTRUPLUS_Q;
    }
    check_case("boundary", 7, input);
}

static void run_random_cases(void)
{
    uint32_t state = 0x4a3c91d5u;
    const size_t random_cases = 4096;

    for (size_t case_index = 0; case_index < random_cases; ++case_index) {
        int16_t input[NTRUPLUS_N];

        for (size_t i = 0; i < NTRUPLUS_N; ++i) {
            input[i] = sample_mod_q(&state);
        }
        check_case("random", case_index, input);
    }

    printf("ntt differential passed: 8 boundary + %zu random vectors, disjoint and in-place\n",
           random_cases);
}

int main(void)
{
    run_boundary_cases();
    run_random_cases();
    return 0;
}
