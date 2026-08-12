#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define NTRUPLUS_N 768
#define NTRUPLUS_Q 3457
#define NTRUPLUS_QINV 12929
#define NTRUPLUS_STAGE1_ZETA (-1033)

extern void jade_ntruplus_ntruplus768_amd64_ref_ntt_stage1(
    int16_t r[NTRUPLUS_N], const int16_t a[NTRUPLUS_N]);

static int16_t montgomery_reduce_ref(int32_t a)
{
    int16_t t;

    t = (int16_t)a * NTRUPLUS_QINV;
    t = (int16_t)((a - (int32_t)t * NTRUPLUS_Q) >> 16);
    return t;
}

static void ntt_stage1_ref(int16_t r[NTRUPLUS_N], const int16_t a[NTRUPLUS_N])
{
    const int16_t zeta1 = NTRUPLUS_STAGE1_ZETA;

    for (size_t i = 0; i < NTRUPLUS_N / 2; ++i) {
        const int16_t t1 = montgomery_reduce_ref((int32_t)zeta1 * a[i + NTRUPLUS_N / 2]);

        r[i + NTRUPLUS_N / 2] = (int16_t)(a[i] + a[i + NTRUPLUS_N / 2] - t1);
        r[i] = (int16_t)(a[i] + t1);
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
    return (int16_t)((int32_t)(next_u32(state) % (2 * NTRUPLUS_Q + 1)) - NTRUPLUS_Q);
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
                    "mismatch in %s %s[%zu] at coeff %zu: ref=%d jasmin=%d input=%d pair=%zu\n",
                    mode,
                    tag,
                    case_index,
                    i,
                    expected[i],
                    actual[i],
                    input[i],
                    i % (NTRUPLUS_N / 2));
            exit(1);
        }
    }
}

static void check_case(const char *tag, size_t case_index, const int16_t input[NTRUPLUS_N])
{
    int16_t expected[NTRUPLUS_N];
    int16_t disjoint[NTRUPLUS_N];
    int16_t inplace[NTRUPLUS_N];

    ntt_stage1_ref(expected, input);
    jade_ntruplus_ntruplus768_amd64_ref_ntt_stage1(disjoint, input);
    compare_output("disjoint", tag, case_index, input, expected, disjoint);

    memcpy(inplace, input, sizeof(inplace));
    jade_ntruplus_ntruplus768_amd64_ref_ntt_stage1(inplace, inplace);
    compare_output("in-place", tag, case_index, input, expected, inplace);
}

static void run_boundary_cases(void)
{
    int16_t input[NTRUPLUS_N];

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

    fill_constant(input, 0);
    input[0] = NTRUPLUS_Q;
    check_case("boundary", 5, input);

    fill_constant(input, 0);
    input[NTRUPLUS_N / 2] = -NTRUPLUS_Q;
    check_case("boundary", 6, input);

    fill_constant(input, 0);
    input[NTRUPLUS_N / 2 - 1] = -NTRUPLUS_Q;
    input[NTRUPLUS_N - 1] = NTRUPLUS_Q;
    check_case("boundary", 7, input);
}

static void run_random_cases(void)
{
    uint32_t state = 0x5c31e97bu;
    const size_t random_cases = 4096;

    for (size_t case_index = 0; case_index < random_cases; ++case_index) {
        int16_t input[NTRUPLUS_N];

        for (size_t i = 0; i < NTRUPLUS_N; ++i) {
            input[i] = sample_mod_q(&state);
        }
        check_case("random", case_index, input);
    }

    printf("ntt stage-1 differential passed: 8 boundary + %zu random vectors, disjoint and in-place\n",
           random_cases);
}

int main(void)
{
    run_boundary_cases();
    run_random_cases();
    return 0;
}
