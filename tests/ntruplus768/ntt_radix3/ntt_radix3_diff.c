#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define NTRUPLUS_N 768
#define NTRUPLUS_Q 3457
#define NTRUPLUS_QINV 12929
#define NTRUPLUS_STAGE1_ZETA (-1033)
#define NTRUPLUS_OMEGA (-886)

static const int16_t radix3_zetas[4] = {-682, -248, -708, 682};

extern void jade_ntruplus_ntruplus768_amd64_ref_ntt_stage1(
    int16_t r[NTRUPLUS_N], const int16_t a[NTRUPLUS_N]);
extern void jade_ntruplus_ntruplus768_amd64_ref_ntt_radix3(
    int16_t r[NTRUPLUS_N]);

static int16_t montgomery_reduce_ref(int32_t a)
{
    int16_t t;

    t = (int16_t)a * NTRUPLUS_QINV;
    t = (int16_t)((a - (int32_t)t * NTRUPLUS_Q) >> 16);
    return t;
}

static int16_t fqmul_ref(int16_t a, int16_t b)
{
    return montgomery_reduce_ref((int32_t)a * b);
}

static void ntt_stage1_ref(int16_t r[NTRUPLUS_N], const int16_t a[NTRUPLUS_N])
{
    for (size_t i = 0; i < NTRUPLUS_N / 2; ++i) {
        const int16_t t1 = fqmul_ref(NTRUPLUS_STAGE1_ZETA, a[i + NTRUPLUS_N / 2]);

        r[i + NTRUPLUS_N / 2] = (int16_t)(a[i] + a[i + NTRUPLUS_N / 2] - t1);
        r[i] = (int16_t)(a[i] + t1);
    }
}

static void ntt_radix3_ref(int16_t r[NTRUPLUS_N])
{
    size_t k = 0;

    for (size_t start = 0; start < NTRUPLUS_N; start += 384) {
        const int16_t zeta1 = radix3_zetas[k++];
        const int16_t zeta2 = radix3_zetas[k++];

        for (size_t i = start; i < start + 128; ++i) {
            const int16_t a0 = r[i];
            const int16_t t1 = fqmul_ref(zeta1, r[i + 128]);
            const int16_t t2 = fqmul_ref(zeta2, r[i + 256]);
            const int16_t t3 = fqmul_ref(NTRUPLUS_OMEGA, (int16_t)(t1 - t2));

            r[i + 256] = (int16_t)(a0 - t1 - t3);
            r[i + 128] = (int16_t)(a0 - t2 + t3);
            r[i] = (int16_t)(a0 + t1 + t2);
        }
    }
}

static void fill_constant_stage1_range(int16_t dst[NTRUPLUS_N],
                                       int16_t low_value,
                                       int16_t high_value)
{
    for (size_t i = 0; i < NTRUPLUS_N / 2; ++i) {
        dst[i] = low_value;
        dst[i + NTRUPLUS_N / 2] = high_value;
    }
}

static void fill_alternating_stage1_range(int16_t dst[NTRUPLUS_N])
{
    for (size_t i = 0; i < NTRUPLUS_N / 2; ++i) {
        dst[i] = (i & 1u) == 0 ? -2 * NTRUPLUS_Q : 2 * NTRUPLUS_Q - 1;
        dst[i + NTRUPLUS_N / 2] =
            (i & 1u) == 0 ? 3 * NTRUPLUS_Q - 1 : -3 * NTRUPLUS_Q;
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

static int16_t sample_symmetric_range(uint32_t *state, int32_t multiple)
{
    const uint32_t width = (uint32_t)(2 * multiple * NTRUPLUS_Q);

    return (int16_t)((int32_t)(next_u32(state) % width) - multiple * NTRUPLUS_Q);
}

static int16_t sample_qrange(uint32_t *state)
{
    return sample_symmetric_range(state, 1);
}

static void compare_output(const char *tag,
                           size_t case_index,
                           const int16_t expected[NTRUPLUS_N],
                           const int16_t actual[NTRUPLUS_N])
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        if (expected[i] != actual[i]) {
            fprintf(stderr,
                    "mismatch in %s[%zu] at coeff %zu: ref=%d jasmin=%d\n",
                    tag,
                    case_index,
                    i,
                    expected[i],
                    actual[i]);
            exit(1);
        }
    }
}

static void check_radix3_case(const char *tag,
                              size_t case_index,
                              const int16_t input[NTRUPLUS_N])
{
    int16_t expected[NTRUPLUS_N];
    int16_t actual[NTRUPLUS_N];

    memcpy(expected, input, sizeof(expected));
    memcpy(actual, input, sizeof(actual));
    ntt_radix3_ref(expected);
    jade_ntruplus_ntruplus768_amd64_ref_ntt_radix3(actual);
    compare_output(tag, case_index, expected, actual);
}

static void check_prefix_case(size_t case_index, const int16_t input[NTRUPLUS_N])
{
    int16_t expected[NTRUPLUS_N];
    int16_t disjoint[NTRUPLUS_N];
    int16_t inplace[NTRUPLUS_N];

    ntt_stage1_ref(expected, input);
    ntt_radix3_ref(expected);

    jade_ntruplus_ntruplus768_amd64_ref_ntt_stage1(disjoint, input);
    jade_ntruplus_ntruplus768_amd64_ref_ntt_radix3(disjoint);
    compare_output("stage1+radix3-disjoint", case_index, expected, disjoint);

    memcpy(inplace, input, sizeof(inplace));
    jade_ntruplus_ntruplus768_amd64_ref_ntt_stage1(inplace, inplace);
    jade_ntruplus_ntruplus768_amd64_ref_ntt_radix3(inplace);
    compare_output("stage1+radix3-in-place", case_index, expected, inplace);
}

static void run_boundary_cases(void)
{
    int16_t input[NTRUPLUS_N];

    fill_constant_stage1_range(input, 0, 0);
    check_radix3_case("boundary", 0, input);

    fill_constant_stage1_range(input, -2 * NTRUPLUS_Q, -3 * NTRUPLUS_Q);
    check_radix3_case("boundary", 1, input);

    fill_constant_stage1_range(input, 2 * NTRUPLUS_Q - 1, 3 * NTRUPLUS_Q - 1);
    check_radix3_case("boundary", 2, input);

    fill_alternating_stage1_range(input);
    check_radix3_case("boundary", 3, input);

    for (size_t sparse_case = 0; sparse_case < 4; ++sparse_case) {
        const size_t indices[4] = {128, 256, 512, 640};
        fill_constant_stage1_range(input, 0, 0);
        input[indices[sparse_case]] = (int16_t)(sparse_case < 2 ? 2 * NTRUPLUS_Q - 1
                                                                : 3 * NTRUPLUS_Q - 1);
        check_radix3_case("boundary", 4 + sparse_case, input);
    }

    fill_constant_stage1_range(input, 0, 0);
    input[128] = 2 * NTRUPLUS_Q - 1;
    input[256] = -2 * NTRUPLUS_Q;
    check_radix3_case("boundary", 8, input);

    fill_constant_stage1_range(input, 0, 0);
    input[512] = -3 * NTRUPLUS_Q;
    input[640] = 3 * NTRUPLUS_Q - 1;
    check_radix3_case("boundary", 9, input);
}

static void run_random_radix3_cases(void)
{
    uint32_t state = 0x9d7b34a1u;
    const size_t random_cases = 4096;

    for (size_t case_index = 0; case_index < random_cases; ++case_index) {
        int16_t input[NTRUPLUS_N];

        for (size_t i = 0; i < NTRUPLUS_N / 2; ++i) {
            input[i] = sample_symmetric_range(&state, 2);
            input[i + NTRUPLUS_N / 2] = sample_symmetric_range(&state, 3);
        }
        check_radix3_case("random-radix3", case_index, input);
    }
}

static void run_random_prefix_cases(void)
{
    uint32_t state = 0x6a09e667u;
    const size_t random_cases = 2048;

    for (size_t case_index = 0; case_index < random_cases; ++case_index) {
        int16_t input[NTRUPLUS_N];

        for (size_t i = 0; i < NTRUPLUS_N; ++i) {
            input[i] = sample_qrange(&state);
        }
        check_prefix_case(case_index, input);
    }
}

int main(void)
{
    run_boundary_cases();
    run_random_radix3_cases();
    run_random_prefix_cases();
    printf("ntt radix-3 differential passed: 10 boundary + 4096 radix-3 + "
           "2048 chained stage1 vectors; chained disjoint and in-place\n");
    return 0;
}
