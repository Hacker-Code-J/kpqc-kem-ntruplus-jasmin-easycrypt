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
static const int16_t radix2_64_zetas[6] = {1, -722, -723, -257, -1124, -867};

extern void jade_ntruplus_ntruplus768_amd64_ref_ntt_stage1(
    int16_t r[NTRUPLUS_N], const int16_t a[NTRUPLUS_N]);
extern void jade_ntruplus_ntruplus768_amd64_ref_ntt_radix3(
    int16_t r[NTRUPLUS_N]);
extern void jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_64(
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

static int16_t barrett_reduce_ref(int16_t a)
{
    int16_t t;
    const int16_t v = ((1 << 26) + NTRUPLUS_Q / 2) / NTRUPLUS_Q;

    t = (int16_t)(((int32_t)v * a + (1 << 25)) >> 26);
    t = (int16_t)(t * NTRUPLUS_Q);
    return (int16_t)(a - t);
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

static void ntt_radix2_64_ref(int16_t r[NTRUPLUS_N])
{
    for (size_t block = 0; block < 6; ++block) {
        const size_t start = block * 128;
        const int16_t zeta = radix2_64_zetas[block];

        for (size_t i = start; i < start + 64; ++i) {
            const int16_t a0 = r[i];
            const int16_t t1 = fqmul_ref(zeta, r[i + 64]);

            r[i + 64] = barrett_reduce_ref((int16_t)(a0 - t1));
            r[i] = barrett_reduce_ref((int16_t)(a0 + t1));
        }
    }
}

static void require_step64_shape(const char *tag,
                                 size_t case_index,
                                 const int16_t values[NTRUPLUS_N])
{
    for (size_t i = 0; i < 384; ++i) {
        if (values[i] < -4 * NTRUPLUS_Q || values[i] >= 4 * NTRUPLUS_Q) {
            fprintf(stderr,
                    "%s[%zu] violates step64 low-half bound at coeff %zu: %d\n",
                    tag,
                    case_index,
                    i,
                    values[i]);
            exit(1);
        }
    }
    for (size_t i = 384; i < NTRUPLUS_N; ++i) {
        if (values[i] < -5 * NTRUPLUS_Q || values[i] >= 5 * NTRUPLUS_Q) {
            fprintf(stderr,
                    "%s[%zu] violates step64 high-half bound at coeff %zu: %d\n",
                    tag,
                    case_index,
                    i,
                    values[i]);
            exit(1);
        }
    }
}

static void fill_constant_step64_range(int16_t dst[NTRUPLUS_N],
                                       int16_t low_value,
                                       int16_t high_value)
{
    for (size_t i = 0; i < 384; ++i) {
        dst[i] = low_value;
        dst[i + 384] = high_value;
    }
}

static void fill_alternating_step64_range(int16_t dst[NTRUPLUS_N])
{
    for (size_t i = 0; i < 384; ++i) {
        dst[i] = (i & 1u) == 0 ? -4 * NTRUPLUS_Q : 4 * NTRUPLUS_Q - 1;
        dst[i + 384] = (i & 1u) == 0 ? -5 * NTRUPLUS_Q : 5 * NTRUPLUS_Q - 1;
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

static int16_t sample_half_open_multiple(uint32_t *state, int32_t multiple)
{
    const uint32_t width = (uint32_t)(2 * multiple * NTRUPLUS_Q);

    return (int16_t)((int32_t)(next_u32(state) % width) - multiple * NTRUPLUS_Q);
}

static int16_t sample_qrange(uint32_t *state)
{
    return sample_half_open_multiple(state, 1);
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

static void check_radix2_64_case(const char *tag,
                                 size_t case_index,
                                 const int16_t input[NTRUPLUS_N])
{
    int16_t expected[NTRUPLUS_N];
    int16_t actual[NTRUPLUS_N];

    require_step64_shape(tag, case_index, input);
    memcpy(expected, input, sizeof(expected));
    memcpy(actual, input, sizeof(actual));
    ntt_radix2_64_ref(expected);
    jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_64(actual);
    compare_output(tag, case_index, expected, actual);
}

static void check_prefix_case(size_t case_index, const int16_t input[NTRUPLUS_N])
{
    int16_t expected[NTRUPLUS_N];
    int16_t disjoint[NTRUPLUS_N];
    int16_t inplace[NTRUPLUS_N];

    ntt_stage1_ref(expected, input);
    ntt_radix3_ref(expected);
    require_step64_shape("prefix-shape", case_index, expected);
    ntt_radix2_64_ref(expected);

    jade_ntruplus_ntruplus768_amd64_ref_ntt_stage1(disjoint, input);
    jade_ntruplus_ntruplus768_amd64_ref_ntt_radix3(disjoint);
    jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_64(disjoint);
    compare_output("stage1+radix3+step64-disjoint", case_index, expected, disjoint);

    memcpy(inplace, input, sizeof(inplace));
    jade_ntruplus_ntruplus768_amd64_ref_ntt_stage1(inplace, inplace);
    jade_ntruplus_ntruplus768_amd64_ref_ntt_radix3(inplace);
    jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_64(inplace);
    compare_output("stage1+radix3+step64-in-place", case_index, expected, inplace);
}

static void run_boundary_cases(void)
{
    int16_t input[NTRUPLUS_N];
    const size_t sparse_indices[] = {0, 64, 127, 128, 192, 255, 384, 448, 640, 704, 767};

    fill_constant_step64_range(input, 0, 0);
    check_radix2_64_case("boundary", 0, input);

    fill_constant_step64_range(input, -4 * NTRUPLUS_Q, -5 * NTRUPLUS_Q);
    check_radix2_64_case("boundary", 1, input);

    fill_constant_step64_range(input, 4 * NTRUPLUS_Q - 1, 5 * NTRUPLUS_Q - 1);
    check_radix2_64_case("boundary", 2, input);

    fill_alternating_step64_range(input);
    check_radix2_64_case("boundary", 3, input);

    for (size_t sparse_case = 0; sparse_case < sizeof(sparse_indices) / sizeof(sparse_indices[0]); ++sparse_case) {
        fill_constant_step64_range(input, 0, 0);
        input[sparse_indices[sparse_case]] =
            (int16_t)(sparse_indices[sparse_case] < 384 ? 4 * NTRUPLUS_Q - 1 : 5 * NTRUPLUS_Q - 1);
        check_radix2_64_case("boundary", 4 + sparse_case, input);
    }
}

static void run_random_radix2_64_cases(void)
{
    uint32_t state = 0x7f4a7c15u;
    const size_t random_cases = 4096;

    for (size_t case_index = 0; case_index < random_cases; ++case_index) {
        int16_t input[NTRUPLUS_N];

        for (size_t i = 0; i < 384; ++i) {
            input[i] = sample_half_open_multiple(&state, 4);
            input[i + 384] = sample_half_open_multiple(&state, 5);
        }
        check_radix2_64_case("random-step64", case_index, input);
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
    run_random_radix2_64_cases();
    run_random_prefix_cases();
    printf("ntt radix-2 step64 differential passed: 15 boundary + 4096 direct + "
           "2048 chained stage1/radix3 vectors; chained disjoint and in-place\n");
    return 0;
}
