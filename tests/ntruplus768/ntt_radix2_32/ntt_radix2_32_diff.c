#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define NTRUPLUS_N 768
#define NTRUPLUS_Q 3457
#define NTRUPLUS_QINV 12929
#define NTRUPLUS_STAGE1_ZETA (-1033)
#define NTRUPLUS_OMEGA (-886)
#define NTRUPLUS_QHALF 1728

static const int16_t radix3_zetas[4] = {-682, -248, -708, 682};
static const int16_t radix2_64_zetas[6] = {1, -722, -723, -257, -1124, -867};
static const int16_t radix2_32_zetas[12] = {
    -256, 1484, 1262, -1590, 1611, 222, 1164, -1346, 1716, -1521, -357, 395};

extern void jade_ntruplus_ntruplus768_amd64_ref_ntt_stage1(
    int16_t r[NTRUPLUS_N], const int16_t a[NTRUPLUS_N]);
extern void jade_ntruplus_ntruplus768_amd64_ref_ntt_radix3(
    int16_t r[NTRUPLUS_N]);
extern void jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_64(
    int16_t r[NTRUPLUS_N]);
extern void jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_32(
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

static void ntt_radix2_32_ref(int16_t r[NTRUPLUS_N])
{
    for (size_t block = 0; block < 12; ++block) {
        const size_t start = block * 64;
        const int16_t zeta = radix2_32_zetas[block];

        for (size_t i = start; i < start + 32; ++i) {
            const int16_t a0 = r[i];
            const int16_t t1 = fqmul_ref(zeta, r[i + 32]);

            r[i + 32] = barrett_reduce_ref((int16_t)(a0 - t1));
            r[i] = barrett_reduce_ref((int16_t)(a0 + t1));
        }
    }
}

static void require_centered_step64_shape(const char *tag,
                                          size_t case_index,
                                          const int16_t values[NTRUPLUS_N])
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        if (values[i] < -NTRUPLUS_QHALF || values[i] > NTRUPLUS_QHALF) {
            fprintf(stderr,
                    "%s[%zu] violates centered step64 bound at coeff %zu: %d\n",
                    tag,
                    case_index,
                    i,
                    values[i]);
            exit(1);
        }
    }
}

static void fill_constant_centered_range(int16_t dst[NTRUPLUS_N], int16_t value)
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        dst[i] = value;
    }
}

static void fill_alternating_centered_range(int16_t dst[NTRUPLUS_N])
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        dst[i] = (i & 1u) == 0 ? -NTRUPLUS_QHALF : NTRUPLUS_QHALF;
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

static int16_t sample_centered_step64_value(uint32_t *state)
{
    return (int16_t)((int32_t)(next_u32(state) % (2u * NTRUPLUS_QHALF + 1u)) - NTRUPLUS_QHALF);
}

static int16_t sample_qrange(uint32_t *state)
{
    return (int16_t)((int32_t)(next_u32(state) % (2u * NTRUPLUS_Q)) - NTRUPLUS_Q);
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

static void check_radix2_32_case(const char *tag,
                                 size_t case_index,
                                 const int16_t input[NTRUPLUS_N])
{
    int16_t expected[NTRUPLUS_N];
    int16_t actual[NTRUPLUS_N];

    require_centered_step64_shape(tag, case_index, input);
    memcpy(expected, input, sizeof(expected));
    memcpy(actual, input, sizeof(actual));
    ntt_radix2_32_ref(expected);
    jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_32(actual);
    compare_output(tag, case_index, expected, actual);
}

static void check_prefix_case(size_t case_index, const int16_t input[NTRUPLUS_N])
{
    int16_t expected[NTRUPLUS_N];
    int16_t disjoint[NTRUPLUS_N];
    int16_t inplace[NTRUPLUS_N];

    ntt_stage1_ref(expected, input);
    ntt_radix3_ref(expected);
    ntt_radix2_64_ref(expected);
    require_centered_step64_shape("prefix-shape", case_index, expected);
    ntt_radix2_32_ref(expected);

    jade_ntruplus_ntruplus768_amd64_ref_ntt_stage1(disjoint, input);
    jade_ntruplus_ntruplus768_amd64_ref_ntt_radix3(disjoint);
    jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_64(disjoint);
    jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_32(disjoint);
    compare_output("stage1+radix3+step64+step32-disjoint", case_index, expected, disjoint);

    memcpy(inplace, input, sizeof(inplace));
    jade_ntruplus_ntruplus768_amd64_ref_ntt_stage1(inplace, inplace);
    jade_ntruplus_ntruplus768_amd64_ref_ntt_radix3(inplace);
    jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_64(inplace);
    jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_32(inplace);
    compare_output("stage1+radix3+step64+step32-in-place", case_index, expected, inplace);
}

static void run_boundary_cases(void)
{
    int16_t input[NTRUPLUS_N];
    const size_t sparse_indices[] = {
        0, 31, 32, 63, 64, 95, 96, 127, 384, 415, 736, 767};

    fill_constant_centered_range(input, 0);
    check_radix2_32_case("boundary", 0, input);

    fill_constant_centered_range(input, -NTRUPLUS_QHALF);
    check_radix2_32_case("boundary", 1, input);

    fill_constant_centered_range(input, NTRUPLUS_QHALF);
    check_radix2_32_case("boundary", 2, input);

    fill_alternating_centered_range(input);
    check_radix2_32_case("boundary", 3, input);

    for (size_t sparse_case = 0; sparse_case < sizeof(sparse_indices) / sizeof(sparse_indices[0]); ++sparse_case) {
        fill_constant_centered_range(input, 0);
        input[sparse_indices[sparse_case]] =
            (int16_t)((sparse_case & 1u) == 0 ? NTRUPLUS_QHALF : -NTRUPLUS_QHALF);
        check_radix2_32_case("boundary", 4 + sparse_case, input);
    }
}

static void run_random_radix2_32_cases(void)
{
    uint32_t state = 0x3c6ef372u;
    const size_t random_cases = 4096;

    for (size_t case_index = 0; case_index < random_cases; ++case_index) {
        int16_t input[NTRUPLUS_N];

        for (size_t i = 0; i < NTRUPLUS_N; ++i) {
            input[i] = sample_centered_step64_value(&state);
        }
        check_radix2_32_case("random-step32", case_index, input);
    }
}

static void run_random_prefix_cases(void)
{
    uint32_t state = 0x510e527fu;
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
    run_random_radix2_32_cases();
    run_random_prefix_cases();
    printf("ntt radix-2 step32 differential passed: 16 boundary + 4096 direct + "
           "2048 chained stage1/radix3/step64 vectors; chained disjoint and in-place\n");
    return 0;
}
