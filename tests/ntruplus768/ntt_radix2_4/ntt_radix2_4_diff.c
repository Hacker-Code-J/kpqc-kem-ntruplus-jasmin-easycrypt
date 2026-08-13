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
static const int16_t radix2_16_zetas[24] = {
    -455, 639, 502, 655, -699, 541, 95, -1577, -1241, 550, -44, 39,
    -820, -216, -121, -757, -348, 937, 893, 387, -603, 1713, -1105, 1058};
static const int16_t radix2_8_zetas[48] = {
    1449, 837, 901, 1637, -569, -1617, -1530, 1199, 50, -830, -625, 4,
    176, -156, 1257, -1507, -380, -606, 1293, 661, 1428, -1580, -565, -992,
    548, -800, 64, -371, 961, 641, 87, 630, 675, -834, 205, 54,
    -1081, 1351, 1413, -1331, -1673, -1267, -1558, 281, -1464, -588, 1015, 436};
static const int16_t radix2_4_zetas[96] = {
    223, 1138, -1059, -397, -183, 1655, 559, -1674, 277, 933, 1723, 437,
    -1514, 242, 1640, 432, -1583, 696, 774, 1671, 927, 514, 512, 489,
    297, 601, 1473, 1130, 1322, 871, 760, 1212, -312, -352, 443, 943,
    8, 1250, -100, 1660, -31, 1206, -1341, -1247, 444, 235, 1364, -1209,
    361, 230, 673, 582, 1409, 1501, 1401, 251, 1022, -1063, 1053, 1188,
    417, -1391, -27, -1626, 1685, -315, 1408, -1248, 400, 274, -1543, 32,
    -1550, 1531, -1367, -124, 1458, 1379, -940, -1681, 22, 1709, -275, 1108,
    354, -1728, -968, 858, 1221, -218, 294, -732, -1095, 892, 1588, -779};

extern void jade_ntruplus_ntruplus768_amd64_ref_ntt_stage1(
    int16_t r[NTRUPLUS_N], const int16_t a[NTRUPLUS_N]);
extern void jade_ntruplus_ntruplus768_amd64_ref_ntt_radix3(
    int16_t r[NTRUPLUS_N]);
extern void jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_64(
    int16_t r[NTRUPLUS_N]);
extern void jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_32(
    int16_t r[NTRUPLUS_N]);
extern void jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_16(
    int16_t r[NTRUPLUS_N]);
extern void jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_8(
    int16_t r[NTRUPLUS_N]);
extern void jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_4(
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

static void ntt_radix2_16_ref(int16_t r[NTRUPLUS_N])
{
    for (size_t block = 0; block < 24; ++block) {
        const size_t start = block * 32;
        const int16_t zeta = radix2_16_zetas[block];

        for (size_t i = start; i < start + 16; ++i) {
            const int16_t a0 = r[i];
            const int16_t t1 = fqmul_ref(zeta, r[i + 16]);

            r[i + 16] = barrett_reduce_ref((int16_t)(a0 - t1));
            r[i] = barrett_reduce_ref((int16_t)(a0 + t1));
        }
    }
}

static void ntt_radix2_8_ref(int16_t r[NTRUPLUS_N])
{
    for (size_t block = 0; block < 48; ++block) {
        const size_t start = block * 16;
        const int16_t zeta = radix2_8_zetas[block];

        for (size_t i = start; i < start + 8; ++i) {
            const int16_t a0 = r[i];
            const int16_t t1 = fqmul_ref(zeta, r[i + 8]);

            r[i + 8] = barrett_reduce_ref((int16_t)(a0 - t1));
            r[i] = barrett_reduce_ref((int16_t)(a0 + t1));
        }
    }
}

static void ntt_radix2_4_ref(int16_t r[NTRUPLUS_N])
{
    for (size_t block = 0; block < 96; ++block) {
        const size_t start = block * 8;
        const int16_t zeta = radix2_4_zetas[block];

        for (size_t i = start; i < start + 4; ++i) {
            const int16_t a0 = r[i];
            const int16_t t1 = fqmul_ref(zeta, r[i + 4]);

            r[i + 4] = barrett_reduce_ref((int16_t)(a0 - t1));
            r[i] = barrett_reduce_ref((int16_t)(a0 + t1));
        }
    }
}

static void require_centered_step8_shape(const char *tag,
                                         size_t case_index,
                                         const int16_t values[NTRUPLUS_N])
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        if (values[i] < -NTRUPLUS_QHALF || values[i] > NTRUPLUS_QHALF) {
            fprintf(stderr,
                    "%s[%zu] violates centered step8 bound at coeff %zu: %d\n",
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

static int16_t sample_centered_step8_value(uint32_t *state)
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

static void check_radix2_4_case(const char *tag,
                                size_t case_index,
                                const int16_t input[NTRUPLUS_N])
{
    int16_t expected[NTRUPLUS_N];
    int16_t actual[NTRUPLUS_N];

    require_centered_step8_shape(tag, case_index, input);
    memcpy(expected, input, sizeof(expected));
    memcpy(actual, input, sizeof(actual));
    ntt_radix2_4_ref(expected);
    jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_4(actual);
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
    ntt_radix2_32_ref(expected);
    ntt_radix2_16_ref(expected);
    ntt_radix2_8_ref(expected);
    require_centered_step8_shape("prefix-shape", case_index, expected);
    ntt_radix2_4_ref(expected);

    jade_ntruplus_ntruplus768_amd64_ref_ntt_stage1(disjoint, input);
    jade_ntruplus_ntruplus768_amd64_ref_ntt_radix3(disjoint);
    jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_64(disjoint);
    jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_32(disjoint);
    jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_16(disjoint);
    jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_8(disjoint);
    jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_4(disjoint);
    compare_output(
        "stage1+radix3+step64+step32+step16+step8+step4-disjoint",
        case_index,
        expected,
        disjoint);

    memcpy(inplace, input, sizeof(inplace));
    jade_ntruplus_ntruplus768_amd64_ref_ntt_stage1(inplace, inplace);
    jade_ntruplus_ntruplus768_amd64_ref_ntt_radix3(inplace);
    jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_64(inplace);
    jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_32(inplace);
    jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_16(inplace);
    jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_8(inplace);
    jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_4(inplace);
    compare_output(
        "stage1+radix3+step64+step32+step16+step8+step4-in-place",
        case_index,
        expected,
        inplace);
}

static void run_boundary_cases(void)
{
    int16_t input[NTRUPLUS_N];
    const size_t sparse_indices[] = {
        0, 3, 4, 7, 8, 11, 12, 15, 16, 19, 20, 23, 24, 27, 28, 31,
        384, 387, 388, 391, 392, 395, 396, 399,
        736, 739, 740, 743, 744, 747, 748, 751, 752, 755, 756, 759, 760, 763, 764, 767};

    fill_constant_centered_range(input, 0);
    check_radix2_4_case("boundary", 0, input);

    fill_constant_centered_range(input, -NTRUPLUS_QHALF);
    check_radix2_4_case("boundary", 1, input);

    fill_constant_centered_range(input, NTRUPLUS_QHALF);
    check_radix2_4_case("boundary", 2, input);

    fill_alternating_centered_range(input);
    check_radix2_4_case("boundary", 3, input);

    for (size_t sparse_case = 0; sparse_case < sizeof(sparse_indices) / sizeof(sparse_indices[0]); ++sparse_case) {
        fill_constant_centered_range(input, 0);
        input[sparse_indices[sparse_case]] =
            (int16_t)((sparse_case & 1u) == 0 ? NTRUPLUS_QHALF : -NTRUPLUS_QHALF);
        check_radix2_4_case("boundary", 4 + sparse_case, input);
    }
}

static void run_random_radix2_4_cases(void)
{
    uint32_t state = 0xc2b2ae35u;
    const size_t random_cases = 4096;

    for (size_t case_index = 0; case_index < random_cases; ++case_index) {
        int16_t input[NTRUPLUS_N];

        for (size_t i = 0; i < NTRUPLUS_N; ++i) {
            input[i] = sample_centered_step8_value(&state);
        }
        check_radix2_4_case("random-step4", case_index, input);
    }
}

static void run_random_prefix_cases(void)
{
    uint32_t state = 0x94d049bbu;
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
    run_random_radix2_4_cases();
    run_random_prefix_cases();
    printf("ntt radix-2 step4 differential passed: 44 boundary + 4096 direct + "
           "2048 chained stage1/radix3/step64/step32/step16/step8 vectors; "
           "chained disjoint and in-place\n");
    return 0;
}
