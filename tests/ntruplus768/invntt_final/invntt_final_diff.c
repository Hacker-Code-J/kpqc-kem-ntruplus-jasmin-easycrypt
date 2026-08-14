#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define NTRUPLUS_N 768
#define NTRUPLUS_HALF 384
#define NTRUPLUS_Q 3457
#define NTRUPLUS_QINV 12929
#define NTRUPLUS_OMEGA (-886)
#define NTRUPLUS_ZMINUSZ5INV (-1665)
#define NTRUPLUS_NINV (-811)
#define NTRUPLUS_2NINV (-1622)
#define STANDALONE_RANDOM_CASES 2048
#define COMPOSED_RANDOM_CASES 2048

static const int16_t invntt_radix2_4_zetas[96] = {
    -779, 1588, 892, -1095, -732, 294, -218, 1221, 858, -968, -1728, 354,
    1108, -275, 1709, 22, -1681, -940, 1379, 1458, -124, -1367, 1531, -1550,
    32, -1543, 274, 400, -1248, 1408, -315, 1685, -1626, -27, -1391, 417,
    1188, 1053, -1063, 1022, 251, 1401, 1501, 1409, 582, 673, 230, 361,
    -1209, 1364, 235, 444, -1247, -1341, 1206, -31, 1660, -100, 1250, 8,
    943, 443, -352, -312, 1212, 760, 871, 1322, 1130, 1473, 601, 297,
    489, 512, 514, 927, 1671, 774, 696, -1583, 432, 1640, 242, -1514,
    437, 1723, 933, 277, -1674, 559, 1655, -183, -397, -1059, 1138, 223,
};

static const int16_t invntt_radix2_8_zetas[48] = {
    436, 1015, -588, -1464, 281, -1558, -1267, -1673, -1331, 1413, 1351, -1081,
    54, 205, -834, 675, 630, 87, 641, 961, -371, 64, -800, 548,
    -992, -565, -1580, 1428, 661, 1293, -606, -380, -1507, 1257, -156, 176,
    4, -625, -830, 50, 1199, -1530, -1617, -569, 1637, 901, 837, 1449,
};

static const int16_t invntt_radix2_16_zetas[24] = {
    1058, -1105, 1713, -603, 387, 893, 937, -348, -757, -121, -216, -820,
    39, -44, 550, -1241, -1577, 95, 541, -699, 655, 502, 639, -455,
};

static const int16_t invntt_radix2_32_zetas[12] = {
    395, -357, -1521, 1716, -1346, 1164, 222, 1611, -1590, 1262, 1484, -256,
};

static const int16_t invntt_radix2_64_zetas[6] = {
    -867, -1124, -257, -723, -722, 1,
};

static const int16_t invntt_radix3_zetas[4] = {
    -708, 682, -682, -248,
};

extern void jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4(
    int16_t r[NTRUPLUS_N]);
extern void jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_8(
    int16_t r[NTRUPLUS_N]);
extern void jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_16(
    int16_t r[NTRUPLUS_N]);
extern void jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_32(
    int16_t r[NTRUPLUS_N]);
extern void jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_64(
    int16_t r[NTRUPLUS_N]);
extern void jade_ntruplus_ntruplus768_amd64_ref_invntt_radix3(
    int16_t r[NTRUPLUS_N]);
extern void jade_ntruplus_ntruplus768_amd64_ref_invntt_final(
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

static void invntt_radix2_4_ref(int16_t r[NTRUPLUS_N], const int16_t a[NTRUPLUS_N])
{
    memcpy(r, a, sizeof(int16_t) * NTRUPLUS_N);

    for (size_t block = 0; block < 96; ++block) {
        const size_t start = block * 8;
        const int16_t zeta = invntt_radix2_4_zetas[block];

        for (size_t i = start; i < start + 4; ++i) {
            const int16_t low = r[i];
            const int16_t high = r[i + 4];

            r[i] = barrett_reduce_ref((int16_t)(low + high));
            r[i + 4] = fqmul_ref(zeta, (int16_t)(high - low));
        }
    }
}

static void invntt_radix2_8_ref(int16_t r[NTRUPLUS_N], const int16_t a[NTRUPLUS_N])
{
    memcpy(r, a, sizeof(int16_t) * NTRUPLUS_N);

    for (size_t block = 0; block < 48; ++block) {
        const size_t start = block * 16;
        const int16_t zeta = invntt_radix2_8_zetas[block];

        for (size_t i = start; i < start + 8; ++i) {
            const int16_t low = r[i];
            const int16_t high = r[i + 8];

            r[i] = barrett_reduce_ref((int16_t)(low + high));
            r[i + 8] = fqmul_ref(zeta, (int16_t)(high - low));
        }
    }
}

static void invntt_radix2_16_ref(int16_t r[NTRUPLUS_N], const int16_t a[NTRUPLUS_N])
{
    memcpy(r, a, sizeof(int16_t) * NTRUPLUS_N);

    for (size_t block = 0; block < 24; ++block) {
        const size_t start = block * 32;
        const int16_t zeta = invntt_radix2_16_zetas[block];

        for (size_t i = start; i < start + 16; ++i) {
            const int16_t low = r[i];
            const int16_t high = r[i + 16];

            r[i] = barrett_reduce_ref((int16_t)(low + high));
            r[i + 16] = fqmul_ref(zeta, (int16_t)(high - low));
        }
    }
}

static void invntt_radix2_32_ref(int16_t r[NTRUPLUS_N], const int16_t a[NTRUPLUS_N])
{
    memcpy(r, a, sizeof(int16_t) * NTRUPLUS_N);

    for (size_t block = 0; block < 12; ++block) {
        const size_t start = block * 64;
        const int16_t zeta = invntt_radix2_32_zetas[block];

        for (size_t i = start; i < start + 32; ++i) {
            const int16_t low = r[i];
            const int16_t high = r[i + 32];

            r[i] = barrett_reduce_ref((int16_t)(low + high));
            r[i + 32] = fqmul_ref(zeta, (int16_t)(high - low));
        }
    }
}

static void invntt_radix2_64_ref(int16_t r[NTRUPLUS_N], const int16_t a[NTRUPLUS_N])
{
    memcpy(r, a, sizeof(int16_t) * NTRUPLUS_N);

    for (size_t block = 0; block < 6; ++block) {
        const size_t start = block * 128;
        const int16_t zeta = invntt_radix2_64_zetas[block];

        for (size_t i = start; i < start + 64; ++i) {
            const int16_t low = r[i];
            const int16_t high = r[i + 64];

            r[i] = barrett_reduce_ref((int16_t)(low + high));
            r[i + 64] = fqmul_ref(zeta, (int16_t)(high - low));
        }
    }
}

static void invntt_radix3_ref(int16_t r[NTRUPLUS_N], const int16_t a[NTRUPLUS_N])
{
    memcpy(r, a, sizeof(int16_t) * NTRUPLUS_N);

    for (size_t block = 0; block < 2; ++block) {
        const size_t start = block * NTRUPLUS_HALF;
        const int16_t zeta1 = invntt_radix3_zetas[2 * block];
        const int16_t zeta2 = invntt_radix3_zetas[2 * block + 1];

        for (size_t i = start; i < start + 128; ++i) {
            const int16_t a0 = r[i];
            const int16_t a1 = r[i + 128];
            const int16_t a2 = r[i + 256];
            const int16_t t1 = fqmul_ref(NTRUPLUS_OMEGA, (int16_t)(a1 - a0));
            const int16_t t2 = fqmul_ref(zeta1, (int16_t)(a2 - a0 + t1));
            const int16_t t3 = fqmul_ref(zeta2, (int16_t)(a2 - a1 - t1));

            r[i] = (int16_t)(a0 + a1 + a2);
            r[i + 128] = t2;
            r[i + 256] = t3;
        }
    }
}

static void invntt_final_ref(int16_t r[NTRUPLUS_N], const int16_t a[NTRUPLUS_N])
{
    memcpy(r, a, sizeof(int16_t) * NTRUPLUS_N);

    for (size_t i = 0; i < NTRUPLUS_HALF; ++i) {
        const int16_t t1 = (int16_t)(r[i] + r[i + NTRUPLUS_HALF]);
        const int16_t t2 = fqmul_ref(NTRUPLUS_ZMINUSZ5INV, (int16_t)(r[i] - r[i + NTRUPLUS_HALF]));

        r[i] = fqmul_ref(NTRUPLUS_NINV, (int16_t)(t1 - t2));
        r[i + NTRUPLUS_HALF] = fqmul_ref(NTRUPLUS_2NINV, t2);
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

static int16_t sample_qrange(uint32_t *state)
{
    return (int16_t)((int32_t)(next_u32(state) % (2u * NTRUPLUS_Q)) - NTRUPLUS_Q);
}

static int16_t sample_signed_range(uint32_t *state, int32_t limit)
{
    return (int16_t)((int32_t)(next_u32(state) % (uint32_t)(2 * limit)) - limit);
}

static int is_sum_lane(size_t index)
{
    return index < 128 || (index >= 384 && index < 512);
}

static void assert_post_radix3_shape(const int16_t input[NTRUPLUS_N], const char *tag, size_t case_index)
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        const int32_t bound = is_sum_lane(i) ? 3 * NTRUPLUS_Q : NTRUPLUS_Q;

        if (input[i] < -bound || input[i] >= bound) {
            fprintf(stderr,
                    "invalid post-radix3 shape in %s[%zu] at coeff %zu: value=%d bound=%d\n",
                    tag,
                    case_index,
                    i,
                    input[i],
                    bound);
            exit(1);
        }
    }
}

static void assert_qrange_input(const int16_t input[NTRUPLUS_N], const char *tag, size_t case_index)
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        if (input[i] < -NTRUPLUS_Q || input[i] >= NTRUPLUS_Q) {
            fprintf(stderr,
                    "invalid qrange input in %s[%zu] at coeff %zu: value=%d bound=%d\n",
                    tag,
                    case_index,
                    i,
                    input[i],
                    NTRUPLUS_Q);
            exit(1);
        }
    }
}

static void fill_zero(int16_t dst[NTRUPLUS_N])
{
    memset(dst, 0, sizeof(int16_t) * NTRUPLUS_N);
}

static void fill_sum_lane_extremes(int16_t dst[NTRUPLUS_N])
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        if (is_sum_lane(i)) {
            dst[i] = (i & 1u) == 0 ? (int16_t)(-3 * NTRUPLUS_Q) : (int16_t)(3 * NTRUPLUS_Q - 1);
        } else {
            dst[i] = (i & 1u) == 0 ? -NTRUPLUS_Q : (NTRUPLUS_Q - 1);
        }
    }
}

static void fill_half_difference_edges(int16_t dst[NTRUPLUS_N])
{
    fill_zero(dst);
    for (size_t i = 0; i < NTRUPLUS_HALF; ++i) {
        const int32_t low_bound = is_sum_lane(i) ? 3 * NTRUPLUS_Q : NTRUPLUS_Q;
        const int32_t high_bound = is_sum_lane(i + NTRUPLUS_HALF) ? 3 * NTRUPLUS_Q : NTRUPLUS_Q;

        dst[i] = (i & 1u) == 0 ? (int16_t)(low_bound - 1) : (int16_t)(-low_bound);
        dst[i + NTRUPLUS_HALF] = (i & 1u) == 0 ? (int16_t)(high_bound - 1) : (int16_t)(-high_bound);
    }
}

static void fill_sparse_pair_edges(int16_t dst[NTRUPLUS_N])
{
    fill_zero(dst);
    dst[0] = (int16_t)(3 * NTRUPLUS_Q - 1);
    dst[127] = (int16_t)(-3 * NTRUPLUS_Q);
    dst[128] = NTRUPLUS_Q - 1;
    dst[255] = -NTRUPLUS_Q;
    dst[256] = -NTRUPLUS_Q;
    dst[383] = NTRUPLUS_Q - 1;
    dst[384] = (int16_t)(-3 * NTRUPLUS_Q);
    dst[511] = (int16_t)(3 * NTRUPLUS_Q - 1);
    dst[512] = NTRUPLUS_Q - 1;
    dst[639] = -NTRUPLUS_Q;
    dst[640] = -NTRUPLUS_Q;
    dst[767] = NTRUPLUS_Q - 1;
}

static void fill_balanced_pair_stress(int16_t dst[NTRUPLUS_N])
{
    fill_zero(dst);
    for (size_t i = 0; i < NTRUPLUS_HALF; ++i) {
        const int16_t low = is_sum_lane(i)
            ? (int16_t)((int)(i % (size_t)(6 * NTRUPLUS_Q)) - (3 * NTRUPLUS_Q))
            : (int16_t)((int)(i % (size_t)(2 * NTRUPLUS_Q)) - NTRUPLUS_Q);
        const int16_t high = is_sum_lane(i + NTRUPLUS_HALF)
            ? (int16_t)((int)((i * 17u) % (size_t)(6 * NTRUPLUS_Q)) - (3 * NTRUPLUS_Q))
            : (int16_t)((int)((i * 11u) % (size_t)(2 * NTRUPLUS_Q)) - NTRUPLUS_Q);

        dst[i] = low;
        dst[i + NTRUPLUS_HALF] = high;
    }
}

static void fill_qrange_alternating_extremes(int16_t dst[NTRUPLUS_N])
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        dst[i] = (i & 1u) == 0 ? -NTRUPLUS_Q : (NTRUPLUS_Q - 1);
    }
}

static void fill_qrange_half_difference_edges(int16_t dst[NTRUPLUS_N])
{
    fill_zero(dst);
    for (size_t i = 0; i < NTRUPLUS_HALF; ++i) {
        dst[i] = (i & 1u) == 0 ? (NTRUPLUS_Q - 1) : -NTRUPLUS_Q;
        dst[i + NTRUPLUS_HALF] = (i & 1u) == 0 ? -NTRUPLUS_Q : (NTRUPLUS_Q - 1);
    }
}

static void fill_qrange_sparse_edges(int16_t dst[NTRUPLUS_N])
{
    fill_zero(dst);
    dst[0] = NTRUPLUS_Q - 1;
    dst[127] = -NTRUPLUS_Q;
    dst[128] = -NTRUPLUS_Q;
    dst[255] = NTRUPLUS_Q - 1;
    dst[256] = NTRUPLUS_Q - 1;
    dst[383] = -NTRUPLUS_Q;
    dst[384] = -NTRUPLUS_Q;
    dst[511] = NTRUPLUS_Q - 1;
    dst[512] = NTRUPLUS_Q - 1;
    dst[639] = -NTRUPLUS_Q;
    dst[640] = -NTRUPLUS_Q;
    dst[767] = NTRUPLUS_Q - 1;
}

static void fill_qrange_balanced_stress(int16_t dst[NTRUPLUS_N])
{
    fill_zero(dst);
    for (size_t i = 0; i < NTRUPLUS_HALF; ++i) {
        const int16_t low = (int16_t)((int)(i % (size_t)(2 * NTRUPLUS_Q)) - NTRUPLUS_Q);
        const int16_t high = (int16_t)((int)((i * 11u) % (size_t)(2 * NTRUPLUS_Q)) - NTRUPLUS_Q);

        dst[i] = low;
        dst[i + NTRUPLUS_HALF] = high;
    }
}

static void fill_post_radix3_random(int16_t dst[NTRUPLUS_N], uint32_t seed)
{
    uint32_t state = seed;

    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        dst[i] = is_sum_lane(i)
            ? sample_signed_range(&state, 3 * NTRUPLUS_Q)
            : sample_signed_range(&state, NTRUPLUS_Q);
    }
}

static void fill_random_qrange(int16_t dst[NTRUPLUS_N], uint32_t seed)
{
    uint32_t state = seed;

    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        dst[i] = sample_qrange(&state);
    }
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

static void run_standalone_case(const char *tag,
                                size_t case_index,
                                const int16_t input[NTRUPLUS_N])
{
    int16_t expected[NTRUPLUS_N];
    int16_t actual[NTRUPLUS_N];

    assert_post_radix3_shape(input, tag, case_index);
    invntt_final_ref(expected, input);
    memcpy(actual, input, sizeof(actual));
    jade_ntruplus_ntruplus768_amd64_ref_invntt_final(actual);
    compare_output(tag, case_index, expected, actual);
}

static void run_composed_case(const char *tag,
                              size_t case_index,
                              const int16_t input[NTRUPLUS_N])
{
    int16_t step4_out[NTRUPLUS_N];
    int16_t step8_out[NTRUPLUS_N];
    int16_t step16_out[NTRUPLUS_N];
    int16_t step32_out[NTRUPLUS_N];
    int16_t step64_out[NTRUPLUS_N];
    int16_t radix3_out[NTRUPLUS_N];
    int16_t expected[NTRUPLUS_N];
    int16_t actual[NTRUPLUS_N];

    assert_qrange_input(input, tag, case_index);
    invntt_radix2_4_ref(step4_out, input);
    invntt_radix2_8_ref(step8_out, step4_out);
    invntt_radix2_16_ref(step16_out, step8_out);
    invntt_radix2_32_ref(step32_out, step16_out);
    invntt_radix2_64_ref(step64_out, step32_out);
    invntt_radix3_ref(radix3_out, step64_out);
    invntt_final_ref(expected, radix3_out);

    memcpy(actual, input, sizeof(actual));
    jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4(actual);
    jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_8(actual);
    jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_16(actual);
    jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_32(actual);
    jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_64(actual);
    jade_ntruplus_ntruplus768_amd64_ref_invntt_radix3(actual);
    jade_ntruplus_ntruplus768_amd64_ref_invntt_final(actual);
    compare_output(tag, case_index, expected, actual);
}

int main(void)
{
    int16_t standalone_vectors[5][NTRUPLUS_N];
    int16_t composed_vectors[5][NTRUPLUS_N];
    int16_t random_input[NTRUPLUS_N];

    fill_zero(standalone_vectors[0]);
    fill_sum_lane_extremes(standalone_vectors[1]);
    fill_half_difference_edges(standalone_vectors[2]);
    fill_sparse_pair_edges(standalone_vectors[3]);
    fill_balanced_pair_stress(standalone_vectors[4]);

    fill_zero(composed_vectors[0]);
    fill_qrange_alternating_extremes(composed_vectors[1]);
    fill_qrange_half_difference_edges(composed_vectors[2]);
    fill_qrange_sparse_edges(composed_vectors[3]);
    fill_qrange_balanced_stress(composed_vectors[4]);

    for (size_t i = 0; i < 5; ++i) {
        run_standalone_case("invntt-final-standalone", i, standalone_vectors[i]);
        run_composed_case("invntt-step4-8-16-32-64-radix3-final", i, composed_vectors[i]);
    }

    for (size_t i = 0; i < STANDALONE_RANDOM_CASES; ++i) {
        const uint32_t seed = 0x4ec3f29bu ^ ((uint32_t)i * 0x243f6a88u);

        fill_post_radix3_random(random_input, seed);
        run_standalone_case("invntt-final-standalone-random", i, random_input);
    }

    for (size_t i = 0; i < COMPOSED_RANDOM_CASES; ++i) {
        const uint32_t seed = 0x91e10da5u ^ ((uint32_t)i * 0x9e3779b9u);

        fill_random_qrange(random_input, seed);
        run_composed_case("invntt-step4-8-16-32-64-radix3-final-random", i, random_input);
    }

    printf("PASS: NTRU+768 invntt final differential checks: "
           "5 standalone boundary + %d standalone random + "
           "5 composed boundary + %d composed random vectors\n",
           STANDALONE_RANDOM_CASES,
           COMPOSED_RANDOM_CASES);
    return 0;
}
