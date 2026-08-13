#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define NTRUPLUS_N 768
#define NTRUPLUS_Q 3457
#define NTRUPLUS_QINV 12929
#define STANDALONE_RANDOM_CASES 2048
#define PREFIX_RANDOM_CASES 2048

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

extern void jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4(
    int16_t r[NTRUPLUS_N]);
extern void jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_8(
    int16_t r[NTRUPLUS_N]);
extern void jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_16(
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

static void fill_zero(int16_t dst[NTRUPLUS_N])
{
    memset(dst, 0, sizeof(int16_t) * NTRUPLUS_N);
}

static void fill_constant(int16_t dst[NTRUPLUS_N], int16_t value)
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        dst[i] = value;
    }
}

static void fill_alternating_extremes(int16_t dst[NTRUPLUS_N])
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        dst[i] = (i & 1u) == 0 ? -NTRUPLUS_Q : (NTRUPLUS_Q - 1);
    }
}

static void fill_step16_block_gradient(int16_t dst[NTRUPLUS_N])
{
    for (size_t block = 0; block < 24; ++block) {
        const size_t base = block * 32;
        for (size_t lane = 0; lane < 16; ++lane) {
            dst[base + lane] = (int16_t)((int)block - (int)lane);
            dst[base + 16 + lane] = (int16_t)((int)lane - (int)block);
        }
    }
}

static void fill_step16_pair_stress(int16_t dst[NTRUPLUS_N])
{
    for (size_t block = 0; block < 24; ++block) {
        const size_t base = block * 32;
        for (size_t lane = 0; lane < 16; ++lane) {
            dst[base + lane] = (lane & 1u) == 0 ? (NTRUPLUS_Q - 1) : -NTRUPLUS_Q;
            dst[base + 16 + lane] = (lane & 1u) == 0 ? -NTRUPLUS_Q : (NTRUPLUS_Q - 1);
        }
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

    invntt_radix2_16_ref(expected, input);
    memcpy(actual, input, sizeof(actual));
    jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_16(actual);
    compare_output(tag, case_index, expected, actual);
}

static void run_prefix_case(const char *tag,
                            size_t case_index,
                            const int16_t input[NTRUPLUS_N])
{
    int16_t step4_out[NTRUPLUS_N];
    int16_t step8_out[NTRUPLUS_N];
    int16_t expected[NTRUPLUS_N];
    int16_t actual[NTRUPLUS_N];

    invntt_radix2_4_ref(step4_out, input);
    invntt_radix2_8_ref(step8_out, step4_out);
    invntt_radix2_16_ref(expected, step8_out);

    memcpy(actual, input, sizeof(actual));
    jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4(actual);
    jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_8(actual);
    jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_16(actual);
    compare_output(tag, case_index, expected, actual);
}

int main(void)
{
    int16_t standalone_vectors[6][NTRUPLUS_N];
    int16_t prefix_vectors[6][NTRUPLUS_N];
    int16_t random_input[NTRUPLUS_N];

    fill_zero(standalone_vectors[0]);
    fill_constant(standalone_vectors[1], NTRUPLUS_Q - 1);
    fill_constant(standalone_vectors[2], -NTRUPLUS_Q);
    fill_alternating_extremes(standalone_vectors[3]);
    fill_step16_pair_stress(standalone_vectors[4]);
    fill_step16_block_gradient(standalone_vectors[5]);

    fill_zero(prefix_vectors[0]);
    fill_constant(prefix_vectors[1], NTRUPLUS_Q - 1);
    fill_constant(prefix_vectors[2], -NTRUPLUS_Q);
    fill_alternating_extremes(prefix_vectors[3]);
    fill_step16_pair_stress(prefix_vectors[4]);
    fill_step16_block_gradient(prefix_vectors[5]);

    for (size_t i = 0; i < 6; ++i) {
        run_standalone_case("invntt-radix2-16", i, standalone_vectors[i]);
        run_prefix_case("invntt-radix2-4-then-8-then-16", i, prefix_vectors[i]);
    }

    for (size_t i = 0; i < STANDALONE_RANDOM_CASES; ++i) {
        const uint32_t seed = 0x3c6ef372u ^ ((uint32_t)i * 0x9e3779b9u);

        fill_random_qrange(random_input, seed);
        run_standalone_case("invntt-radix2-16-random", i, random_input);
    }

    for (size_t i = 0; i < PREFIX_RANDOM_CASES; ++i) {
        const uint32_t seed = 0xa54ff53au ^ ((uint32_t)i * 0x85ebca6bu);

        fill_random_qrange(random_input, seed);
        run_prefix_case("invntt-radix2-4-then-8-then-16-random", i, random_input);
    }

    printf("PASS: NTRU+768 inverse radix-2 step16 differential checks: "
           "6 standalone boundary + %d standalone random + "
           "6 prefix boundary + %d prefix random vectors\n",
           STANDALONE_RANDOM_CASES,
           PREFIX_RANDOM_CASES);
    return 0;
}
