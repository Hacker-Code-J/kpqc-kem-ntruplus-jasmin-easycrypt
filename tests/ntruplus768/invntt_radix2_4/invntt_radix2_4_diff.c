#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define NTRUPLUS_N 768
#define NTRUPLUS_Q 3457
#define NTRUPLUS_QINV 12929
#define RANDOM_CASES 4096

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

extern void jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4(
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
            const int16_t high = r[i + 4];

            r[i + 4] = fqmul_ref(zeta, (int16_t)(high - r[i]));
            r[i] = barrett_reduce_ref((int16_t)(r[i] + high));
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

static void fill_block_gradient(int16_t dst[NTRUPLUS_N])
{
    for (size_t block = 0; block < 96; ++block) {
        const size_t base = block * 8;
        for (size_t lane = 0; lane < 4; ++lane) {
            dst[base + lane] = (int16_t)(block - (int)lane);
            dst[base + 4 + lane] = (int16_t)(lane - (int)block);
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

static void run_case(const char *tag,
                     size_t case_index,
                     const int16_t input[NTRUPLUS_N])
{
    int16_t expected[NTRUPLUS_N];
    int16_t actual[NTRUPLUS_N];

    invntt_radix2_4_ref(expected, input);
    memcpy(actual, input, sizeof(actual));
    jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4(actual);
    compare_output(tag, case_index, expected, actual);
}

int main(void)
{
    int16_t vectors[5][NTRUPLUS_N];
    int16_t random_input[NTRUPLUS_N];

    fill_zero(vectors[0]);
    fill_constant(vectors[1], NTRUPLUS_Q - 1);
    fill_constant(vectors[2], -NTRUPLUS_Q);
    fill_alternating_extremes(vectors[3]);
    fill_block_gradient(vectors[4]);

    for (size_t i = 0; i < 5; ++i) {
        run_case("invntt-radix2-4", i, vectors[i]);
    }

    for (size_t i = 0; i < RANDOM_CASES; ++i) {
        const uint32_t seed = 0x9e3779b9u ^ ((uint32_t)i * 0x85ebca6bu);

        fill_random_qrange(random_input, seed);
        run_case("invntt-radix2-4-random", i, random_input);
    }

    printf("PASS: NTRU+768 inverse radix-2 step4 differential checks: "
           "5 boundary + %d random vectors\n",
           RANDOM_CASES);
    return 0;
}
