#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../../../NTRU+/NTRU+768/ntt.h"
#include "../../../NTRU+/NTRU+768/poly.h"

#define NTRUPLUS_N 768
#define NTRUPLUS_Q 3457
#define NTRUPLUS_RINV 2775
#define SIGNED12_MIN (-4096)
#define SIGNED12_MAX 4095
#define DECAP_SUB_MIN (-3456)
#define DECAP_SUB_MAX 7552
#define CANONICAL_Q_MIN 0
#define CANONICAL_Q_MAX (NTRUPLUS_Q - 1)

extern void jade_ntruplus_ntruplus768_amd64_ref_poly_basemul(
    int16_t r[NTRUPLUS_N], const int16_t a[NTRUPLUS_N], const int16_t b[NTRUPLUS_N]);

static void poly_basemul_ref(int16_t r[NTRUPLUS_N], const int16_t a[NTRUPLUS_N], const int16_t b[NTRUPLUS_N])
{
    poly pa;
    poly pb;
    poly pr;

    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        pa.coeffs[i] = a[i];
        pb.coeffs[i] = b[i];
    }

    poly_basemul(&pr, &pa, &pb);

    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        r[i] = pr.coeffs[i];
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

static int16_t sample_signed12(uint32_t *state)
{
    return (int16_t)((int32_t)(next_u32(state) & 0x1fffu) + SIGNED12_MIN);
}

static int16_t sample_decap_sub(uint32_t *state)
{
    const uint32_t width = (uint32_t)(DECAP_SUB_MAX - DECAP_SUB_MIN + 1);

    return (int16_t)((int32_t)(next_u32(state) % width) + DECAP_SUB_MIN);
}

static int16_t sample_canonical_q(uint32_t *state)
{
    return (int16_t)(next_u32(state) % NTRUPLUS_Q);
}

static int32_t mod_q(int64_t value)
{
    int32_t reduced = (int32_t)(value % NTRUPLUS_Q);

    return reduced < 0 ? reduced + NTRUPLUS_Q : reduced;
}

static void check_mod_q_oracle(const char *tag,
                               size_t idx,
                               const int16_t out[NTRUPLUS_N],
                               const int16_t a[NTRUPLUS_N],
                               const int16_t b[NTRUPLUS_N])
{
    for (size_t block = 0; block < NTRUPLUS_N / 4; ++block) {
        const size_t off = 4 * block;
        const int16_t zeta_word = (block & 1u) == 0
            ? zetas[96 + block / 2]
            : (int16_t)-zetas[96 + block / 2];
        const int32_t zeta_math = mod_q((int64_t)zeta_word * NTRUPLUS_RINV);
        const int64_t expected[4] = {
            (int64_t)a[off] * b[off] +
                (int64_t)zeta_math *
                    ((int64_t)a[off + 1] * b[off + 3] +
                     (int64_t)a[off + 2] * b[off + 2] +
                     (int64_t)a[off + 3] * b[off + 1]),
            (int64_t)a[off] * b[off + 1] +
                (int64_t)a[off + 1] * b[off] +
                (int64_t)zeta_math *
                    ((int64_t)a[off + 2] * b[off + 3] +
                     (int64_t)a[off + 3] * b[off + 2]),
            (int64_t)a[off] * b[off + 2] +
                (int64_t)a[off + 1] * b[off + 1] +
                (int64_t)a[off + 2] * b[off] +
                (int64_t)zeta_math * a[off + 3] * b[off + 3],
            (int64_t)a[off] * b[off + 3] +
                (int64_t)a[off + 1] * b[off + 2] +
                (int64_t)a[off + 2] * b[off + 1] +
                (int64_t)a[off + 3] * b[off]
        };

        for (size_t lane = 0; lane < 4; ++lane) {
            if (mod_q(out[off + lane]) != mod_q(expected[lane])) {
                fprintf(stderr,
                        "mod-q mismatch in %s[%zu] at block %zu lane %zu: "
                        "output=%d expected_mod_q=%d\n",
                        tag,
                        idx,
                        block,
                        lane,
                        out[off + lane],
                        mod_q(expected[lane]));
                exit(1);
            }
        }
    }
}

static void check_output_range(const char *impl,
                               const char *tag,
                               size_t idx,
                               size_t coeff_idx,
                               int16_t value,
                               const int16_t a[NTRUPLUS_N],
                               const int16_t b[NTRUPLUS_N])
{
    if (value < -NTRUPLUS_Q || value >= NTRUPLUS_Q) {
        fprintf(stderr,
                "%s out-of-range in %s[%zu] at coeff %zu: value=%d expected in [%d,%d)\n",
                impl,
                tag,
                idx,
                coeff_idx,
                value,
                -NTRUPLUS_Q,
                NTRUPLUS_Q);
        fprintf(stderr,
                "a[%zu]=%d b[%zu]=%d block=%zu\n",
                coeff_idx,
                a[coeff_idx],
                coeff_idx,
                b[coeff_idx],
                coeff_idx / 8);
        exit(1);
    }
}

static void check_case(const char *tag,
                       size_t idx,
                       const int16_t a[NTRUPLUS_N],
                       const int16_t b[NTRUPLUS_N])
{
    int16_t ref[NTRUPLUS_N];
    int16_t jasmin[NTRUPLUS_N];
    int16_t a_before[NTRUPLUS_N];
    int16_t b_before[NTRUPLUS_N];

    memcpy(a_before, a, sizeof(a_before));
    memcpy(b_before, b, sizeof(b_before));

    poly_basemul_ref(ref, a, b);
    jade_ntruplus_ntruplus768_amd64_ref_poly_basemul(jasmin, a, b);

    if (memcmp(a, a_before, sizeof(a_before)) != 0 ||
        memcmp(b, b_before, sizeof(b_before)) != 0) {
        fprintf(stderr, "input mutation in %s[%zu]\n", tag, idx);
        exit(1);
    }

    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        check_output_range("ref", tag, idx, i, ref[i], a, b);
        check_output_range("jasmin", tag, idx, i, jasmin[i], a, b);
        if (ref[i] != jasmin[i]) {
            fprintf(stderr,
                    "mismatch in %s[%zu] at coeff %zu: ref=%d jasmin=%d\n",
                    tag,
                    idx,
                    i,
                    ref[i],
                    jasmin[i]);
            fprintf(stderr, "a[%zu]=%d b[%zu]=%d block=%zu\n",
                    i,
                    a[i],
                    i,
                    b[i],
                    i / 8);
            exit(1);
        }
    }

    check_mod_q_oracle(tag, idx, ref, a, b);
    check_mod_q_oracle(tag, idx, jasmin, a, b);
}

static void run_boundary_cases(void)
{
    int16_t a[NTRUPLUS_N];
    int16_t b[NTRUPLUS_N];

    fill_constant(a, 0);
    fill_constant(b, 0);
    check_case("boundary", 0, a, b);

    fill_constant(a, NTRUPLUS_Q);
    fill_constant(b, NTRUPLUS_Q);
    check_case("boundary", 1, a, b);

    fill_constant(a, -NTRUPLUS_Q);
    fill_constant(b, -NTRUPLUS_Q);
    check_case("boundary", 2, a, b);

    fill_alternating(a, NTRUPLUS_Q, -NTRUPLUS_Q);
    fill_alternating(b, -NTRUPLUS_Q, NTRUPLUS_Q);
    check_case("boundary", 3, a, b);

    fill_alternating(a, 1, -1);
    fill_alternating(b, -1, 1);
    check_case("boundary", 4, a, b);

    fill_staircase(a, -NTRUPLUS_Q, 17);
    fill_staircase(b, NTRUPLUS_Q, -19);
    check_case("boundary", 5, a, b);

    fill_constant(a, 0);
    fill_constant(b, 0);
    a[0] = NTRUPLUS_Q;
    b[NTRUPLUS_N - 1] = -NTRUPLUS_Q;
    check_case("boundary", 6, a, b);

    fill_constant(a, 0);
    fill_constant(b, 0);
    a[NTRUPLUS_N - 4] = -NTRUPLUS_Q;
    a[NTRUPLUS_N - 1] = NTRUPLUS_Q;
    b[4] = NTRUPLUS_Q;
    b[7] = -NTRUPLUS_Q;
    check_case("boundary", 7, a, b);
}

static void run_signed12_boundary_cases(void)
{
    int16_t a[NTRUPLUS_N];
    int16_t b[NTRUPLUS_N];

    fill_constant(a, SIGNED12_MIN);
    fill_constant(b, SIGNED12_MAX);
    check_case("signed12-boundary", 0, a, b);

    fill_alternating(a, SIGNED12_MIN, SIGNED12_MAX);
    fill_alternating(b, SIGNED12_MAX, SIGNED12_MIN);
    check_case("signed12-boundary", 1, a, b);
}

static void run_random_cases(void)
{
    uint32_t state = 0x8f37c129u;
    const size_t random_cases = 4096;

    for (size_t i = 0; i < random_cases; ++i) {
        int16_t a[NTRUPLUS_N];
        int16_t b[NTRUPLUS_N];

        for (size_t j = 0; j < NTRUPLUS_N; ++j) {
            a[j] = sample_mod_q(&state);
            b[j] = sample_mod_q(&state);
        }

        check_case("random", i, a, b);
    }
}

static void run_signed12_random_cases(void)
{
    uint32_t state = 0xa4e1276bu;
    const size_t random_cases = 1024;

    for (size_t i = 0; i < random_cases; ++i) {
        int16_t a[NTRUPLUS_N];
        int16_t b[NTRUPLUS_N];

        for (size_t j = 0; j < NTRUPLUS_N; ++j) {
            a[j] = sample_signed12(&state);
            b[j] = sample_signed12(&state);
        }

        check_case("signed12-random", i, a, b);
    }
}

static void run_decap_wide_boundary_cases(void)
{
    int16_t a[NTRUPLUS_N];
    int16_t b[NTRUPLUS_N];

    fill_constant(a, DECAP_SUB_MIN);
    fill_constant(b, CANONICAL_Q_MIN);
    check_case("decap-wide-boundary", 0, a, b);

    fill_constant(a, DECAP_SUB_MAX);
    fill_constant(b, CANONICAL_Q_MAX);
    check_case("decap-wide-boundary", 1, a, b);

    fill_constant(a, DECAP_SUB_MIN);
    fill_constant(b, CANONICAL_Q_MAX);
    check_case("decap-wide-boundary", 2, a, b);

    fill_alternating(a, DECAP_SUB_MIN, DECAP_SUB_MAX);
    fill_alternating(b, CANONICAL_Q_MAX, CANONICAL_Q_MIN);
    check_case("decap-wide-boundary", 3, a, b);

    fill_constant(a, 0);
    fill_constant(b, 0);
    a[0] = DECAP_SUB_MAX;
    a[1] = DECAP_SUB_MIN;
    a[2] = DECAP_SUB_MAX;
    a[3] = DECAP_SUB_MIN;
    b[0] = CANONICAL_Q_MAX;
    b[1] = CANONICAL_Q_MAX;
    b[2] = CANONICAL_Q_MAX;
    b[3] = CANONICAL_Q_MAX;
    check_case("decap-wide-boundary", 4, a, b);
}

static void run_decap_wide_random_cases(void)
{
    uint32_t state = 0x3fd29417u;
    const size_t random_cases = 4096;

    for (size_t i = 0; i < random_cases; ++i) {
        int16_t a[NTRUPLUS_N];
        int16_t b[NTRUPLUS_N];

        for (size_t j = 0; j < NTRUPLUS_N; ++j) {
            a[j] = sample_decap_sub(&state);
            b[j] = sample_canonical_q(&state);
        }

        check_case("decap-wide-random", i, a, b);
    }
}

int main(void)
{
    run_boundary_cases();
    run_random_cases();
    run_signed12_boundary_cases();
    run_signed12_random_cases();
    run_decap_wide_boundary_cases();
    run_decap_wide_random_cases();
    printf("poly_basemul differential passed: 8 q-boundary + 4096 random signed-domain + "
           "2 signed12-boundary + 1024 random signed12-domain + "
           "5 decap-wide boundary + 4096 decap-wide random cases; "
           "all checked for input immutability, q-range output, and mod-q algebra\n");
    return 0;
}
