#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../../../NTRU+/NTRU+768/poly.h"

_Static_assert(NTRUPLUS_N == 768, "proof model requires NTRU+768");
_Static_assert(NTRUPLUS_Q == 3457, "proof model requires q = 3457");
_Static_assert(NTRUPLUS_POLYBYTES == 1152, "proof model requires 1152 serialized bytes");

extern void jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes(
    uint8_t out[NTRUPLUS_POLYBYTES], const int16_t in[NTRUPLUS_N]);

static uint32_t next_u32(uint32_t *state)
{
    uint32_t x = *state;

    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    *state = x;
    return x;
}

static uint16_t canonical_coeff(int16_t x)
{
    return (uint16_t)(x < 0 ? x + NTRUPLUS_Q : x);
}

static void poly_tobytes_oracle(uint8_t out[NTRUPLUS_POLYBYTES], const int16_t in[NTRUPLUS_N])
{
    for (size_t i = 0; i < NTRUPLUS_N / 2; ++i) {
        const uint16_t t0 = canonical_coeff(in[2 * i]);
        const uint16_t t1 = canonical_coeff(in[2 * i + 1]);
        const size_t j = 3 * i;

        out[j + 0] = (uint8_t)t0;
        out[j + 1] = (uint8_t)((t0 >> 8) | (t1 << 4));
        out[j + 2] = (uint8_t)(t1 >> 4);
    }
}

static void poly_tobytes_ref(uint8_t out[NTRUPLUS_POLYBYTES], const int16_t in[NTRUPLUS_N])
{
    poly p;

    memcpy(p.coeffs, in, sizeof(p.coeffs));
    poly_tobytes(out, &p);
}

static void poly_tobytes_roundtrip_ref(int16_t out[NTRUPLUS_N], const int16_t in[NTRUPLUS_N])
{
    poly p;
    uint8_t bytes[NTRUPLUS_POLYBYTES];

    memcpy(p.coeffs, in, sizeof(p.coeffs));
    poly_tobytes(bytes, &p);
    poly_frombytes(&p, bytes);
    memcpy(out, p.coeffs, sizeof(p.coeffs));
}

static void fill_constant(int16_t dst[NTRUPLUS_N], int16_t value)
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        dst[i] = value;
    }
}

static void fill_alternating(int16_t dst[NTRUPLUS_N], int16_t lo, int16_t hi)
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        dst[i] = (int16_t)((i & 1u) == 0 ? lo : hi);
    }
}

static void fill_ramp(int16_t dst[NTRUPLUS_N], int16_t start, int16_t step)
{
    int32_t value = start;

    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        while (value < -NTRUPLUS_Q) {
            value += 2 * NTRUPLUS_Q - 1;
        }
        while (value >= NTRUPLUS_Q) {
            value -= 2 * NTRUPLUS_Q - 1;
        }
        dst[i] = (int16_t)value;
        value += step;
    }
}

static void fill_random_qrange(int16_t dst[NTRUPLUS_N], uint32_t *state)
{
    const uint32_t span = (uint32_t)(2 * NTRUPLUS_Q);

    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        const uint32_t sample = next_u32(state) % span;
        dst[i] = (int16_t)((int32_t)sample - NTRUPLUS_Q);
    }
}

static void assert_bytes_equal(const char *lhs_name,
                               const char *rhs_name,
                               const char *tag,
                               size_t case_index,
                               const uint8_t lhs[NTRUPLUS_POLYBYTES],
                               const uint8_t rhs[NTRUPLUS_POLYBYTES])
{
    for (size_t i = 0; i < NTRUPLUS_POLYBYTES; ++i) {
        if (lhs[i] != rhs[i]) {
            fprintf(stderr,
                    "mismatch %s vs %s in %s[%zu] at byte %zu: %02x != %02x\n",
                    lhs_name,
                    rhs_name,
                    tag,
                    case_index,
                    i,
                    lhs[i],
                    rhs[i]);
            exit(1);
        }
    }
}

static void assert_coeffs_equal(const char *tag,
                                size_t case_index,
                                const int16_t lhs[NTRUPLUS_N],
                                const int16_t rhs[NTRUPLUS_N])
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        if (lhs[i] != rhs[i]) {
            fprintf(stderr,
                    "roundtrip mismatch in %s[%zu] at coeff %zu: %d != %d\n",
                    tag,
                    case_index,
                    i,
                    lhs[i],
                    rhs[i]);
            exit(1);
        }
    }
}

static void assert_unchanged(const char *name,
                             const char *tag,
                             size_t case_index,
                             const int16_t before[NTRUPLUS_N],
                             const int16_t after[NTRUPLUS_N])
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        if (before[i] != after[i]) {
            fprintf(stderr,
                    "%s modified input in %s[%zu] at coeff %zu: %d != %d\n",
                    name,
                    tag,
                    case_index,
                    i,
                    before[i],
                    after[i]);
            exit(1);
        }
    }
}

static void build_expected_roundtrip(int16_t out[NTRUPLUS_N], const int16_t in[NTRUPLUS_N])
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        out[i] = (int16_t)canonical_coeff(in[i]);
        if (out[i] < 0 || out[i] >= NTRUPLUS_Q) {
            fprintf(stderr,
                    "canonical coefficient escaped [0,q) at coeff %zu: %d\n",
                    i,
                    out[i]);
            exit(1);
        }
    }
}

static void check_case(const char *tag, size_t case_index, const int16_t input[NTRUPLUS_N])
{
    uint8_t oracle[NTRUPLUS_POLYBYTES];
    uint8_t c_bytes[NTRUPLUS_POLYBYTES];
    uint8_t jasmin_bytes[NTRUPLUS_POLYBYTES];
    int16_t expected_roundtrip[NTRUPLUS_N];
    int16_t actual_roundtrip[NTRUPLUS_N];
    int16_t c_input[NTRUPLUS_N];
    int16_t jasmin_input[NTRUPLUS_N];

    memcpy(c_input, input, sizeof(c_input));
    memcpy(jasmin_input, input, sizeof(jasmin_input));

    poly_tobytes_oracle(oracle, input);
    poly_tobytes_ref(c_bytes, c_input);
    jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes(jasmin_bytes, jasmin_input);
    poly_tobytes_roundtrip_ref(actual_roundtrip, input);
    build_expected_roundtrip(expected_roundtrip, input);

    assert_bytes_equal("oracle", "C", tag, case_index, oracle, c_bytes);
    assert_bytes_equal("oracle", "Jasmin", tag, case_index, oracle, jasmin_bytes);
    assert_coeffs_equal(tag, case_index, expected_roundtrip, actual_roundtrip);
    assert_unchanged("Jasmin poly_tobytes()", tag, case_index, input, jasmin_input);
    assert_unchanged("C poly_tobytes() test input", tag, case_index, input, c_input);
}

static void run_boundary_cases(void)
{
    int16_t input[NTRUPLUS_N];

    fill_constant(input, 0);
    check_case("boundary", 0, input);

    fill_constant(input, -1);
    check_case("boundary", 1, input);

    fill_constant(input, (int16_t)(NTRUPLUS_Q - 1));
    check_case("boundary", 2, input);

    fill_constant(input, (int16_t)(-NTRUPLUS_Q));
    check_case("boundary", 3, input);

    fill_alternating(input, -1, (int16_t)(NTRUPLUS_Q - 1));
    check_case("boundary", 4, input);

    fill_alternating(input, (int16_t)(-NTRUPLUS_Q), 0);
    check_case("boundary", 5, input);

    fill_ramp(input, (int16_t)(-NTRUPLUS_Q), 17);
    check_case("boundary", 6, input);

    fill_ramp(input, (int16_t)(NTRUPLUS_Q - 1), -29);
    check_case("boundary", 7, input);
}

static void run_triplet_focus_cases(void)
{
    int16_t input[NTRUPLUS_N];
    const size_t pairs[] = {0u, 1u, 127u, 128u, 255u, 256u, 382u, 383u};
    const int16_t coeff_pairs[][2] = {
        {0, 0},
        {-1, 0},
        {0, -1},
        {(int16_t)(NTRUPLUS_Q - 1), (int16_t)(NTRUPLUS_Q - 1)},
        {(int16_t)(-NTRUPLUS_Q), (int16_t)(NTRUPLUS_Q - 1)},
        {123, -321},
    };
    size_t case_index = 0;

    for (size_t i = 0; i < sizeof(pairs) / sizeof(pairs[0]); ++i) {
        for (size_t j = 0; j < sizeof(coeff_pairs) / sizeof(coeff_pairs[0]); ++j) {
            fill_constant(input, 0);
            input[2 * pairs[i]] = coeff_pairs[j][0];
            input[2 * pairs[i] + 1] = coeff_pairs[j][1];
            check_case("triplet", case_index++, input);
        }
    }
}

static void run_random_cases(void)
{
    uint32_t state = 0x31415926u;
    const size_t random_cases = 4096;

    for (size_t case_index = 0; case_index < random_cases; ++case_index) {
        int16_t input[NTRUPLUS_N];

        fill_random_qrange(input, &state);
        check_case("random", case_index, input);
    }

    printf("poly_tobytes differential passed: 8 boundary + 48 triplet + %zu random q-range vectors\n",
           random_cases);
}

int main(void)
{
    run_boundary_cases();
    run_triplet_focus_cases();
    run_random_cases();
    return 0;
}
