#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../../../NTRU+/NTRU+768/params.h"
#include "../../../NTRU+/NTRU+768/poly.h"

_Static_assert(CHAR_BIT == 8, "keygen_secret_f test requires 8-bit bytes");
_Static_assert(sizeof(int16_t) * CHAR_BIT == 16,
               "keygen_secret_f test requires 16-bit int16_t");
_Static_assert(NTRUPLUS_N == 768, "keygen_secret_f test requires N=768");
_Static_assert(NTRUPLUS_Q == 3457, "keygen_secret_f test requires q=3457");
_Static_assert(NTRUPLUS_POLYBYTES == 1152,
               "keygen_secret_f test requires 1152 serialized bytes");

enum {
    RANDOM_KEYGEN_CASES = 4096,
    RANDOM_QRANGE_CASES = 1024,
};

static uint32_t next_u32(uint32_t *state)
{
    uint32_t x = *state;

    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    *state = x;
    return x;
}

static uint16_t canonical_coeff(int16_t value)
{
    return (uint16_t)(value < 0 ? value + NTRUPLUS_Q : value);
}

static int coeff_mod_q_equal(int16_t left, int16_t right)
{
    int32_t delta = (int32_t)left - (int32_t)right;

    delta %= NTRUPLUS_Q;
    if (delta < 0) {
        delta += NTRUPLUS_Q;
    }
    return delta == 0;
}

static void fill_constant(poly *dst, int16_t value)
{
    size_t i;

    for (i = 0; i < NTRUPLUS_N; ++i) {
        dst->coeffs[i] = value;
    }
}

static void fill_alternating(poly *dst, int16_t lo, int16_t hi)
{
    size_t i;

    for (i = 0; i < NTRUPLUS_N; ++i) {
        dst->coeffs[i] = (int16_t)((i & 1u) == 0u ? lo : hi);
    }
}

static void fill_ramp(poly *dst, int16_t start, int16_t step)
{
    int32_t value = start;
    size_t i;

    for (i = 0; i < NTRUPLUS_N; ++i) {
        while (value < -NTRUPLUS_Q) {
            value += 2 * NTRUPLUS_Q - 1;
        }
        while (value >= NTRUPLUS_Q) {
            value -= 2 * NTRUPLUS_Q - 1;
        }
        dst->coeffs[i] = (int16_t)value;
        value += step;
    }
}

static void fill_random_qrange(poly *dst, uint32_t *state)
{
    const uint32_t span = (uint32_t)(2 * NTRUPLUS_Q);
    size_t i;

    for (i = 0; i < NTRUPLUS_N; ++i) {
        const uint32_t sample = next_u32(state) % span;
        dst->coeffs[i] = (int16_t)((int32_t)sample - NTRUPLUS_Q);
    }
}

static void fill_sampler_buf(uint8_t buf[NTRUPLUS_N / 4], uint32_t seed)
{
    uint32_t state = seed;
    size_t i;

    for (i = 0; i < NTRUPLUS_N / 4; ++i) {
        buf[i] = (uint8_t)next_u32(&state);
    }
}

static void make_keygen_ntt_f(poly *dst, uint32_t seed)
{
    uint8_t buf[NTRUPLUS_N / 4];
    poly time_domain;

    fill_sampler_buf(buf, seed);
    poly_cbd1(&time_domain, buf);
    poly_triple(&time_domain, &time_domain);
    time_domain.coeffs[0] += 1;
    poly_ntt(dst, &time_domain);
}

static void poly_tobytes_oracle(uint8_t out[NTRUPLUS_POLYBYTES], const poly *in)
{
    size_t i;

    for (i = 0; i < NTRUPLUS_N / 2; ++i) {
        const uint16_t t0 = canonical_coeff(in->coeffs[2 * i]);
        const uint16_t t1 = canonical_coeff(in->coeffs[2 * i + 1]);
        const size_t off = 3 * i;

        out[off + 0] = (uint8_t)t0;
        out[off + 1] = (uint8_t)((t0 >> 8) | (t1 << 4));
        out[off + 2] = (uint8_t)(t1 >> 4);
    }
}

static void require_bytes_equal(const uint8_t *left,
                                const uint8_t *right,
                                size_t length,
                                const char *label,
                                const char *group,
                                size_t case_index)
{
    size_t i;

    for (i = 0; i < length; ++i) {
        if (left[i] != right[i]) {
            fprintf(stderr,
                    "%s mismatch in %s[%zu] at byte %zu: %02x != %02x\n",
                    label,
                    group,
                    case_index,
                    i,
                    left[i],
                    right[i]);
            exit(1);
        }
    }
}

static void require_poly_unchanged(const poly *before,
                                   const poly *after,
                                   const char *label,
                                   const char *group,
                                   size_t case_index)
{
    if (memcmp(before, after, sizeof(*before)) != 0) {
        fprintf(stderr, "%s mutated source in %s[%zu]\n", label, group, case_index);
        exit(1);
    }
}

static void require_decoded_matches(const poly *original,
                                    const poly *decoded,
                                    const char *group,
                                    size_t case_index)
{
    size_t i;

    for (i = 0; i < NTRUPLUS_N; ++i) {
        const uint16_t expected = canonical_coeff(original->coeffs[i]);
        const int16_t actual = decoded->coeffs[i];

        if (actual < 0 || actual >= NTRUPLUS_Q) {
            fprintf(stderr,
                    "decoded coefficient escaped [0,q) in %s[%zu] at coeff %zu: %d\n",
                    group,
                    case_index,
                    i,
                    actual);
            exit(1);
        }
        if ((uint16_t)actual != expected) {
            fprintf(stderr,
                    "decoded canonical mismatch in %s[%zu] at coeff %zu: %u != %u\n",
                    group,
                    case_index,
                    i,
                    (unsigned)((uint16_t)actual),
                    (unsigned)expected);
            exit(1);
        }
        if (!coeff_mod_q_equal(original->coeffs[i], actual)) {
            fprintf(stderr,
                    "decoded mod-q mismatch in %s[%zu] at coeff %zu: %d vs %d\n",
                    group,
                    case_index,
                    i,
                    original->coeffs[i],
                    actual);
            exit(1);
        }
    }
}

static void run_case(const char *group, size_t case_index, const poly *input)
{
    uint8_t oracle[NTRUPLUS_POLYBYTES];
    uint8_t bytes[NTRUPLUS_POLYBYTES];
    uint8_t bytes_before[NTRUPLUS_POLYBYTES];
    poly original = *input;
    poly source = *input;
    poly decoded;

    fill_constant(&decoded, (int16_t)0x4444);
    poly_tobytes_oracle(oracle, &original);
    poly_tobytes(bytes, &source);
    memcpy(bytes_before, bytes, sizeof(bytes));
    poly_frombytes(&decoded, bytes);

    require_bytes_equal(oracle, bytes, sizeof(bytes), "serialized bytes", group, case_index);
    require_poly_unchanged(&original, &source, "poly_tobytes()", group, case_index);
    require_bytes_equal(bytes_before, bytes, sizeof(bytes), "poly_frombytes() input", group, case_index);
    require_decoded_matches(&original, &decoded, group, case_index);
}

static void run_boundary_cases(void)
{
    poly input;

    fill_constant(&input, 0);
    run_case("boundary", 0, &input);

    fill_constant(&input, -1);
    run_case("boundary", 1, &input);

    fill_constant(&input, (int16_t)(NTRUPLUS_Q - 1));
    run_case("boundary", 2, &input);

    fill_constant(&input, (int16_t)(-NTRUPLUS_Q));
    run_case("boundary", 3, &input);

    fill_alternating(&input, -1, (int16_t)(NTRUPLUS_Q - 1));
    run_case("boundary", 4, &input);

    fill_alternating(&input, (int16_t)(-NTRUPLUS_Q), 0);
    run_case("boundary", 5, &input);

    fill_ramp(&input, (int16_t)(-NTRUPLUS_Q), 17);
    run_case("boundary", 6, &input);

    fill_ramp(&input, (int16_t)(NTRUPLUS_Q - 1), -29);
    run_case("boundary", 7, &input);
}

static void run_keygen_cases(void)
{
    size_t case_index;

    for (case_index = 0; case_index < RANDOM_KEYGEN_CASES; ++case_index) {
        poly input;
        const uint32_t seed = (uint32_t)(0x6A09E667u + 0x01000193u * (uint32_t)case_index);

        make_keygen_ntt_f(&input, seed);
        run_case("keygen-ntt", case_index, &input);
    }
}

static void run_random_qrange_cases(void)
{
    uint32_t state = 0x31415926u;
    size_t case_index;

    for (case_index = 0; case_index < RANDOM_QRANGE_CASES; ++case_index) {
        poly input;

        fill_random_qrange(&input, &state);
        run_case("random-qrange", case_index, &input);
    }
}

int main(void)
{
    run_boundary_cases();
    run_keygen_cases();
    run_random_qrange_cases();
    printf("keygen_secret_f passed: 8 boundary + %u keygen NTT + %u random q-range cases\n",
           (unsigned)RANDOM_KEYGEN_CASES,
           (unsigned)RANDOM_QRANGE_CASES);
    return 0;
}
