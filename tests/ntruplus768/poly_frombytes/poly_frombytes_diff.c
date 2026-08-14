#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../../../NTRU+/NTRU+768/poly.h"

#define COEFF_MASK 0x0FFFu

_Static_assert(NTRUPLUS_N == 768, "proof model requires NTRU+768");
_Static_assert(NTRUPLUS_POLYBYTES == 1152, "proof model requires 1152 serialized bytes");

static void poly_frombytes_oracle(int16_t r[NTRUPLUS_N], const uint8_t a[NTRUPLUS_POLYBYTES])
{
    for (size_t i = 0; i < NTRUPLUS_N / 2; ++i) {
        const size_t j = 3 * i;
        const uint16_t a0 = a[j + 0];
        const uint16_t a1 = a[j + 1];
        const uint16_t a2 = a[j + 2];
        const uint16_t lo = a0 + ((a1 & 0x0fu) << 8);
        const uint16_t hi = (a1 >> 4) + (a2 << 4);

        r[2 * i] = (int16_t)(lo & COEFF_MASK);
        r[2 * i + 1] = (int16_t)(hi & COEFF_MASK);
    }
}

static void poly_frombytes_ref(int16_t r[NTRUPLUS_N], const uint8_t a[NTRUPLUS_POLYBYTES])
{
    poly out;

    poly_frombytes(&out, a);
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        r[i] = out.coeffs[i];
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

static void fill_constant(uint8_t dst[NTRUPLUS_POLYBYTES], uint8_t value)
{
    memset(dst, value, NTRUPLUS_POLYBYTES);
}

static void fill_incrementing(uint8_t dst[NTRUPLUS_POLYBYTES], uint8_t start, uint8_t step)
{
    uint8_t value = start;

    for (size_t i = 0; i < NTRUPLUS_POLYBYTES; ++i) {
        dst[i] = value;
        value = (uint8_t)(value + step);
    }
}

static void fill_random(uint8_t dst[NTRUPLUS_POLYBYTES], uint32_t *state)
{
    for (size_t i = 0; i < NTRUPLUS_POLYBYTES; ++i) {
        dst[i] = (uint8_t)(next_u32(state) & 0xffu);
    }
}

static void set_triplet(uint8_t dst[NTRUPLUS_POLYBYTES], size_t pair_index, uint8_t b0, uint8_t b1, uint8_t b2)
{
    const size_t j = 3 * pair_index;

    dst[j + 0] = b0;
    dst[j + 1] = b1;
    dst[j + 2] = b2;
}

static void assert_range(const char *impl,
                         const char *tag,
                         size_t case_index,
                         size_t coeff_index,
                         int16_t value,
                         const uint8_t input[NTRUPLUS_POLYBYTES])
{
    if (value < 0 || value > (int16_t)COEFF_MASK) {
        const size_t triplet = coeff_index / 2;
        const size_t j = 3 * triplet;

        fprintf(stderr,
                "%s out-of-range in %s[%zu] at coeff %zu: value=%d expected in [0,4095]\n",
                impl,
                tag,
                case_index,
                coeff_index,
                value);
        fprintf(stderr,
                "input triplet %zu: %02x %02x %02x\n",
                triplet,
                input[j + 0],
                input[j + 1],
                input[j + 2]);
        exit(1);
    }
}

static void check_equal(const char *lhs_name,
                        const char *rhs_name,
                        const char *tag,
                        size_t case_index,
                        const int16_t lhs[NTRUPLUS_N],
                        const int16_t rhs[NTRUPLUS_N],
                        const uint8_t input[NTRUPLUS_POLYBYTES])
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        if (lhs[i] != rhs[i]) {
            const size_t triplet = i / 2;
            const size_t j = 3 * triplet;

            fprintf(stderr,
                    "mismatch %s vs %s in %s[%zu] at coeff %zu: %d != %d\n",
                    lhs_name,
                    rhs_name,
                    tag,
                    case_index,
                    i,
                    lhs[i],
                    rhs[i]);
            fprintf(stderr,
                    "input triplet %zu: %02x %02x %02x\n",
                    triplet,
                    input[j + 0],
                    input[j + 1],
                    input[j + 2]);
            exit(1);
        }
    }
}

static void check_case(const char *tag, size_t case_index, const uint8_t input[NTRUPLUS_POLYBYTES])
{
    int16_t oracle[NTRUPLUS_N];
    int16_t ref[NTRUPLUS_N];

    poly_frombytes_oracle(oracle, input);
    poly_frombytes_ref(ref, input);

    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        assert_range("oracle", tag, case_index, i, oracle[i], input);
        assert_range("ref", tag, case_index, i, ref[i], input);
    }

    check_equal("oracle", "ref", tag, case_index, oracle, ref, input);
}

static void run_boundary_cases(void)
{
    uint8_t input[NTRUPLUS_POLYBYTES];

    fill_constant(input, 0x00u);
    check_case("boundary", 0, input);

    fill_constant(input, 0xffu);
    check_case("boundary", 1, input);

    fill_constant(input, 0x0fu);
    check_case("boundary", 2, input);

    fill_constant(input, 0xf0u);
    check_case("boundary", 3, input);

    fill_constant(input, 0xaau);
    check_case("boundary", 4, input);

    fill_constant(input, 0x55u);
    check_case("boundary", 5, input);

    fill_incrementing(input, 0x00u, 0x01u);
    check_case("boundary", 6, input);

    fill_incrementing(input, 0xffu, 0xf7u);
    check_case("boundary", 7, input);
}

static void run_nibble_pattern_cases(void)
{
    uint8_t input[NTRUPLUS_POLYBYTES];

    fill_constant(input, 0x00u);
    set_triplet(input, 0, 0x00u, 0x00u, 0x00u);
    check_case("nibble", 0, input);

    fill_constant(input, 0x00u);
    set_triplet(input, 0, 0xffu, 0x0fu, 0x00u);
    check_case("nibble", 1, input);

    fill_constant(input, 0x00u);
    set_triplet(input, 0, 0x00u, 0xf0u, 0xffu);
    check_case("nibble", 2, input);

    fill_constant(input, 0x00u);
    set_triplet(input, 191, 0x34u, 0x12u, 0xabu);
    set_triplet(input, 192, 0xcdu, 0xefu, 0x01u);
    check_case("nibble", 3, input);

    fill_constant(input, 0x00u);
    set_triplet(input, 383, 0x89u, 0x7fu, 0x45u);
    check_case("nibble", 4, input);

    fill_constant(input, 0x00u);
    for (size_t i = 0; i < NTRUPLUS_N / 2; ++i) {
        set_triplet(input,
                    i,
                    (uint8_t)(i & 0xffu),
                    (uint8_t)(((i << 4) | (i >> 4)) & 0xffu),
                    (uint8_t)(~i & 0xffu));
    }
    check_case("nibble", 5, input);
}

static void run_single_triplet_cases(void)
{
    uint8_t input[NTRUPLUS_POLYBYTES];
    const size_t interesting_pairs[] = {0u, 1u, 127u, 128u, 255u, 256u, 382u, 383u};
    const uint8_t triplets[][3] = {
        {0x01u, 0x00u, 0x00u},
        {0x00u, 0x10u, 0x00u},
        {0x00u, 0x00u, 0x01u},
        {0xffu, 0xffu, 0xffu},
        {0x5au, 0xa5u, 0x3cu},
    };
    size_t case_index = 0;

    for (size_t i = 0; i < sizeof(interesting_pairs) / sizeof(interesting_pairs[0]); ++i) {
        for (size_t j = 0; j < sizeof(triplets) / sizeof(triplets[0]); ++j) {
            fill_constant(input, 0x00u);
            set_triplet(input,
                        interesting_pairs[i],
                        triplets[j][0],
                        triplets[j][1],
                        triplets[j][2]);
            check_case("single-triplet", case_index++, input);
        }
    }
}

static void run_random_cases(void)
{
    uint32_t state = 0x7a4f9d13u;
    const size_t random_cases = 4096;

    for (size_t case_index = 0; case_index < random_cases; ++case_index) {
        uint8_t input[NTRUPLUS_POLYBYTES];

        fill_random(input, &state);
        check_case("random", case_index, input);
    }

    printf("poly_frombytes differential passed: 8 boundary + 6 nibble + 40 single-triplet + %zu random vectors\n",
           random_cases);
}

int main(void)
{
    run_boundary_cases();
    run_nibble_pattern_cases();
    run_single_triplet_cases();
    run_random_cases();
    return 0;
}
