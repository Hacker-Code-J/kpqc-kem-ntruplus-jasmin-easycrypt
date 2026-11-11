#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "poly.h"

extern uint32_t jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes(
    uint16_t output[768], const uint8_t input[1152]);

enum { GUARD = 32, SELECTED_POSITIONS = 6, RANDOM_CASES = 4096 };
_Static_assert(NTRUPLUS_N == 768, "NTRU+768 coefficient count");
_Static_assert(NTRUPLUS_Q == 3457, "official checked-decoder threshold");
_Static_assert(NTRUPLUS_POLYBYTES == 1152, "serialized byte count");
_Static_assert(sizeof(poly) == 1536, "reference polynomial layout");

typedef struct { uint8_t pre[GUARD], data[1152], post[GUARD]; } guarded_input;
typedef struct { uint8_t pre[GUARD]; poly data; uint8_t post[GUARD]; } guarded_c_output;
typedef struct { uint8_t pre[GUARD]; uint16_t data[768]; uint8_t post[GUARD]; } guarded_j_output;

static uint64_t cases, success_cases, failure_cases, assertions;
static const char *group = "initialization";
static size_t position;
static unsigned value;

static void require(int condition, const char *message)
{
    assertions++;
    if (!condition) {
        fprintf(stderr, "FAIL group=%s position=%zu value=%u case=%" PRIu64 ": %s\n",
                group, position, value, cases, message);
        exit(EXIT_FAILURE);
    }
}

static int all_byte(const uint8_t *p, size_t length, uint8_t value8)
{
    for (size_t i = 0; i < length; i++)
        if (p[i] != value8) return 0;
    return 1;
}

#define GUARDS_OK(x) (all_byte((x).pre, GUARD, 0xa5) && all_byte((x).post, GUARD, 0xa5))

/* A separate bit-stream encoding avoids copying the implementation's paired
 * three-byte shift expressions into the test oracle. */
static void put12(uint8_t bytes[1152], size_t index, uint16_t coefficient)
{
    require(index < 768 && coefficient < 4096, "fixture encoding bounds");
    for (unsigned bit = 0; bit < 12; bit++) {
        size_t offset = 12 * index + bit;
        uint8_t mask = (uint8_t)(1u << (offset % 8));
        bytes[offset / 8] = (uint8_t)((bytes[offset / 8] & (uint8_t)~mask) |
            ((coefficient & (1u << bit)) ? mask : 0u));
    }
}

static void bit_oracle(const uint8_t bytes[1152], uint16_t expected[768])
{
    for (size_t i = 0; i < 768; i++) {
        uint16_t x = 0;
        for (unsigned bit = 0; bit < 12; bit++) {
            size_t offset = 12 * i + bit;
            x |= (uint16_t)(((bytes[offset / 8] >> (offset % 8)) & 1u) << bit);
        }
        expected[i] = x;
    }
}

static int disjoint(const void *a, size_t an, const void *b, size_t bn)
{
    uintptr_t x = (uintptr_t)a, y = (uintptr_t)b;
    return x + an <= y || y + bn <= x;
}

static void check_case(const uint8_t bytes[1152], const uint16_t expected[768])
{
    guarded_input c_input, j_input;
    guarded_c_output c_output;
    guarded_j_output j_output;
    memset(&c_input, 0xa5, sizeof c_input);
    memset(&j_input, 0xa5, sizeof j_input);
    memset(&c_output, 0xa5, sizeof c_output);
    memset(&j_output, 0xa5, sizeof j_output);
    memcpy(c_input.data, bytes, sizeof c_input.data);
    memcpy(j_input.data, bytes, sizeof j_input.data);
    require(disjoint(&c_output.data, sizeof c_output.data, c_input.data, sizeof c_input.data),
            "reference input/output contract is disjoint");
    require(disjoint(j_output.data, sizeof j_output.data, j_input.data, sizeof j_input.data),
            "Jasmin input/output contract is disjoint");
    require((uintptr_t)j_output.data % _Alignof(uint16_t) == 0, "Jasmin u16 output alignment");

    uint32_t expected_status = 0;
    for (size_t i = 0; i < 768; i++) expected_status |= expected[i] >= NTRUPLUS_Q;
    int c_status = poly_frombytes(&c_output.data, c_input.data);
    uint32_t j_status = jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes(j_output.data, j_input.data);
    require(c_status == (int)expected_status, "official C canonicality status");
    require(j_status == expected_status, "Jasmin canonicality status");
    require(j_status == (uint32_t)c_status, "C/Jasmin status equality");
    for (size_t i = 0; i < 768; i++) {
        require(c_output.data.coeffs[i] == (int16_t)expected[i], "official C retains decoded value on success and failure");
        require(j_output.data[i] == expected[i], "Jasmin retains decoded value on success and failure");
    }
    require(memcmp(c_input.data, bytes, 1152) == 0, "official C input unchanged");
    require(memcmp(j_input.data, bytes, 1152) == 0, "Jasmin input unchanged");
    require(GUARDS_OK(c_input), "official C input guards");
    require(GUARDS_OK(j_input), "Jasmin input guards");
    require(GUARDS_OK(c_output), "official C output guards");
    require(GUARDS_OK(j_output), "Jasmin output guards");
    cases++;
    if (expected_status) failure_cases++; else success_cases++;
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

int main(void)
{
    uint8_t base[1152] = {0}, bytes[1152];
    uint16_t expected[768];
    const size_t positions[SELECTED_POSITIONS] = {0, 1, 384, 385, 766, 767};
    const uint16_t boundaries[] = {0, NTRUPLUS_Q - 1, NTRUPLUS_Q, 4095};
    uint32_t rng = UINT32_C(0x5ec9a731);

    group = "canonical-baseline";
    for (size_t i = 0; i < 768; i++) {
        expected[i] = (uint16_t)((97 * i + 13) % NTRUPLUS_Q);
        put12(base, i, expected[i]);
    }
    check_case(base, expected);

    group = "all-4096-values-first-middle-last-two-lanes";
    for (size_t k = 0; k < SELECTED_POSITIONS; k++) {
        position = positions[k];
        uint16_t saved = expected[position];
        for (value = 0; value < 4096; value++) {
            memcpy(bytes, base, sizeof bytes);
            put12(bytes, position, (uint16_t)value);
            expected[position] = (uint16_t)value;
            check_case(bytes, expected);
        }
        expected[position] = saved;
    }

    group = "four-boundaries-every-position";
    for (position = 0; position < 768; position++) {
        uint16_t saved = expected[position];
        for (size_t k = 0; k < sizeof boundaries / sizeof boundaries[0]; k++) {
            value = boundaries[k];
            memcpy(bytes, base, sizeof bytes);
            put12(bytes, position, (uint16_t)value);
            expected[position] = (uint16_t)value;
            check_case(bytes, expected);
        }
        expected[position] = saved;
    }

    group = "whole-array-patterns";
    for (unsigned pattern = 0; pattern < 5; pattern++) {
        memset(bytes, 0, sizeof bytes);
        for (position = 0; position < 768; position++) {
            value = pattern == 0 ? 4095u : pattern == 1 ?
                ((position & 1u) ? NTRUPLUS_Q - 1u : NTRUPLUS_Q) : pattern == 2 ?
                ((position == 0 || position == 767) ? NTRUPLUS_Q : 0u) :
                pattern == 3 ? 0u : NTRUPLUS_Q - 1u;
            expected[position] = (uint16_t)value;
            put12(bytes, position, expected[position]);
        }
        check_case(bytes, expected);
    }

    group = "constant-byte-patterns";
    for (value = 0; value < 256; value++) {
        memset(bytes, (int)value, sizeof bytes);
        bit_oracle(bytes, expected);
        check_case(bytes, expected);
    }

    group = "deterministic-random-bytes";
    for (value = 0; value < RANDOM_CASES; value++) {
        for (size_t i = 0; i < sizeof bytes; i++) bytes[i] = (uint8_t)next_u32(&rng);
        bit_oracle(bytes, expected);
        check_case(bytes, expected);
    }

    group = "deterministic-random-canonical-values";
    for (value = 0; value < RANDOM_CASES; value++) {
        memset(bytes, 0, sizeof bytes);
        for (position = 0; position < 768; position++) {
            expected[position] = (uint16_t)(next_u32(&rng) % NTRUPLUS_Q);
            put12(bytes, position, expected[position]);
        }
        check_case(bytes, expected);
    }

    require(cases == 36102 && success_cases > 0 && failure_cases > 0, "complete coverage and both statuses");
    printf("{\"status\":\"PASS\",\"cases\":%" PRIu64 ",\"success_cases\":%" PRIu64
           ",\"failure_cases\":%" PRIu64 ",\"coefficients_per_implementation\":%" PRIu64
           ",\"assertions\":%" PRIu64 "}\n", cases, success_cases, failure_cases, cases * 768, assertions);
    return EXIT_SUCCESS;
}
