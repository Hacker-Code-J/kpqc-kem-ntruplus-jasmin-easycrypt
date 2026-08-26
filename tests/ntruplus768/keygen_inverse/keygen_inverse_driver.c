#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../../../NTRU+/NTRU+768/params.h"
#include "../../../NTRU+/NTRU+768/ntt.h"
#include "../../../NTRU+/NTRU+768/poly.h"

#define NTRUPLUS_RINV_MOD_Q 2775
#define BOUNDARY_CASES 7u
#define RANDOM_CASES 16u
#define TOTAL_CASES (BOUNDARY_CASES + RANDOM_CASES)

extern uint64_t jade_ntruplus_ntruplus768_amd64_ref_poly_baseinv(
    poly *r, const poly *a);

_Static_assert(CHAR_BIT == 8, "keygen inverse test requires 8-bit bytes");
_Static_assert(sizeof(int16_t) * CHAR_BIT == 16,
               "keygen inverse test requires 16-bit int16_t");
_Static_assert(NTRUPLUS_N == 768, "keygen inverse test requires N=768");
_Static_assert(NTRUPLUS_Q == 3457, "keygen inverse test requires q=3457");

static uint32_t rng_state = UINT32_C(0x7A6D4E21);

static uint32_t next_u32(uint32_t *state)
{
    uint32_t x = *state;

    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    *state = x;
    return x;
}

static uint32_t next_random(void)
{
    return next_u32(&rng_state);
}

static int32_t mod_q(int64_t value)
{
    int64_t reduced = value % NTRUPLUS_Q;

    if (reduced < 0) {
        reduced += NTRUPLUS_Q;
    }
    return (int32_t)reduced;
}

static void fill_case(uint8_t buf[NTRUPLUS_N / 4], size_t case_index)
{
    uint32_t f_failure_state = UINT32_C(16372);
    size_t i;

    for (i = 0; i < NTRUPLUS_N / 4; ++i) {
        switch (case_index) {
        case 0:
            buf[i] = 0;
            break;
        case 1:
            buf[i] = i < NTRUPLUS_N / 8 ? UINT8_C(0xFF) : 0;
            break;
        case 2:
            buf[i] = i < NTRUPLUS_N / 8 ? 0 : UINT8_C(0xFF);
            break;
        case 3:
            buf[i] = (i & 1u) != 0u ? UINT8_C(0xAA) : UINT8_C(0x55);
            break;
        case 4:
            buf[i] = i == 0 || i == NTRUPLUS_N / 8 ? UINT8_C(0x81) : 0;
            break;
        case 5:
            buf[i] = i < NTRUPLUS_N / 8 ? (uint8_t)i : (uint8_t)~i;
            break;
        case 6:
            buf[i] = (uint8_t)next_u32(&f_failure_state);
            break;
        default:
            buf[i] = (uint8_t)next_random();
            break;
        }
    }
}

static void fill_poly(poly *value, int16_t coefficient)
{
    size_t i;

    for (i = 0; i < NTRUPLUS_N; ++i) {
        value->coeffs[i] = coefficient;
    }
}

static int poly_equal(const poly *left, const poly *right)
{
    return memcmp(left, right, sizeof(*left)) == 0;
}

static int poly_all_zero(const poly *value)
{
    size_t i;

    for (i = 0; i < NTRUPLUS_N; ++i) {
        if (value->coeffs[i] != 0) {
            return 0;
        }
    }
    return 1;
}

static int strict_qrange_poly(const poly *value)
{
    size_t i;

    for (i = 0; i < NTRUPLUS_N; ++i) {
        if (!(-NTRUPLUS_Q < value->coeffs[i] &&
              value->coeffs[i] < NTRUPLUS_Q)) {
            return 0;
        }
    }
    return 1;
}

static int block_inverse_ok(
    const int16_t input[4], const int16_t inverse[4], int16_t zeta_word)
{
    const int32_t zeta =
        mod_q((int64_t)zeta_word * NTRUPLUS_RINV_MOD_Q);
    const int64_t c0 =
        (int64_t)input[0] * inverse[0] +
        (int64_t)zeta *
            ((int64_t)input[1] * inverse[3] +
             (int64_t)input[2] * inverse[2] +
             (int64_t)input[3] * inverse[1]);
    const int64_t c1 =
        (int64_t)input[0] * inverse[1] +
        (int64_t)input[1] * inverse[0] +
        (int64_t)zeta *
            ((int64_t)input[2] * inverse[3] +
             (int64_t)input[3] * inverse[2]);
    const int64_t c2 =
        (int64_t)input[0] * inverse[2] +
        (int64_t)input[1] * inverse[1] +
        (int64_t)input[2] * inverse[0] +
        (int64_t)zeta * (int64_t)input[3] * inverse[3];
    const int64_t c3 =
        (int64_t)input[0] * inverse[3] +
        (int64_t)input[1] * inverse[2] +
        (int64_t)input[2] * inverse[1] +
        (int64_t)input[3] * inverse[0];

    return mod_q(c0) == 1 && mod_q(c1) == 0 &&
           mod_q(c2) == 0 && mod_q(c3) == 0;
}

static int poly_inverse_ok(const poly *input, const poly *inverse)
{
    size_t block;

    for (block = 0; block < NTRUPLUS_N / 4; ++block) {
        const int16_t zeta =
            (block & 1u) == 0u ? zetas[96u + block / 2u]
                               : (int16_t)-zetas[96u + block / 2u];

        if (!block_inverse_ok(input->coeffs + 4 * block,
                              inverse->coeffs + 4 * block,
                              zeta)) {
            return 0;
        }
    }
    return 1;
}

static int check_inverse(
    const char *label, size_t case_index, const poly *input,
    size_t *successes, size_t *failures)
{
    poly c_input = *input;
    poly jasmin_input = *input;
    poly c_output;
    poly jasmin_output;
    const poly input_before = *input;
    int c_status;
    uint64_t jasmin_status;

    if (!strict_qrange_poly(input)) {
        fprintf(stderr, "%s[%zu] NTT input is out of strict q-range\n",
                label, case_index);
        return 1;
    }

    fill_poly(&c_output, (int16_t)0x4444);
    fill_poly(&jasmin_output, (int16_t)0x7777);
    c_status = poly_baseinv(&c_output, &c_input);
    jasmin_status = jade_ntruplus_ntruplus768_amd64_ref_poly_baseinv(
        &jasmin_output, &jasmin_input);

    if (c_status < 0 || c_status > 1 ||
        jasmin_status != (uint64_t)c_status) {
        fprintf(stderr, "%s[%zu] status mismatch: C=%d Jasmin=%llu\n",
                label, case_index, c_status,
                (unsigned long long)jasmin_status);
        return 1;
    }
    if (!poly_equal(&c_input, &input_before) ||
        !poly_equal(&jasmin_input, &input_before)) {
        fprintf(stderr, "%s[%zu] inverse call mutated its input\n",
                label, case_index);
        return 1;
    }
    if (!poly_equal(&c_output, &jasmin_output)) {
        fprintf(stderr, "%s[%zu] C/Jasmin output mismatch\n",
                label, case_index);
        return 1;
    }

    if (c_status == 0) {
        ++*successes;
        if (!strict_qrange_poly(&c_output) ||
            !poly_inverse_ok(&input_before, &c_output)) {
            fprintf(stderr, "%s[%zu] success output violates inverse contract\n",
                    label, case_index);
            return 1;
        }
    } else {
        ++*failures;
        if (!poly_all_zero(&c_output)) {
            fprintf(stderr, "%s[%zu] failure output is not fully zero\n",
                    label, case_index);
            return 1;
        }
    }
    return 0;
}

static int check_case(
    size_t case_index,
    size_t *f_successes, size_t *f_failures,
    size_t *g_successes, size_t *g_failures)
{
    uint8_t buf[NTRUPLUS_N / 4];
    poly sample;
    poly f;
    poly g;

    fill_case(buf, case_index);
    poly_cbd1(&sample, buf);
    poly_triple(&f, &sample);
    f.coeffs[0] += 1;
    g = sample;
    poly_triple(&g, &g);
    poly_ntt(&f, &f);
    poly_ntt(&g, &g);

    if (check_inverse("f", case_index, &f, f_successes, f_failures) != 0 ||
        check_inverse("g", case_index, &g, g_successes, g_failures) != 0) {
        return 1;
    }
    return 0;
}

int main(void)
{
    size_t f_successes = 0;
    size_t f_failures = 0;
    size_t g_successes = 0;
    size_t g_failures = 0;
    size_t case_index;

    for (case_index = 0; case_index < TOTAL_CASES; ++case_index) {
        if (check_case(case_index,
                       &f_successes, &f_failures,
                       &g_successes, &g_failures) != 0) {
            return 1;
        }
    }

    if (f_successes == 0 || f_failures == 0 ||
        g_successes == 0 || g_failures == 0) {
        fprintf(stderr,
                "branch coverage missing: f=%zu/%zu g=%zu/%zu\n",
                f_successes, f_failures, g_successes, g_failures);
        return 1;
    }

    printf("keygen inverse composition passed: %u f + %u g cases; "
           "f=%zu success/%zu failure, g=%zu success/%zu failure\n",
           TOTAL_CASES, TOTAL_CASES,
           f_successes, f_failures, g_successes, g_failures);
    return 0;
}
