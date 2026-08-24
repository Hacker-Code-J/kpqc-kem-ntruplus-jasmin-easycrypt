#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "../../../NTRU+/NTRU+768/params.h"
#include "../../../NTRU+/NTRU+768/poly.h"

#define BOUNDARY_CASES 6
#define RANDOM_CASES 16
#define TOTAL_CASES (BOUNDARY_CASES + RANDOM_CASES)

_Static_assert(NTRUPLUS_N == 768, "keygen sampler test requires N=768");
_Static_assert(NTRUPLUS_Q == 3457, "keygen sampler test requires q=3457");
_Static_assert(sizeof(((poly *)0)->coeffs) / sizeof(int16_t) == NTRUPLUS_N,
               "poly ABI must contain exactly N coefficients");

static uint32_t rng_state = UINT32_C(0x7A6D4E21);

static uint32_t next_random(void)
{
    uint32_t x = rng_state;
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    rng_state = x;
    return x;
}

static void fill_case(uint8_t buf[NTRUPLUS_N / 4], size_t case_index)
{
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
            buf[i] = (i & 1U) != 0U ? UINT8_C(0xAA) : UINT8_C(0x55);
            break;
        case 4:
            buf[i] = i == 0 || i == NTRUPLUS_N / 8 ? UINT8_C(0x81) : 0;
            break;
        case 5:
            buf[i] = i < NTRUPLUS_N / 8 ? (uint8_t)i : (uint8_t)~i;
            break;
        default:
            buf[i] = (uint8_t)next_random();
            break;
        }
    }
}

static int expected_sample(const uint8_t buf[NTRUPLUS_N / 4], size_t k)
{
    const size_t byte_index = k / 8;
    const unsigned bit_index = (unsigned)(k % 8);
    const int head = (buf[byte_index] >> bit_index) & 1;
    const int tail = (buf[NTRUPLUS_N / 8 + byte_index] >> bit_index) & 1;
    return head - tail;
}

static int mod3_nonnegative(int value)
{
    const int residue = value % 3;
    return residue < 0 ? residue + 3 : residue;
}

static int check_equal(const poly *left, const poly *right, const char *label, size_t case_index)
{
    size_t k;
    for (k = 0; k < NTRUPLUS_N; ++k) {
        if (left->coeffs[k] != right->coeffs[k]) {
            fprintf(stderr, "%s mismatch at case %zu coefficient %zu\n", label, case_index, k);
            return 1;
        }
    }
    return 0;
}

static int check_ntt_range(const poly *value, const char *label, size_t case_index)
{
    size_t k;
    for (k = 0; k < NTRUPLUS_N; ++k) {
        if (value->coeffs[k] < -NTRUPLUS_Q || value->coeffs[k] >= NTRUPLUS_Q) {
            fprintf(stderr, "%s range failure at case %zu coefficient %zu: %d\n",
                    label, case_index, k, value->coeffs[k]);
            return 1;
        }
    }
    return 0;
}

static int check_case(size_t case_index)
{
    uint8_t buf[NTRUPLUS_N / 4];
    poly sample;
    poly sample_before;
    poly triple;
    poly triple_alias;
    poly f_pre;
    poly g_pre;
    poly f_before;
    poly g_before;
    poly f_ntt;
    poly g_ntt;
    poly f_ntt_alias;
    poly g_ntt_alias;
    size_t k;

    fill_case(buf, case_index);
    poly_cbd1(&sample, buf);
    sample_before = sample;
    poly_triple(&triple, &sample);
    if (check_equal(&sample, &sample_before, "poly_triple input mutation", case_index) != 0) {
        return 1;
    }
    triple_alias = sample;
    poly_triple(&triple_alias, &triple_alias);
    if (check_equal(&triple, &triple_alias, "poly_triple exact alias", case_index) != 0) {
        return 1;
    }

    f_pre = triple;
    f_pre.coeffs[0] += 1;
    g_pre = triple;
    for (k = 0; k < NTRUPLUS_N; ++k) {
        const int sampled = expected_sample(buf, k);
        const int expected_g = 3 * sampled;
        const int expected_f = expected_g + (k == 0 ? 1 : 0);
        if (sample.coeffs[k] != sampled || triple.coeffs[k] != expected_g ||
            f_pre.coeffs[k] != expected_f || g_pre.coeffs[k] != expected_g) {
            fprintf(stderr, "sampler shaping mismatch at case %zu coefficient %zu\n", case_index, k);
            return 1;
        }
        if (expected_g < -3 || expected_g > 3 || mod3_nonnegative(expected_g) != 0) {
            fprintf(stderr, "g shape failure at case %zu coefficient %zu\n", case_index, k);
            return 1;
        }
        if (k == 0) {
            if (expected_f < -2 || expected_f > 4 || mod3_nonnegative(expected_f) != 1) {
                fprintf(stderr, "f constant shape failure at case %zu\n", case_index);
                return 1;
            }
        } else if (expected_f < -3 || expected_f > 3 || mod3_nonnegative(expected_f) != 0) {
            fprintf(stderr, "f nonconstant shape failure at case %zu coefficient %zu\n", case_index, k);
            return 1;
        }
    }

    f_before = f_pre;
    g_before = g_pre;
    poly_ntt(&f_ntt, &f_pre);
    poly_ntt(&g_ntt, &g_pre);
    if (check_equal(&f_pre, &f_before, "f NTT input mutation", case_index) != 0 ||
        check_equal(&g_pre, &g_before, "g NTT input mutation", case_index) != 0) {
        return 1;
    }
    f_ntt_alias = f_pre;
    g_ntt_alias = g_pre;
    poly_ntt(&f_ntt_alias, &f_ntt_alias);
    poly_ntt(&g_ntt_alias, &g_ntt_alias);
    if (check_equal(&f_ntt, &f_ntt_alias, "f NTT exact alias", case_index) != 0 ||
        check_equal(&g_ntt, &g_ntt_alias, "g NTT exact alias", case_index) != 0 ||
        check_ntt_range(&f_ntt, "f NTT", case_index) != 0 ||
        check_ntt_range(&g_ntt, "g NTT", case_index) != 0) {
        return 1;
    }
    return 0;
}

int main(void)
{
    size_t case_index;
    for (case_index = 0; case_index < TOTAL_CASES; ++case_index) {
        if (check_case(case_index) != 0) {
            return 1;
        }
    }
    printf("keygen sampler vectors passed: %d full-polynomial cases\n", TOTAL_CASES);
    return 0;
}
