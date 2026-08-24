#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../../../NTRU+/NTRU+768/ntt.h"
#include "../../../NTRU+/NTRU+768/poly.h"

#define NTRUPLUS_Q 3457
#define NTT_CENTERED_BOUND 1728
#define CASES_BOUNDARY 6u
#define CASES_RANDOM 16u
#define CASES_TOTAL (CASES_BOUNDARY + CASES_RANDOM)

_Static_assert(CHAR_BIT == 8, "test requires 8-bit bytes");
_Static_assert(sizeof(int16_t) * CHAR_BIT == 16,
               "test requires 16-bit coefficients");
_Static_assert(INT16_MIN == (-INT16_MAX - 1),
               "test requires two's-complement int16_t");
_Static_assert(NTRUPLUS_N == 768, "test requires NTRU+768");
_Static_assert(NTRUPLUS_Q == 3457, "test requires q=3457");

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
    return (int16_t)((int32_t)(next_u32(state) % (2 * NTRUPLUS_Q)) - NTRUPLUS_Q);
}

static int16_t sample_centered(uint32_t *state)
{
    return (int16_t)((int32_t)(next_u32(state) %
        (2 * NTT_CENTERED_BOUND + 1)) - NTT_CENTERED_BOUND);
}

static int32_t mod_q(int64_t value)
{
    int32_t reduced = (int32_t)(value % NTRUPLUS_Q);

    return reduced < 0 ? reduced + NTRUPLUS_Q : reduced;
}

static void fill_constant(poly *dst, int16_t value)
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        dst->coeffs[i] = value;
    }
}

static void fill_alternating(poly *dst, int16_t even_value, int16_t odd_value)
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        dst->coeffs[i] = (i & 1u) == 0 ? even_value : odd_value;
    }
}

static void fill_staircase(poly *dst, int16_t start, int16_t step)
{
    int32_t value = start;

    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        dst->coeffs[i] = (int16_t)value;
        value += step;
        if (value >= NTRUPLUS_Q) {
            value = -NTRUPLUS_Q;
        } else if (value < -NTRUPLUS_Q) {
            value = NTRUPLUS_Q - 1;
        }
    }
}

static void fill_random(poly *dst, uint32_t *state)
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        dst->coeffs[i] = sample_mod_q(state);
    }
}

static void fill_random_centered(poly *dst, uint32_t *state)
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        dst->coeffs[i] = sample_centered(state);
    }
}

static void fill_centered_staircase(poly *dst, int16_t start, int16_t step)
{
    int32_t value = start;

    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        dst->coeffs[i] = (int16_t)value;
        value += step;
        if (value > NTT_CENTERED_BOUND) {
            value = -NTT_CENTERED_BOUND;
        } else if (value < -NTT_CENTERED_BOUND) {
            value = NTT_CENTERED_BOUND;
        }
    }
}

static void init_case(size_t idx, poly *h, poly *r, poly *m)
{
    uint32_t state = (uint32_t)(0x45d9f3bu + 0x9e3779b9u * (uint32_t)idx);

    switch (idx) {
    case 0:
        fill_constant(h, 0);
        fill_constant(r, 0);
        fill_constant(m, 0);
        return;
    case 1:
        fill_constant(h, NTRUPLUS_Q - 1);
        fill_constant(r, NTRUPLUS_Q - 1);
        fill_constant(m, NTT_CENTERED_BOUND);
        return;
    case 2:
        fill_constant(h, -NTRUPLUS_Q);
        fill_constant(r, -NTRUPLUS_Q);
        fill_constant(m, -NTT_CENTERED_BOUND);
        return;
    case 3:
        fill_alternating(h, NTRUPLUS_Q - 1, -NTRUPLUS_Q);
        fill_alternating(r, -NTRUPLUS_Q, NTRUPLUS_Q - 1);
        fill_alternating(m, NTT_CENTERED_BOUND, -NTT_CENTERED_BOUND);
        return;
    case 4:
        fill_staircase(h, -NTRUPLUS_Q, 17);
        fill_staircase(r, NTRUPLUS_Q, -19);
        fill_centered_staircase(m, -NTT_CENTERED_BOUND, 29);
        return;
    case 5:
        for (size_t block = 0; block < NTRUPLUS_N / 8; ++block) {
            const size_t off = 8 * block;
            const int16_t left = (block & 1u) == 0 ? (int16_t)(NTRUPLUS_Q - 1) : -NTRUPLUS_Q;
            const int16_t right = (block % 3u) == 0 ? (int16_t)(NTRUPLUS_Q - 1) : (int16_t)(1 - NTRUPLUS_Q);

            h->coeffs[off + 0] = left;
            h->coeffs[off + 1] = right;
            h->coeffs[off + 2] = (int16_t)-right;
            h->coeffs[off + 3] = (int16_t)-left;
            h->coeffs[off + 4] = right;
            h->coeffs[off + 5] = left;
            h->coeffs[off + 6] = (int16_t)-left;
            h->coeffs[off + 7] = (int16_t)-right;

            r->coeffs[off + 0] = right;
            r->coeffs[off + 1] = left;
            r->coeffs[off + 2] = (int16_t)-left;
            r->coeffs[off + 3] = (int16_t)-right;
            r->coeffs[off + 4] = left;
            r->coeffs[off + 5] = right;
            r->coeffs[off + 6] = (int16_t)-right;
            r->coeffs[off + 7] = (int16_t)-left;

            m->coeffs[off + 0] = (int16_t)(block % NTRUPLUS_Q);
            m->coeffs[off + 1] = (int16_t)(-(int16_t)(block % NTRUPLUS_Q));
            m->coeffs[off + 2] = (int16_t)((3 * block) % NTRUPLUS_Q);
            m->coeffs[off + 3] = (int16_t)(-((int16_t)((5 * block) % NTRUPLUS_Q)));
            m->coeffs[off + 4] = (int16_t)((7 * block) % NTRUPLUS_Q);
            m->coeffs[off + 5] = (int16_t)(-((int16_t)((11 * block) % NTRUPLUS_Q)));
            m->coeffs[off + 6] = (int16_t)((13 * block) % NTRUPLUS_Q);
            m->coeffs[off + 7] = (int16_t)(-((int16_t)((17 * block) % NTRUPLUS_Q)));
        }
        return;
    default:
        fill_random(h, &state);
        fill_random(r, &state);
        fill_random_centered(m, &state);
        return;
    }
}

static void check_equal(const char *label, size_t case_idx, const poly *lhs, const poly *rhs)
{
    if (memcmp(lhs, rhs, sizeof(*lhs)) != 0) {
        fprintf(stderr, "%s mismatch in case %zu\n", label, case_idx);
        exit(1);
    }
}

static void check_output_range(const char *label, size_t case_idx, const poly *p)
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        const int16_t value = p->coeffs[i];
        if (value < -NTRUPLUS_Q || value >= NTRUPLUS_Q) {
            fprintf(stderr,
                    "%s out-of-range in case %zu at coeff %zu: value=%d\n",
                    label,
                    case_idx,
                    i,
                    value);
            exit(1);
        }
    }
}

static void check_relation(size_t case_idx, const poly *mul, const poly *add, const poly *m)
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        const int32_t lhs = mod_q(add->coeffs[i]);
        const int32_t rhs = mod_q((int64_t)mul->coeffs[i] + m->coeffs[i]);
        if (lhs != rhs) {
            fprintf(stderr,
                    "poly_basemul_add relation mismatch in case %zu at coeff %zu: add=%d mul_plus_m=%d\n",
                    case_idx,
                    i,
                    lhs,
                    rhs);
            exit(1);
        }
    }
}

static void print_poly(const char *tag, size_t idx, const poly *p)
{
    printf("%s %zu", tag, idx);
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        printf(" %d", p->coeffs[i]);
    }
    printf("\n");
}

int main(void)
{
    for (size_t idx = 0; idx < CASES_TOTAL; ++idx) {
        poly h;
        poly r;
        poly m;
        poly h_before;
        poly r_before;
        poly m_before;
        poly add_once;
        poly add_twice;
        poly mul_only;

        init_case(idx, &h, &r, &m);
        h_before = h;
        r_before = r;
        m_before = m;

        poly_basemul_add(&add_once, &h, &r, &m);
        poly_basemul_add(&add_twice, &h, &r, &m);
        poly_basemul(&mul_only, &h, &r);

        check_equal("h input mutated", idx, &h, &h_before);
        check_equal("r input mutated", idx, &r, &r_before);
        check_equal("m input mutated", idx, &m, &m_before);
        check_equal("poly_basemul_add determinism", idx, &add_once, &add_twice);
        check_output_range("poly_basemul_add", idx, &add_once);
        check_output_range("poly_basemul", idx, &mul_only);
        check_relation(idx, &mul_only, &add_once, &m);

        print_poly("ADD", idx, &add_once);
        print_poly("MUL", idx, &mul_only);
        print_poly("MSG", idx, &m);
    }

    return 0;
}
