#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "../../../NTRU+/NTRU+768/poly.h"

#define NTRUPLUS_N 768
#define NTRUPLUS_Q 3457

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

static void check_case(const char *tag,
                       size_t idx,
                       const int16_t a[NTRUPLUS_N],
                       const int16_t b[NTRUPLUS_N])
{
    int16_t ref[NTRUPLUS_N];
    int16_t jasmin[NTRUPLUS_N];

    poly_basemul_ref(ref, a, b);
    jade_ntruplus_ntruplus768_amd64_ref_poly_basemul(jasmin, a, b);

    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
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

    printf("poly_basemul differential passed: 8 signed-boundary + %zu random signed-domain cases\n",
           random_cases);
}

int main(void)
{
    run_boundary_cases();
    run_random_cases();
    return 0;
}
