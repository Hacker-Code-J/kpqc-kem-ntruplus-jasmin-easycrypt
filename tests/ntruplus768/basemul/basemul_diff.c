#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#define NTRUPLUS_Q 3457
#define NTRUPLUS_QINV 12929
#define NTRUPLUS_RSQ 867

/* The correspondence contract uses distinct output and input buffers. */

extern void basemul(int16_t r[4], const int16_t a[4], const int16_t b[4], const int16_t zeta);
/* The source-level mutable-pointer return is not a scalar C ABI return. */
extern void jade_ntruplus_ntruplus768_amd64_ref_basemul(
    int16_t r[4], const int16_t a[4], const int16_t b[4], int16_t zeta);

static int16_t montgomery_reduce_ref(int32_t a)
{
    int16_t t;

    t = (int16_t)a * NTRUPLUS_QINV;
    t = (int16_t)((a - (int32_t)t * NTRUPLUS_Q) >> 16);
    return t;
}

static int fits_i32(int64_t x)
{
    return x >= INT32_MIN && x <= INT32_MAX;
}

static int basemul_inputs_are_defined(const int16_t a[4], const int16_t b[4], int16_t zeta)
{
    int64_t s0;
    int64_t s1;
    int64_t s2;
    int64_t s3;
    int16_t t0;
    int16_t t1;
    int16_t t2;
    int16_t t3;

    s0 = (int64_t)a[1] * b[3] + (int64_t)a[2] * b[2] + (int64_t)a[3] * b[1];
    s1 = (int64_t)a[2] * b[3] + (int64_t)a[3] * b[2];
    s2 = (int64_t)a[3] * b[3];
    s3 = (int64_t)a[0] * b[3] + (int64_t)a[1] * b[2] + (int64_t)a[2] * b[1] + (int64_t)a[3] * b[0];

    if (!fits_i32(s0) || !fits_i32(s1) || !fits_i32(s2) || !fits_i32(s3)) {
        return 0;
    }

    t0 = montgomery_reduce_ref((int32_t)s0);
    t1 = montgomery_reduce_ref((int32_t)s1);
    t2 = montgomery_reduce_ref((int32_t)s2);
    t3 = montgomery_reduce_ref((int32_t)s3);

    s0 = (int64_t)t0 * zeta + (int64_t)a[0] * b[0];
    s1 = (int64_t)t1 * zeta + (int64_t)a[0] * b[1] + (int64_t)a[1] * b[0];
    s2 = (int64_t)t2 * zeta + (int64_t)a[0] * b[2] + (int64_t)a[1] * b[1] + (int64_t)a[2] * b[0];

    if (!fits_i32(s0) || !fits_i32(s1) || !fits_i32(s2)) {
        return 0;
    }

    t0 = montgomery_reduce_ref((int32_t)s0);
    t1 = montgomery_reduce_ref((int32_t)s1);
    t2 = montgomery_reduce_ref((int32_t)s2);

    s0 = (int64_t)t0 * NTRUPLUS_RSQ;
    s1 = (int64_t)t1 * NTRUPLUS_RSQ;
    s2 = (int64_t)t2 * NTRUPLUS_RSQ;
    s3 = (int64_t)t3 * NTRUPLUS_RSQ;

    return fits_i32(s0) && fits_i32(s1) && fits_i32(s2) && fits_i32(s3);
}

static void check_case(const char *tag, size_t idx, const int16_t a[4], const int16_t b[4], int16_t zeta)
{
    int16_t c_ref[4];
    int16_t c_jasmin[4];

    if (!basemul_inputs_are_defined(a, b, zeta)) {
        fprintf(stderr, "undefined-domain case rejected: %s[%zu]\n", tag, idx);
        exit(1);
    }

    basemul(c_ref, a, b, zeta);
    jade_ntruplus_ntruplus768_amd64_ref_basemul(c_jasmin, a, b, zeta);

    for (size_t i = 0; i < 4; ++i) {
        if (c_ref[i] != c_jasmin[i]) {
            fprintf(stderr,
                    "mismatch in %s[%zu] at limb %zu: ref=%d jasmin=%d\n",
                    tag,
                    idx,
                    i,
                    c_ref[i],
                    c_jasmin[i]);
            fprintf(stderr,
                    "a={%d,%d,%d,%d} b={%d,%d,%d,%d} zeta=%d\n",
                    a[0],
                    a[1],
                    a[2],
                    a[3],
                    b[0],
                    b[1],
                    b[2],
                    b[3],
                    zeta);
            exit(1);
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

int main(void)
{
    static const int16_t boundary_a[][4] = {
        {0, 0, 0, 0},
        {NTRUPLUS_Q, NTRUPLUS_Q, NTRUPLUS_Q, NTRUPLUS_Q},
        {-NTRUPLUS_Q, -NTRUPLUS_Q, -NTRUPLUS_Q, -NTRUPLUS_Q},
        {INT16_MIN, 0, 0, 0},
        {INT16_MAX, 0, 0, 0},
        {0, INT16_MIN, 0, 0},
        {0, INT16_MAX, 0, 0},
        {0, 0, INT16_MIN, 0},
        {0, 0, INT16_MAX, 0},
        {0, 0, 0, INT16_MIN},
        {0, 0, 0, INT16_MAX},
        {INT16_MIN, INT16_MAX, 0, 0},
        {0, INT16_MIN, INT16_MAX, 0},
        {0, 0, INT16_MIN, INT16_MAX},
    };
    static const int16_t boundary_b[][4] = {
        {0, 0, 0, 0},
        {NTRUPLUS_Q, NTRUPLUS_Q, NTRUPLUS_Q, NTRUPLUS_Q},
        {-NTRUPLUS_Q, -NTRUPLUS_Q, -NTRUPLUS_Q, -NTRUPLUS_Q},
        {INT16_MAX, 0, 0, 0},
        {INT16_MIN, 0, 0, 0},
        {0, INT16_MAX, 0, 0},
        {0, INT16_MIN, 0, 0},
        {0, 0, INT16_MAX, 0},
        {0, 0, INT16_MIN, 0},
        {0, 0, 0, INT16_MAX},
        {0, 0, 0, INT16_MIN},
        {INT16_MAX, INT16_MIN, 0, 0},
        {0, INT16_MAX, INT16_MIN, 0},
        {0, 0, INT16_MAX, INT16_MIN},
    };
    static const int16_t boundary_zeta[] = {
        0,
        1,
        -1,
        NTRUPLUS_Q,
        -NTRUPLUS_Q,
        INT16_MAX,
        INT16_MIN,
        123,
        -321,
        2048,
        -2048,
        7,
        -11,
        42,
    };
    uint32_t state = 0x6d5a56e9u;
    size_t random_cases = 20000;

    for (size_t i = 0; i < sizeof(boundary_zeta) / sizeof(boundary_zeta[0]); ++i) {
        check_case("boundary", i, boundary_a[i], boundary_b[i], boundary_zeta[i]);
    }

    for (size_t i = 0; i < random_cases; ++i) {
        int16_t a[4];
        int16_t b[4];
        int16_t zeta;

        for (size_t j = 0; j < 4; ++j) {
            a[j] = sample_mod_q(&state);
            b[j] = sample_mod_q(&state);
        }
        zeta = sample_mod_q(&state);
        check_case("random", i, a, b, zeta);
    }

    printf("basemul differential passed: %zu boundary + %zu random defined-domain cases\n",
           sizeof(boundary_zeta) / sizeof(boundary_zeta[0]),
           random_cases);
    return 0;
}
