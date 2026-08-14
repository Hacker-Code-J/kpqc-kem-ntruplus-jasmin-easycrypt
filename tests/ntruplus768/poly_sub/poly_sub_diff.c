#include <limits.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../../../NTRU+/NTRU+768/poly.h"

#define DECODER_MIN 0
#define DECODER_MAX 4095
#define QRANGE_MIN (-NTRUPLUS_Q)
#define QRANGE_MAX (NTRUPLUS_Q - 1)
#define RAW_MIN (DECODER_MIN - QRANGE_MAX)
#define RAW_MAX (DECODER_MAX - QRANGE_MIN)
#define RANDOM_CASES 4096u

_Static_assert(NTRUPLUS_N == 768, "unexpected NTRUPLUS_N");
_Static_assert(NTRUPLUS_Q == 3457, "unexpected NTRUPLUS_Q");
_Static_assert(RAW_MIN == -3456, "unexpected decoder/q-range minimum");
_Static_assert(RAW_MAX == 7552, "unexpected decoder/q-range maximum");

extern void jade_ntruplus_ntruplus768_amd64_ref_poly_sub(
    int16_t r[NTRUPLUS_N], const int16_t a[NTRUPLUS_N], const int16_t b[NTRUPLUS_N]);

static void poly_sub_ref_disjoint(int16_t r[NTRUPLUS_N],
                                  int16_t a_inout[NTRUPLUS_N],
                                  int16_t b_inout[NTRUPLUS_N])
{
    poly pa;
    poly pb;
    poly pr;

    memcpy(pa.coeffs, a_inout, sizeof(pa.coeffs));
    memcpy(pb.coeffs, b_inout, sizeof(pb.coeffs));
    poly_sub(&pr, &pa, &pb);
    memcpy(r, pr.coeffs, sizeof(pr.coeffs));
    memcpy(a_inout, pa.coeffs, sizeof(pa.coeffs));
    memcpy(b_inout, pb.coeffs, sizeof(pb.coeffs));
}

static void poly_sub_ref_alias_a(int16_t a_inout[NTRUPLUS_N], int16_t b_inout[NTRUPLUS_N])
{
    poly pa;
    poly pb;

    memcpy(pa.coeffs, a_inout, sizeof(pa.coeffs));
    memcpy(pb.coeffs, b_inout, sizeof(pb.coeffs));
    poly_sub(&pa, &pa, &pb);
    memcpy(a_inout, pa.coeffs, sizeof(pa.coeffs));
    memcpy(b_inout, pb.coeffs, sizeof(pb.coeffs));
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

static int16_t sample_decoder_value(uint32_t *state)
{
    return (int16_t)(next_u32(state) % (DECODER_MAX + 1u));
}

static int16_t sample_qrange_value(uint32_t *state)
{
    return (int16_t)((int32_t)(next_u32(state) % (2u * NTRUPLUS_Q)) - NTRUPLUS_Q);
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

static void fill_random_domain(int16_t a[NTRUPLUS_N], int16_t b[NTRUPLUS_N], uint32_t *state)
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        a[i] = sample_decoder_value(state);
        b[i] = sample_qrange_value(state);
    }
}

static int32_t mod_q(int32_t value)
{
    int32_t reduced = value % NTRUPLUS_Q;

    if (reduced < 0) {
        reduced += NTRUPLUS_Q;
    }
    return reduced;
}

static int16_t wrap_sub_oracle(int16_t a, int16_t b)
{
    const uint16_t aw = (uint16_t)a;
    const uint16_t bw = (uint16_t)b;

    return (int16_t)(uint16_t)(aw - bw);
}

static void require_unchanged(const char *who,
                              const char *tag,
                              size_t case_index,
                              const int16_t before[NTRUPLUS_N],
                              const int16_t after[NTRUPLUS_N])
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        if (before[i] != after[i]) {
            fprintf(stderr,
                    "%s mutated input in %s[%zu] at coeff %zu: before=%d after=%d\n",
                    who,
                    tag,
                    case_index,
                    i,
                    before[i],
                    after[i]);
            exit(1);
        }
    }
}

static void compare_defined_vectors(const char *mode,
                                    const char *tag,
                                    size_t case_index,
                                    size_t active_count,
                                    const int16_t a[NTRUPLUS_N],
                                    const int16_t b[NTRUPLUS_N],
                                    const int16_t actual[NTRUPLUS_N])
{
    for (size_t i = 0; i < active_count; ++i) {
        const int32_t raw = (int32_t)a[i] - (int32_t)b[i];
        const int32_t reduced = mod_q(raw);
        const int32_t mod_sub = mod_q((int32_t)a[i] - (int32_t)b[i]);

        if (raw < RAW_MIN || raw > RAW_MAX) {
            fprintf(stderr,
                    "%s left defined decoder/q-range in %s[%zu] at coeff %zu: a=%d b=%d raw=%d\n",
                    mode,
                    tag,
                    case_index,
                    i,
                    a[i],
                    b[i],
                    raw);
            exit(1);
        }
        if (actual[i] != raw) {
            fprintf(stderr,
                    "%s mismatch in %s[%zu] at coeff %zu: got=%d expected=%d (a=%d b=%d)\n",
                    mode,
                    tag,
                    case_index,
                    i,
                    actual[i],
                    (int16_t)raw,
                    a[i],
                    b[i]);
            exit(1);
        }
        if (mod_q(actual[i]) != reduced || reduced != mod_sub) {
            fprintf(stderr,
                    "%s broke mod-q subtraction in %s[%zu] at coeff %zu: a=%d b=%d raw=%d mod(raw)=%d mod(actual)=%d\n",
                    mode,
                    tag,
                    case_index,
                    i,
                    a[i],
                    b[i],
                    raw,
                    reduced,
                    mod_q(actual[i]));
            exit(1);
        }
    }
}

static void compare_equal(const char *lhs_name,
                          const char *rhs_name,
                          const char *mode,
                          const char *tag,
                          size_t case_index,
                          size_t active_count,
                          const int16_t lhs[NTRUPLUS_N],
                          const int16_t rhs[NTRUPLUS_N],
                          const int16_t a[NTRUPLUS_N],
                          const int16_t b[NTRUPLUS_N])
{
    for (size_t i = 0; i < active_count; ++i) {
        if (lhs[i] != rhs[i]) {
            fprintf(stderr,
                    "%s/%s mismatch in %s %s[%zu] at coeff %zu: %d != %d (a=%d b=%d)\n",
                    lhs_name,
                    rhs_name,
                    mode,
                    tag,
                    case_index,
                    i,
                    lhs[i],
                    rhs[i],
                    a[i],
                    b[i]);
            exit(1);
        }
    }
}

static void check_defined_case(const char *tag,
                               size_t case_index,
                               size_t active_count,
                               const int16_t a[NTRUPLUS_N],
                               const int16_t b[NTRUPLUS_N])
{
    int16_t c_a[NTRUPLUS_N];
    int16_t c_b[NTRUPLUS_N];
    int16_t jasmin_a[NTRUPLUS_N];
    int16_t jasmin_b[NTRUPLUS_N];
    int16_t expected_disjoint[NTRUPLUS_N];
    int16_t actual_disjoint[NTRUPLUS_N];
    int16_t expected_alias[NTRUPLUS_N];
    int16_t actual_alias[NTRUPLUS_N];

    memcpy(c_a, a, sizeof(c_a));
    memcpy(c_b, b, sizeof(c_b));
    memcpy(jasmin_a, a, sizeof(jasmin_a));
    memcpy(jasmin_b, b, sizeof(jasmin_b));

    poly_sub_ref_disjoint(expected_disjoint, c_a, c_b);
    jade_ntruplus_ntruplus768_amd64_ref_poly_sub(actual_disjoint, jasmin_a, jasmin_b);

    compare_defined_vectors("C-disjoint", tag, case_index, active_count, a, b, expected_disjoint);
    compare_defined_vectors("Jasmin-disjoint", tag, case_index, active_count, a, b, actual_disjoint);
    compare_equal("C", "Jasmin", "disjoint", tag, case_index, active_count, expected_disjoint, actual_disjoint, a, b);
    require_unchanged("C poly_sub() a", tag, case_index, a, c_a);
    require_unchanged("C poly_sub() b", tag, case_index, b, c_b);
    require_unchanged("Jasmin poly_sub() a", tag, case_index, a, jasmin_a);
    require_unchanged("Jasmin poly_sub() b", tag, case_index, b, jasmin_b);

    memcpy(expected_alias, a, sizeof(expected_alias));
    memcpy(actual_alias, a, sizeof(actual_alias));
    memcpy(c_b, b, sizeof(c_b));
    memcpy(jasmin_b, b, sizeof(jasmin_b));

    poly_sub_ref_alias_a(expected_alias, c_b);
    jade_ntruplus_ntruplus768_amd64_ref_poly_sub(actual_alias, actual_alias, jasmin_b);

    compare_defined_vectors("C-alias", tag, case_index, active_count, a, b, expected_alias);
    compare_defined_vectors("Jasmin-alias", tag, case_index, active_count, a, b, actual_alias);
    compare_equal("C", "Jasmin", "alias", tag, case_index, active_count, expected_alias, actual_alias, a, b);
    require_unchanged("C poly_sub() alias b", tag, case_index, b, c_b);
    require_unchanged("Jasmin poly_sub() alias b", tag, case_index, b, jasmin_b);
}

static void compare_wrap_vectors(const char *mode,
                                 const char *tag,
                                 size_t case_index,
                                 const int16_t expected[NTRUPLUS_N],
                                 const int16_t actual[NTRUPLUS_N],
                                 const int16_t a[NTRUPLUS_N],
                                 const int16_t b[NTRUPLUS_N])
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        if (actual[i] != expected[i]) {
            fprintf(stderr,
                    "%s wrap mismatch in %s[%zu] at coeff %zu: got=%d expected=%d (a=%d b=%d)\n",
                    mode,
                    tag,
                    case_index,
                    i,
                    actual[i],
                    expected[i],
                    a[i],
                    b[i]);
            exit(1);
        }
    }
}

static void check_wrap_case(const char *tag,
                            size_t case_index,
                            const int16_t a[NTRUPLUS_N],
                            const int16_t b[NTRUPLUS_N])
{
    int16_t c_a[NTRUPLUS_N];
    int16_t c_b[NTRUPLUS_N];
    int16_t jasmin_a[NTRUPLUS_N];
    int16_t jasmin_b[NTRUPLUS_N];
    int16_t expected[NTRUPLUS_N];
    int16_t c_disjoint[NTRUPLUS_N];
    int16_t c_alias[NTRUPLUS_N];
    int16_t actual_disjoint[NTRUPLUS_N];
    int16_t actual_alias[NTRUPLUS_N];

    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        expected[i] = wrap_sub_oracle(a[i], b[i]);
    }

    memcpy(c_a, a, sizeof(c_a));
    memcpy(c_b, b, sizeof(c_b));
    poly_sub_ref_disjoint(c_disjoint, c_a, c_b);
    compare_wrap_vectors("C-disjoint/GCC", tag, case_index, expected, c_disjoint, a, b);
    require_unchanged("C poly_sub() wrap a", tag, case_index, a, c_a);
    require_unchanged("C poly_sub() wrap b", tag, case_index, b, c_b);

    memcpy(c_alias, a, sizeof(c_alias));
    memcpy(c_b, b, sizeof(c_b));
    poly_sub_ref_alias_a(c_alias, c_b);
    compare_wrap_vectors("C-alias/GCC", tag, case_index, expected, c_alias, a, b);
    require_unchanged("C poly_sub() wrap alias b", tag, case_index, b, c_b);

    memcpy(jasmin_a, a, sizeof(jasmin_a));
    memcpy(jasmin_b, b, sizeof(jasmin_b));
    jade_ntruplus_ntruplus768_amd64_ref_poly_sub(actual_disjoint, jasmin_a, jasmin_b);
    compare_wrap_vectors("Jasmin-disjoint", tag, case_index, expected, actual_disjoint, a, b);
    require_unchanged("Jasmin poly_sub() wrap a", tag, case_index, a, jasmin_a);
    require_unchanged("Jasmin poly_sub() wrap b", tag, case_index, b, jasmin_b);

    memcpy(actual_alias, a, sizeof(actual_alias));
    memcpy(jasmin_b, b, sizeof(jasmin_b));
    jade_ntruplus_ntruplus768_amd64_ref_poly_sub(actual_alias, actual_alias, jasmin_b);
    compare_wrap_vectors("Jasmin-alias", tag, case_index, expected, actual_alias, a, b);
    require_unchanged("Jasmin poly_sub() wrap alias b", tag, case_index, b, jasmin_b);
}

static void run_boundary_cases(void)
{
    int16_t a[NTRUPLUS_N];
    int16_t b[NTRUPLUS_N];
    const size_t edge_indices[] = {0u, 1u, 2u, 383u, 384u, 385u, 766u, 767u};

    fill_constant(a, 0);
    fill_constant(b, 0);
    check_defined_case("boundary", 0, NTRUPLUS_N, a, b);

    fill_constant(a, DECODER_MAX);
    fill_constant(b, QRANGE_MIN);
    check_defined_case("boundary", 1, NTRUPLUS_N, a, b);

    fill_constant(a, DECODER_MIN);
    fill_constant(b, QRANGE_MAX);
    check_defined_case("boundary", 2, NTRUPLUS_N, a, b);

    fill_alternating(a, DECODER_MIN, DECODER_MAX);
    fill_alternating(b, QRANGE_MIN, QRANGE_MAX);
    check_defined_case("boundary", 3, NTRUPLUS_N, a, b);

    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        a[i] = (int16_t)(i & 0x0fffu);
        b[i] = (int16_t)((int32_t)(i % (2u * NTRUPLUS_Q)) - NTRUPLUS_Q);
    }
    check_defined_case("boundary", 4, NTRUPLUS_N, a, b);

    fill_constant(a, 0);
    fill_constant(b, 0);
    for (size_t i = 0; i < sizeof(edge_indices) / sizeof(edge_indices[0]); ++i) {
        const size_t idx = edge_indices[i];

        a[idx] = (i & 1u) == 0 ? DECODER_MAX : DECODER_MIN;
        b[idx] = (i & 1u) == 0 ? QRANGE_MAX : QRANGE_MIN;
    }
    check_defined_case("boundary", 5, NTRUPLUS_N, a, b);
}

static void run_random_cases(void)
{
    uint32_t state = 0x4c1d2a77u;

    for (size_t case_index = 0; case_index < RANDOM_CASES; ++case_index) {
        int16_t a[NTRUPLUS_N];
        int16_t b[NTRUPLUS_N];

        fill_random_domain(a, b, &state);
        check_defined_case("random", case_index, NTRUPLUS_N, a, b);
    }
}

static void run_domain_sweep(uint64_t *pair_count)
{
    const uint64_t a_count = (uint64_t)DECODER_MAX + 1u;
    const uint64_t b_count = (uint64_t)(2 * NTRUPLUS_Q);
    const uint64_t total_pairs = a_count * b_count;
    const uint64_t blocks = (total_pairs + NTRUPLUS_N - 1u) / NTRUPLUS_N;

    *pair_count = 0;
    for (uint64_t block = 0; block < blocks; ++block) {
        int16_t a[NTRUPLUS_N];
        int16_t b[NTRUPLUS_N];
        size_t active = 0;

        fill_constant(a, 0);
        fill_constant(b, 0);
        for (size_t i = 0; i < NTRUPLUS_N; ++i) {
            const uint64_t pair_index = block * NTRUPLUS_N + i;

            if (pair_index >= total_pairs) {
                break;
            }
            a[i] = (int16_t)(pair_index / b_count);
            b[i] = (int16_t)((int64_t)(pair_index % b_count) - NTRUPLUS_Q);
            active += 1;
        }

        check_defined_case("sweep", (size_t)block, active, a, b);
        *pair_count += active;
    }
}

static void run_full_word_cases(void)
{
    int16_t a[NTRUPLUS_N];
    int16_t b[NTRUPLUS_N];

    fill_constant(a, INT16_MIN);
    fill_constant(b, 1);
    check_wrap_case("full-word", 0, a, b);

    fill_constant(a, INT16_MAX);
    fill_constant(b, -1);
    check_wrap_case("full-word", 1, a, b);

    fill_alternating(a, INT16_MIN, INT16_MAX);
    fill_alternating(b, INT16_MAX, INT16_MIN);
    check_wrap_case("full-word", 2, a, b);

    fill_alternating(a, -12345, 12345);
    fill_alternating(b, 23456, -23456);
    check_wrap_case("full-word", 3, a, b);

    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        a[i] = (int16_t)(INT16_MIN + (int16_t)i);
        b[i] = (int16_t)(INT16_MAX - (int16_t)i);
    }
    check_wrap_case("full-word", 4, a, b);

    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        a[i] = (int16_t)((uint16_t)(0x8000u + i));
        b[i] = (int16_t)((uint16_t)(0x7fffu - i));
    }
    check_wrap_case("full-word", 5, a, b);
}

int main(void)
{
    uint64_t pair_count = 0;

    run_boundary_cases();
    run_random_cases();
    run_domain_sweep(&pair_count);
    run_full_word_cases();

    printf(
        "poly_sub differential passed: 6 boundary + %u random + %" PRIu64
        " exhaustive decoder/q-range pairs across disjoint and rp==ap alias; 6 wraparound word cases bound to tested GCC behavior\n",
        RANDOM_CASES,
        pair_count);
    return 0;
}
