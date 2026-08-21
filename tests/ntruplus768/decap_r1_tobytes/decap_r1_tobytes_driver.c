#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../../../NTRU+/NTRU+768/poly.h"

_Static_assert(NTRUPLUS_N == 768, "test requires NTRU+768");
_Static_assert(NTRUPLUS_Q == 3457, "test requires q = 3457");
_Static_assert(NTRUPLUS_POLYBYTES == 1152, "test requires 1152-byte polynomials");

extern void jade_ntruplus_ntruplus768_amd64_ref_ntt(
    int16_t r[NTRUPLUS_N], const int16_t a[NTRUPLUS_N]);
extern void jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes(
    uint8_t out[NTRUPLUS_POLYBYTES], const int16_t in[NTRUPLUS_N]);

static void fail(const char *message)
{
    fprintf(stderr, "%s\n", message);
    exit(1);
}

static void cbd1_oracle(int16_t coeffs[NTRUPLUS_N], const uint8_t tail[NTRUPLUS_N / 4])
{
    for (size_t i = 0; i < NTRUPLUS_N / 8; ++i) {
        uint8_t t1 = tail[i];
        uint8_t t2 = tail[i + NTRUPLUS_N / 8];

        for (size_t j = 0; j < 8; ++j) {
            coeffs[8 * i + j] = (int16_t)((t1 & 0x1u) - (t2 & 0x1u));
            t1 >>= 1;
            t2 >>= 1;
        }
    }
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

static void assert_tail_unchanged(const uint8_t before[NTRUPLUS_N / 4], const uint8_t after[NTRUPLUS_N / 4])
{
    if (memcmp(before, after, NTRUPLUS_N / 4) != 0) {
        fail("poly_cbd1 modified its 192-byte input");
    }
}

static void assert_bytes_equal(const char *lhs_name,
                               const char *rhs_name,
                               const uint8_t lhs[NTRUPLUS_POLYBYTES],
                               const uint8_t rhs[NTRUPLUS_POLYBYTES])
{
    for (size_t i = 0; i < NTRUPLUS_POLYBYTES; ++i) {
        if (lhs[i] != rhs[i]) {
            fprintf(stderr,
                    "byte mismatch %s vs %s at %zu: %02x != %02x\n",
                    lhs_name,
                    rhs_name,
                    i,
                    lhs[i],
                    rhs[i]);
            exit(1);
        }
    }
}

static void assert_coeffs_equal(const char *name,
                                const int16_t expected[NTRUPLUS_N],
                                const int16_t actual[NTRUPLUS_N])
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        if (expected[i] != actual[i]) {
            fprintf(stderr,
                    "%s mismatch at coeff %zu: expected=%d actual=%d\n",
                    name,
                    i,
                    expected[i],
                    actual[i]);
            exit(1);
        }
    }
}

static void assert_unchanged(const char *name,
                             const int16_t before[NTRUPLUS_N],
                             const int16_t after[NTRUPLUS_N])
{
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        if (before[i] != after[i]) {
            fprintf(stderr,
                    "%s modified input at coeff %zu: %d != %d\n",
                    name,
                    i,
                    before[i],
                    after[i]);
            exit(1);
        }
    }
}

static void write_hex(FILE *stream, const uint8_t bytes[NTRUPLUS_POLYBYTES])
{
    static const char hex[] = "0123456789abcdef";

    for (size_t i = 0; i < NTRUPLUS_POLYBYTES; ++i) {
        const uint8_t byte = bytes[i];
        fputc(hex[byte >> 4], stream);
        fputc(hex[byte & 0x0Fu], stream);
    }
}

static void write_coeff_hex(FILE *stream, const int16_t coeffs[NTRUPLUS_N])
{
    static const char hex[] = "0123456789abcdef";

    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        const uint16_t word = (uint16_t)coeffs[i];
        const uint8_t lo = (uint8_t)word;
        const uint8_t hi = (uint8_t)(word >> 8);

        fputc(hex[lo >> 4], stream);
        fputc(hex[lo & 0x0Fu], stream);
        fputc(hex[hi >> 4], stream);
        fputc(hex[hi & 0x0Fu], stream);
    }
}

int main(void)
{
    uint8_t tail[NTRUPLUS_N / 4];
    uint8_t tail_copy[NTRUPLUS_N / 4];
    uint8_t target_bytes[NTRUPLUS_POLYBYTES];
    uint8_t oracle_bytes[NTRUPLUS_POLYBYTES];
    uint8_t jasmin_bytes[NTRUPLUS_POLYBYTES];
    int16_t sampled_oracle[NTRUPLUS_N];
    int16_t sampled_oracle_copy[NTRUPLUS_N];
    int16_t jasmin_ntt[NTRUPLUS_N];
    int16_t jasmin_ntt_copy[NTRUPLUS_N];
    poly target_poly;
    poly target_poly_before_tobytes;
    poly sampled_poly;
    poly oracle_poly;

    if (fread(tail, 1, sizeof tail, stdin) != sizeof tail) {
        return 2;
    }
    if (fgetc(stdin) != EOF) {
        return 3;
    }

    memcpy(tail_copy, tail, sizeof tail);

    poly_cbd1(&target_poly, tail);
    assert_tail_unchanged(tail_copy, tail);
    memcpy(&sampled_poly, &target_poly, sizeof sampled_poly);

    cbd1_oracle(sampled_oracle, tail_copy);
    memcpy(sampled_oracle_copy, sampled_oracle, sizeof sampled_oracle_copy);
    assert_coeffs_equal("poly_cbd1 oracle", sampled_oracle, sampled_poly.coeffs);

    poly_ntt(&target_poly, &target_poly);
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        if (target_poly.coeffs[i] < -NTRUPLUS_Q ||
            target_poly.coeffs[i] >= NTRUPLUS_Q) {
            fail("poly_ntt output escaped the proved centered range");
        }
    }
    memcpy(&target_poly_before_tobytes, &target_poly, sizeof target_poly_before_tobytes);
    poly_tobytes(target_bytes, &target_poly);
    assert_coeffs_equal("C poly_tobytes input", target_poly_before_tobytes.coeffs, target_poly.coeffs);

    jade_ntruplus_ntruplus768_amd64_ref_ntt(jasmin_ntt, sampled_oracle);
    assert_unchanged("Jasmin NTT", sampled_oracle_copy, sampled_oracle);
    assert_coeffs_equal("C poly_ntt/Jasmin NTT", jasmin_ntt, target_poly.coeffs);

    memcpy(jasmin_ntt_copy, jasmin_ntt, sizeof jasmin_ntt_copy);
    poly_tobytes_oracle(oracle_bytes, jasmin_ntt);
    jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes(jasmin_bytes, jasmin_ntt);
    assert_unchanged("Jasmin poly_tobytes()", jasmin_ntt_copy, jasmin_ntt);

    memcpy(oracle_poly.coeffs, jasmin_ntt, sizeof jasmin_ntt);
    {
        uint8_t c_reencoded[NTRUPLUS_POLYBYTES];

        poly_tobytes(c_reencoded, &oracle_poly);
        assert_bytes_equal("oracle", "C reencode", oracle_bytes, c_reencoded);
    }

    assert_bytes_equal("oracle", "C target", oracle_bytes, target_bytes);
    assert_bytes_equal("oracle", "Jasmin", oracle_bytes, jasmin_bytes);

    fputs("{\"target_hex\":\"", stdout);
    write_hex(stdout, target_bytes);
    fputs("\",\"oracle_hex\":\"", stdout);
    write_hex(stdout, oracle_bytes);
    fputs("\",\"jasmin_hex\":\"", stdout);
    write_hex(stdout, jasmin_bytes);
    fputs("\",\"sampled_hex\":\"", stdout);
    write_coeff_hex(stdout, sampled_poly.coeffs);
    fputs("\"}\n", stdout);
    return 0;
}
