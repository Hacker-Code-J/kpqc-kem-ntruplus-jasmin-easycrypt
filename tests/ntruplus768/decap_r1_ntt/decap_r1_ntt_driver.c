#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../../../NTRU+/NTRU+768/poly.h"

_Static_assert(NTRUPLUS_N == 768, "test requires NTRU+768");
_Static_assert(NTRUPLUS_POLYBYTES == 1152, "test requires 1152-byte polynomials");

extern void jade_ntruplus_ntruplus768_amd64_ref_ntt(
    int16_t r[NTRUPLUS_N], const int16_t a[NTRUPLUS_N]);

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
            const int head = (int)(t1 & 0x1u);
            const int tail_bit = (int)(t2 & 0x1u);

            coeffs[8 * i + j] = (int16_t)(head - tail_bit);
            t1 >>= 1;
            t2 >>= 1;
        }
    }
}

static void assert_tail_unchanged(const uint8_t before[NTRUPLUS_N / 4], const uint8_t after[NTRUPLUS_N / 4])
{
    if (memcmp(before, after, NTRUPLUS_N / 4) != 0) {
        fail("poly_cbd1 modified its 192-byte input");
    }
}

static void assert_coeffs_equal(
    const char *name,
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
    int16_t oracle_input[NTRUPLUS_N];
    int16_t oracle_input_copy[NTRUPLUS_N];
    int16_t oracle_ntt[NTRUPLUS_N];
    int16_t oracle_ntt_inplace[NTRUPLUS_N];
    poly target_poly;
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

    cbd1_oracle(oracle_input, tail_copy);
    memcpy(oracle_input_copy, oracle_input, sizeof oracle_input_copy);
    assert_coeffs_equal("poly_cbd1 oracle", oracle_input, sampled_poly.coeffs);

    poly_ntt(&target_poly, &target_poly);
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        if (target_poly.coeffs[i] < -NTRUPLUS_Q ||
            target_poly.coeffs[i] >= NTRUPLUS_Q) {
            fail("poly_ntt output escaped the proved centered range");
        }
    }
    poly_tobytes(target_bytes, &target_poly);

    jade_ntruplus_ntruplus768_amd64_ref_ntt(oracle_ntt, oracle_input);
    assert_coeffs_equal("Jasmin NTT input immutability", oracle_input_copy, oracle_input);
    memcpy(oracle_ntt_inplace, oracle_input_copy, sizeof oracle_ntt_inplace);
    jade_ntruplus_ntruplus768_amd64_ref_ntt(oracle_ntt_inplace, oracle_ntt_inplace);
    assert_coeffs_equal("Jasmin NTT in-place", oracle_ntt, oracle_ntt_inplace);
    assert_coeffs_equal("C poly_ntt/Jasmin NTT", oracle_ntt, target_poly.coeffs);
    memcpy(oracle_poly.coeffs, oracle_ntt, sizeof oracle_ntt);
    poly_tobytes(oracle_bytes, &oracle_poly);

    fputs("{\"target_hex\":\"", stdout);
    write_hex(stdout, target_bytes);
    fputs("\",\"oracle_hex\":\"", stdout);
    write_hex(stdout, oracle_bytes);
    fputs("\",\"sampled_hex\":\"", stdout);
    write_coeff_hex(stdout, sampled_poly.coeffs);
    fputs("\"}\n", stdout);
    return 0;
}
