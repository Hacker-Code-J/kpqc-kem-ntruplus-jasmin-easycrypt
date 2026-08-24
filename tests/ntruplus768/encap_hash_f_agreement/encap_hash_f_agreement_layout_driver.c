#include <limits.h>
#include <stdint.h>
#include <stdio.h>

#include "params.h"
#include "symmetric.h"

_Static_assert(CHAR_BIT == 8, "test requires 8-bit bytes");
_Static_assert(sizeof(int) * CHAR_BIT == 32, "test requires 32-bit int");
_Static_assert(INT_MIN == (-INT_MAX - 1), "test requires two's-complement int");
_Static_assert(NTRUPLUS_N == 768, "test requires NTRU+768");
_Static_assert(NTRUPLUS_POLYBYTES == 1152, "test requires 1152-byte polynomial bytes");
_Static_assert(NTRUPLUS_SYMBYTES == 32, "test requires 32-byte suffix");
_Static_assert(NTRUPLUS_SECRETKEYBYTES == 2336, "test requires 2336-byte secret key");

static void write_hex(FILE *stream, const uint8_t *bytes, size_t len)
{
    static const char hex[] = "0123456789abcdef";

    for (size_t i = 0; i < len; ++i) {
        const uint8_t byte = bytes[i];
        fputc(hex[byte >> 4], stream);
        fputc(hex[byte & 0x0F], stream);
    }
}

int main(void)
{
    uint8_t pk[NTRUPLUS_POLYBYTES];
    uint8_t pk_copy[NTRUPLUS_POLYBYTES];
    uint8_t sk[NTRUPLUS_SECRETKEYBYTES];
    uint8_t encap_msg[NTRUPLUS_N / 8 + NTRUPLUS_SYMBYTES];
    uint8_t decap_msg[NTRUPLUS_N / 8 + NTRUPLUS_SYMBYTES];
    uint8_t encap_prefix_copy[NTRUPLUS_N / 8];
    uint8_t decap_prefix_copy[NTRUPLUS_N / 8];

    if (fread(pk, 1, sizeof pk, stdin) != sizeof pk)
        return 2;
    if (fread(encap_msg, 1, NTRUPLUS_N / 8, stdin) != NTRUPLUS_N / 8)
        return 3;
    if (fread(decap_msg, 1, NTRUPLUS_N / 8, stdin) != NTRUPLUS_N / 8)
        return 4;
    if (fgetc(stdin) != EOF)
        return 5;

    for (size_t i = 0; i < sizeof pk; ++i)
        pk_copy[i] = pk[i];
    for (size_t i = 0; i < NTRUPLUS_SECRETKEYBYTES; ++i)
        sk[i] = 0xA5u;
    for (size_t i = 0; i < NTRUPLUS_N / 8; ++i) {
        encap_prefix_copy[i] = encap_msg[i];
        decap_prefix_copy[i] = decap_msg[i];
    }
    for (size_t i = NTRUPLUS_N / 8; i < sizeof encap_msg; ++i)
        encap_msg[i] = 0xCCu;
    for (size_t i = NTRUPLUS_N / 8; i < sizeof decap_msg; ++i)
        decap_msg[i] = 0xDDu;

    hash_f(sk + 2 * NTRUPLUS_POLYBYTES, pk);
    hash_f(encap_msg + NTRUPLUS_N / 8, pk);
    for (size_t i = 0; i < NTRUPLUS_SYMBYTES; i++)
        decap_msg[i + NTRUPLUS_N / 8] = sk[i + 2 * NTRUPLUS_POLYBYTES];

    for (size_t i = 0; i < sizeof pk; ++i) {
        if (pk[i] != pk_copy[i])
            return 6;
    }
    for (size_t i = 0; i < 2 * NTRUPLUS_POLYBYTES; ++i) {
        if (sk[i] != 0xA5u)
            return 7;
    }
    for (size_t i = 0; i < NTRUPLUS_N / 8; ++i) {
        if (encap_msg[i] != encap_prefix_copy[i])
            return 8;
        if (decap_msg[i] != decap_prefix_copy[i])
            return 9;
    }

    fputs("{\"suffix_hex\":\"", stdout);
    write_hex(stdout, sk + 2 * NTRUPLUS_POLYBYTES, NTRUPLUS_SYMBYTES);
    fputs("\",\"encap_tail_hex\":\"", stdout);
    write_hex(stdout, encap_msg + NTRUPLUS_N / 8, NTRUPLUS_SYMBYTES);
    fputs("\",\"decap_tail_hex\":\"", stdout);
    write_hex(stdout, decap_msg + NTRUPLUS_N / 8, NTRUPLUS_SYMBYTES);
    fputs("\"}\n", stdout);
    return 0;
}
