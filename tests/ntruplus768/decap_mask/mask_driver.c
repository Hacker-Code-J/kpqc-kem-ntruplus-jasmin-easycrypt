#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <limits.h>

#include "params.h"

_Static_assert(NTRUPLUS_SSBYTES == 32, "test requires 32-byte shared secret");
_Static_assert(CHAR_BIT == 8, "test requires 8-bit bytes");
_Static_assert(sizeof(int) * CHAR_BIT == 32, "test requires 32-bit int");
_Static_assert(INT_MIN == (-INT_MAX - 1), "test requires two's-complement int");

static void write_hex(FILE *stream, const uint8_t bytes[NTRUPLUS_SSBYTES])
{
    static const char hex[] = "0123456789abcdef";

    for (size_t i = 0; i < NTRUPLUS_SSBYTES; ++i) {
        const uint8_t byte = bytes[i];
        fputc(hex[byte >> 4], stream);
        fputc(hex[byte & 0x0Fu], stream);
    }
}

static int mask_and_return(uint8_t ss[NTRUPLUS_SSBYTES],
                           const uint8_t buf3[NTRUPLUS_SSBYTES],
                           int8_t fail)
{
    for (size_t i = 0; i < NTRUPLUS_SSBYTES; i++)
        ss[i] = buf3[i] & ~(-fail);

    return fail;
}

int main(void)
{
    int fail_byte;
    uint8_t buf3[NTRUPLUS_SSBYTES];
    uint8_t buf3_copy[NTRUPLUS_SSBYTES];
    uint8_t ss[NTRUPLUS_SSBYTES];
    int8_t fail;
    int return_fail;

    fail_byte = fgetc(stdin);
    if (fail_byte == EOF)
        return 2;
    if (fail_byte != 0 && fail_byte != 1)
        return 3;
    if (fread(buf3, 1, sizeof buf3, stdin) != sizeof buf3)
        return 4;
    if (fgetc(stdin) != EOF)
        return 5;

    for (size_t i = 0; i < NTRUPLUS_SSBYTES; ++i) {
        buf3_copy[i] = buf3[i];
        ss[i] = 0xCC;
    }

    fail = (int8_t)fail_byte;
    return_fail = mask_and_return(ss, buf3, fail);

    if (memcmp(buf3, buf3_copy, sizeof buf3) != 0)
        return 6;
    if (fail != 0 && fail != 1)
        return 7;
    if (return_fail != 0 && return_fail != 1)
        return 8;

    fputs("{\"return_fail\":", stdout);
    printf("%d", return_fail);
    fputs(",\"ss_hex\":\"", stdout);
    write_hex(stdout, ss);
    fputs("\"}\n", stdout);
    return 0;
}
