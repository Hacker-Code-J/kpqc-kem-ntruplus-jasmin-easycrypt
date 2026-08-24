#include <stdint.h>
#include <stdio.h>
#include <limits.h>

#include "params.h"
#include "symmetric.h"

_Static_assert(CHAR_BIT == 8, "test requires 8-bit bytes");
_Static_assert(sizeof(int) * CHAR_BIT == 32, "test requires 32-bit int");
_Static_assert(INT_MIN == (-INT_MAX - 1), "test requires two's-complement int");
_Static_assert(NTRUPLUS_POLYBYTES == 1152, "test requires 1152-byte public key");
_Static_assert(NTRUPLUS_SYMBYTES == 32, "test requires 32-byte hash output");

int main(void)
{
    uint8_t message[NTRUPLUS_POLYBYTES];
    uint8_t original[NTRUPLUS_POLYBYTES];
    uint8_t output[NTRUPLUS_SYMBYTES];

    if (fread(message, 1, sizeof message, stdin) != sizeof message)
        return 2;
    if (fgetc(stdin) != EOF)
        return 3;

    for (size_t i = 0; i < sizeof message; ++i)
        original[i] = message[i];

    hash_f(output, message);

    for (size_t i = 0; i < sizeof message; ++i) {
        if (message[i] != original[i])
            return 4;
    }

    if (fwrite(output, 1, sizeof output, stdout) != sizeof output)
        return 5;
    return 0;
}
