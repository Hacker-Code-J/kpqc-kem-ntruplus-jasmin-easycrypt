#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "params.h"
#include "symmetric.h"

int main(void)
{
    uint8_t message[NTRUPLUS_N / 8 + NTRUPLUS_SYMBYTES];
    uint8_t original[NTRUPLUS_N / 8 + NTRUPLUS_SYMBYTES];
    uint8_t output[NTRUPLUS_SSBYTES + NTRUPLUS_N / 4];

    if (fread(message, 1, sizeof message, stdin) != sizeof message)
        return 2;
    if (fgetc(stdin) != EOF)
        return 3;

    memcpy(original, message, sizeof message);
    hash_h(output, message);
    if (memcmp(message, original, sizeof message) != 0)
        return 5;

    if (fwrite(output, 1, sizeof output, stdout) != sizeof output)
        return 4;
    return 0;
}
