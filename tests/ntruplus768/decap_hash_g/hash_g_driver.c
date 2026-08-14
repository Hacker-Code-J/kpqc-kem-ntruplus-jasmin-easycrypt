#include <stdint.h>
#include <stdio.h>

#include "params.h"
#include "symmetric.h"

int main(void)
{
    uint8_t message[NTRUPLUS_POLYBYTES];
    uint8_t output[NTRUPLUS_N / 4];

    if (fread(message, 1, sizeof message, stdin) != sizeof message)
        return 2;
    if (fgetc(stdin) != EOF)
        return 3;

    hash_g(output, message);

    if (fwrite(output, 1, sizeof output, stdout) != sizeof output)
        return 4;
    return 0;
}
