#include <stdint.h>
#include <stdio.h>
#include <string.h>

#define crypto_kem_keypair test_only_crypto_kem_keypair
#define crypto_kem_enc test_only_crypto_kem_enc
#define crypto_kem_dec test_only_crypto_kem_dec
#include "../../../NTRU+/NTRU+768/kem.c"
#undef crypto_kem_keypair
#undef crypto_kem_enc
#undef crypto_kem_dec

_Static_assert(NTRUPLUS_POLYBYTES == 1152, "test requires 1152-byte polynomials");

int main(void)
{
    uint8_t left[NTRUPLUS_POLYBYTES];
    uint8_t right[NTRUPLUS_POLYBYTES];
    uint8_t left_copy[NTRUPLUS_POLYBYTES];
    uint8_t right_copy[NTRUPLUS_POLYBYTES];
    int result;

    if (fread(left, 1, sizeof left, stdin) != sizeof left)
        return 2;
    if (fread(right, 1, sizeof right, stdin) != sizeof right)
        return 3;
    if (fgetc(stdin) != EOF)
        return 4;

    for (size_t index = 0; index < NTRUPLUS_POLYBYTES; ++index) {
        left_copy[index] = left[index];
        right_copy[index] = right[index];
    }

    result = verify(left, right, NTRUPLUS_POLYBYTES);
    if (memcmp(left, left_copy, sizeof left) != 0)
        return 5;
    if (memcmp(right, right_copy, sizeof right) != 0)
        return 6;
    if (result != 0 && result != 1)
        return 7;

    printf("{\"result\":%d}\n", result);
    return 0;
}
