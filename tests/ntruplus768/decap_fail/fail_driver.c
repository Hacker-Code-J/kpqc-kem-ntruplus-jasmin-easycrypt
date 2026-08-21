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
    int decode_flag_byte;
    uint8_t left[NTRUPLUS_POLYBYTES];
    uint8_t right[NTRUPLUS_POLYBYTES];
    uint8_t left_copy[NTRUPLUS_POLYBYTES];
    uint8_t right_copy[NTRUPLUS_POLYBYTES];
    int verify_result;
    int8_t fail;
    size_t i;

    decode_flag_byte = fgetc(stdin);
    if (decode_flag_byte == EOF)
        return 2;
    if (decode_flag_byte != 0 && decode_flag_byte != 1)
        return 3;
    if (fread(left, 1, sizeof left, stdin) != sizeof left)
        return 4;
    if (fread(right, 1, sizeof right, stdin) != sizeof right)
        return 5;
    if (fgetc(stdin) != EOF)
        return 6;

    for (i = 0; i < sizeof left; ++i) {
        left_copy[i] = left[i];
        right_copy[i] = right[i];
    }

    fail = (int8_t)decode_flag_byte;
    verify_result = verify(left, right, NTRUPLUS_POLYBYTES);
    fail |= verify_result;

    if (memcmp(left, left_copy, sizeof left) != 0)
        return 7;
    if (memcmp(right, right_copy, sizeof right) != 0)
        return 8;
    if (verify_result != 0 && verify_result != 1)
        return 9;
    if (fail != 0 && fail != 1)
        return 10;

    printf("{\"verify_result\":%d,\"fail_result\":%d}\n",
           verify_result,
           fail);
    return 0;
}
