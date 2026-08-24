#include <stdint.h>
#include <stdio.h>
#include <limits.h>

#define crypto_kem_keypair test_only_crypto_kem_keypair
#define crypto_kem_enc test_only_crypto_kem_enc
#define crypto_kem_dec test_only_crypto_kem_dec
#include "../../../NTRU+/NTRU+768/kem.c"
#undef crypto_kem_keypair
#undef crypto_kem_enc
#undef crypto_kem_dec

_Static_assert(CHAR_BIT == 8, "test requires 8-bit bytes");
_Static_assert(sizeof(int) * CHAR_BIT == 32, "test requires 32-bit int");
_Static_assert(INT_MIN == (-INT_MAX - 1), "test requires two's-complement int");
_Static_assert(NTRUPLUS_POLYBYTES == 1152, "test requires 1152-byte polynomials");
_Static_assert(NTRUPLUS_SSBYTES == 32, "test requires 32-byte shared secret");

static void write_hex(FILE *stream, const uint8_t bytes[NTRUPLUS_SSBYTES])
{
    static const char hex[] = "0123456789abcdef";

    for (size_t i = 0; i < NTRUPLUS_SSBYTES; ++i) {
        const uint8_t byte = bytes[i];
        fputc(hex[byte >> 4], stream);
        fputc(hex[byte & 0x0Fu], stream);
    }
}

static int terminal_step(uint8_t ss[NTRUPLUS_SSBYTES],
                         const uint8_t candidate[NTRUPLUS_SSBYTES],
                         const uint8_t left[NTRUPLUS_POLYBYTES],
                         const uint8_t right[NTRUPLUS_POLYBYTES],
                         int *verify_result_out,
                         int8_t decode_fail)
{
    int8_t fail = decode_fail;
    int verify_result;

    verify_result = verify(left, right, NTRUPLUS_POLYBYTES);
    *verify_result_out = verify_result;
    fail |= verify_result;

    for (size_t i = 0; i < NTRUPLUS_SSBYTES; i++)
        ss[i] = candidate[i] & ~(-fail);

    return fail;
}

int main(void)
{
    int decode_flag_byte;
    uint8_t candidate[NTRUPLUS_SSBYTES];
    uint8_t candidate_copy[NTRUPLUS_SSBYTES];
    uint8_t left[NTRUPLUS_POLYBYTES];
    uint8_t left_copy[NTRUPLUS_POLYBYTES];
    uint8_t right[NTRUPLUS_POLYBYTES];
    uint8_t right_copy[NTRUPLUS_POLYBYTES];
    uint8_t ss[NTRUPLUS_SSBYTES];
    int verify_result;
    int return_fail;

    decode_flag_byte = fgetc(stdin);
    if (decode_flag_byte == EOF)
        return 2;
    if (decode_flag_byte != 0 && decode_flag_byte != 1)
        return 3;
    if (fread(candidate, 1, sizeof candidate, stdin) != sizeof candidate)
        return 4;
    if (fread(left, 1, sizeof left, stdin) != sizeof left)
        return 5;
    if (fread(right, 1, sizeof right, stdin) != sizeof right)
        return 6;
    if (fgetc(stdin) != EOF)
        return 7;

    for (size_t i = 0; i < sizeof candidate; ++i)
        candidate_copy[i] = candidate[i];
    for (size_t i = 0; i < sizeof left; ++i)
        left_copy[i] = left[i];
    for (size_t i = 0; i < sizeof right; ++i)
        right_copy[i] = right[i];
    for (size_t i = 0; i < sizeof ss; ++i)
        ss[i] = 0xCCu;

    return_fail = terminal_step(ss, candidate, left, right, &verify_result, (int8_t)decode_flag_byte);

    for (size_t i = 0; i < sizeof candidate; ++i) {
        if (candidate[i] != candidate_copy[i])
            return 8;
    }
    for (size_t i = 0; i < sizeof left; ++i) {
        if (left[i] != left_copy[i])
            return 9;
    }
    for (size_t i = 0; i < sizeof right; ++i) {
        if (right[i] != right_copy[i])
            return 10;
    }
    if (verify_result != 0 && verify_result != 1)
        return 11;
    if (return_fail != 0 && return_fail != 1)
        return 12;

    fputs("{\"verify_result\":", stdout);
    printf("%d", verify_result);
    fputs(",\"return_fail\":", stdout);
    printf("%d", return_fail);
    fputs(",\"ss_hex\":\"", stdout);
    write_hex(stdout, ss);
    fputs("\"}\n", stdout);
    return 0;
}
