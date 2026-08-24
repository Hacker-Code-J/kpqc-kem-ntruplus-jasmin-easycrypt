#include <limits.h>
#include <stdint.h>
#include <stdio.h>

#include "params.h"
#include "poly.h"

_Static_assert(CHAR_BIT == 8, "test requires 8-bit bytes");
_Static_assert(sizeof(int16_t) * CHAR_BIT == 16,
               "test requires 16-bit polynomial coefficients");
_Static_assert(INT16_MIN == (-INT16_MAX - 1),
               "test requires two's-complement int16_t");
_Static_assert(NTRUPLUS_N == 768, "test requires NTRU+768");
_Static_assert(NTRUPLUS_N / 8 == 96, "test requires 96-byte messages");
_Static_assert(NTRUPLUS_N / 4 == 192, "test requires 192-byte pads");

#ifdef NTRUPLUS_SOTP_JASMIN
extern uint32_t jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_decode(
    uint8_t msg[NTRUPLUS_N / 8],
    const int16_t coeffs[NTRUPLUS_N],
    const uint8_t buf[NTRUPLUS_N / 4]);
#endif

enum {
    DRIVER_PAD_BYTES = NTRUPLUS_N / 4,
    DRIVER_MSG_BYTES = NTRUPLUS_N / 8,
};

static uint32_t decode(uint8_t msg[DRIVER_MSG_BYTES], const poly *a,
                       const uint8_t buf[DRIVER_PAD_BYTES])
{
#ifdef NTRUPLUS_SOTP_JASMIN
    return jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_decode(
        msg, a->coeffs, buf);
#else
    return (uint32_t)poly_sotp_decode(msg, a, buf);
#endif
}

int main(void)
{
    uint8_t msg[DRIVER_MSG_BYTES];
    uint8_t msg_before[DRIVER_MSG_BYTES];
    uint8_t pad[DRIVER_PAD_BYTES];
    uint8_t pad_before[DRIVER_PAD_BYTES];
    uint8_t decoded[DRIVER_MSG_BYTES];
    poly encoded;
    poly encoded_before;
    uint32_t fail;

    if (fread(msg, 1, sizeof msg, stdin) != sizeof msg)
        return 2;
    if (fread(pad, 1, sizeof pad, stdin) != sizeof pad)
        return 3;
    if (fgetc(stdin) != EOF)
        return 4;

    for (size_t i = 0; i < sizeof msg; ++i)
        msg_before[i] = msg[i];
    for (size_t i = 0; i < sizeof pad; ++i)
        pad_before[i] = pad[i];
    for (size_t i = 0; i < sizeof decoded; ++i)
        decoded[i] = 0xA5u;

    poly_sotp_encode(&encoded, msg, pad);

    for (size_t i = 0; i < DRIVER_MSG_BYTES; ++i) {
        const uint8_t head = (uint8_t)(pad[i] ^ msg[i]);
        const uint8_t tail = pad[DRIVER_MSG_BYTES + i];

        for (size_t j = 0; j < 8; ++j) {
            const int16_t expected =
                (int16_t)((head >> j) & 1u) -
                (int16_t)((tail >> j) & 1u);

            if (encoded.coeffs[8 * i + j] != expected)
                return 5;
        }
    }

    encoded_before = encoded;
    fail = decode(decoded, &encoded, pad);

    for (size_t i = 0; i < sizeof msg; ++i) {
        if (msg[i] != msg_before[i])
            return 6;
    }
    for (size_t i = 0; i < sizeof pad; ++i) {
        if (pad[i] != pad_before[i])
            return 7;
    }
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        if (encoded.coeffs[i] != encoded_before.coeffs[i])
            return 8;
    }
    if (fail > 1)
        return 9;
    if (fputc((int)fail, stdout) == EOF)
        return 10;
    if (fwrite(decoded, 1, sizeof decoded, stdout) != sizeof decoded)
        return 11;
    return 0;
}
