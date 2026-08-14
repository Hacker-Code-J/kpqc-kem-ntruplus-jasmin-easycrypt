#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "params.h"
#include "poly.h"

#ifdef NTRUPLUS_SOTP_JASMIN
extern uint32_t jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_decode(
    uint8_t msg[NTRUPLUS_N / 8],
    const int16_t coeffs[NTRUPLUS_N],
    const uint8_t buf[NTRUPLUS_N / 4]);
#endif

enum {
    DRIVER_BUF_BYTES = NTRUPLUS_N / 4,
    DRIVER_MSG_BYTES = NTRUPLUS_N / 8,
    DRIVER_COEFF_BYTES = NTRUPLUS_N * 2,
};

static int16_t load_i16_le(const uint8_t src[2])
{
    return (int16_t)((uint16_t)src[0] | ((uint16_t)src[1] << 8));
}

static uint32_t decode(uint8_t msg[DRIVER_MSG_BYTES], const poly *a,
                       const uint8_t buf[DRIVER_BUF_BYTES])
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
    uint8_t raw[DRIVER_BUF_BYTES + DRIVER_COEFF_BYTES];
    uint8_t msg[DRIVER_MSG_BYTES];
    uint8_t buf[DRIVER_BUF_BYTES];
    uint8_t buf_before[DRIVER_BUF_BYTES];
    poly a;
    poly before;
    uint32_t result;

    if (fread(raw, 1, sizeof raw, stdin) != sizeof raw)
        return 2;
    if (fgetc(stdin) != EOF)
        return 3;

    memcpy(buf, raw, sizeof buf);
    memcpy(buf_before, buf, sizeof buf);

    for (size_t i = 0; i < NTRUPLUS_N; i++)
        a.coeffs[i] = load_i16_le(&raw[DRIVER_BUF_BYTES + 2 * i]);

    before = a;
    memset(msg, 0xA5, sizeof msg);

    result = decode(msg, &a, buf);

    if (memcmp(buf, buf_before, sizeof buf) != 0)
        return 4;
    if (memcmp(&a, &before, sizeof a) != 0)
        return 5;

    if (result > 1)
        return 6;
    if (fputc((int)result, stdout) == EOF)
        return 7;
    if (fwrite(msg, 1, sizeof msg, stdout) != sizeof msg)
        return 8;
    return 0;
}
