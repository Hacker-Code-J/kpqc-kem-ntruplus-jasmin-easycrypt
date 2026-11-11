#include "decap_message.h"

/* Build against the pinned official 3991b2a reference headers and SHAKE256.
 * These C dependencies are an explicit external implementation boundary.
 */
#include "fips202/fips202.h"
#include "util.h"

extern void jade_ntruplus_ntruplus768_amd64_ref_decap_message_prepare(
    uint8_t serialized[1152], uint8_t input[1153], const uint16_t r2[768]);

extern uint32_t jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_decode(
    uint8_t msg[96], const uint16_t m1[768], const uint8_t pad[192]);

uint32_t ntruplus768_decap_message(uint8_t msg[96],
                                 uint8_t serialized[1152],
                                 const uint16_t m1[768],
                                 const uint16_t r2[768])
{
    uint8_t input[1153];
    uint8_t pad[192];
    uint32_t fail;

    jade_ntruplus_ntruplus768_amd64_ref_decap_message_prepare(
        serialized, input, r2);
    shake256(pad, sizeof pad, input, sizeof input);
    fail = jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_decode(msg, m1, pad);
    secure_clear(input, sizeof input);
    secure_clear(pad, sizeof pad);
    return fail;
}
