#ifndef NTRUPLUS768_DECAP_MESSAGE_H
#define NTRUPLUS768_DECAP_MESSAGE_H

#include <stdint.h>

/* Mixed C/Jasmin continuation, not a complete Decaps entry point.
 * All four regions must be disjoint and accessible for their full lengths;
 * m1/r2 are initialized, u16-aligned arrays. Signed r2 coefficients are in
 * [-3457,3457), encoded as uint16_t words. m1 is normally the candidate trits.
 * msg is overwritten, and serialized is retained for the later comparison.
 * The result is 0 or 1; a result of 1 sets all 96 message bytes to zero.
 * SHAKE256 and volatile C clearing are external to the Jasmin/EC proofs.
 */
uint32_t ntruplus768_decap_message(uint8_t msg[96],
                                 uint8_t serialized[1152],
                                 const uint16_t m1[768],
                                 const uint16_t r2[768]);

#endif
