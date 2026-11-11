#ifndef NTRUPLUS768_ENCAP_COMPLETE_H
#define NTRUPLUS768_ENCAP_COMPLETE_H

#include <stdint.h>

/* Mixed C/Jasmin Encaps. All external regions are disjoint and accessible
 * for the indicated lengths; pk and coins initially contain readable data.
 * Noncanonical pk causes status1 and zero ct/ss. Success returns0.
 * SHAKE256, C orchestration and memory/ABI correspondence are external proof
 * boundaries. Cleanup covers this wrapper's13634-byte workspace and the
 * randomized wrapper's96 coins bytes, not registers, spills or nested calls.
 */
int ntruplus768_encaps_derand(uint8_t ct[1152], uint8_t ss[32],
                             const uint8_t pk[1152], const uint8_t coins[96]);

/* Calls the external void randombytes primitive once for96 bytes before
 * checking pk, as the pinned official API does. The RNG contract requires
 * full initialization, termination, memory/ABI behavior and the distribution
 * used by the caller's probabilistic model; no distribution is inferred here.
 */
int ntruplus768_encaps(uint8_t ct[1152], uint8_t ss[32], const uint8_t pk[1152]);

#endif
