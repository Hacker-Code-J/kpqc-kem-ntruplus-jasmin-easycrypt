#ifndef NTRUPLUS768_KEYGEN_COMPLETE_H
#define NTRUPLUS768_KEYGEN_COMPLETE_H

#include <stdint.h>

/* Mixed C/Jasmin KeyGen. pk[1152] and sk[2336] are disjoint, writable regions.
 * Each candidate consumes one external randombytes call for 32 seed bytes,
 * then SHAKE256 expands that seed to 192 bytes. The f and g rejection loops
 * run independently and in that order. The function returns 0 on success.
 * RNG/SHAKE contracts, C orchestration and memory/ABI correspondence remain
 * external proof boundaries. Termination requires an appropriate source of
 * randomness and a positive probability of an invertible candidate.
 * Inverse failure and retry counts are observable; no whole-API CT/SCT claim
 * is made. Cleanup covers the entire 14466-byte local workspace, including
 * the seed, but not registers, spills or private storage of nested calls.
 */
int ntruplus768_keypair(uint8_t pk[1152], uint8_t sk[2336]);

#endif
