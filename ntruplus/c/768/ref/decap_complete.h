#ifndef NTRUPLUS768_DECAP_COMPLETE_H
#define NTRUPLUS768_DECAP_COMPLETE_H

#include <stdint.h>

/* Complete mixed C/Jasmin Decaps entry point. The three external regions
 * must be disjoint and accessible for 32, 1152, and 2336 bytes respectively.
 * ct and sk must initially contain readable data. Returns 0 on acceptance
 * and 1 on rejection; rejection writes exactly 32 zero shared-secret bytes.
 * Native SHAKE256, C orchestration and its memory/ABI behavior remain explicit
 * external proof boundaries. Cleanup covers this wrapper's 13506-byte
 * workspace, not registers, spills, or workspaces of nested calls.
 */
int ntruplus768_decaps(uint8_t ss[32], const uint8_t ct[1152],
                      const uint8_t sk[2336]);

#endif
