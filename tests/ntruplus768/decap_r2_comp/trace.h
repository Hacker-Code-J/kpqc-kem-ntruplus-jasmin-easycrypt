#ifndef DECAP_R2_COMP_TRACE_H
#define DECAP_R2_COMP_TRACE_H
#include <stddef.h>
#include <stdint.h>
#include "poly.h"
typedef struct {
    unsigned random_calls, random_bytes, decoder_calls, guard_calls, candidate_calls, r2_calls, success_calls;
    unsigned event_count;
    char events[64];
} call_trace;
extern call_trace trace;
void trace_reset(void);
void seed_rng(const uint8_t seed[48]);
uint32_t jade_ntruplus_ntruplus768_amd64_ref_decap_guard(
    uint16_t cp[768], uint16_t fp[768], uint16_t hp[768], uint8_t ss[32],
    const uint8_t ct[1152], const uint8_t skpoly[2304]);
uint32_t trace_guard(uint16_t *, uint16_t *, uint16_t *, uint8_t *, const uint8_t *, const uint8_t *);
void jade_ntruplus_ntruplus768_amd64_ref_decap_candidate(uint16_t *, const uint16_t *, const uint16_t *);
void trace_candidate(uint16_t *, const uint16_t *, const uint16_t *);
int both_keypair(uint8_t *, uint8_t *);
int both_enc(uint8_t *, uint8_t *, const uint8_t *);
int both_dec(uint8_t *, const uint8_t *, const uint8_t *);
void trace_randombytes(uint8_t *, size_t);
int trace_poly_frombytes(poly *, const uint8_t [1152]);
void trace_hash_f(uint8_t *, const uint8_t *);
void trace_hash_g(uint8_t *, const uint8_t *);
void trace_hash_h(uint8_t *, const uint8_t *);
void trace_poly_cbd1(poly *, const uint8_t [192]);
void trace_poly_ntt(poly *);
void trace_poly_invntt(poly *);
void trace_poly_tobytes(uint8_t [1152], const poly *);
int trace_poly_sotp_decode(uint8_t [96], const poly *, const uint8_t [192]);
void trace_poly_basemul(poly *, const poly *, const poly *);
void trace_poly_sub(poly *, const poly *, const poly *);
void trace_poly_crepmod3(poly *);
int official_keypair(uint8_t *, uint8_t *);
int mixed_keypair(uint8_t *, uint8_t *);
int official_enc(uint8_t *, uint8_t *, const uint8_t *);
int mixed_enc(uint8_t *, uint8_t *, const uint8_t *);
int official_dec(uint8_t *, const uint8_t *, const uint8_t *);
int mixed_dec(uint8_t *, const uint8_t *, const uint8_t *);
void jade_ntruplus_ntruplus768_amd64_ref_decap_r2(uint16_t *, const uint16_t *, const uint16_t *, const uint16_t *);
void trace_r2(uint16_t *, const uint16_t *, const uint16_t *, const uint16_t *);
#endif
