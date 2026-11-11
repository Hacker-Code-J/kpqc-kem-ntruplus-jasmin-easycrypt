#ifndef ENCAP_COMPLETE_TRACE_H
#define ENCAP_COMPLETE_TRACE_H
#include <stddef.h>
#include <stdint.h>
#include "poly.h"
typedef struct {
    unsigned rng_calls, rng_bytes, hash_f_calls, hash_g_calls, hash_h_calls;
    unsigned clear_calls, coins_clear_calls, clear_bad, hash_bad, event_count;
    char events[96];
} encap_trace;
extern encap_trace trace;
extern uint8_t hash_f_input[1153], hash_f_output[32], hash_g_input[1153], hash_g_output[192];
extern uint8_t hash_h_input[129], hash_h_output[224], last_coins[96];
void trace_reset(void);
void seed_rng(const uint8_t seed[48]);
void e_randombytes(uint8_t *, size_t);
void e_shake256(uint8_t *, size_t, const uint8_t *, size_t);
int official_keypair(uint8_t *, uint8_t *);
int official_enc(uint8_t *, uint8_t *, const uint8_t *);
int official_derand(uint8_t *, uint8_t *, const uint8_t *, const uint8_t *);
int official_dec(uint8_t *, const uint8_t *, const uint8_t *);
int ntruplus768_encaps(uint8_t *, uint8_t *, const uint8_t *);
int ntruplus768_encaps_derand(uint8_t *, uint8_t *, const uint8_t *, const uint8_t *);
int ntruplus768_decaps(uint8_t *, const uint8_t *, const uint8_t *);
int e_poly_frombytes(poly *, const uint8_t *);
void e_hash_f(uint8_t *, const uint8_t *);
void e_hash_g(uint8_t *, const uint8_t *);
void e_hash_h(uint8_t *, const uint8_t *);
void e_poly_cbd1(poly *, const uint8_t *);
void e_poly_ntt(poly *);
void e_poly_tobytes(uint8_t *, const poly *);
void e_poly_sotp_encode(poly *, const uint8_t *, const uint8_t *);
void e_poly_basemul_add(poly *, const poly *, const poly *, const poly *);
uint32_t jade_ntruplus_ntruplus768_amd64_ref_encap_guard(uint16_t *, uint8_t *, uint8_t *, const uint8_t *);
void jade_ntruplus_ntruplus768_amd64_ref_encap_hash_f_prepare(uint8_t *, const uint8_t *);
void jade_ntruplus_ntruplus768_amd64_ref_decap_hash_h_prepare(uint8_t *, const uint8_t *, const uint8_t *);
void jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(uint16_t *, const uint8_t *);
void jade_ntruplus_ntruplus768_amd64_ref_ntt(uint16_t *, const uint16_t *);
void jade_ntruplus_ntruplus768_amd64_ref_decap_message_prepare(uint8_t *, uint8_t *, const uint16_t *);
void jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_encode(uint16_t *, const uint8_t *, const uint8_t *);
void jade_ntruplus_ntruplus768_amd64_ref_poly_basemul(uint16_t *, const uint16_t *, const uint16_t *);
void jade_ntruplus_ntruplus768_amd64_ref_poly_centered_add(uint16_t *, const uint16_t *, const uint16_t *);
void jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes(uint8_t *, const uint16_t *);
void jade_ntruplus_ntruplus768_amd64_ref_encap_copy_key(uint8_t *, const uint8_t *);
void jade_ntruplus_ntruplus768_amd64_ref_encap_clear(uint8_t *);
void jade_ntruplus_ntruplus768_amd64_ref_encap_clear_coins(uint8_t *);
uint32_t e_guard(uint16_t *, uint8_t *, uint8_t *, const uint8_t *);
void e_prepare_f(uint8_t *, const uint8_t *);
void e_prepare_h(uint8_t *, const uint8_t *, const uint8_t *);
void e_cbd(uint16_t *, const uint8_t *);
void e_ntt(uint16_t *, const uint16_t *);
void e_prepare_g(uint8_t *, uint8_t *, const uint16_t *);
void e_encode(uint16_t *, const uint8_t *, const uint8_t *);
void e_basemul(uint16_t *, const uint16_t *, const uint16_t *);
void e_centered_add(uint16_t *, const uint16_t *, const uint16_t *);
void e_tobytes(uint8_t *, const uint16_t *);
void e_copy_key(uint8_t *, const uint8_t *);
void e_clear(uint8_t *);
void e_clear_coins(uint8_t *);
#endif
