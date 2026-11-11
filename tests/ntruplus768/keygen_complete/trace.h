#ifndef KEYGEN_COMPLETE_TRACE_H
#define KEYGEN_COMPLETE_TRACE_H
#include <stddef.h>
#include <stdint.h>
#include "poly.h"
enum { TRACE_LIMIT=64, KEYGEN_WORKSPACE=14466 };
typedef struct {
 unsigned rng_calls,rng_bytes,seed_hash_calls,hash_f_calls,clear_calls,clear_bad,bad;
 unsigned f_attempts,g_attempts,phase,event_count,scripted;
 char events[1024];
 uint8_t seeds[TRACE_LIMIT][32],buffers[TRACE_LIMIT][192];
 uint64_t inverse_status[TRACE_LIMIT];
 uint8_t hash_f_input[1153],hash_f_output[32];
} keygen_trace;
extern keygen_trace trace;
void trace_reset(unsigned f_fail,unsigned g_fail,int scripted);
void seed_rng(const uint8_t seed[48]);
void next_rng(uint8_t out[32]);
void prepare_retry_fixtures(void);
void retry_fixture(uint8_t out[192],unsigned phase,unsigned success);
void k_randombytes(uint8_t *,size_t);
void k_shake256(uint8_t *,size_t,const uint8_t *,size_t);
void k_poly_cbd1(poly *,const uint8_t *);
void k_poly_triple(poly *);
void k_poly_ntt(poly *);
int k_poly_baseinv(poly *,const poly *);
void k_poly_basemul(poly *,const poly *,const poly *);
void k_poly_tobytes(uint8_t *,const poly *);
void k_hash_f(uint8_t *,const uint8_t *);
void k_cbd(uint16_t *,const uint8_t *);
void k_shape_f(uint16_t *);
void k_shape_g(uint16_t *);
void k_ntt(uint16_t *,const uint16_t *);
uint64_t k_baseinv(uint16_t *,const uint16_t *);
void k_basemul(uint16_t *,const uint16_t *,const uint16_t *);
void k_tobytes(uint8_t *,const uint16_t *);
void k_hash_prepare(uint8_t *,const uint8_t *);
void k_pack(uint8_t *,const uint8_t *,const uint8_t *,const uint8_t *);
void k_clear(uint8_t *);
int official_keypair(uint8_t *,uint8_t *);
int official_enc(uint8_t *,uint8_t *,const uint8_t *);
int official_dec(uint8_t *,const uint8_t *,const uint8_t *);
int ntruplus768_keypair(uint8_t *,uint8_t *);
int ntruplus768_encaps(uint8_t *,uint8_t *,const uint8_t *);
int ntruplus768_encaps_derand(uint8_t *,uint8_t *,const uint8_t *,const uint8_t *);
int ntruplus768_decaps(uint8_t *,const uint8_t *,const uint8_t *);
#define JP(name) jade_ntruplus_ntruplus768_amd64_ref_##name
void JP(poly_cbd1)(uint16_t *,const uint8_t *);
void JP(keygen_shape_f)(uint16_t *);
void JP(keygen_shape_g)(uint16_t *);
void JP(ntt)(uint16_t *,const uint16_t *);
uint64_t JP(poly_baseinv)(uint16_t *,const uint16_t *);
void JP(poly_basemul)(uint16_t *,const uint16_t *,const uint16_t *);
void JP(poly_tobytes)(uint8_t *,const uint16_t *);
void JP(encap_hash_f_prepare)(uint8_t *,const uint8_t *);
void JP(keygen_pack_sk)(uint8_t *,const uint8_t *,const uint8_t *,const uint8_t *);
void JP(keygen_clear)(uint8_t *);
#endif
