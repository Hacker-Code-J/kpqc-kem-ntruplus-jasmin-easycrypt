#include <stdlib.h>
#include <string.h>
#include "trace.h"
#include "symmetric.h"
#include "fips202/fips202.h"
int kat_randombytes(unsigned char *, unsigned long long);
void randombytes_init(unsigned char *, unsigned char *, int);
encap_trace trace;
uint8_t hash_f_input[1153], hash_f_output[32], hash_g_input[1153], hash_g_output[192];
uint8_t hash_h_input[129], hash_h_output[224], last_coins[96];
static void event(char c) {
    if (trace.event_count + 1 < sizeof trace.events) {
        trace.events[trace.event_count] = c; trace.events[trace.event_count+1] = 0;
    }
    trace.event_count++;
}
void trace_reset(void) { memset(&trace, 0, sizeof trace); }
void seed_rng(const uint8_t seed[48]) { uint8_t tmp[48]; memcpy(tmp, seed, 48); randombytes_init(tmp, NULL, 256); }
void e_randombytes(uint8_t *out, size_t n) {
    trace.rng_calls++; trace.rng_bytes += (unsigned)n; event('R');
    if (kat_randombytes(out, n)) abort();
    if (n == 96) memcpy(last_coins, out, 96);
}
int e_poly_frombytes(poly *out, const uint8_t *in) { event('D'); return poly_frombytes(out,in); }
void e_hash_f(uint8_t *out,const uint8_t *in) { event('F'); hash_f(out,in); }
void e_hash_g(uint8_t *out,const uint8_t *in) { event('G'); hash_g(out,in); }
void e_hash_h(uint8_t *out,const uint8_t *in) { event('H'); hash_h(out,in); }
void e_poly_cbd1(poly *out,const uint8_t *in) { event('C'); poly_cbd1(out,in); }
void e_poly_ntt(poly *p) { event('N'); poly_ntt(p); }
void e_poly_tobytes(uint8_t *out,const poly *p) { event('T'); poly_tobytes(out,p); }
void e_poly_sotp_encode(poly *out,const uint8_t *msg,const uint8_t *pad) { event('E'); poly_sotp_encode(out,msg,pad); }
void e_poly_basemul_add(poly *out,const poly *a,const poly *b,const poly *m) { event('A'); poly_basemul_add(out,a,b,m); }
void e_shake256(uint8_t *out,size_t on,const uint8_t *in,size_t n) {
    uint8_t *ci=NULL,*co=NULL;
    if (n==1153 && on==32) { trace.hash_f_calls++; event('F'); if(in[0]!=0) trace.hash_bad++; ci=hash_f_input;co=hash_f_output; }
    else if(n==1153 && on==192) { trace.hash_g_calls++; event('G'); if(in[0]!=1) trace.hash_bad++; ci=hash_g_input;co=hash_g_output; }
    else if(n==129 && on==224) { trace.hash_h_calls++; event('H'); if(in[0]!=2) trace.hash_bad++; ci=hash_h_input;co=hash_h_output; }
    else trace.hash_bad++;
    if(ci) memcpy(ci,in,n);
    shake256(out,on,in,n);
    if(co) memcpy(co,out,on);
}
uint32_t e_guard(uint16_t *h,uint8_t *ct,uint8_t *ss,const uint8_t *pk) { event('J'); return jade_ntruplus_ntruplus768_amd64_ref_encap_guard(h,ct,ss,pk); }
void e_prepare_f(uint8_t *out,const uint8_t *pk) { event('P'); jade_ntruplus_ntruplus768_amd64_ref_encap_hash_f_prepare(out,pk); }
void e_prepare_h(uint8_t *out,const uint8_t *msg,const uint8_t *suffix) { event('U'); jade_ntruplus_ntruplus768_amd64_ref_decap_hash_h_prepare(out,msg,suffix); }
void e_cbd(uint16_t *out,const uint8_t *in) { event('C'); jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(out,in); }
void e_ntt(uint16_t *out,const uint16_t *in) { event('N'); jade_ntruplus_ntruplus768_amd64_ref_ntt(out,in); }
void e_prepare_g(uint8_t *bs,uint8_t *input,const uint16_t *r) { event('T'); jade_ntruplus_ntruplus768_amd64_ref_decap_message_prepare(bs,input,r); }
void e_encode(uint16_t *out,const uint8_t *msg,const uint8_t *pad) { event('E'); jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_encode(out,msg,pad); }
void e_basemul(uint16_t *out,const uint16_t *a,const uint16_t *b) { event('B'); jade_ntruplus_ntruplus768_amd64_ref_poly_basemul(out,a,b); }
void e_centered_add(uint16_t *out,const uint16_t *a,const uint16_t *b) { event('A'); jade_ntruplus_ntruplus768_amd64_ref_poly_centered_add(out,a,b); }
void e_tobytes(uint8_t *out,const uint16_t *in) { event('T'); jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes(out,in); }
void e_copy_key(uint8_t *out,const uint8_t *in) { event('K'); jade_ntruplus_ntruplus768_amd64_ref_encap_copy_key(out,in); }
void e_clear(uint8_t *p) { event('Z'); trace.clear_calls++; jade_ntruplus_ntruplus768_amd64_ref_encap_clear(p); for(size_t i=0;i<13634;i++) if(p[i]) trace.clear_bad++; }
void e_clear_coins(uint8_t *p) { event('z'); trace.coins_clear_calls++; jade_ntruplus_ntruplus768_amd64_ref_encap_clear_coins(p); for(size_t i=0;i<96;i++) if(p[i]) trace.clear_bad++; }
unsigned oracle_rng_calls(void) { return trace.rng_calls; }
unsigned oracle_rng_bytes(void) { return trace.rng_bytes; }
unsigned oracle_hash_calls(void) { return trace.hash_f_calls+trace.hash_g_calls+trace.hash_h_calls; }
unsigned oracle_clear_calls(void) { return trace.clear_calls; }
unsigned oracle_coin_clear_calls(void) { return trace.coins_clear_calls; }
unsigned oracle_clear_bad(void) { return trace.clear_bad; }
void oracle_hash_f(uint8_t *out,const uint8_t *in) { hash_f(out,in); }
