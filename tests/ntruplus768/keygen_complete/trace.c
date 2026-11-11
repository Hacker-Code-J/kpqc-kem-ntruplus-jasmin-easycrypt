#include <stdlib.h>
#include <string.h>
#include "trace.h"
#include "symmetric.h"
#include "fips202/fips202.h"
int kat_randombytes(unsigned char *,unsigned long long);
void randombytes_init(unsigned char *,unsigned char *,int);
keygen_trace trace;
static unsigned requested_failures[2];
static uint8_t fixtures[2][2][192];
static void event(char e) {
 if(trace.event_count+1>=sizeof trace.events)abort();
 trace.events[trace.event_count++]=e;trace.events[trace.event_count]=0;
}
void seed_rng(const uint8_t seed[48]) { uint8_t s[48];memcpy(s,seed,48);randombytes_init(s,NULL,256); }
void next_rng(uint8_t out[32]) { if(kat_randombytes(out,32))abort(); }
void randombytes(uint8_t *out,size_t n) { if(kat_randombytes(out,n))abort(); }
void trace_reset(unsigned f_fail,unsigned g_fail,int scripted) {
 memset(&trace,0,sizeof trace);requested_failures[0]=f_fail;requested_failures[1]=g_fail;trace.scripted=(unsigned)scripted;
}
static int fixture_status(const uint8_t buf[192],unsigned phase) {
 poly p,inv;poly_cbd1(&p,buf);poly_triple(&p);if(!phase)p.coeffs[0]++;
 poly_ntt(&p);return poly_baseinv(&inv,&p)!=0;
}
void prepare_retry_fixtures(void) {
 /* Deterministic search through actual CBD/shape/NTT/inverse executions, not forced return values. */
 uint32_t state=UINT32_C(0x49f386a1);unsigned found[2][2]={{0}};
 for(unsigned n=0;n<100000;n++) {
  uint8_t b[192];for(unsigned i=0;i<192;i++){state^=state<<13;state^=state>>17;state^=state<<5;b[i]=(uint8_t)state;}
  for(unsigned phase=0;phase<2;phase++){unsigned success=(unsigned)!fixture_status(b,phase);if(!found[phase][success]){memcpy(fixtures[phase][success],b,192);found[phase][success]=1;}}
  if(found[0][0]&&found[0][1]&&found[1][0]&&found[1][1])return;
 }
 abort();
}
void retry_fixture(uint8_t out[192],unsigned phase,unsigned success){if(phase>1||success>1)abort();memcpy(out,fixtures[phase][success],192);}
void k_randombytes(uint8_t *out,size_t n) {
 event('R');if(n!=32||trace.rng_calls>=TRACE_LIMIT)abort();
 if(kat_randombytes(out,n))abort();
 memcpy(trace.seeds[trace.rng_calls],out,32);
 trace.rng_calls++;trace.rng_bytes+=(unsigned)n;
}
void k_shake256(uint8_t *out,size_t on,const uint8_t *in,size_t n) {
 if(on==192&&n==32) {
  unsigned index=trace.seed_hash_calls,attempt=trace.phase?trace.g_attempts:trace.f_attempts;
  event('S');if(index>=TRACE_LIMIT||trace.phase>1||index+1!=trace.rng_calls)abort();
  if(memcmp(in,trace.seeds[index],32))trace.bad++;
  if(trace.scripted)memcpy(out,fixtures[trace.phase][attempt>=requested_failures[trace.phase]],192);
  else shake256(out,on,in,n);
  memcpy(trace.buffers[index],out,192);trace.seed_hash_calls++;
 } else if(on==32&&n==1153) {
  event('H');trace.hash_f_calls++;if(in[0]!=0)trace.bad++;
  memcpy(trace.hash_f_input,in,n);shake256(out,on,in,n);memcpy(trace.hash_f_output,out,on);
 } else abort();
}
void k_poly_cbd1(poly *p,const uint8_t *b){event('C');poly_cbd1(p,b);}
void k_poly_triple(poly *p){event('T');poly_triple(p);}
void k_poly_ntt(poly *p){event('N');poly_ntt(p);}
static void inverse_result(uint64_t r){
 event('I');unsigned i=trace.f_attempts+trace.g_attempts;if(i>=TRACE_LIMIT||trace.phase>1)abort();trace.inverse_status[i]=r;
 if(trace.phase)trace.g_attempts++;else trace.f_attempts++;
 if(r==0)trace.phase++;else if(r!=1)trace.bad++;
}
int k_poly_baseinv(poly *out,const poly *in){int r=poly_baseinv(out,in);inverse_result((uint64_t)r);return r;}
void k_poly_basemul(poly *out,const poly *a,const poly *b){event('B');poly_basemul(out,a,b);}
void k_poly_tobytes(uint8_t *out,const poly *in){event('P');poly_tobytes(out,in);}
void k_hash_f(uint8_t *out,const uint8_t *pk){
 event('H');trace.hash_f_calls++;trace.hash_f_input[0]=0;
 memcpy(trace.hash_f_input+1,pk,1152);hash_f(out,pk);memcpy(trace.hash_f_output,out,32);
}
void k_cbd(uint16_t *p,const uint8_t *b){event('C');JP(poly_cbd1)(p,b);}
void k_shape_f(uint16_t *p){event('T');JP(keygen_shape_f)(p);}
void k_shape_g(uint16_t *p){event('T');JP(keygen_shape_g)(p);}
void k_ntt(uint16_t *out,const uint16_t *in){event('N');JP(ntt)(out,in);}
uint64_t k_baseinv(uint16_t *out,const uint16_t *in){uint64_t r=JP(poly_baseinv)(out,in);inverse_result(r);return r;}
void k_basemul(uint16_t *out,const uint16_t *a,const uint16_t *b){event('B');JP(poly_basemul)(out,a,b);}
void k_tobytes(uint8_t *out,const uint16_t *in){event('P');JP(poly_tobytes)(out,in);}
void k_hash_prepare(uint8_t *out,const uint8_t *pk){JP(encap_hash_f_prepare)(out,pk);}
void k_pack(uint8_t *out,const uint8_t *f,const uint8_t *h,const uint8_t *hash){JP(keygen_pack_sk)(out,f,h,hash);}
void k_clear(uint8_t *p){trace.clear_calls++;JP(keygen_clear)(p);for(size_t i=0;i<KEYGEN_WORKSPACE;i++)if(p[i])trace.clear_bad++;}
unsigned oracle_rng_calls(void){return trace.rng_calls;}
unsigned oracle_f_attempts(void){return trace.f_attempts;}
unsigned oracle_g_attempts(void){return trace.g_attempts;}
unsigned oracle_bad(void){return trace.bad+trace.clear_bad;}
unsigned oracle_clear_calls(void){return trace.clear_calls;}
void oracle_seed(uint8_t *out,unsigned i){if(i>=trace.seed_hash_calls)abort();memcpy(out,trace.seeds[i],32);}
void oracle_buffer(uint8_t *out,unsigned i){if(i>=trace.seed_hash_calls)abort();memcpy(out,trace.buffers[i],192);}
uint64_t oracle_inverse(unsigned i){if(i>=trace.seed_hash_calls)abort();return trace.inverse_status[i];}
void oracle_hash_f_input(uint8_t *out){memcpy(out,trace.hash_f_input,1153);}
void oracle_hash_f_output(uint8_t *out){memcpy(out,trace.hash_f_output,32);}
