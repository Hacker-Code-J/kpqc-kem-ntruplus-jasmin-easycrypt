#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "trace.h"
enum { GUARD=32, N=768, BYTES=1152, SKBYTES=2336 };
_Static_assert(NTRUPLUS_N==768 && NTRUPLUS_Q==3457 && sizeof(poly)==1536,"reference layout");
typedef struct { uint8_t pre[32], data[1152], post[32]; } guarded_input;
typedef struct { uint8_t pre[32], data[2336], post[32]; } guarded_sk;
typedef struct { uint8_t pre[32], data[32], post[32]; } guarded_ss;
typedef struct { uint8_t pre[32], data[96], post[32]; } guarded_coins;
static uint64_t assertions,cases,derand_cases,random_cases,encap_calls,clear_calls,coin_clear_calls,roundtrips;
static const char *group="init";
static size_t position;
static unsigned value;
static void require(int ok,const char *message) {
 assertions++; if(!ok) { fprintf(stderr,"FAIL %s pos=%zu value=%u case=%" PRIu64 ": %s\n",group,position,value,cases,message);exit(1); }
}
static int all_byte(const uint8_t *p,size_t n,uint8_t v) { for(size_t i=0;i<n;i++) if(p[i]!=v)return 0;return 1; }
#define GUARDS_OK(x) (all_byte((x).pre,32,165)&&all_byte((x).post,32,165))
static uint32_t next_u32(uint32_t *s) { uint32_t x=*s;x^=x<<13;x^=x>>17;x^=x<<5;return *s=x; }
static void put12(uint8_t *p,size_t i,uint16_t v) {
 for(unsigned b=0;b<12;b++) { size_t bit=12*i+b;uint8_t mask=(uint8_t)(1u<<(bit%8));p[bit/8]=(uint8_t)((p[bit/8]&~mask)|((v&(1u<<b))?mask:0)); }
}
typedef struct { uint8_t seed[48], pk[BYTES], sk[SKBYTES], ct[BYTES], ss[32]; } kat_case;
static kat_case kats[100];
static unsigned hex_digit(char c)
{
    if (c >= '0' && c <= '9') return (unsigned)(c - '0');
    if (c >= 'A' && c <= 'F') return (unsigned)(c - 'A' + 10);
    if (c >= 'a' && c <= 'f') return (unsigned)(c - 'a' + 10);
    require(0, "invalid official KAT hex digit"); return 0;
}
static void read_hex(FILE *stream, const char *name, uint8_t *out, size_t n)
{
    char line[5000]; require(fgets(line, sizeof line, stream) != NULL, "KAT field present");
    size_t prefix = strlen(name);
    require(strncmp(line, name, prefix) == 0 && strncmp(line + prefix, " = ", 3) == 0, "KAT label");
    const char *hex = line + prefix + 3;
    require(strcspn(hex, "\r\n") == 2 * n, "KAT field byte length");
    for (size_t i = 0; i < n; i++) out[i] = (uint8_t)(16 * hex_digit(hex[2 * i]) + hex_digit(hex[2 * i + 1]));
}
static void load_kats(const char *path)
{
    FILE *stream = fopen(path, "r"); require(stream != NULL, "open official KAT");
    char line[5000]; unsigned count = 0;
    while (fgets(line, sizeof line, stream)) {
        if (strncmp(line, "count = ", 8) != 0) continue;
        require(count < 100 && strtoul(line + 8, NULL, 10) == count, "100 ordered KAT counts");
        read_hex(stream, "seed", kats[count].seed, 48); read_hex(stream, "pk", kats[count].pk, BYTES);
        read_hex(stream, "sk", kats[count].sk, SKBYTES); read_hex(stream, "ct", kats[count].ct, BYTES);
        read_hex(stream, "ss", kats[count].ss, 32); count++;
    }
    require(count == 100 && !ferror(stream), "complete KAT fixture");
    require(fclose(stream) == 0, "close KAT");
}

static void check_trace(int impl,int randomized,int invalid,const uint8_t *pk,const uint8_t *coins) {
 char expected[96];
 snprintf(expected,sizeof expected,"%s%s%s",randomized?"R":"",
   impl?(invalid?"JZ":"JPFUHCNTGENBATKZ"):(invalid?"D":"DFHCNTGENAT"),
   impl&&randomized?"z":"");
 require(strcmp(trace.events,expected)==0,"exact RNG, guard, hash and cleanup order");
 require(trace.rng_calls==(unsigned)randomized && trace.rng_bytes==(unsigned)(randomized?96:0),"exact RNG consumption");
 unsigned active=(unsigned)(impl&&!invalid);
 require(trace.hash_f_calls==active && trace.hash_g_calls==active && trace.hash_h_calls==active && !trace.hash_bad,"three exact native hashes iff canonical");
 require(trace.clear_calls==(unsigned)impl && trace.coins_clear_calls==(unsigned)(impl&&randomized) && !trace.clear_bad,"all workspace and sampled coins cleared");
 if(active) {
  require(hash_f_input[0]==0 && memcmp(hash_f_input+1,pk,BYTES)==0,"actual HashF public key bytes");
  require(hash_h_input[0]==2 && memcmp(hash_h_input+1,randomized?last_coins:coins,96)==0 &&
    memcmp(hash_h_input+97,hash_f_output,32)==0,"actual HashH coins and HashF result");
  require(hash_g_input[0]==1,"actual HashG domain byte");
 }
 clear_calls+=trace.clear_calls;coin_clear_calls+=trace.coins_clear_calls;
}
static void roundtrip(const uint8_t *ct,const uint8_t *ss,const uint8_t *sk) {
 guarded_input input;guarded_sk key;guarded_ss output;
 memset(&input,165,sizeof input);memset(&key,165,sizeof key);memset(&output,165,sizeof output);
 memcpy(input.data,ct,BYTES);memcpy(key.data,sk,SKBYTES);
 require(ntruplus768_decaps(output.data,input.data,key.data)==0 && memcmp(output.data,ss,32)==0,"existing full Decaps agreement on generated ciphertext");
 require(memcmp(input.data,ct,BYTES)==0 && memcmp(key.data,sk,SKBYTES)==0 && GUARDS_OK(input)&&GUARDS_OK(key)&&GUARDS_OK(output),"roundtrip input preservation/canaries");roundtrips++;
}
static void api_case(const uint8_t *pk0,const uint8_t *coins0,const uint8_t *seed,int randomized,int invalid,
                     const uint8_t *sk0,const uint8_t *expected_ct,const uint8_t *expected_ss) {
 const uint8_t initial[]={0,255,165,90};
 for(unsigned pattern=0;pattern<4;pattern++) {
  guarded_input pk[2],ct[2];guarded_ss ss[2];guarded_coins coins[2];int status[2];uint8_t consumed[2][96];
  for(int impl=0;impl<2;impl++) {
   memset(&pk[impl],165,sizeof pk[impl]);memset(&ct[impl],165,sizeof ct[impl]);memset(&ss[impl],165,sizeof ss[impl]);memset(&coins[impl],165,sizeof coins[impl]);
   memcpy(pk[impl].data,pk0,BYTES);memcpy(coins[impl].data,coins0,96);memset(ct[impl].data,initial[pattern],BYTES);memset(ss[impl].data,initial[3-pattern],32);
   if(randomized)seed_rng(seed);
   trace_reset();
   status[impl]=randomized?(impl?ntruplus768_encaps:official_enc)(ct[impl].data,ss[impl].data,pk[impl].data):
    (impl?ntruplus768_encaps_derand:official_derand)(ct[impl].data,ss[impl].data,pk[impl].data,coins[impl].data);
   check_trace(impl,randomized,invalid,pk0,coins0);encap_calls++;
   if(randomized)memcpy(consumed[impl],last_coins,96);
   require(status[impl]==invalid,"canonical acceptance or malformed rejection");
   if(invalid)require(all_byte(ct[impl].data,BYTES,0)&&all_byte(ss[impl].data,32,0),"invalid key zero ciphertext and shared secret");
   if(expected_ct)require(memcmp(ct[impl].data,expected_ct,BYTES)==0 && memcmp(ss[impl].data,expected_ss,32)==0,"official deterministic KAT bytes");
   require(memcmp(pk[impl].data,pk0,BYTES)==0 && memcmp(coins[impl].data,coins0,96)==0,"public key and external coins preserved");
   require(GUARDS_OK(pk[impl])&&GUARDS_OK(ct[impl])&&GUARDS_OK(ss[impl])&&GUARDS_OK(coins[impl]),"all Encaps canaries");
   if(impl)require(status[0]==status[1] && memcmp(ct[0].data,ct[1].data,BYTES)==0 && memcmp(ss[0].data,ss[1].data,32)==0,"exact official/new API bytes");
   if(impl&&randomized)require(memcmp(consumed[0],consumed[1],96)==0,"same actual sampled coins");
   if(sk0&&!invalid)roundtrip(ct[impl].data,ss[impl].data,sk0);
  }
 }
 if(randomized)random_cases++;else derand_cases++;cases++;
}
static void integration(void) {
 uint8_t coins[96],pk[BYTES],sk[SKBYTES],ct[BYTES],ss[32],seed[48];uint32_t rng=UINT32_C(0x8ea551f3);
 group="100-official-KAT-randomized-and-deterministic";
 for(unsigned k=0;k<100;k++) {
  for(int impl=0;impl<2;impl++) {
   seed_rng(kats[k].seed);trace_reset();require(official_keypair(pk,sk)==0,"KAT key generation");
   require(memcmp(pk,kats[k].pk,BYTES)==0&&memcmp(sk,kats[k].sk,SKBYTES)==0,"exact KAT keys");
   trace_reset();require((impl?ntruplus768_encaps:official_enc)(ct,ss,pk)==0,"KAT randomized Encaps");
   check_trace(impl,1,0,pk,NULL);encap_calls++;
   require(memcmp(ct,kats[k].ct,BYTES)==0&&memcmp(ss,kats[k].ss,32)==0,"exact randomized KAT ciphertext and secret");
   memcpy(coins,last_coins,96);roundtrip(ct,ss,sk);
  }
  api_case(kats[k].pk,coins,kats[k].seed,0,0,kats[k].sk,kats[k].ct,kats[k].ss);
 }
 for(unsigned i=0;i<96;i++)coins[i]=(uint8_t)next_u32(&rng);
 for(unsigned i=0;i<48;i++)seed[i]=(uint8_t)next_u32(&rng);
 group="malformed-every-public-key-coefficient";
 for(position=0;position<768;position++)for(value=3457;value<=4095;value+=638) {
  memcpy(pk,kats[0].pk,BYTES);put12(pk,position,(uint16_t)value);
  for(int mode=0;mode<2;mode++)api_case(pk,coins,seed,mode,1,NULL,NULL,NULL);
 }
 group="malformed-multiple-coefficients";
 for(unsigned n=0;n<4;n++) {
  memcpy(pk,kats[0].pk,BYTES);put12(pk,0,(uint16_t)(n&1?4095:3457));put12(pk,767,(uint16_t)(n&2?4095:3457));
  for(int mode=0;mode<2;mode++)api_case(pk,coins,seed,mode,1,NULL,NULL,NULL);
 }
 group="canonical-public-key-tampering";
 for(unsigned n=0;n<128;n++) {
  memcpy(pk,kats[n%100].pk,BYTES);put12(pk,next_u32(&rng)%768,(uint16_t)(next_u32(&rng)%3457));
  for(int mode=0;mode<2;mode++)api_case(pk,coins,seed,mode,0,NULL,NULL,NULL);
 }
 group="32-fresh-keypairs";
 for(unsigned n=0;n<32;n++) {
  for(unsigned i=0;i<48;i++)seed[i]=(uint8_t)next_u32(&rng);
  seed_rng(seed);trace_reset();require(official_keypair(pk,sk)==0,"fresh key pair");
  for(unsigned i=0;i<96;i++)coins[i]=(uint8_t)next_u32(&rng);
  for(int mode=0;mode<2;mode++)api_case(pk,coins,seed,mode,0,sk,NULL,NULL);
 }
 require(derand_cases==1800&&random_cases==1700&&encap_calls==28200,"complete API coverage");
 require(clear_calls==14100&&coin_clear_calls==6900&&roundtrips==1512,"cleanup/roundtrip coverage");
}
int main(int argc,char **argv) {
 require(argc==2,"usage: encap-complete-test official-KAT.rsp");load_kats(argv[1]);integration();
 printf("{\"status\":\"PASS\",\"kat_vectors\":100,\"kat_randomized_runs\":200,\"derand_cases\":%" PRIu64
  ",\"random_cases\":%" PRIu64 ",\"encap_calls\":%" PRIu64 ",\"workspace_clear_calls\":%" PRIu64
  ",\"coin_clear_calls\":%" PRIu64 ",\"roundtrips\":%" PRIu64 ",\"output_initial_patterns\":4,\"assertions\":%" PRIu64 "}\n",
 derand_cases,random_cases,encap_calls,clear_calls,coin_clear_calls,roundtrips,assertions);return 0;
}
