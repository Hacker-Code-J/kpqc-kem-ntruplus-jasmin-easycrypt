#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "trace.h"
#define randombytes kat_randombytes
#include "kat/rng.h"
#undef randombytes
extern AES256_CTR_DRBG_struct DRBG_ctx;
enum { BYTES=1152,SKBYTES=2336 };
_Static_assert(NTRUPLUS_N==768 && NTRUPLUS_Q==3457 && sizeof(poly)==1536,"reference layout");
typedef struct { uint8_t pre[32],data[1152],post[32]; } guarded_pk;
typedef struct { uint8_t pre[32],data[2336],post[32]; } guarded_sk;
typedef struct { uint8_t pre[32],data[32],post[32]; } guarded_ss;
static uint64_t assertions,keygen_calls,roundtrips,clear_calls,real_hash_attempts,scripted_attempts,f_rejections,g_rejections;
static const char *group="init";
static unsigned case_no;
static void require(int ok,const char *message){assertions++;if(!ok){fprintf(stderr,"FAIL %s case=%u: %s\n",group,case_no,message);exit(1);}}
static int all_byte(const uint8_t *p,size_t n,uint8_t b){for(size_t i=0;i<n;i++)if(p[i]!=b)return 0;return 1;}
#define GUARDS_OK(x) (all_byte((x).pre,32,165)&&all_byte((x).post,32,165))
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

static void check_trace(unsigned impl,int scripted,unsigned ff,unsigned gf,const uint8_t *pk,const uint8_t *sk) {
 unsigned attempts=trace.f_attempts+trace.g_attempts;char events[1024]="";
 for(unsigned i=0;i<attempts;i++)strcat(events,"RSCTNI");
 strcat(events,"BBPPPH");
 require(strcmp(trace.events,events)==0,"exact seed RNG/hash/CBD/shape/NTT/inverse/retry/output order");
 require(trace.phase==2 && trace.rng_calls==attempts && trace.rng_bytes==32*attempts && trace.seed_hash_calls==attempts,"each attempt samples exactly32 bytes");
 require(trace.f_attempts>0&&trace.g_attempts>0&&trace.hash_f_calls==1&&!trace.bad,"independent f then g completion and one HashF");
 require(trace.clear_calls==impl&&!trace.clear_bad,"actual workspace clear after successful output");
 require(trace.hash_f_input[0]==0&&memcmp(trace.hash_f_input+1,pk,1152)==0&&memcmp(trace.hash_f_output,sk+2304,32)==0,"actual HashF(pk) and secret-key suffix");
 for(unsigned i=0;i<attempts;i++)require(trace.inverse_status[i]==(uint64_t)(i+1!=trace.f_attempts&&i+1!=attempts),"retry iff actual inverse fails");
 if(scripted){require(trace.f_attempts==ff+1&&trace.g_attempts==gf+1,"scripted f/g rejection schedule");scripted_attempts+=attempts;}else real_hash_attempts+=attempts;
 f_rejections+=trace.f_attempts-1;g_rejections+=trace.g_attempts-1;clear_calls+=trace.clear_calls;
}
static void keypair_case(const uint8_t seed[48],int scripted,unsigned ff,unsigned gf,const kat_case *kat) {
 const uint8_t patterns[]={0,255,165,90};
 for(unsigned pattern=0;pattern<4;pattern++){
  guarded_pk pk[2];guarded_sk sk[2];uint8_t after[2][32];keygen_trace saved[2];AES256_CTR_DRBG_struct rng_state[2];
  for(unsigned impl=0;impl<2;impl++){
   memset(&pk[impl],165,sizeof pk[impl]);memset(&sk[impl],165,sizeof sk[impl]);
   memset(pk[impl].data,patterns[pattern],1152);memset(sk[impl].data,patterns[3-pattern],2336);
   seed_rng(seed);trace_reset(ff,gf,scripted);
   require((impl?ntruplus768_keypair:official_keypair)(pk[impl].data,sk[impl].data)==0,"KeyGen succeeds after independent f/g retries");
   keygen_calls++;check_trace(impl,scripted,ff,gf,pk[impl].data,sk[impl].data);saved[impl]=trace;rng_state[impl]=DRBG_ctx;
   require(GUARDS_OK(pk[impl])&&GUARDS_OK(sk[impl]),"KeyGen output canaries");
   if(kat)require(memcmp(pk[impl].data,kat->pk,1152)==0&&memcmp(sk[impl].data,kat->sk,2336)==0,"exact official KAT public and secret keys");
   guarded_pk ct;guarded_ss ss,decoded;uint8_t coins[96];uint8_t pk_saved[1152],sk_saved[2336];
   memset(&ct,165,sizeof ct);memset(&ss,165,sizeof ss);memset(&decoded,165,sizeof decoded);
   memcpy(pk_saved,pk[impl].data,1152);memcpy(sk_saved,sk[impl].data,2336);
   for(unsigned i=0;i<96;i++)coins[i]=(uint8_t)(seed[i%48]+i);
   int er=kat?ntruplus768_encaps(ct.data,ss.data,pk[impl].data):ntruplus768_encaps_derand(ct.data,ss.data,pk[impl].data,coins);
   require(er==0,"actual Encaps accepts generated public key");
   if(kat)require(memcmp(ct.data,kat->ct,1152)==0&&memcmp(ss.data,kat->ss,32)==0,"KAT post-KeyGen RNG state produces exact ciphertext and shared secret");
   require(ntruplus768_decaps(decoded.data,ct.data,sk[impl].data)==0&&memcmp(ss.data,decoded.data,32)==0,"three-API generated-key roundtrip");roundtrips++;
   require(GUARDS_OK(ct)&&GUARDS_OK(ss)&&GUARDS_OK(decoded)&&GUARDS_OK(pk[impl])&&GUARDS_OK(sk[impl]),"roundtrip canaries");
   require(memcmp(pk_saved,pk[impl].data,1152)==0&&memcmp(sk_saved,sk[impl].data,2336)==0,"roundtrip preserves key inputs");
   next_rng(after[impl]);
  }
  require(memcmp(pk[0].data,pk[1].data,1152)==0&&memcmp(sk[0].data,sk[1].data,2336)==0,"exact official/new generated key bytes");
  require(memcmp(rng_state[0].Key,rng_state[1].Key,32)==0&&memcmp(rng_state[0].V,rng_state[1].V,16)==0&&rng_state[0].reseed_counter==rng_state[1].reseed_counter,"exact complete DRBG state immediately after KeyGen");
  require(memcmp(after[0],after[1],32)==0,"same subsequent RNG output");
  saved[0].clear_calls=saved[1].clear_calls=0;
  require(memcmp(&saved[0],&saved[1],sizeof saved[0])==0,"exact RNG/seed expansion/inverse status trace agreement");
 }
}
int main(int argc,char **argv){
 require(argc==2,"usage: keygen-complete-test official-KAT.rsp");load_kats(argv[1]);prepare_retry_fixtures();
 group="100-official-KAT";for(case_no=0;case_no<100;case_no++)keypair_case(kats[case_no].seed,0,0,0,&kats[case_no]);
 group="64-fresh-seeds";for(case_no=0;case_no<64;case_no++){uint8_t seed[48];for(unsigned i=0;i<48;i++)seed[i]=(uint8_t)(case_no*73+i*31);keypair_case(seed,0,0,0,NULL);}
 group="controlled-SHAKE-retry-fixtures";for(unsigned f=0;f<4;f++)for(unsigned g=0;g<4;g++){case_no=4*f+g;keypair_case(kats[case_no].seed,1,f,g,NULL);}
 require(keygen_calls==1440&&clear_calls==720&&roundtrips==1440,"complete native coverage");
 printf("{\"status\":\"PASS\",\"kat_vectors\":100,\"fresh_seeds\":64,\"scripted_retry_schedules\":16,\"output_initial_patterns\":4,\"keygen_calls\":%" PRIu64 ",\"workspace_clear_calls\":%" PRIu64 ",\"roundtrips\":%" PRIu64 ",\"real_hash_attempts\":%" PRIu64 ",\"scripted_hash_attempts\":%" PRIu64 ",\"f_rejections\":%" PRIu64 ",\"g_rejections\":%" PRIu64 ",\"assertions\":%" PRIu64 "}\n",keygen_calls,clear_calls,roundtrips,real_hash_attempts,scripted_attempts,f_rejections,g_rejections,assertions);return 0;
}
