#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "poly.h"
#include "trace.h"


enum { GUARD = 32, SELECTED_POSITIONS = 6, RANDOM_CASES = 4096 };
_Static_assert(NTRUPLUS_N == 768, "NTRU+768 coefficient count");
_Static_assert(NTRUPLUS_Q == 3457, "official checked-decoder threshold");
_Static_assert(NTRUPLUS_POLYBYTES == 1152, "serialized byte count");
_Static_assert(sizeof(poly) == 1536, "reference polynomial layout");

typedef struct { uint8_t pre[GUARD], data[1152], post[GUARD]; } guarded_input;
typedef struct { uint8_t pre[GUARD]; poly data; uint8_t post[GUARD]; } guarded_c_output;
typedef struct { uint8_t pre[GUARD]; uint16_t data[768]; uint8_t post[GUARD]; } guarded_j_output;
typedef struct { uint8_t pre[GUARD], data[32], post[GUARD]; } guarded_ss;
typedef struct { uint8_t pre[GUARD], data[2336], post[GUARD]; } guarded_sk;

static uint64_t cases, success_cases, failure_cases, assertions;
static const char *group = "initialization";
static size_t position;
static unsigned value;
static uint32_t next_u32(uint32_t *state);

static void require(int condition, const char *message)
{
    assertions++;
    if (!condition) {
        fprintf(stderr, "FAIL group=%s position=%zu value=%u case=%" PRIu64 ": %s\n",
                group, position, value, cases, message);
        exit(EXIT_FAILURE);
    }
}

static int all_byte(const uint8_t *p, size_t length, uint8_t value8)
{
    for (size_t i = 0; i < length; i++)
        if (p[i] != value8) return 0;
    return 1;
}

#define GUARDS_OK(x) (all_byte((x).pre, GUARD, 0xa5) && all_byte((x).post, GUARD, 0xa5))

/* A separate bit-stream encoding avoids copying the implementation's paired
 * three-byte shift expressions into the test oracle. */
static void put12(uint8_t bytes[1152], size_t index, uint16_t coefficient)
{
    require(index < 768 && coefficient < 4096, "fixture encoding bounds");
    for (unsigned bit = 0; bit < 12; bit++) {
        size_t offset = 12 * index + bit;
        uint8_t mask = (uint8_t)(1u << (offset % 8));
        bytes[offset / 8] = (uint8_t)((bytes[offset / 8] & (uint8_t)~mask) |
            ((coefficient & (1u << bit)) ? mask : 0u));
    }
}

static void bit_oracle(const uint8_t bytes[1152], uint16_t expected[768])
{
    for (size_t i = 0; i < 768; i++) {
        uint16_t x = 0;
        for (unsigned bit = 0; bit < 12; bit++) {
            size_t offset = 12 * i + bit;
            x |= (uint16_t)(((bytes[offset / 8] >> (offset % 8)) & 1u) << bit);
        }
        expected[i] = x;
    }
}

static int disjoint(const void *a, size_t an, const void *b, size_t bn)
{
    uintptr_t x = (uintptr_t)a, y = (uintptr_t)b;
    return x + an <= y || y + bn <= x;
}

static void check_case(const uint8_t bytes[1152], const uint16_t expected[768])
{
    guarded_input c_input, j_input;
    guarded_c_output c_output;
    guarded_j_output j_output;
    guarded_input c_ct, j_ct;
    guarded_ss c_ss, j_ss;
    uint8_t initial_ct[1152], initial_ss[32];
    memset(&c_ct, 0xa5, sizeof c_ct);
    memset(&j_ct, 0xa5, sizeof j_ct);
    memset(&c_ss, 0xa5, sizeof c_ss);
    memset(&j_ss, 0xa5, sizeof j_ss);
    uint32_t buffer_rng = UINT32_C(0x317915af) ^ (uint32_t)(cases + 1);
    for (size_t i = 0; i < sizeof initial_ct; i++) initial_ct[i] = (uint8_t)next_u32(&buffer_rng);
    for (size_t i = 0; i < sizeof initial_ss; i++) initial_ss[i] = (uint8_t)next_u32(&buffer_rng);
    memcpy(c_ct.data, initial_ct, sizeof initial_ct);
    memcpy(j_ct.data, initial_ct, sizeof initial_ct);
    memcpy(c_ss.data, initial_ss, sizeof initial_ss);
    memcpy(j_ss.data, initial_ss, sizeof initial_ss);
    memset(&c_input, 0xa5, sizeof c_input);
    memset(&j_input, 0xa5, sizeof j_input);
    memset(&c_output, 0xa5, sizeof c_output);
    memset(&j_output, 0xa5, sizeof j_output);
    memcpy(c_input.data, bytes, sizeof c_input.data);
    memcpy(j_input.data, bytes, sizeof j_input.data);
    require(disjoint(&c_output.data, sizeof c_output.data, c_input.data, sizeof c_input.data),
            "reference input/output contract is disjoint");
    require(disjoint(j_output.data, sizeof j_output.data, j_input.data, sizeof j_input.data),
            "Jasmin input/output contract is disjoint");
    require((uintptr_t)j_output.data % _Alignof(uint16_t) == 0, "Jasmin u16 output alignment");

    uint32_t expected_status = 0;
    for (size_t i = 0; i < 768; i++) expected_status |= expected[i] >= NTRUPLUS_Q;
    const void *regions[] = {j_output.data, j_ct.data, j_ss.data, j_input.data};
    const size_t sizes[] = {1536, 1152, 32, 1152};
    for (size_t a = 0; a < 4; a++)
        for (size_t b = a + 1; b < 4; b++)
            require(disjoint(regions[a], sizes[a], regions[b], sizes[b]), "all Jasmin buffers disjoint");
    int c_status = official_prefix(&c_output.data, c_ct.data, c_ss.data, c_input.data);
    uint32_t j_status = jade_ntruplus_ntruplus768_amd64_ref_encap_guard(
        j_output.data, j_ct.data, j_ss.data, j_input.data);
    require(memcmp(c_ct.data, j_ct.data, 1152) == 0, "guard ct C/Jasmin equality");
    require(memcmp(c_ss.data, j_ss.data, 32) == 0, "guard ss C/Jasmin equality");
    require(expected_status ? all_byte(j_ct.data,1152,0) : memcmp(j_ct.data,initial_ct,1152)==0,
            "guard ct rejected zero or canonical arbitrary initial value preserved");
    require(expected_status ? all_byte(j_ss.data,32,0) : memcmp(j_ss.data,initial_ss,32)==0,
            "guard ss rejected zero or canonical arbitrary initial value preserved");
    require(GUARDS_OK(c_ct) && GUARDS_OK(j_ct) && GUARDS_OK(c_ss) && GUARDS_OK(j_ss),
            "guard output memory guards");
    require(c_status == (int)expected_status, "official C canonicality status");
    require(j_status == expected_status, "Jasmin canonicality status");
    require(j_status == (uint32_t)c_status, "C/Jasmin status equality");
    for (size_t i = 0; i < 768; i++) {
        require(c_output.data.coeffs[i] == (int16_t)expected[i], "official C retains decoded value on success and failure");
        require(j_output.data[i] == expected[i], "Jasmin retains decoded value on success and failure");
    }
    require(memcmp(c_input.data, bytes, 1152) == 0, "official C input unchanged");
    require(memcmp(j_input.data, bytes, 1152) == 0, "Jasmin input unchanged");
    require(GUARDS_OK(c_input), "official C input guards");
    require(GUARDS_OK(j_input), "Jasmin input guards");
    require(GUARDS_OK(c_output), "official C output guards");
    require(GUARDS_OK(j_output), "Jasmin output guards");
    cases++;
    if (expected_status) failure_cases++; else success_cases++;
}

static uint32_t next_u32(uint32_t *state)
{
    uint32_t x = *state;
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    *state = x;
    return x;
}

static void standalone(void)
{
    uint8_t base[1152] = {0}, bytes[1152];
    uint16_t expected[768];
    const size_t positions[SELECTED_POSITIONS] = {0, 1, 384, 385, 766, 767};
    const uint16_t boundaries[] = {0, NTRUPLUS_Q - 1, NTRUPLUS_Q, 4095};
    uint32_t rng = UINT32_C(0x5ec9a731);

    group = "canonical-baseline";
    for (size_t i = 0; i < 768; i++) {
        expected[i] = (uint16_t)((97 * i + 13) % NTRUPLUS_Q);
        put12(base, i, expected[i]);
    }
    check_case(base, expected);

    group = "all-4096-values-first-middle-last-two-lanes";
    for (size_t k = 0; k < SELECTED_POSITIONS; k++) {
        position = positions[k];
        uint16_t saved = expected[position];
        for (value = 0; value < 4096; value++) {
            memcpy(bytes, base, sizeof bytes);
            put12(bytes, position, (uint16_t)value);
            expected[position] = (uint16_t)value;
            check_case(bytes, expected);
        }
        expected[position] = saved;
    }

    group = "four-boundaries-every-position";
    for (position = 0; position < 768; position++) {
        uint16_t saved = expected[position];
        for (size_t k = 0; k < sizeof boundaries / sizeof boundaries[0]; k++) {
            value = boundaries[k];
            memcpy(bytes, base, sizeof bytes);
            put12(bytes, position, (uint16_t)value);
            expected[position] = (uint16_t)value;
            check_case(bytes, expected);
        }
        expected[position] = saved;
    }

    group = "whole-array-patterns";
    for (unsigned pattern = 0; pattern < 5; pattern++) {
        memset(bytes, 0, sizeof bytes);
        for (position = 0; position < 768; position++) {
            value = pattern == 0 ? 4095u : pattern == 1 ?
                ((position & 1u) ? NTRUPLUS_Q - 1u : NTRUPLUS_Q) : pattern == 2 ?
                ((position == 0 || position == 767) ? NTRUPLUS_Q : 0u) :
                pattern == 3 ? 0u : NTRUPLUS_Q - 1u;
            expected[position] = (uint16_t)value;
            put12(bytes, position, expected[position]);
        }
        check_case(bytes, expected);
    }

    group = "constant-byte-patterns";
    for (value = 0; value < 256; value++) {
        memset(bytes, (int)value, sizeof bytes);
        bit_oracle(bytes, expected);
        check_case(bytes, expected);
    }

    group = "deterministic-random-bytes";
    for (value = 0; value < RANDOM_CASES; value++) {
        for (size_t i = 0; i < sizeof bytes; i++) bytes[i] = (uint8_t)next_u32(&rng);
        bit_oracle(bytes, expected);
        check_case(bytes, expected);
    }

    group = "deterministic-random-canonical-values";
    for (value = 0; value < RANDOM_CASES; value++) {
        memset(bytes, 0, sizeof bytes);
        for (position = 0; position < 768; position++) {
            expected[position] = (uint16_t)(next_u32(&rng) % NTRUPLUS_Q);
            put12(bytes, position, expected[position]);
        }
        check_case(bytes, expected);
    }

    require(cases == 36102 && success_cases > 0 && failure_cases > 0, "complete coverage and both statuses");
}

typedef struct { uint8_t seed[48], pk[1152], sk[2336], ct[1152], ss[32]; } kat_case;
static kat_case kats[100];
static uint64_t kat_api_runs, valid_api_pairs, invalid_public_pairs, invalid_derand_pairs;
static uint64_t valid_decaps, uninitialized_native_api_runs;

static unsigned hex_digit(char c)
{
    if (c >= '0' && c <= '9') return (unsigned)(c - '0');
    if (c >= 'A' && c <= 'F') return (unsigned)(c - 'A' + 10);
    if (c >= 'a' && c <= 'f') return (unsigned)(c - 'a' + 10);
    require(0, "invalid official KAT hex digit");
    return 0;
}

static void read_hex(FILE *stream, const char *name, uint8_t *out, size_t n)
{
    char line[5000];
    require(fgets(line, sizeof line, stream) != NULL, "KAT field present");
    size_t prefix = strlen(name);
    require(strncmp(line,name,prefix)==0 && strncmp(line+prefix," = ",3)==0, "KAT field label");
    const char *hex = line + prefix + 3;
    require(strcspn(hex,"\r\n") == 2*n, "KAT field byte length");
    for (size_t i=0;i<n;i++) out[i]=(uint8_t)(16*hex_digit(hex[2*i])+hex_digit(hex[2*i+1]));
}

static void load_kats(const char *path)
{
    FILE *stream=fopen(path,"r");
    require(stream != NULL,"open official KAT fixture");
    char line[5000];
    unsigned count=0;
    while(fgets(line,sizeof line,stream)) {
        if(strncmp(line,"count = ",8)!=0) continue;
        require(count<100 && strtoul(line+8,NULL,10)==count,"100 ordered KAT counts");
        read_hex(stream,"seed",kats[count].seed,48);
        read_hex(stream,"pk",kats[count].pk,1152);
        read_hex(stream,"sk",kats[count].sk,2336);
        read_hex(stream,"ct",kats[count].ct,1152);
        read_hex(stream,"ss",kats[count].ss,32);
        count++;
    }
    require(count==100 && !ferror(stream),"complete official KAT fixture");
    require(fclose(stream)==0,"close KAT fixture");
}

static void check_trace(int mixed, int public_api, int failed)
{
    char expected[32];
    snprintf(expected,sizeof expected,"%s%c%s", public_api?"R":"", mixed?'J':'D',
             failed?"":"FHCNTGENBT");
    require(strcmp(trace.events,expected)==0,"exact validation/continuation event order");
    require(trace.random_calls==(unsigned)public_api,"public wrapper consumes RNG once, derand never");
    require(trace.random_bytes==(unsigned)(public_api?96:0),"public wrapper consumes 96 bytes");
    require(trace.guard_calls==(unsigned)mixed && trace.decoder_calls==(unsigned)!mixed,
            "exact one guard or official decoder dispatch");
    require(trace.success_calls==(unsigned)(failed?0:10),"rejected pk never reaches success dependencies");
}

static void kat_api(const kat_case *kat, int mixed, int uninitialized)
{
    guarded_input pk,ct;
    guarded_sk sk;
    guarded_ss ss, recovered;
    memset(&pk,0xa5,sizeof pk); memset(&sk,0xa5,sizeof sk);
    memset(ct.pre,0xa5,GUARD); memset(ct.post,0xa5,GUARD);
    memset(ss.pre,0xa5,GUARD); memset(ss.post,0xa5,GUARD);
    if(!uninitialized) { memset(ct.data,0x73,1152); memset(ss.data,0x49,32); }
    seed_rng(kat->seed);
    require((mixed?mixed_keypair:official_keypair)(pk.data,sk.data)==0,"KAT keypair success");
    require(memcmp(pk.data,kat->pk,1152)==0 && memcmp(sk.data,kat->sk,2336)==0,"KAT exact pk and sk");
    trace_reset();
    require((mixed?mixed_enc:official_enc)(ct.data,ss.data,pk.data)==0,"KAT full public Encaps success");
    check_trace(mixed,1,0);
    require(memcmp(ct.data,kat->ct,1152)==0 && memcmp(ss.data,kat->ss,32)==0,"KAT exact ciphertext and shared secret");
    require(memcmp(pk.data,kat->pk,1152)==0 && memcmp(sk.data,kat->sk,2336)==0,"KAT public and secret inputs unchanged");
    for(int decoder=0;decoder<2;decoder++) {
        memset(&recovered,0xa5,sizeof recovered);
        require((decoder?mixed_dec:official_dec)(recovered.data,ct.data,sk.data)==0,"KAT actual C decapsulation success");
        require(memcmp(recovered.data,kat->ss,32)==0 && GUARDS_OK(recovered),"KAT decapsulation shared secret and guards");
        valid_decaps++;
    }
    require(GUARDS_OK(pk)&&GUARDS_OK(sk)&&GUARDS_OK(ct)&&GUARDS_OK(ss),"KAT all buffer guards");
    require(memcmp(ct.data,kat->ct,1152)==0 && memcmp(sk.data,kat->sk,2336)==0,"KAT decapsulation inputs unchanged");
    if(uninitialized) uninitialized_native_api_runs++; else kat_api_runs++;
}

static void api_pair(const uint8_t input[1152], const uint8_t *sk, int public_api,
                     int failed, uint32_t nonce)
{
    guarded_input pk[2],ct[2];
    guarded_ss ss[2], recovered;
    uint8_t seed[48],coins[96],coins_before[96],seed_before[48];
    uint32_t rng=UINT32_C(0x81775a31)^nonce;
    for(size_t i=0;i<48;i++) seed[i]=(uint8_t)next_u32(&rng);
    for(size_t i=0;i<96;i++) coins[i]=(uint8_t)next_u32(&rng);
    memcpy(coins_before,coins,sizeof coins); memcpy(seed_before,seed,sizeof seed);
    for(int implementation=0;implementation<2;implementation++) {
        memset(&pk[implementation],0xa5,sizeof pk[implementation]);
        memset(&ct[implementation],0xa5,sizeof ct[implementation]);
        memset(&ss[implementation],0xa5,sizeof ss[implementation]);
        memcpy(pk[implementation].data,input,1152);
        for(size_t i=0;i<1152;i++) ct[implementation].data[i]=(uint8_t)next_u32(&rng);
        for(size_t i=0;i<32;i++) ss[implementation].data[i]=(uint8_t)next_u32(&rng);
        seed_rng(seed);
        trace_reset();
        int result=public_api ? (implementation?mixed_enc:official_enc)(ct[implementation].data,ss[implementation].data,pk[implementation].data) :
            (implementation?mixed_derand:official_derand)(ct[implementation].data,ss[implementation].data,pk[implementation].data,coins);
        require(result==failed,"full API exact status");
        check_trace(implementation,public_api,failed);
        if(failed) {
            require(all_byte(ct[implementation].data,1152,0)&&all_byte(ss[implementation].data,32,0),"full API invalid outputs all zero");
        } else if(sk) {
            memset(&recovered,0xa5,sizeof recovered);
            require(official_dec(recovered.data,ct[implementation].data,sk)==0,"random full Encaps decapsulates");
            require(memcmp(recovered.data,ss[implementation].data,32)==0 && GUARDS_OK(recovered),"random full API shared secret and guards");
            valid_decaps++;
        }
        require(memcmp(pk[implementation].data,input,1152)==0,"full API pk input unchanged");
        require(GUARDS_OK(pk[implementation])&&GUARDS_OK(ct[implementation])&&GUARDS_OK(ss[implementation]),"full API all buffer guards");
    }
    require(memcmp(coins,coins_before,sizeof coins)==0 && memcmp(seed,seed_before,sizeof seed)==0,"randomness inputs unchanged");
    require(memcmp(ct[0].data,ct[1].data,1152)==0 && memcmp(ss[0].data,ss[1].data,32)==0,"full official/mixed API outputs equal");
    if(!failed) valid_api_pairs++;
    else if(public_api) invalid_public_pairs++;
    else invalid_derand_pairs++;
}

static void integration(void)
{
    group="official-100-KAT-public-API-and-decapsulation";
    for(unsigned k=0;k<100;k++) for(int mixed=0;mixed<2;mixed++) kat_api(&kats[k],mixed,0);
    group="native-uninitialized-output-observation-not-formal-contract";
    for(int mixed=0;mixed<2;mixed++) kat_api(&kats[0],mixed,1);
    group="every-coefficient-early-and-late-invalid-public-and-derand";
    uint8_t bytes[1152],seed[48],pk[1152],sk[2336];
    for(position=0;position<768;position++) {
        for(value=3457;value<=4095;value+=638) {
            memcpy(bytes,kats[0].pk,1152); put12(bytes,position,(uint16_t)value);
            for(int public_api=0;public_api<2;public_api++)
                api_pair(bytes,NULL,public_api,1,(uint32_t)(position*4096+value));
        }
    }
    group="random-invalid-full-API";
    uint32_t rng=UINT32_C(0x68a37f25);
    for(unsigned k=0;k<128;k++) {
        for(size_t i=0;i<1152;i++) bytes[i]=(uint8_t)next_u32(&rng);
        put12(bytes,767,4095); /* late rejection is guaranteed */
        for(int public_api=0;public_api<2;public_api++) api_pair(bytes,NULL,public_api,1,k+8192);
    }
    group="random-valid-keypairs-public-and-derand";
    for(unsigned k=0;k<32;k++) {
        for(size_t i=0;i<48;i++) seed[i]=(uint8_t)next_u32(&rng);
        seed_rng(seed); require(official_keypair(pk,sk)==0,"random keypair");
        for(int public_api=0;public_api<2;public_api++) api_pair(pk,sk,public_api,0,k+16384);
    }
}

int main(int argc,char **argv)
{
    require(argc==2,"usage: encap-guard-test official-KAT.rsp");
    load_kats(argv[1]);
    standalone();
    integration();
    require(kat_api_runs==200 && valid_api_pairs==64 && invalid_public_pairs==1664 &&
            invalid_derand_pairs==1664 && valid_decaps==532 && uninitialized_native_api_runs==2,
            "complete integration coverage");
    printf("{\"status\":\"PASS\",\"guard_cases\":%" PRIu64 ",\"guard_success_cases\":%" PRIu64
           ",\"guard_failure_cases\":%" PRIu64 ",\"kat_api_runs\":%" PRIu64
           ",\"valid_api_pairs\":%" PRIu64 ",\"invalid_public_pairs\":%" PRIu64
           ",\"invalid_derand_pairs\":%" PRIu64 ",\"valid_decaps\":%" PRIu64
           ",\"uninitialized_native_api_runs\":%" PRIu64 ",\"assertions\":%" PRIu64 "}\n",
           cases,success_cases,failure_cases,kat_api_runs,valid_api_pairs,invalid_public_pairs,
           invalid_derand_pairs,valid_decaps,uninitialized_native_api_runs,assertions);
    return EXIT_SUCCESS;
}
