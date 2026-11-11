#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "trace.h"

enum { GUARD = 32, N = 768, BYTES = 1152, SKBYTES = 2336 };
_Static_assert(NTRUPLUS_N == N && NTRUPLUS_Q == 3457, "official NTRU+768 parameters");
_Static_assert(NTRUPLUS_POLYBYTES == BYTES && sizeof(poly) == 1536, "reference layout");
typedef struct { uint8_t pre[GUARD], data[BYTES], post[GUARD]; } guarded_input;
typedef struct { uint8_t pre[GUARD], data[SKBYTES], post[GUARD]; } guarded_sk;
typedef struct { uint8_t pre[GUARD], data[2 * BYTES], post[GUARD]; } guarded_skpoly;
typedef struct { uint8_t pre[GUARD]; poly data; uint8_t post[GUARD]; } guarded_poly;
typedef struct { uint8_t pre[GUARD], data[32], post[GUARD]; } guarded_ss;
static uint64_t assertions, cases, success_cases, rejection_stage[3];
static uint64_t kat_api_runs, malformed_api_pairs, canonical_api_pairs, fresh_api_pairs;
static const char *group = "initialization";
static size_t position;
static unsigned value, component;
static void require(int condition, const char *message)
{
    assertions++;
    if (!condition) {
        fprintf(stderr, "FAIL group=%s component=%u position=%zu value=%u case=%" PRIu64 ": %s\n",
                group, component, position, value, cases, message);
        exit(EXIT_FAILURE);
    }
}
static int all_byte(const uint8_t *p, size_t n, uint8_t v)
{ for (size_t i = 0; i < n; i++) if (p[i] != v) return 0; return 1; }
#define GUARDS_OK(x) (all_byte((x).pre, GUARD, 0xa5) && all_byte((x).post, GUARD, 0xa5))
static uint32_t next_u32(uint32_t *state)
{ uint32_t x = *state; x ^= x << 13; x ^= x >> 17; x ^= x << 5; return *state = x; }
/* Independent bit-stream oracle, not a copy of paired decoder shifts. */
static void put12(uint8_t bytes[BYTES], size_t index, uint16_t coefficient)
{
    require(index < N && coefficient < 4096, "fixture encoding bounds");
    for (unsigned bit = 0; bit < 12; bit++) {
        size_t offset = 12 * index + bit;
        uint8_t mask = (uint8_t)(1u << (offset % 8));
        bytes[offset / 8] = (uint8_t)((bytes[offset / 8] & (uint8_t)~mask) |
            ((coefficient & (1u << bit)) ? mask : 0u));
    }
}
static int decode_oracle(const uint8_t bytes[BYTES], uint16_t expected[N])
{
    int invalid = 0;
    for (size_t i = 0; i < N; i++) {
        uint16_t x = 0;
        for (unsigned bit = 0; bit < 12; bit++) {
            size_t offset = 12 * i + bit;
            x |= (uint16_t)(((bytes[offset / 8] >> (offset % 8)) & 1u) << bit);
        }
        expected[i] = x; invalid |= x >= NTRUPLUS_Q;
    }
    return invalid;
}
static int disjoint(const void *a, size_t an, const void *b, size_t bn)
{ uintptr_t x = (uintptr_t)a, y = (uintptr_t)b; return x + an <= y || y + bn <= x; }
static void check_case(const uint8_t inputs[3][BYTES])
{
    guarded_input ct[2]; guarded_skpoly sk[2]; guarded_ss ss[2];
    guarded_poly out[2][3]; uint16_t expected[3][N], initial[3][N]; uint8_t initial_ss[32];
    int bad[3], first = 3;
    for (unsigned k = 0; k < 3; k++) {
        bad[k] = decode_oracle(inputs[k], expected[k]);
        if (bad[k] && first == 3) first = (int)k;
    }
    uint32_t rng = UINT32_C(0x421995ab) ^ (uint32_t)(cases + 1);
    for (size_t i = 0; i < 32; i++) initial_ss[i] = (uint8_t)next_u32(&rng);
    for (unsigned k = 0; k < 3; k++) for (size_t i = 0; i < N; i++)
        initial[k][i] = (uint16_t)(next_u32(&rng) & 32767u);
    for (int impl = 0; impl < 2; impl++) {
        memset(&ct[impl], 0xa5, sizeof ct[impl]); memset(&sk[impl], 0xa5, sizeof sk[impl]);
        memset(&ss[impl], 0xa5, sizeof ss[impl]);
        memcpy(ct[impl].data, inputs[0], BYTES);
        memcpy(sk[impl].data, inputs[1], BYTES); memcpy(sk[impl].data + BYTES, inputs[2], BYTES);
        memcpy(ss[impl].data, initial_ss, 32);
        for (unsigned k = 0; k < 3; k++) {
            memset(&out[impl][k], 0xa5, sizeof out[impl][k]);
            memcpy(out[impl][k].data.coeffs, initial[k], sizeof initial[k]);
            require((uintptr_t)out[impl][k].data.coeffs % _Alignof(uint16_t) == 0, "u16 output alignment");
        }
        const void *regions[] = {&out[impl][0].data, &out[impl][1].data, &out[impl][2].data,
                                 ss[impl].data, ct[impl].data, sk[impl].data};
        const size_t sizes[] = {1536, 1536, 1536, 32, BYTES, 2 * BYTES};
        for (unsigned a = 0; a < 6; a++) for (unsigned b = a + 1; b < 6; b++)
            require(disjoint(regions[a], sizes[a], regions[b], sizes[b]), "all six buffers disjoint");
        trace_reset();
        int status = impl ? (int)jade_ntruplus_ntruplus768_amd64_ref_decap_guard(
            (uint16_t *)out[impl][0].data.coeffs, (uint16_t *)out[impl][1].data.coeffs,
            (uint16_t *)out[impl][2].data.coeffs, ss[impl].data, ct[impl].data, sk[impl].data) :
            official_prefix(&out[impl][0].data, &out[impl][1].data, &out[impl][2].data,
                            ss[impl].data, ct[impl].data, sk[impl].data);
        require(status == (first != 3), "exact binary guard status");
        if (!impl) require(trace.decoder_calls == (unsigned)(first == 3 ? 3 : first + 1),
                           "official guard short circuit decoder count");
        for (unsigned k = 0; k < 3; k++) {
            const uint16_t *want = (int)k <= first ? expected[k] : initial[k];
            require(memcmp(out[impl][k].data.coeffs, want, sizeof expected[k]) == 0,
                    "complete decoded output or untouched later output");
            require(GUARDS_OK(out[impl][k]), "polynomial output canaries");
        }
        require(first == 3 ? memcmp(ss[impl].data, initial_ss, 32) == 0 : all_byte(ss[impl].data, 32, 0),
                "all 32 secret bytes zero on rejection; arbitrary original secret preserved on acceptance");
        require(memcmp(ct[impl].data, inputs[0], BYTES) == 0 &&
                memcmp(sk[impl].data, inputs[1], BYTES) == 0 &&
                memcmp(sk[impl].data + BYTES, inputs[2], BYTES) == 0, "all input bytes unchanged");
        require(GUARDS_OK(ct[impl]) && GUARDS_OK(sk[impl]) && GUARDS_OK(ss[impl]), "input and shared secret canaries");
    }
    require(memcmp(ss[0].data, ss[1].data, 32) == 0, "C/Jasmin shared secret equality");
    for (unsigned k = 0; k < 3; k++)
        require(memcmp(&out[0][k].data, &out[1][k].data, sizeof(poly)) == 0, "C/Jasmin polynomial equality");
    cases++; if (first == 3) success_cases++; else rejection_stage[first]++;
}
static void standalone(void)
{
    uint8_t base[3][BYTES] = {{0}}, bytes[3][BYTES];
    const size_t positions[] = {0, 1, 384, 385, 766, 767};
    const uint16_t boundaries[] = {0, 3456, 3457, 4095};
    uint32_t rng = UINT32_C(0x489113af);
    group = "canonical-baseline";
    for (unsigned k = 0; k < 3; k++) for (size_t i = 0; i < N; i++)
        put12(base[k], i, (uint16_t)((97 * i + 29 * k + 13) % NTRUPLUS_Q));
    check_case((const uint8_t (*)[BYTES])base);
    group = "4096-values-first-middle-last-two-lanes-each-component";
    for (component = 0; component < 3; component++) for (unsigned p = 0; p < 6; p++) {
        position = positions[p];
        for (value = 0; value < 4096; value++) {
            memcpy(bytes, base, sizeof bytes); put12(bytes[component], position, (uint16_t)value);
            check_case((const uint8_t (*)[BYTES])bytes);
        }
    }
    group = "four-boundaries-every-coefficient-each-component";
    for (component = 0; component < 3; component++) for (position = 0; position < N; position++)
        for (unsigned v = 0; v < 4; v++) {
            value = boundaries[v]; memcpy(bytes, base, sizeof bytes);
            put12(bytes[component], position, (uint16_t)value); check_case((const uint8_t (*)[BYTES])bytes);
        }
    group = "all-seven-multiple-invalid-combinations-first-and-last-lanes";
    for (unsigned mask = 1; mask < 8; mask++) for (unsigned p = 0; p < 6; p++) {
        memcpy(bytes, base, sizeof bytes);
        for (component = 0; component < 3; component++) if (mask & (1u << component))
            put12(bytes[component], positions[p], 4095);
        check_case((const uint8_t (*)[BYTES])bytes);
    }
    group = "constant-byte-patterns-each-component";
    for (component = 0; component < 3; component++) for (value = 0; value < 256; value++) {
        memcpy(bytes, base, sizeof bytes); memset(bytes[component], (int)value, BYTES);
        check_case((const uint8_t (*)[BYTES])bytes);
    }
    group = "random-canonical-arrays";
    for (unsigned n = 0; n < 1024; n++) {
        memset(bytes, 0, sizeof bytes);
        for (component = 0; component < 3; component++) for (position = 0; position < N; position++)
            put12(bytes[component], position, (uint16_t)(next_u32(&rng) % NTRUPLUS_Q));
        check_case((const uint8_t (*)[BYTES])bytes);
    }
    group = "random-bytes-each-component";
    for (component = 0; component < 3; component++) for (unsigned n = 0; n < 1024; n++) {
        memcpy(bytes, base, sizeof bytes);
        for (size_t i = 0; i < BYTES; i++) bytes[component][i] = (uint8_t)next_u32(&rng);
        check_case((const uint8_t (*)[BYTES])bytes);
    }
    require(cases == 87851 && success_cases > 0 && rejection_stage[0] > 0 &&
            rejection_stage[1] > 0 && rejection_stage[2] > 0, "complete standalone coverage");
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
static int first_invalid(const uint8_t ct[BYTES], const uint8_t sk[SKBYTES])
{
    uint16_t decoded[N];
    if (decode_oracle(ct, decoded)) return 0;
    if (decode_oracle(sk, decoded)) return 1;
    if (decode_oracle(sk + BYTES, decoded)) return 2;
    return 3;
}
static void check_trace(int mixed, int first)
{
    char expected[64];
    const char *decoders = first == 0 ? "D" : first == 1 ? "DD" : "DDD";
    snprintf(expected, sizeof expected, "%s%s", mixed ? "J" : decoders,
             first == 3 ? "BIMNUBTGSHCNT" : "");
    require(strcmp(trace.events, expected) == 0, "exact short circuit and continuation event order");
    require(trace.guard_calls == (unsigned)mixed, "exact guard call count");
    require(trace.decoder_calls == (unsigned)(mixed ? 0 : first == 3 ? 3 : first + 1), "exact decoder count");
    require(trace.random_calls == 0 && trace.random_bytes == 0, "Decaps consumes no randomness");
    require(trace.success_calls == (unsigned)(first == 3 ? 13 : 0), "rejection invokes no success dependencies");
}
static void api_pair(const uint8_t ct0[BYTES], const uint8_t sk0[SKBYTES], const uint8_t *valid_ss)
{
    guarded_input ct[2]; guarded_sk sk[2]; guarded_ss ss[2]; int status[2];
    int first = first_invalid(ct0, sk0);
    for (int impl = 0; impl < 2; impl++) {
        memset(&ct[impl], 0xa5, sizeof ct[impl]); memset(&sk[impl], 0xa5, sizeof sk[impl]);
        memset(&ss[impl], 0xa5, sizeof ss[impl]); memcpy(ct[impl].data, ct0, BYTES);
        memcpy(sk[impl].data, sk0, SKBYTES); trace_reset();
        status[impl] = (impl ? mixed_dec : official_dec)(ss[impl].data, ct[impl].data, sk[impl].data);
        check_trace(impl, first);
        require(status[impl] == 0 || status[impl] == 1, "full Decaps status binary");
        if (first != 3) require(status[impl] == 1, "malformed encoding rejected");
        if (status[impl]) require(all_byte(ss[impl].data, 32, 0), "all Decaps failure secret bytes zero");
        if (valid_ss) require(status[impl] == 0 && memcmp(ss[impl].data, valid_ss, 32) == 0, "valid Decaps expected secret");
        require(memcmp(ct[impl].data, ct0, BYTES) == 0 && memcmp(sk[impl].data, sk0, SKBYTES) == 0,
                "full Decaps inputs unchanged");
        require(GUARDS_OK(ct[impl]) && GUARDS_OK(sk[impl]) && GUARDS_OK(ss[impl]), "full Decaps all canaries");
    }
    require(status[0] == status[1] && memcmp(ss[0].data, ss[1].data, 32) == 0, "full C/mixed Decaps equality");
    if (first != 3) malformed_api_pairs++; else canonical_api_pairs++;
}
static void integration(void)
{
    group = "official-100-KAT-all-three-APIs";
    for (unsigned k = 0; k < 100; k++) {
        for (int impl = 0; impl < 2; impl++) {
            guarded_input pk, ct; guarded_sk sk; guarded_ss ss;
            memset(&pk, 0xa5, sizeof pk); memset(&ct, 0xa5, sizeof ct);
            memset(&sk, 0xa5, sizeof sk); memset(&ss, 0xa5, sizeof ss);
            trace_reset(); seed_rng(kats[k].seed);
            require((impl ? mixed_keypair : official_keypair)(pk.data, sk.data) == 0, "KAT keypair success");
            require(memcmp(pk.data, kats[k].pk, BYTES) == 0 && memcmp(sk.data, kats[k].sk, SKBYTES) == 0, "KAT exact keys");
            trace_reset();
            require((impl ? mixed_enc : official_enc)(ct.data, ss.data, pk.data) == 0, "KAT Encaps success");
            require(memcmp(ct.data, kats[k].ct, BYTES) == 0 && memcmp(ss.data, kats[k].ss, 32) == 0, "KAT exact ciphertext and secret");
            require(GUARDS_OK(pk) && GUARDS_OK(ct) && GUARDS_OK(sk) && GUARDS_OK(ss), "KAT API canaries");
            kat_api_runs++;
        }
        api_pair(kats[k].ct, kats[k].sk, kats[k].ss);
    }
    uint8_t ct[BYTES], sk[SKBYTES];
    group = "malformed-every-coefficient-each-component";
    for (component = 0; component < 3; component++) for (position = 0; position < N; position++)
        for (value = 3457; value <= 4095; value += 638) {
            memcpy(ct, kats[0].ct, BYTES); memcpy(sk, kats[0].sk, SKBYTES);
            put12(component == 0 ? ct : sk + (component - 1) * BYTES, position, (uint16_t)value);
            api_pair(ct, sk, NULL);
        }
    group = "malformed-multiple-components-first-and-last";
    for (unsigned mask = 1; mask < 8; mask++) for (unsigned side = 0; side < 2; side++) {
        memcpy(ct, kats[0].ct, BYTES); memcpy(sk, kats[0].sk, SKBYTES);
        for (component = 0; component < 3; component++) if (mask & (1u << component))
            put12(component == 0 ? ct : sk + (component - 1) * BYTES, side ? 767 : 0, 4095);
        api_pair(ct, sk, NULL);
    }
    group = "canonical-ciphertext-and-secret-key-tampering";
    uint32_t rng = UINT32_C(0x46723189);
    for (component = 0; component < 3; component++) for (unsigned n = 0; n < 64; n++) {
        memcpy(ct, kats[n % 100].ct, BYTES); memcpy(sk, kats[n % 100].sk, SKBYTES);
        put12(component == 0 ? ct : sk + (component - 1) * BYTES, next_u32(&rng) % N,
              (uint16_t)(next_u32(&rng) % NTRUPLUS_Q));
        api_pair(ct, sk, NULL);
    }
    group = "secret-key-hash-tail-tampering";
    for (unsigned n = 0; n < 32; n++) {
        memcpy(sk, kats[0].sk, SKBYTES); sk[2 * BYTES + n] ^= 1;
        api_pair(kats[0].ct, sk, NULL);
    }
    group = "fresh-keypairs-and-encapsulations";
    for (unsigned n = 0; n < 32; n++) {
        uint8_t seed[48], pk[BYTES], ss[32];
        for (unsigned i = 0; i < 48; i++) seed[i] = (uint8_t)next_u32(&rng);
        trace_reset(); seed_rng(seed); require(official_keypair(pk, sk) == 0, "fresh keypair");
        trace_reset(); require(official_enc(ct, ss, pk) == 0, "fresh Encaps");
        api_pair(ct, sk, ss); fresh_api_pairs++;
    }
    require(kat_api_runs == 200 && malformed_api_pairs == 4622 && canonical_api_pairs == 356 &&
            fresh_api_pairs == 32, "complete integration coverage");
}
int main(int argc, char **argv)
{
    require(argc == 2, "usage: decap-guard-test official-KAT.rsp");
    load_kats(argv[1]); standalone(); integration();
    printf("{\"status\":\"PASS\",\"guard_cases\":%" PRIu64 ",\"guard_success_cases\":%" PRIu64
           ",\"ct_rejection_cases\":%" PRIu64 ",\"f_rejection_cases\":%" PRIu64 ",\"h_rejection_cases\":%" PRIu64
           ",\"kat_api_runs\":%" PRIu64 ",\"malformed_api_pairs\":%" PRIu64 ",\"canonical_api_pairs\":%" PRIu64
           ",\"fresh_api_pairs\":%" PRIu64 ",\"assertions\":%" PRIu64 "}\n",
           cases, success_cases, rejection_stage[0], rejection_stage[1], rejection_stage[2],
           kat_api_runs, malformed_api_pairs, canonical_api_pairs, fresh_api_pairs, assertions);
    return 0;
}
