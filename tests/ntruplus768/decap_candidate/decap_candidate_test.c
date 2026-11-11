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
typedef struct { uint8_t pre[GUARD]; poly data; uint8_t post[GUARD]; } guarded_poly;
typedef struct { uint8_t pre[GUARD], data[32], post[GUARD]; } guarded_ss;
static uint64_t assertions, cases;
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
static void check_candidate(const poly *c0, const poly *f0)
{
    guarded_poly c, f, output, expected;
    memset(&c, 0xa5, sizeof c); memset(&f, 0xa5, sizeof f);
    memset(&output, 0xa5, sizeof output); memset(&expected, 0xa5, sizeof expected);
    c.data = *c0; f.data = *f0;
    require((uintptr_t)c.data.coeffs % _Alignof(uint16_t) == 0 &&
            (uintptr_t)f.data.coeffs % _Alignof(uint16_t) == 0 &&
            (uintptr_t)output.data.coeffs % _Alignof(uint16_t) == 0, "u16 alignment");
    require(disjoint(&c.data, sizeof(poly), &f.data, sizeof(poly)) &&
            disjoint(&c.data, sizeof(poly), &output.data, sizeof(poly)) &&
            disjoint(&f.data, sizeof(poly), &output.data, sizeof(poly)), "three disjoint buffers");
    for (unsigned i = 0; i < N; i++) {
        require(c.data.coeffs[i] >= 0 && c.data.coeffs[i] < NTRUPLUS_Q &&
                f.data.coeffs[i] >= 0 && f.data.coeffs[i] < NTRUPLUS_Q, "canonical inputs");
        output.data.coeffs[i] = (int16_t)(i % 2 ? 0x1234 : -0x1234);
    }
    poly_basemul(&expected.data, &c.data, &f.data);
    poly_invntt(&expected.data); poly_crepmod3(&expected.data);
    jade_ntruplus_ntruplus768_amd64_ref_decap_candidate((uint16_t *)output.data.coeffs,
        (const uint16_t *)c.data.coeffs, (const uint16_t *)f.data.coeffs);
    require(memcmp(&output.data, &expected.data, sizeof(poly)) == 0, "exact candidate C/Jasmin equality");
    for (unsigned i = 0; i < N; i++)
        require(output.data.coeffs[i] >= -1 && output.data.coeffs[i] <= 1, "ternary output range");
    require(memcmp(&c.data, c0, sizeof(poly)) == 0 && memcmp(&f.data, f0, sizeof(poly)) == 0,
            "all input coefficients preserved");
    require(GUARDS_OK(c) && GUARDS_OK(f) && GUARDS_OK(output) && GUARDS_OK(expected), "all polynomial canaries");
    cases++;
}
static void standalone(void)
{
    poly c = {{0}}, f = {{0}}, baseline[2];
    const int16_t bounds[] = {0, 1, 1728, 1729, 3455, 3456};
    const unsigned positions[] = {0, 3, 4, 383, 384, 763, 764, 767};
    uint32_t rng = UINT32_C(0x74be156d);
    group = "constant-boundary-products";
    for (unsigned a = 0; a < 6; a++) for (unsigned b = 0; b < 6; b++) {
        for (unsigned i = 0; i < N; i++) { c.coeffs[i] = bounds[a]; f.coeffs[i] = bounds[b]; }
        check_candidate(&c, &f);
    }
    for (unsigned k = 0; k < 2; k++) for (unsigned i = 0; i < N; i++)
        baseline[k].coeffs[i] = (int16_t)((97 * i + 183 * k + 23) % NTRUPLUS_Q);
    group = "every-coefficient-six-boundaries-both-inputs";
    for (component = 0; component < 2; component++) for (position = 0; position < N; position++)
        for (unsigned b = 0; b < 6; b++) {
            c = baseline[0]; f = baseline[1]; value = (unsigned)bounds[b];
            (component ? f.coeffs : c.coeffs)[position] = bounds[b]; check_candidate(&c, &f);
        }
    group = "every-canonical-value-eight-terminal-block-lanes-both-inputs";
    for (component = 0; component < 2; component++) for (unsigned p = 0; p < 8; p++) {
        position = positions[p];
        for (value = 0; value < NTRUPLUS_Q; value++) {
            c = baseline[0]; f = baseline[1];
            (component ? f.coeffs : c.coeffs)[position] = (int16_t)value; check_candidate(&c, &f);
        }
    }
    group = "sparse-polynomials-every-position";
    for (position = 0; position < N; position++) {
        memset(&c, 0, sizeof c); memset(&f, 0, sizeof f);
        c.coeffs[position] = 3456; f.coeffs[(position * 17 + 3) % N] = 3456; check_candidate(&c, &f);
    }
    group = "deterministic-random-canonical-pairs";
    for (unsigned n = 0; n < 4096; n++) {
        for (unsigned i = 0; i < N; i++) {
            c.coeffs[i] = (int16_t)(next_u32(&rng) % NTRUPLUS_Q);
            f.coeffs[i] = (int16_t)(next_u32(&rng) % NTRUPLUS_Q);
        }
        check_candidate(&c, &f);
    }
    require(cases == 69428, "complete standalone coverage");
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
static void check_trace(int impl, int first)
{
    char expected[64];
    const char *decoders = first == 0 ? "D" : first == 1 ? "DD" : "DDD";
    snprintf(expected, sizeof expected, "%s%s", impl == 2 ? "J" : decoders,
             first == 3 ? (impl ? "QNUBTGSHCNT" : "BIMNUBTGSHCNT") : "");
    require(strcmp(trace.events, expected) == 0, "exact short circuit and continuation event order");
    require(trace.guard_calls == (unsigned)(impl == 2), "exact guard call count");
    require(trace.candidate_calls == (unsigned)(impl != 0 && first == 3), "candidate called exactly once iff mixed guard accepts");
    require(trace.decoder_calls == (unsigned)(impl == 2 ? 0 : first == 3 ? 3 : first + 1), "exact decoder count");
    require(trace.random_calls == 0 && trace.random_bytes == 0, "Decaps consumes no randomness");
    require(trace.success_calls == (unsigned)(first == 3 ? (impl ? 10 : 13) : 0), "rejection invokes no normal dependencies");
}
static void api_pair(const uint8_t ct0[BYTES], const uint8_t sk0[SKBYTES], const uint8_t *valid_ss)
{
    guarded_input ct[3]; guarded_sk sk[3]; guarded_ss ss[3]; int status[3];
    int first = first_invalid(ct0, sk0);
    for (int impl = 0; impl < 3; impl++) {
        memset(&ct[impl], 0xa5, sizeof ct[impl]); memset(&sk[impl], 0xa5, sizeof sk[impl]);
        memset(&ss[impl], 0xa5, sizeof ss[impl]); memcpy(ct[impl].data, ct0, BYTES);
        memcpy(sk[impl].data, sk0, SKBYTES); trace_reset();
        status[impl] = (impl == 2 ? both_dec : impl == 1 ? mixed_dec : official_dec)(ss[impl].data, ct[impl].data, sk[impl].data);
        check_trace(impl, first);
        require(status[impl] == 0 || status[impl] == 1, "full Decaps status binary");
        if (first != 3) require(status[impl] == 1, "malformed encoding rejected");
        if (status[impl]) require(all_byte(ss[impl].data, 32, 0), "all Decaps failure secret bytes zero");
        if (valid_ss) require(status[impl] == 0 && memcmp(ss[impl].data, valid_ss, 32) == 0, "valid Decaps expected secret");
        require(memcmp(ct[impl].data, ct0, BYTES) == 0 && memcmp(sk[impl].data, sk0, SKBYTES) == 0,
                "full Decaps inputs unchanged");
        require(GUARDS_OK(ct[impl]) && GUARDS_OK(sk[impl]) && GUARDS_OK(ss[impl]), "full Decaps all canaries");
        if (impl) require(status[0] == status[impl] && memcmp(ss[0].data, ss[impl].data, 32) == 0, "full official/mixed Decaps equality");
    }
    if (first != 3) malformed_api_pairs++; else canonical_api_pairs++;
}
static void integration(void)
{
    group = "official-100-KAT-all-three-APIs";
    for (unsigned k = 0; k < 100; k++) {
        for (int impl = 0; impl < 3; impl++) {
            guarded_input pk, ct; guarded_sk sk; guarded_ss ss;
            memset(&pk, 0xa5, sizeof pk); memset(&ct, 0xa5, sizeof ct);
            memset(&sk, 0xa5, sizeof sk); memset(&ss, 0xa5, sizeof ss);
            trace_reset(); seed_rng(kats[k].seed);
            require((impl == 2 ? both_keypair : impl == 1 ? mixed_keypair : official_keypair)(pk.data, sk.data) == 0, "KAT keypair success");
            require(memcmp(pk.data, kats[k].pk, BYTES) == 0 && memcmp(sk.data, kats[k].sk, SKBYTES) == 0, "KAT exact keys");
            trace_reset();
            require((impl == 2 ? both_enc : impl == 1 ? mixed_enc : official_enc)(ct.data, ss.data, pk.data) == 0, "KAT Encaps success");
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
    require(kat_api_runs == 300 && malformed_api_pairs == 4622 && canonical_api_pairs == 356 &&
            fresh_api_pairs == 32, "complete integration coverage");
}
int main(int argc, char **argv)
{
    require(argc == 2, "usage: decap-candidate-test official-KAT.rsp");
    load_kats(argv[1]); standalone(); integration();
    printf("{\"status\":\"PASS\",\"candidate_cases\":%" PRIu64
           ",\"kat_api_runs\":%" PRIu64 ",\"malformed_api_triples\":%" PRIu64 ",\"canonical_api_triples\":%" PRIu64
           ",\"fresh_api_triples\":%" PRIu64 ",\"assertions\":%" PRIu64 "}\n",
           cases, kat_api_runs, malformed_api_pairs, canonical_api_pairs, fresh_api_pairs, assertions);
    return 0;
}
