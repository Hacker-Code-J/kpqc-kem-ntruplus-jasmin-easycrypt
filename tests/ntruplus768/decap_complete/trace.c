#include <stdlib.h>
#include <string.h>
#include "trace.h"
#include "symmetric.h"
#include "fips202/fips202.h"

int kat_randombytes(unsigned char *, unsigned long long);
void randombytes_init(unsigned char *, unsigned char *, int);
call_trace trace;
uint8_t message_shake_input[1153], message_shake_output[192];
uint8_t hash_h_input[129], hash_h_output[224], decoded_message[96];
static void event(char label)
{
    if (trace.event_count + 1 < sizeof trace.events) {
        trace.events[trace.event_count] = label;
        trace.events[trace.event_count + 1] = 0;
    }
    trace.event_count++;
}
void trace_reset(void) { memset(&trace, 0, sizeof trace); }
void seed_rng(const uint8_t seed[48])
{
    uint8_t copy[48]; memcpy(copy, seed, sizeof copy);
    randombytes_init(copy, NULL, 256);
}
void trace_randombytes(uint8_t *out, size_t n)
{
    trace.random_calls++; trace.random_bytes += (unsigned)n; event('R');
    if (kat_randombytes(out, n)) abort();
}
int trace_poly_frombytes(poly *out, const uint8_t in[1152])
{ trace.decoder_calls++; event('D'); return poly_frombytes(out, in); }
uint32_t trace_guard(uint16_t *cp, uint16_t *fp, uint16_t *hp, uint8_t *ss,
                     const uint8_t *ct, const uint8_t *skpoly)
{
    trace.guard_calls++; event('J');
    return jade_ntruplus_ntruplus768_amd64_ref_decap_guard(cp, fp, hp, ss, ct, skpoly);
}
#define SUCCESS(label) do { trace.success_calls++; event(label); } while (0)
void trace_hash_f(uint8_t *out, const uint8_t *in) { SUCCESS('F'); hash_f(out, in); }
void trace_hash_g(uint8_t *out, const uint8_t *in) { SUCCESS('G'); hash_g(out, in); }
void trace_hash_h(uint8_t *out, const uint8_t *in) { SUCCESS('H'); hash_h(out, in); }
void trace_poly_cbd1(poly *out, const uint8_t in[192]) { SUCCESS('C'); poly_cbd1(out, in); }
void trace_poly_ntt(poly *out) { SUCCESS('N'); poly_ntt(out); }
void trace_poly_invntt(poly *out) { SUCCESS('I'); poly_invntt(out); }
void trace_poly_tobytes(uint8_t out[1152], const poly *in) { SUCCESS('T'); poly_tobytes(out, in); }
int trace_poly_sotp_decode(uint8_t msg[96], const poly *a, const uint8_t buf[192])
{ SUCCESS('S'); trace.sotp_status = poly_sotp_decode(msg, a, buf); return trace.sotp_status; }
void trace_poly_basemul(poly *out, const poly *a, const poly *b)
{ SUCCESS('B'); poly_basemul(out, a, b); }
void trace_poly_sub(poly *out, const poly *a, const poly *b)
{ SUCCESS('U'); poly_sub(out, a, b); }
void trace_poly_crepmod3(poly *out) { SUCCESS('M'); poly_crepmod3(out); }

void trace_candidate(uint16_t *out, const uint16_t *cp, const uint16_t *fp)
{
    trace.candidate_calls++; event('Q');
    jade_ntruplus_ntruplus768_amd64_ref_decap_candidate(out, cp, fp);
}

void trace_r2(uint16_t *out, const uint16_t *cp, const uint16_t *mp, const uint16_t *hp)
{
    trace.r2_calls++; event('X');
    jade_ntruplus_ntruplus768_amd64_ref_decap_r2(out, cp, mp, hp);
}

void trace_message_shake256(uint8_t *out, size_t outlen, const uint8_t *in, size_t inlen)
{
    if (inlen == 1153 && outlen == 192) {
        trace.shake_calls++; event('G');
        if (in[0] != 1) trace.shake_bad++;
        memcpy(message_shake_input, in, inlen);
        shake256(out, outlen, in, inlen);
        memcpy(message_shake_output, out, outlen);
    } else if (inlen == 129 && outlen == 224) {
        trace.hash_h_calls++; event('H');
        if (in[0] != 2) trace.shake_bad++;
        memcpy(hash_h_input, in, inlen);
        shake256(out, outlen, in, inlen);
        memcpy(hash_h_output, out, outlen);
    } else { trace.shake_bad++; shake256(out, outlen, in, inlen); }
}
uint32_t trace_message(uint8_t *msg, uint8_t *serialized, const uint16_t *m1, const uint16_t *r2)
{
    trace.message_calls++; event('Y');
    uint32_t result = ntruplus768_decap_message(msg, serialized, m1, r2);
    trace.sotp_status = (int)result;
    memcpy(decoded_message, msg, 96);
    return result;
}

void oracle_hash_g(uint8_t *out, const uint8_t *in) { hash_g(out, in); }

void trace_hash_h_prepare(uint8_t *input, const uint8_t *msg, const uint8_t *suffix)
{
    trace.prepare_calls++; event('P');
    jade_ntruplus_ntruplus768_amd64_ref_decap_hash_h_prepare(input, msg, suffix);
}
void trace_cbd1(uint16_t *out, const uint8_t *buf)
{
    trace.cbd_calls++; event('C');
    jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(out, buf);
}
void trace_ntt(uint16_t *out, const uint16_t *in)
{
    trace.ntt_calls++; event('N');
    jade_ntruplus_ntruplus768_amd64_ref_ntt(out, in);
}
void trace_tobytes(uint8_t *out, const uint16_t *in)
{
    trace.tobytes_calls++; event('T');
    jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes(out, in);
}
uint32_t trace_finish(uint8_t *ss, const uint8_t *hash, const uint8_t *left, const uint8_t *right, uint32_t fail)
{
    trace.finish_calls++; event('F');
    return jade_ntruplus_ntruplus768_amd64_ref_decap_finish(ss, hash, left, right, fail);
}
void trace_clear(uint8_t *workspace)
{
    trace.clear_calls++; event('Z');
    jade_ntruplus_ntruplus768_amd64_ref_decap_clear(workspace);
    for (size_t i = 0; i < 13506; i++) if (workspace[i] != 0) trace.clear_bad++;
}
void oracle_hash_h(uint8_t *out, const uint8_t *in) { hash_h(out, in); }
unsigned oracle_hash_g_calls(void) { return trace.shake_calls; }
unsigned oracle_hash_h_calls(void) { return trace.hash_h_calls; }
unsigned oracle_clear_calls(void) { return trace.clear_calls; }
unsigned oracle_clear_bad(void) { return trace.clear_bad; }
