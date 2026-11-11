#include <stdlib.h>
#include <string.h>
#include "trace.h"
#include "symmetric.h"

int kat_randombytes(unsigned char *, unsigned long long);
void randombytes_init(unsigned char *, unsigned char *, int);
call_trace trace;
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
{ SUCCESS('S'); return poly_sotp_decode(msg, a, buf); }
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
