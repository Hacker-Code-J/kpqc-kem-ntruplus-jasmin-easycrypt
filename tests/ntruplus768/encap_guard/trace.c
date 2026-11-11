#include <stdlib.h>
#include <string.h>
#include "trace.h"
#include "symmetric.h"

/* The official KAT DRBG is compiled with its randombytes symbol renamed. */
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
    uint8_t copy[48];
    memcpy(copy, seed, sizeof copy);
    randombytes_init(copy, NULL, 256);
}
void trace_randombytes(uint8_t *out, size_t n)
{
    trace.random_calls++;
    trace.random_bytes += (unsigned)n;
    event('R');
    if (kat_randombytes(out, n)) abort();
}
int trace_poly_frombytes(poly *out, const uint8_t in[1152])
{
    trace.decoder_calls++;
    event('D');
    return poly_frombytes(out, in);
}
uint32_t trace_guard(uint16_t *hp, uint8_t *ct, uint8_t *ss, const uint8_t *pk)
{
    trace.guard_calls++;
    event('J');
    return jade_ntruplus_ntruplus768_amd64_ref_encap_guard(hp, ct, ss, pk);
}
#define SUCCESS(label) do { trace.success_calls++; event(label); } while (0)
void trace_hash_f(uint8_t *out, const uint8_t *in) { SUCCESS('F'); hash_f(out, in); }
void trace_hash_g(uint8_t *out, const uint8_t *in) { SUCCESS('G'); hash_g(out, in); }
void trace_hash_h(uint8_t *out, const uint8_t *in) { SUCCESS('H'); hash_h(out, in); }
void trace_poly_cbd1(poly *out, const uint8_t in[192]) { SUCCESS('C'); poly_cbd1(out, in); }
void trace_poly_ntt(poly *out) { SUCCESS('N'); poly_ntt(out); }
void trace_poly_tobytes(uint8_t out[1152], const poly *in) { SUCCESS('T'); poly_tobytes(out, in); }
void trace_poly_sotp_encode(poly *out, const uint8_t msg[96], const uint8_t buf[192])
{ SUCCESS('E'); poly_sotp_encode(out, msg, buf); }
void trace_poly_basemul_add(poly *out, const poly *a, const poly *b, const poly *c)
{ SUCCESS('B'); poly_basemul_add(out, a, b, c); }
