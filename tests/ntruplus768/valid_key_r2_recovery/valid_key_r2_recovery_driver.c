#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../../../NTRU+/NTRU+768/poly.h"
#include "../../../NTRU+/NTRU+768/symmetric.h"

enum { CENTERED_BOUND = 1728, GUARD_BYTES = 16, FIXED_CASES = 4,
       SAMPLED_CASES = 128 };

_Static_assert(NTRUPLUS_N == 768, "test requires NTRU+768");
_Static_assert(NTRUPLUS_Q == 3457, "test requires q=3457");
_Static_assert(NTRUPLUS_POLYBYTES == 1152, "test requires 1152-byte polynomials");

static size_t no_wrap_cases, wrap_cases, wrap_message_changes;
static size_t key_rejections, different_r2_words, wrong_hinv_changes;

static void require(int condition, const char *message)
{
    if (!condition) {
        fprintf(stderr, "%s\n", message);
        exit(1);
    }
}

static int16_t mod_q(int64_t value)
{
    int32_t r = (int32_t)(value % NTRUPLUS_Q);
    return (int16_t)(r < 0 ? r + NTRUPLUS_Q : r);
}

static int16_t centered_q(int64_t value)
{
    const int32_t r = mod_q(value);
    return (int16_t)(r > CENTERED_BOUND ? r - NTRUPLUS_Q : r);
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

static void fill_bytes(uint8_t *buf, size_t length, uint32_t *state)
{
    for (size_t i = 0; i < length; ++i)
        buf[i] = (uint8_t)next_u32(state);
}

static void check_guards(const uint8_t *frame, size_t payload)
{
    for (size_t i = 0; i < GUARD_BYTES; ++i)
        require(frame[i] == 0xa5 && frame[GUARD_BYTES + payload + i] == 0xa5,
                "serialization or hashing crossed a buffer boundary");
}

/* Independent bit packing, using mathematical residues rather than the
 * production arithmetic-shift canonicalization.
 */
static void packing_oracle(uint8_t out[NTRUPLUS_POLYBYTES], const poly *a)
{
    for (size_t i = 0; i < NTRUPLUS_N / 2; ++i) {
        const uint16_t x = (uint16_t)mod_q(a->coeffs[2 * i]);
        const uint16_t y = (uint16_t)mod_q(a->coeffs[2 * i + 1]);
        out[3 * i] = (uint8_t)x;
        out[3 * i + 1] = (uint8_t)((x >> 8) | (y << 4));
        out[3 * i + 2] = (uint8_t)(y >> 4);
    }
}

static void checked_tobytes(uint8_t out[NTRUPLUS_POLYBYTES], const poly *a)
{
    uint8_t expected[NTRUPLUS_POLYBYTES];
    const poly before = *a;
    poly decoded;

    for (size_t i = 0; i < NTRUPLUS_N; ++i)
        require(-NTRUPLUS_Q <= a->coeffs[i] && a->coeffs[i] < NTRUPLUS_Q,
                "tobytes operand violates the proved representative range");
    packing_oracle(expected, a);
    poly_tobytes(out, a);
    require(memcmp(a, &before, sizeof(before)) == 0, "tobytes changed its input");
    require(memcmp(out, expected, sizeof(expected)) == 0, "packing oracle mismatch");
    poly_frombytes(&decoded, out);
    for (size_t i = 0; i < NTRUPLUS_N; ++i)
        require(decoded.coeffs[i] == mod_q(a->coeffs[i]),
                "frombytes did not return the canonical residue");
}

static void check_representative_invariance(void)
{
    size_t checked = 0;
    for (int start = 0; start < NTRUPLUS_Q; start += NTRUPLUS_N) {
        poly canonical, negative, mixed;
        uint8_t first[NTRUPLUS_POLYBYTES], second[NTRUPLUS_POLYBYTES];
        for (size_t i = 0; i < NTRUPLUS_N; ++i) {
            const int residue = start + (int)i < NTRUPLUS_Q ? start + (int)i : 0;
            canonical.coeffs[i] = (int16_t)residue;
            negative.coeffs[i] = (int16_t)(residue - NTRUPLUS_Q);
            mixed.coeffs[i] = (i & 1u) ? canonical.coeffs[i] : negative.coeffs[i];
            checked += (size_t)(start + (int)i < NTRUPLUS_Q);
        }
        checked_tobytes(first, &canonical);
        checked_tobytes(second, &negative);
        require(memcmp(first, second, sizeof(first)) == 0,
                "subtracting q changed canonical bytes");
        checked_tobytes(second, &mixed);
        require(memcmp(first, second, sizeof(first)) == 0,
                "mixed representatives changed canonical bytes");
        require(memcmp(&canonical, &negative, sizeof(canonical)) != 0,
                "representative test accidentally used equal words");
    }
    require(checked == NTRUPLUS_Q, "representative coverage is incomplete");
    printf("PASS canonical serialization: %zu residues, positive/negative/mixed words\n",
           checked);
}

/* Integer convolution and descending division by X^768-X^384+1. This
 * independent no-wrap oracle does not use NTT or coefficient reduction mod q.
 */
static void integer_product_sum(int64_t result[NTRUPLUS_N],
                                const poly *a, const poly *b,
                                const poly *c, const poly *d)
{
    int64_t raw[2 * NTRUPLUS_N - 1] = {0};
    for (size_t i = 0; i < NTRUPLUS_N; ++i)
        for (size_t j = 0; j < NTRUPLUS_N; ++j)
            raw[i + j] += (int64_t)a->coeffs[i] * b->coeffs[j] +
                          (int64_t)c->coeffs[i] * d->coeffs[j];
    for (int k = 2 * NTRUPLUS_N - 2; k >= NTRUPLUS_N; --k) {
        raw[k - NTRUPLUS_N / 2] += raw[k];
        raw[k - NTRUPLUS_N] -= raw[k];
    }
    memcpy(result, raw, NTRUPLUS_N * sizeof(result[0]));
}

static void check_integer_oracle(void)
{
    static const size_t left[] = {0, 384, 767, 767};
    static const size_t right[] = {0, 384, 1, 767};
    const poly zero = {{0}};
    int64_t result[NTRUPLUS_N];
    for (size_t k = 0; k < sizeof(left) / sizeof(left[0]); ++k) {
        poly a = {{0}}, b = {{0}};
        a.coeffs[left[k]] = b.coeffs[right[k]] = 1;
        integer_product_sum(result, &a, &b, &zero, &zero);
        for (size_t i = 0; i < NTRUPLUS_N; ++i) {
            const int64_t expected = k == 0 ? (i == 0) :
                k == 3 ? -(int64_t)(i == 382) :
                (int64_t)(i == 384) - (int64_t)(i == 0);
            require(result[i] == expected, "integer monomial reduction mismatch");
        }
    }
    poly ones;
    for (size_t i = 0; i < NTRUPLUS_N; ++i)
        ones.coeffs[i] = 1;
    integer_product_sum(result, &ones, &ones, &zero, &zero);
    require(result[767] == 1152, "all-ones integer square coefficient mismatch");
}

/* Fixed and pseudorandom CBD1 input buffers are test vectors, not KEM seeds.
 * Rejected inverses are retried only for the pseudorandom cases.
 */
static void make_key_poly(poly *coefficient, poly *terminal, poly *inverse,
                          int is_f, size_t index, uint32_t *state)
{
    uint8_t buf[NTRUPLUS_N / 4];
    for (size_t attempt = 0; attempt < 1000; ++attempt) {
        memset(buf, 0, sizeof(buf));
        if (index < 2) {
            if (!is_f)
                buf[0] = 1;
        } else if (index == 2) {
            memset(buf, 0xff, NTRUPLUS_N / 8);
        } else if (index == 3) {
            memset(buf + NTRUPLUS_N / 8, 0xff, NTRUPLUS_N / 8);
        } else {
            fill_bytes(buf, sizeof(buf), state);
        }
        poly_cbd1(coefficient, buf);
        poly_triple(coefficient, coefficient);
        coefficient->coeffs[0] += (int16_t)is_f;
        poly_ntt(terminal, coefficient);
        if (!poly_baseinv(inverse, terminal))
            return;
        require(index >= FIXED_CASES, "fixed key polynomial is not invertible");
        ++key_rejections;
    }
    require(0, "could not construct an invertible test key");
}

static void check_case(size_t index, uint32_t *state)
{
    poly f, g, fn, gn, finv, ginv, h, hinv, r, rn, m, mn, c;
    poly decoded_h, decoded_c, decoded_f, decoded_hinv, m1, pre, m2, diff, r2, wrong_r2;
    uint8_t pk_frame[2 * GUARD_BYTES + NTRUPLUS_PUBLICKEYBYTES];
    uint8_t sk_frame[2 * GUARD_BYTES + NTRUPLUS_SECRETKEYBYTES];
    uint8_t ct_frame[2 * GUARD_BYTES + NTRUPLUS_CIPHERTEXTBYTES];
    uint8_t pad_frame[2 * GUARD_BYTES + NTRUPLUS_N / 4];
    uint8_t *const pk = pk_frame + GUARD_BYTES;
    uint8_t *const sk = sk_frame + GUARD_BYTES;
    uint8_t *const ct = ct_frame + GUARD_BYTES;
    uint8_t *const pad = pad_frame + GUARD_BYTES;
    uint8_t cbd[NTRUPLUS_N / 4], msg[NTRUPLUS_N / 8], decoded[NTRUPLUS_N / 8];
    uint8_t rbytes[NTRUPLUS_POLYBYTES], r2bytes[NTRUPLUS_POLYBYTES];
    uint8_t alias_pad[NTRUPLUS_POLYBYTES], decap_pad[NTRUPLUS_N / 4];
    uint8_t secret_f_bytes[NTRUPLUS_POLYBYTES];
    int64_t lifted[NTRUPLUS_N];
    int no_wrap = 1;

    make_key_poly(&f, &fn, &finv, 1, index, state);
    make_key_poly(&g, &gn, &ginv, 0, index, state);
    poly_basemul(&h, &gn, &finv);
    poly_basemul(&hinv, &fn, &ginv);
    memset(pk_frame, 0xa5, sizeof(pk_frame));
    memset(sk_frame, 0xa5, sizeof(sk_frame));
    memset(ct_frame, 0xa5, sizeof(ct_frame));
    memset(pad_frame, 0xa5, sizeof(pad_frame));
    checked_tobytes(pk, &h);
    checked_tobytes(sk, &fn);
    memcpy(secret_f_bytes, sk, sizeof(secret_f_bytes));
    checked_tobytes(sk + NTRUPLUS_POLYBYTES, &hinv);
    require(memcmp(sk, secret_f_bytes, sizeof(secret_f_bytes)) == 0,
            "hinv serialization overwrote the f block");
    for (size_t i = 0; i < NTRUPLUS_SYMBYTES; ++i)
        require(sk[2 * NTRUPLUS_POLYBYTES + i] == 0xa5,
                "hinv serialization crossed into the hash_f suffix");
    hash_f(sk + 2 * NTRUPLUS_POLYBYTES, pk);

    memset(cbd, 0, sizeof(cbd));
    if (0 < index && index < FIXED_CASES)
        memset(cbd, 0xff, NTRUPLUS_N / 8);
    else if (index >= FIXED_CASES)
        fill_bytes(cbd, sizeof(cbd), state);
    poly_cbd1(&r, cbd);
    poly_ntt(&rn, &r);
    checked_tobytes(rbytes, &rn);
    memcpy(alias_pad, rbytes, sizeof(alias_pad));
    hash_g(pad, rbytes);
    hash_g(alias_pad, alias_pad); /* The encapsulation call aliases its buffers. */
    require(memcmp(alias_pad, pad, NTRUPLUS_N / 4) == 0,
            "encapsulation hash_g alias disagrees with disjoint call");
    require(memcmp(alias_pad + NTRUPLUS_N / 4, rbytes + NTRUPLUS_N / 4,
                   NTRUPLUS_POLYBYTES - NTRUPLUS_N / 4) == 0,
            "hash_g wrote beyond its pad output");
    fill_bytes(msg, sizeof(msg), state);
    if (index % 4 == 0)
        memset(msg, 0, sizeof(msg));
    else if (index % 4 == 1)
        memset(msg, 0xff, sizeof(msg));
    poly_sotp_encode(&m, msg, alias_pad);
    poly_ntt(&mn, &m);
    poly_frombytes(&decoded_h, pk);
    poly_basemul_add(&c, &decoded_h, &rn, &mn);
    checked_tobytes(ct, &c);

    integer_product_sum(lifted, &g, &r, &m, &f);
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        require((lifted[i] - m.coeffs[i]) % 3 == 0,
                "sampled-form cancellation modulo 3 failed");
        no_wrap &= -CENTERED_BOUND <= lifted[i] && lifted[i] <= CENTERED_BOUND;
    }

    /* Reconstruct the production caller seam, using its actual byte offsets
     * and primitives. This does not call crypto_kem_dec or model its AST.
     */
    poly_frombytes(&decoded_c, ct);
    poly_frombytes(&decoded_f, sk);
    poly_frombytes(&decoded_hinv, sk + NTRUPLUS_POLYBYTES);
    poly_basemul(&m1, &decoded_c, &decoded_f);
    poly_invntt(&pre, &m1);
    poly_crepmod3(&m1, &pre);
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        if (mod_q(pre.coeffs[i]) != mod_q(lifted[i])) {
            fprintf(stderr, "case %zu coefficient %zu: lift=%" PRId64 " pre=%d\n",
                    index, i, lifted[i], pre.coeffs[i]);
            require(0, "serialized key/ciphertext changed pre-crepmod3 semantics");
        }
        const int16_t centered = centered_q(lifted[i]);
        const int residue = ((centered % 3) + 3) % 3;
        require(m1.coeffs[i] == (residue == 2 ? -1 : residue),
                "crepmod3 disagrees with the independent integer oracle");
    }
    poly_ntt(&m2, &m1);
    poly_sub(&diff, &decoded_c, &m2);
    poly_basemul(&r2, &diff, &decoded_hinv);
    checked_tobytes(r2bytes, &r2);
    hash_g(decap_pad, r2bytes);
    const int decode_fail = poly_sotp_decode(decoded, &m1, decap_pad);

    if (no_wrap) {
        require(memcmp(&m1, &m, sizeof(m)) == 0, "conditional m1 recovery failed");
        for (size_t i = 0; i < NTRUPLUS_N; ++i)
            require(mod_q(r2.coeffs[i]) == mod_q(rn.coeffs[i]),
                    "conditional r2 congruence failed");
        require(memcmp(r2bytes, rbytes, sizeof(rbytes)) == 0,
                "conditional r2 byte recovery failed");
        require(memcmp(decap_pad, pad, sizeof(decap_pad)) == 0,
                "equal r2 hash inputs did not yield equal pads");
        require(!decode_fail && memcmp(decoded, msg, sizeof(msg)) == 0,
                "conditional SOTP recovery with the actual hash_g pad failed");
        different_r2_words += (size_t)(memcmp(&r2, &rn, sizeof(rn)) != 0);
        poly_basemul(&wrong_r2, &diff, &decoded_f);
        poly_tobytes(r2bytes, &wrong_r2);
        wrong_hinv_changes += (size_t)(memcmp(r2bytes, rbytes, sizeof(rbytes)) != 0);
        ++no_wrap_cases;
    } else {
        ++wrap_cases;
        wrap_message_changes += (size_t)(memcmp(&m1, &m, sizeof(m)) != 0);
    }
    check_guards(pk_frame, NTRUPLUS_PUBLICKEYBYTES);
    check_guards(sk_frame, NTRUPLUS_SECRETKEYBYTES);
    check_guards(ct_frame, NTRUPLUS_CIPHERTEXTBYTES);
    check_guards(pad_frame, NTRUPLUS_N / 4);
}

int main(void)
{
    uint32_t state = 0x72e364b9u;
    check_integer_oracle();
    check_representative_invariance();
    for (size_t i = 0; i < FIXED_CASES + SAMPLED_CASES; ++i)
        check_case(i, &state);
    require(no_wrap_cases >= 2 && wrap_cases >= 2 && wrap_message_changes >= 1,
            "missing conditional recovery or wrap-boundary coverage");
    require(different_r2_words > 0 && wrong_hinv_changes > 0,
            "missing nonliteral r2 recovery or wrong-offset sensitivity");
    printf("PASS r2/pad/SOTP recovery: %zu no-wrap cases; %zu wrap cases (%zu changed m1)\n",
           no_wrap_cases, wrap_cases, wrap_message_changes);
    printf("PASS byte seams: %zu unequal r/r2 word arrays; %zu wrong-hinv detections; "
           "%zu inverse rejections\n", different_r2_words, wrong_hinv_changes, key_rejections);
    puts("Scope: deterministic primitive/caller-seam regression; no DFR estimate or C-AST proof");
    return 0;
}
