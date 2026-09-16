#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../../../NTRU+/NTRU+768/poly.h"

enum { CENTERED_BOUND = 1728, FIXED_CASES = 6, RANDOM_CASES = 128 };

_Static_assert(NTRUPLUS_N == 768, "test requires NTRU+768");
_Static_assert(NTRUPLUS_Q == 3457, "test requires q=3457");

static size_t no_wrap_cases;
static size_t wrap_cases;
static size_t recovery_failures;

static void require(int condition, const char *message)
{
    if (!condition) {
        fprintf(stderr, "%s\n", message);
        exit(1);
    }
}

static int32_t mod_q(int64_t value)
{
    int32_t r = (int32_t)(value % NTRUPLUS_Q);
    return r < 0 ? r + NTRUPLUS_Q : r;
}

static int16_t centered_q(int64_t value)
{
    int32_t r = mod_q(value);
    return (int16_t)(r > CENTERED_BOUND ? r - NTRUPLUS_Q : r);
}

static int16_t centered_3(int64_t value)
{
    int32_t r = (int32_t)(value % 3);
    if (r < 0)
        r += 3;
    return (int16_t)(r == 2 ? -1 : r);
}

/* Ordinary integer convolution followed by descending polynomial division.
 * No NTT, twiddle table, Montgomery reduction, or coefficient mod-q is used.
 * The divisor is X^768 - X^384 + 1.
 */
static void integer_product_sum(int64_t result[NTRUPLUS_N],
                                const poly *a, const poly *b,
                                const poly *c, const poly *d)
{
    int64_t raw[2 * NTRUPLUS_N - 1] = {0};

    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        for (size_t j = 0; j < NTRUPLUS_N; ++j) {
            raw[i + j] += (int64_t)a->coeffs[i] * b->coeffs[j] +
                          (int64_t)c->coeffs[i] * d->coeffs[j];
        }
    }
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
    require(result[767] == 1152, "all-ones square coefficient changed");
}

/* Exhaust all 6914 supported integer representatives, including the two
 * representatives of each residue. Each lane has an independent % oracle.
 */
static void check_scalar_representatives(void)
{
    size_t checked = 0;

    for (int start = -NTRUPLUS_Q; start < NTRUPLUS_Q; start += NTRUPLUS_N) {
        poly input, output, alias;
        for (size_t i = 0; i < NTRUPLUS_N; ++i) {
            const int v = start + (int)i;
            input.coeffs[i] = (int16_t)(v < NTRUPLUS_Q ? v : 0);
        }
        alias = input;
        poly_crepmod3(&output, &input);
        poly_crepmod3(&alias, &alias);
        for (size_t i = 0; i < NTRUPLUS_N; ++i) {
            const int v = start + (int)i;
            if (v >= NTRUPLUS_Q)
                break;
            require(input.coeffs[i] == v, "crepmod3 changed disjoint input");
            require(output.coeffs[i] == centered_3(centered_q(v)),
                    "crepmod3 disagrees with centered integer oracle");
            require(alias.coeffs[i] == output.coeffs[i], "crepmod3 alias mismatch");
            if (-CENTERED_BOUND <= v && v <= CENTERED_BOUND)
                require(output.coeffs[i] == centered_3(v),
                        "centered no-wrap scalar recovery failed");
            if (v == 1729 || v == -1729)
                require(output.coeffs[i] != centered_3(v),
                        "wrap boundary failed to expose message change");
            ++checked;
        }
    }
    require(checked == 2 * NTRUPLUS_Q, "incomplete representative coverage");
    printf("PASS scalar recovery: %zu representatives, +/-1728 and +/-1729 boundaries\n",
           checked);
}

static int check_ring_case(size_t index, const poly *fp, const poly *gp,
                           const poly *r, const poly *m, poly *recovered)
{
    poly f, g, fn, gn, rn, mn, gr, mf, terminal, pre, alias, reps;
    int64_t lifted[NTRUPLUS_N];
    int no_wrap = 1, differs = 0;

    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        require(-1 <= fp->coeffs[i] && fp->coeffs[i] <= 1 &&
                -1 <= gp->coeffs[i] && gp->coeffs[i] <= 1 &&
                -1 <= r->coeffs[i] && r->coeffs[i] <= 1 &&
                -1 <= m->coeffs[i] && m->coeffs[i] <= 1,
                "test input is outside the sampler/message trit domain");
        f.coeffs[i] = (int16_t)(3 * fp->coeffs[i] + (i == 0));
        g.coeffs[i] = (int16_t)(3 * gp->coeffs[i]);
    }
    integer_product_sum(lifted, &g, r, m, &f);
    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        require((lifted[i] - m->coeffs[i]) % 3 == 0,
                "integer sampled-form cancellation modulo 3 failed");
        no_wrap &= -CENTERED_BOUND <= lifted[i] && lifted[i] <= CENTERED_BOUND;
    }

    /* The post-valid-key expression G*R + M*F is executed with production
     * transforms and products. This does not call crypto_kem_dec or assert
     * that the fixed sampler-domain counterexamples are reachable KEM seeds.
     */
    poly_ntt(&fn, &f);
    poly_ntt(&gn, &g);
    poly_ntt(&rn, r);
    poly_ntt(&mn, m);
    poly_basemul(&gr, &gn, &rn);
    poly_basemul(&mf, &mn, &fn);
    for (size_t i = 0; i < NTRUPLUS_N; ++i)
        terminal.coeffs[i] = centered_q((int32_t)gr.coeffs[i] + mf.coeffs[i]);
    poly_invntt(&pre, &terminal);
    alias = pre;
    poly_crepmod3(recovered, &pre);
    poly_crepmod3(&alias, &alias);

    for (size_t i = 0; i < NTRUPLUS_N; ++i) {
        require(-NTRUPLUS_Q <= pre.coeffs[i] && pre.coeffs[i] < NTRUPLUS_Q,
                "inverse output is outside the crepmod3 input contract");
        if (mod_q(pre.coeffs[i]) != mod_q(lifted[i]) ||
            recovered->coeffs[i] != centered_3(centered_q(lifted[i]))) {
            fprintf(stderr, "case %zu coefficient %zu: lift=%" PRId64
                    " pre=%d recovered=%d\n", index, i, lifted[i],
                    pre.coeffs[i], recovered->coeffs[i]);
            exit(1);
        }
        require(alias.coeffs[i] == recovered->coeffs[i], "pipeline alias mismatch");
        if (no_wrap)
            require(recovered->coeffs[i] == m->coeffs[i],
                    "conditional exact message-polynomial recovery failed");
        differs |= recovered->coeffs[i] != m->coeffs[i];
        reps.coeffs[i] = (int16_t)(mod_q(lifted[i]) -
                                  ((i & 1u) ? NTRUPLUS_Q : 0));
    }
    poly_crepmod3(&reps, &reps);
    require(memcmp(&reps, recovered, sizeof(reps)) == 0,
            "q-congruent representatives changed recovery");

    if (index == 1 || index == 2) {
        const int sign = index == 1 ? 1 : -1;
        require(lifted[767] == sign * 6913 &&
                centered_q(lifted[767]) == -sign &&
                recovered->coeffs[767] == -sign &&
                m->coeffs[767] == sign && !no_wrap,
                "all-ones sampler-domain wrap counterexample changed");
    }
    no_wrap_cases += (size_t)no_wrap;
    wrap_cases += (size_t)!no_wrap;
    recovery_failures += (size_t)differs;
    return no_wrap;
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

static int16_t next_trit(uint32_t *state)
{
    const uint32_t x = next_u32(state);
    return (int16_t)((int)(x & 1u) - (int)((x >> 1) & 1u));
}

int main(void)
{
    uint32_t state = 0x8ae7c6d5u;
    size_t decoded_messages = 0;

    check_integer_oracle();
    check_scalar_representatives();
    for (size_t k = 0; k < FIXED_CASES + RANDOM_CASES; ++k) {
        poly fp = {{0}}, gp = {{0}}, r = {{0}}, m = {{0}}, recovered;
        uint8_t msg[NTRUPLUS_N / 8], pad[NTRUPLUS_N / 4], decoded[NTRUPLUS_N / 8];

        if (k >= FIXED_CASES) {
            for (size_t i = 0; i < NTRUPLUS_N; ++i) {
                fp.coeffs[i] = next_trit(&state);
                gp.coeffs[i] = next_trit(&state);
                r.coeffs[i] = next_trit(&state);
            }
            for (size_t i = 0; i < sizeof(msg); ++i)
                msg[i] = (uint8_t)next_u32(&state);
            for (size_t i = 0; i < sizeof(pad); ++i)
                pad[i] = (uint8_t)next_u32(&state);
            poly_sotp_encode(&m, msg, pad);
        } else if (k == 1 || k == 2) {
            for (size_t i = 0; i < NTRUPLUS_N; ++i) {
                fp.coeffs[i] = r.coeffs[i] = 1;
                gp.coeffs[i] = m.coeffs[i] = k == 1 ? 1 : -1;
            }
        } else if (k == 3) {
            for (size_t i = 0; i < NTRUPLUS_N; ++i)
                m.coeffs[i] = (int16_t)((int)(i % 3) - 1);
        } else if (k == 4) {
            fp.coeffs[767] = gp.coeffs[384] = r.coeffs[767] = m.coeffs[767] = 1;
        } else if (k == 5) {
            for (size_t i = 0; i < NTRUPLUS_N; ++i) {
                fp.coeffs[i] = (i & 1u) ? -1 : 1;
                gp.coeffs[i] = (int16_t)-fp.coeffs[i];
                r.coeffs[i] = (int16_t)((int)(i % 3) - 1);
                m.coeffs[i] = (int16_t)-r.coeffs[i];
            }
        }
        const int no_wrap = check_ring_case(k, &fp, &gp, &r, &m, &recovered);
        if (k >= FIXED_CASES && no_wrap) {
            require(poly_sotp_decode(decoded, &recovered, pad) == 0 &&
                    memcmp(decoded, msg, sizeof(msg)) == 0,
                    "conditional SOTP message recovery failed");
            ++decoded_messages;
        }
    }
    require(no_wrap_cases > 0 && wrap_cases >= 2 && recovery_failures >= 2 &&
            decoded_messages > 0, "recovery test coverage is incomplete");
    printf("PASS integer-ring/NTT recovery: %d polynomials, %zu no-wrap, %zu wrap, "
           "%zu observed mismatches outside no-wrap, %zu SOTP messages\n",
           FIXED_CASES + RANDOM_CASES, no_wrap_cases, wrap_cases,
           recovery_failures, decoded_messages);
    puts("Scope: deterministic regression; no KEM seed witness or failure-probability claim.");
    return 0;
}
