#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../../../NTRU+/NTRU+768/ntt.h"
#include "../../../NTRU+/NTRU+768/params.h"

#define NTRUPLUS_RINV_MOD_Q 2775
#define RANDOM_CASES 20000u

extern uint64_t jade_ntruplus_ntruplus768_amd64_ref_baseinv(
    int16_t r[4], const int16_t a[4], uint16_t zeta);

_Static_assert(CHAR_BIT == 8, "baseinv test requires 8-bit bytes");
_Static_assert(sizeof(int16_t) * CHAR_BIT == 16,
               "baseinv test requires 16-bit int16_t");
_Static_assert(NTRUPLUS_Q == 3457, "baseinv test requires q=3457");

static uint16_t i16_to_word(int16_t value)
{
    uint16_t word;

    memcpy(&word, &value, sizeof(word));
    return word;
}

static int32_t mod_q(int64_t value)
{
    int64_t reduced = value % NTRUPLUS_Q;

    if (reduced < 0) {
        reduced += NTRUPLUS_Q;
    }
    return (int32_t)reduced;
}

static uint32_t next_u32(uint32_t *state)
{
    uint32_t value = *state;

    value ^= value << 13;
    value ^= value >> 17;
    value ^= value << 5;
    *state = value;
    return value;
}

static int16_t sample_qrange(uint32_t *state)
{
    return (int16_t)((int32_t)(next_u32(state) % (2u * NTRUPLUS_Q)) -
                     NTRUPLUS_Q);
}

static int strict_qrange4(const int16_t value[4])
{
    size_t i;

    for (i = 0; i < 4; ++i) {
        if (!(-NTRUPLUS_Q < value[i] && value[i] < NTRUPLUS_Q)) {
            return 0;
        }
    }
    return 1;
}

static int is_quartic_inverse(
    const int16_t a[4], const int16_t inverse[4], int16_t zeta_word)
{
    const int32_t zeta =
        mod_q((int64_t)zeta_word * NTRUPLUS_RINV_MOD_Q);
    const int64_t c0 =
        (int64_t)a[0] * inverse[0] +
        (int64_t)zeta *
            ((int64_t)a[1] * inverse[3] +
             (int64_t)a[2] * inverse[2] +
             (int64_t)a[3] * inverse[1]);
    const int64_t c1 =
        (int64_t)a[0] * inverse[1] +
        (int64_t)a[1] * inverse[0] +
        (int64_t)zeta *
            ((int64_t)a[2] * inverse[3] +
             (int64_t)a[3] * inverse[2]);
    const int64_t c2 =
        (int64_t)a[0] * inverse[2] +
        (int64_t)a[1] * inverse[1] +
        (int64_t)a[2] * inverse[0] +
        (int64_t)zeta * (int64_t)a[3] * inverse[3];
    const int64_t c3 =
        (int64_t)a[0] * inverse[3] +
        (int64_t)a[1] * inverse[2] +
        (int64_t)a[2] * inverse[1] +
        (int64_t)a[3] * inverse[0];

    return mod_q(c0) == 1 && mod_q(c1) == 0 &&
           mod_q(c2) == 0 && mod_q(c3) == 0;
}

static void check_case(
    const char *tag,
    size_t case_index,
    const int16_t input[4],
    int16_t zeta,
    size_t *successes,
    size_t *failures)
{
    static const int16_t sentinel[4] = {1234, -2345, 3000, -3000};
    int16_t c_input[4];
    int16_t j_input[4];
    int16_t j_alias[4];
    int16_t c_output[4];
    int16_t j_output[4];
    int c_status;
    uint64_t j_status;
    uint64_t j_alias_status;

    memcpy(c_input, input, sizeof(c_input));
    memcpy(j_input, input, sizeof(j_input));
    memcpy(j_alias, input, sizeof(j_alias));
    memcpy(c_output, sentinel, sizeof(c_output));
    memcpy(j_output, sentinel, sizeof(j_output));

    c_status = baseinv(c_output, c_input, zeta);
    j_status = jade_ntruplus_ntruplus768_amd64_ref_baseinv(
        j_output, j_input, i16_to_word(zeta));
    j_alias_status = jade_ntruplus_ntruplus768_amd64_ref_baseinv(
        j_alias, j_alias, i16_to_word(zeta));

    if (c_status < 0 || c_status > 1 ||
        j_status != (uint64_t)c_status || j_alias_status != j_status) {
        fprintf(stderr,
                "%s[%zu] status mismatch: C=%d Jasmin=%llu alias=%llu\n",
                tag,
                case_index,
                c_status,
                (unsigned long long)j_status,
                (unsigned long long)j_alias_status);
        exit(1);
    }
    if (memcmp(c_input, input, sizeof(c_input)) != 0 ||
        memcmp(j_input, input, sizeof(j_input)) != 0) {
        fprintf(stderr, "%s[%zu] mutated its input\n", tag, case_index);
        exit(1);
    }
    if (memcmp(c_output, j_output, sizeof(c_output)) != 0) {
        fprintf(stderr, "%s[%zu] output mismatch\n", tag, case_index);
        exit(1);
    }

    if (c_status == 0) {
        ++*successes;
        if (memcmp(j_alias, j_output, sizeof(j_alias)) != 0) {
            fprintf(stderr, "%s[%zu] Jasmin alias output mismatch\n", tag, case_index);
            exit(1);
        }
        if (!strict_qrange4(c_output)) {
            fprintf(stderr, "%s[%zu] success output is out of range\n", tag, case_index);
            exit(1);
        }
        if (!is_quartic_inverse(input, c_output, zeta)) {
            fprintf(stderr, "%s[%zu] success output is not an inverse\n", tag, case_index);
            exit(1);
        }
    } else {
        ++*failures;
        if (memcmp(j_alias, input, sizeof(j_alias)) != 0) {
            fprintf(stderr, "%s[%zu] Jasmin alias failure modified input\n", tag, case_index);
            exit(1);
        }
        if (memcmp(c_output, sentinel, sizeof(c_output)) != 0) {
            fprintf(stderr, "%s[%zu] failure modified the output\n", tag, case_index);
            exit(1);
        }
    }
}

int main(void)
{
    static const int16_t fixed_inputs[][4] = {
        {0, 0, 0, 0},
        {1, 0, 0, 0},
        {-1, 0, 0, 0},
        {0, 1, 0, 0},
        {0, 0, 1, 0},
        {0, 0, 0, 1},
        {1, 1, 0, 0},
        {1, 0, 1, 0},
        {1, 0, 0, 1},
        {NTRUPLUS_Q - 1, 0, 0, 0},
        {-NTRUPLUS_Q, 0, 0, 0},
        {NTRUPLUS_Q - 1, -NTRUPLUS_Q, 1, -1},
    };
    static const int16_t fixed_zetas[] = {
        1, 1, -1, 2, -2, 3, 1728, -1728, 867, -682, 147, -147,
    };
    uint32_t random_state = 0x7f4a7c15u;
    size_t successes = 0;
    size_t failures = 0;
    size_t case_index;

    for (case_index = 0;
         case_index < sizeof(fixed_zetas) / sizeof(fixed_zetas[0]);
         ++case_index) {
        check_case(
            "fixed",
            case_index,
            fixed_inputs[case_index],
            fixed_zetas[case_index],
            &successes,
            &failures);
    }

    for (case_index = 0; case_index < RANDOM_CASES; ++case_index) {
        int16_t input[4];
        int16_t zeta;
        size_t lane;

        for (lane = 0; lane < 4; ++lane) {
            input[lane] = sample_qrange(&random_state);
        }
        zeta = sample_qrange(&random_state);
        check_case(
            "random",
            case_index,
            input,
            zeta,
            &successes,
            &failures);
    }

    if (successes == 0 || failures == 0) {
        fprintf(stderr,
                "branch coverage missing: successes=%zu failures=%zu\n",
                successes,
                failures);
        return 1;
    }

    printf("baseinv differential passed: %zu fixed + %u random cases; "
           "%zu success, %zu failure\n",
           sizeof(fixed_zetas) / sizeof(fixed_zetas[0]),
           RANDOM_CASES,
           successes,
           failures);
    return 0;
}
