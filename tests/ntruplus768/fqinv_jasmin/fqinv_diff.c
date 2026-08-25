#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define NTRUPLUS_Q 3457

extern int16_t test_only_fqinv(int16_t a);
extern uint16_t jade_ntruplus_ntruplus768_amd64_ref_fqinv(uint16_t a);

_Static_assert(CHAR_BIT == 8, "fqinv test requires 8-bit bytes");
_Static_assert(sizeof(int16_t) * CHAR_BIT == 16,
               "fqinv test requires 16-bit int16_t");
_Static_assert(INT16_MIN == -32768 && INT16_MAX == 32767,
               "fqinv test requires the expected signed 16-bit range");

static int16_t word_to_i16(uint16_t word)
{
    int16_t value;

    memcpy(&value, &word, sizeof(value));
    return value;
}

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

static void check_exact_word(uint16_t input_word)
{
    const int16_t input = word_to_i16(input_word);
    const int16_t c_output = test_only_fqinv(input);
    const uint16_t jasmin_output =
        jade_ntruplus_ntruplus768_amd64_ref_fqinv(input_word);

    if (i16_to_word(c_output) != jasmin_output) {
        fprintf(stderr,
                "fqinv mismatch for word 0x%04x (%d): C=%d Jasmin=%d\n",
                (unsigned)input_word,
                input,
                c_output,
                word_to_i16(jasmin_output));
        exit(1);
    }
}

static void check_inverse_residue(int16_t input)
{
    const uint16_t output_word =
        jade_ntruplus_ntruplus768_amd64_ref_fqinv(i16_to_word(input));
    const int16_t output = word_to_i16(output_word);

    if (!(-NTRUPLUS_Q < output && output < NTRUPLUS_Q)) {
        fprintf(stderr, "fqinv(%d) returned out-of-range value %d\n", input, output);
        exit(1);
    }
    if (mod_q((int64_t)input * output) != 1) {
        fprintf(stderr, "fqinv(%d) returned non-inverse value %d\n", input, output);
        exit(1);
    }
}

int main(void)
{
    uint32_t input_word;
    int32_t residue;

    for (input_word = 0; input_word <= UINT16_MAX; ++input_word) {
        check_exact_word((uint16_t)input_word);
    }

    for (residue = 1; residue < NTRUPLUS_Q; ++residue) {
        check_inverse_residue((int16_t)residue);
    }

    printf("fqinv differential passed: 65536 exact word inputs; "
           "3456 nonzero inverse residues\n");
    return 0;
}
