#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "params.h"
#include "poly.h"

static int write_coeffs_json(const poly *r)
{
    if (putchar('[') == EOF)
        return 4;

    for (size_t i = 0; i < NTRUPLUS_N; i++) {
        if (i != 0 && putchar(',') == EOF)
            return 4;
        if (fprintf(stdout, "%d", (int)r->coeffs[i]) < 0)
            return 4;
    }

    if (putchar(']') == EOF || putchar('\n') == EOF)
        return 4;
    return 0;
}

int main(void)
{
    uint8_t tail[NTRUPLUS_N / 4];
    uint8_t original[NTRUPLUS_N / 4];
    poly r;
    int status;

    if (fread(tail, 1, sizeof tail, stdin) != sizeof tail)
        return 2;
    if (fgetc(stdin) != EOF)
        return 3;

    memcpy(original, tail, sizeof tail);
    poly_cbd1(&r, tail);
    if (memcmp(tail, original, sizeof tail) != 0)
        return 5;

    status = write_coeffs_json(&r);
    if (status != 0)
        return status;
    return 0;
}
