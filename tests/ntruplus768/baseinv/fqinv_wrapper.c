#include <stdint.h>

#define zetas test_only_fqinv_hidden_zetas
#define ntt test_only_fqinv_hidden_ntt
#define invntt test_only_fqinv_hidden_invntt
#define baseinv test_only_fqinv_hidden_baseinv
#define basemul test_only_fqinv_hidden_basemul
#define basemul_add test_only_fqinv_hidden_basemul_add
#include "../../../NTRU+/NTRU+768/ntt.c"
#undef zetas
#undef ntt
#undef invntt
#undef baseinv
#undef basemul
#undef basemul_add

int16_t test_only_fqinv(int16_t a)
{
    return fqinv(a);
}
