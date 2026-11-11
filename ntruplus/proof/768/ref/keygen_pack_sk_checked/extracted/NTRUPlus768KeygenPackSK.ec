require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import Array32 Array1152 Array2336 WArray32 WArray1152 WArray2336.

module M = {
  proc jade_ntruplus_ntruplus768_amd64_ref_keygen_pack_sk (sk:W8.t Array2336.t,
                                                           fbytes:W8.t Array1152.t,
                                                           hinvbytes:W8.t Array1152.t,
                                                           hash_f:W8.t Array32.t) : 
  W8.t Array2336.t = {
    var i:W64.t;
    var b:W8.t;
    var  _0:W64.t;
     _0 <- (init_msf);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 2336))) {
      if ((i \ult (W64.of_int 1152))) {
        b <- fbytes.[(W64.to_uint i)];
      } else {
        if ((i \ult (W64.of_int (2 * 1152)))) {
          b <- hinvbytes.[(W64.to_uint (i - (W64.of_int 1152)))];
        } else {
          b <- hash_f.[(W64.to_uint (i - (W64.of_int (2 * 1152))))];
        }
      }
      sk.[(W64.to_uint i)] <- b;
      i <- (i + (W64.of_int 1));
    }
    return sk;
  }
}.
