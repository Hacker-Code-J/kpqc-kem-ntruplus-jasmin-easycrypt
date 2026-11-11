require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import Array1152 Array1153 WArray1152 WArray1153.

module M = {
  proc jade_ntruplus_ntruplus768_amd64_ref_encap_hash_f_prepare (input:W8.t Array1153.t,
                                                                 pk:W8.t Array1152.t) : 
  W8.t Array1153.t = {
    var i:W64.t;
    var b:W8.t;
    var  _0:W64.t;
     _0 <- (init_msf);
    input.[0] <- (W8.of_int 0);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 1152))) {
      b <- pk.[(W64.to_uint i)];
      input.[(W64.to_uint (i + (W64.of_int 1)))] <- b;
      i <- (i + (W64.of_int 1));
    }
    return input;
  }
}.
