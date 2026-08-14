require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import Array768 WArray1536.

module M = {
  proc jade_ntruplus_ntruplus768_amd64_ref_poly_sub (rp:W16.t Array768.t,
                                                     ap:W16.t Array768.t,
                                                     bp:W16.t Array768.t) :
  W16.t Array768.t = {
    var i:W64.t;
    var t:W16.t;
    var  _0:W64.t;
     _0 <- (init_msf);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 768))) {
      t <- ap.[(W64.to_uint i)];
      t <- (t - bp.[(W64.to_uint i)]);
      rp.[(W64.to_uint i)] <- t;
      i <- (i + (W64.of_int 1));
    }
    return rp;
  }
}.
