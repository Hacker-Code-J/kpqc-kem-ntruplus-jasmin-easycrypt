require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import Array768 WArray1536.

module M = {
  proc jade_ntruplus_ntruplus768_amd64_ref_keygen_shape_g (rp:W16.t Array768.t) : 
  W16.t Array768.t = {
    var i:W64.t;
    var x:W16.t;
    var y:W16.t;
    var  _0:W64.t;
     _0 <- (init_msf);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 768))) {
      x <- rp.[(W64.to_uint i)];
      y <- x;
      x <- (x + x);
      x <- (x + y);
      rp.[(W64.to_uint i)] <- x;
      i <- (i + (W64.of_int 1));
    }
    return rp;
  }
}.
