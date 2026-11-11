require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import Array768 Array1152 Array1153 WArray1152 WArray1153 WArray1536.

module M = {
  proc serialize__jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes (rp:W8.t Array1152.t,
                                                                    ap:W16.t Array768.t) : 
  W8.t Array1152.t = {
    var i:W64.t;
    var off:W64.t;
    var t0:W16.t;
    var mask:W16.t;
    var t1:W16.t;
    var t:W16.t;
    var  _0:W64.t;
     _0 <- (init_msf);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int (768 %/ 2)))) {
      off <- i;
      off <- (off `<<` (W8.of_int 1));
      t0 <- ap.[(W64.to_uint ((W64.of_int 2) * i))];
      mask <- t0;
      mask <- (mask `|>>` (W8.of_int 15));
      mask <- (mask `&` (W16.of_int 3457));
      t0 <- (t0 + mask);
      t1 <- ap.[(W64.to_uint (((W64.of_int 2) * i) + (W64.of_int 1)))];
      mask <- t1;
      mask <- (mask `|>>` (W8.of_int 15));
      mask <- (mask `&` (W16.of_int 3457));
      t1 <- (t1 + mask);
      off <- (off + i);
      rp.[(W64.to_uint off)] <- (truncateu8 t0);
      t <- t0;
      t <- (t `>>` (W8.of_int 8));
      mask <- t1;
      mask <- (mask `<<` (W8.of_int 4));
      t <- (t `|` mask);
      rp.[(W64.to_uint (off + (W64.of_int 1)))] <- (truncateu8 t);
      t <- t1;
      t <- (t `>>` (W8.of_int 4));
      rp.[(W64.to_uint (off + (W64.of_int 2)))] <- (truncateu8 t);
      i <- (i + (W64.of_int 1));
    }
    return rp;
  }
  proc jade_ntruplus_ntruplus768_amd64_ref_decap_message_prepare (serialized:W8.t Array1152.t,
                                                                  input:W8.t Array1153.t,
                                                                  r2:W16.t Array768.t) : 
  W8.t Array1152.t * W8.t Array1153.t = {
    var i:W64.t;
    var b:W8.t;
    var  _0:W64.t;
     _0 <- (init_msf);
    serialized <@ serialize__jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes (
    serialized, r2);
    input.[0] <- (W8.of_int 1);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 1152))) {
      b <- serialized.[(W64.to_uint i)];
      input.[(W64.to_uint (i + (W64.of_int 1)))] <- b;
      i <- (i + (W64.of_int 1));
    }
    return (serialized, input);
  }
}.
