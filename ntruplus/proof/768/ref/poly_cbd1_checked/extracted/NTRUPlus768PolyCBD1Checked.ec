require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import Array192 Array768 WArray192 WArray1536.

module M = {
  proc jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1 (rp:W16.t Array768.t,
                                                      buf:W8.t Array192.t) : 
  W16.t Array768.t = {
    var k:W64.t;
    var i:W64.t;
    var j:W8.t;
    var t1:W16.t;
    var t2:W16.t;
    var  _0:W64.t;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var  _8:bool;
    var  _9:bool;
    var  _10:bool;
     _0 <- (init_msf);
    k <- (W64.of_int 0);
    while ((k \ult (W64.of_int 768))) {
      i <- k;
      i <- (i `>>` (W8.of_int 3));
      j <- (truncateu8 k);
      j <- (j `&` (W8.of_int 7));
      t1 <- (zeroextu16 buf.[(W64.to_uint i)]);
      t2 <- (zeroextu16 buf.[(W64.to_uint (i + (W64.of_int (768 %/ 8))))]);
      ( _1,  _2,  _3,  _4,  _5, t1) <- (SHR_16 t1 j);
      ( _6,  _7,  _8,  _9,  _10, t2) <- (SHR_16 t2 j);
      t1 <- (t1 `&` (W16.of_int 1));
      t2 <- (t2 `&` (W16.of_int 1));
      t1 <- (t1 - t2);
      rp.[(W64.to_uint k)] <- t1;
      k <- (k + (W64.of_int 1));
    }
    return rp;
  }
}.
