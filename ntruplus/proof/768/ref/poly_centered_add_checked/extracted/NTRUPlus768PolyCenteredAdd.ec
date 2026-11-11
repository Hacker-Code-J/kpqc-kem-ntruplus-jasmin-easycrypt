require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import Array768 WArray1536.

module M = {
  proc jade_ntruplus_ntruplus768_amd64_ref_poly_centered_add (output:W16.t Array768.t,
                                                              product:W16.t Array768.t,
                                                              add:W16.t Array768.t) : 
  W16.t Array768.t = {
    var i:W64.t;
    var p:W16.t;
    var a:W16.t;
    var s:W32.t;
    var t:W32.t;
    var low:bool;
    var high:bool;
    var  _0:W64.t;
     _0 <- (init_msf);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 768))) {
      p <- product.[(W64.to_uint i)];
      a <- add.[(W64.to_uint i)];
      s <- (sigextu32 p);
      t <- (sigextu32 a);
      s <- (s + t);
      t <- s;
      t <- (t + (W32.of_int 3457));
      low <- (s \slt (W32.of_int (- 3457)));
      s <- (low ? t : s);
      t <- s;
      t <- (t - (W32.of_int 3457));
      high <- ((W32.of_int 3457) \sle s);
      s <- (high ? t : s);
      output.[(W64.to_uint i)] <- (truncateu16 s);
      i <- (i + (W64.of_int 1));
    }
    return output;
  }
}.
