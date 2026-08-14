require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import Array768 WArray1536.

module M = {
  proc __crepmod3 (a:W16.t) : W16.t = {
    var mask:W16.t;
    var td:W32.t;
    var t:W16.t;
    mask <- a;
    mask <- (mask `|>>` (W8.of_int 15));
    mask <- (mask `&` (W16.of_int 3457));
    a <- (a + mask);
    a <- (a - (W16.of_int ((3457 + 1) %/ 2)));
    mask <- a;
    mask <- (mask `|>>` (W8.of_int 15));
    mask <- (mask `&` (W16.of_int 3457));
    a <- (a + mask);
    a <- (a - (W16.of_int ((3457 - 1) %/ 2)));
    td <- (sigextu32 a);
    td <- (td * (W32.of_int 10923));
    td <- (td + (W32.of_int 16384));
    td <- (td `|>>` (W8.of_int 15));
    t <- (truncateu16 td);
    t <- (t * (W16.of_int 3));
    a <- (a - t);
    return a;
  }
  proc jade_ntruplus_ntruplus768_amd64_ref_poly_crepmod3 (rp:W16.t Array768.t,
                                                          ap:W16.t Array768.t) :
  W16.t Array768.t = {
    var aux:W16.t;
    var i:W64.t;
    var  _0:W64.t;
     _0 <- (init_msf);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 768))) {
      aux <@ __crepmod3 (ap.[(W64.to_uint i)]);
      rp.[(W64.to_uint i)] <- aux;
      i <- (i + (W64.of_int 1));
    }
    return rp;
  }
}.
