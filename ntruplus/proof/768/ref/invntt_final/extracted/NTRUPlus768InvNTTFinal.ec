require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import Array768 WArray1536.

module M = {
  proc __mul_i16 (a:W16.t, b:W16.t) : W32.t = {
    var c:W32.t;
    var ad:W32.t;
    var bd:W32.t;
    ad <- (sigextu32 a);
    bd <- (sigextu32 b);
    c <- (ad * bd);
    return c;
  }
  proc __montgomery_reduce (a:W32.t) : W16.t = {
    var t:W16.t;
    var q:W32.t;
    var td:W32.t;
    var r:W32.t;
    q <- (W32.of_int 3457);
    td <- a;
    td <- (td * (W32.of_int 12929));
    t <- (truncateu16 td);
    td <- (sigextu32 t);
    r <- a;
    td <- (td * q);
    r <- (r - td);
    r <- (r `|>>` (W8.of_int 16));
    t <- (truncateu16 r);
    return t;
  }
  proc jade_ntruplus_ntruplus768_amd64_ref_invntt_final (rp:W16.t Array768.t) : 
  W16.t Array768.t = {
    var aux:W16.t;
    var i:W64.t;
    var lo:W16.t;
    var hi:W16.t;
    var t1:W16.t;
    var td:W16.t;
    var acc:W32.t;
    var t2:W16.t;
    var  _0:W64.t;
     _0 <- (init_msf);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int (768 %/ 2)))) {
      lo <- rp.[(W64.to_uint i)];
      hi <- rp.[(W64.to_uint (i + (W64.of_int (768 %/ 2))))];
      t1 <- lo;
      t1 <- (t1 + hi);
      td <- lo;
      td <- (td - hi);
      acc <@ __mul_i16 ((W16.of_int (- 1665)), td);
      t2 <@ __montgomery_reduce (acc);
      td <- t1;
      td <- (td - t2);
      acc <@ __mul_i16 ((W16.of_int (- 811)), td);
      aux <@ __montgomery_reduce (acc);
      rp.[(W64.to_uint i)] <- aux;
      acc <@ __mul_i16 ((W16.of_int (- 1622)), t2);
      aux <@ __montgomery_reduce (acc);
      rp.[(W64.to_uint (i + (W64.of_int (768 %/ 2))))] <- aux;
      i <- (i + (W64.of_int 1));
    }
    return rp;
  }
}.
