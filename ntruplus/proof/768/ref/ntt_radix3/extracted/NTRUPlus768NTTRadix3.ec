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
  proc jade_ntruplus_ntruplus768_amd64_ref_ntt_radix3 (rp:W16.t Array768.t) : 
  W16.t Array768.t = {
    var i:W64.t;
    var a0:W16.t;
    var a1:W16.t;
    var a2:W16.t;
    var acc:W32.t;
    var t1:W16.t;
    var t2:W16.t;
    var td:W16.t;
    var t3:W16.t;
    var r0:W16.t;
    var r1:W16.t;
    var r2:W16.t;
    var  _0:W64.t;
     _0 <- (init_msf);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 128))) {
      a0 <- rp.[(W64.to_uint i)];
      a1 <- rp.[(W64.to_uint (i + (W64.of_int 128)))];
      a2 <- rp.[(W64.to_uint (i + (W64.of_int 256)))];
      acc <@ __mul_i16 ((W16.of_int (- 682)), a1);
      t1 <@ __montgomery_reduce (acc);
      acc <@ __mul_i16 ((W16.of_int (- 248)), a2);
      t2 <@ __montgomery_reduce (acc);
      td <- t1;
      td <- (td - t2);
      acc <@ __mul_i16 ((W16.of_int (- 886)), td);
      t3 <@ __montgomery_reduce (acc);
      r0 <- a0;
      r0 <- (r0 + t1);
      r0 <- (r0 + t2);
      r1 <- a0;
      r1 <- (r1 - t2);
      r1 <- (r1 + t3);
      r2 <- a0;
      r2 <- (r2 - t1);
      r2 <- (r2 - t3);
      rp.[(W64.to_uint i)] <- r0;
      rp.[(W64.to_uint (i + (W64.of_int 128)))] <- r1;
      rp.[(W64.to_uint (i + (W64.of_int 256)))] <- r2;
      i <- (i + (W64.of_int 1));
    }
    i <- (W64.of_int 384);
    while ((i \ult (W64.of_int 512))) {
      a0 <- rp.[(W64.to_uint i)];
      a1 <- rp.[(W64.to_uint (i + (W64.of_int 128)))];
      a2 <- rp.[(W64.to_uint (i + (W64.of_int 256)))];
      acc <@ __mul_i16 ((W16.of_int (- 708)), a1);
      t1 <@ __montgomery_reduce (acc);
      acc <@ __mul_i16 ((W16.of_int 682), a2);
      t2 <@ __montgomery_reduce (acc);
      td <- t1;
      td <- (td - t2);
      acc <@ __mul_i16 ((W16.of_int (- 886)), td);
      t3 <@ __montgomery_reduce (acc);
      r0 <- a0;
      r0 <- (r0 + t1);
      r0 <- (r0 + t2);
      r1 <- a0;
      r1 <- (r1 - t2);
      r1 <- (r1 + t3);
      r2 <- a0;
      r2 <- (r2 - t1);
      r2 <- (r2 - t3);
      rp.[(W64.to_uint i)] <- r0;
      rp.[(W64.to_uint (i + (W64.of_int 128)))] <- r1;
      rp.[(W64.to_uint (i + (W64.of_int 256)))] <- r2;
      i <- (i + (W64.of_int 1));
    }
    return rp;
  }
}.
