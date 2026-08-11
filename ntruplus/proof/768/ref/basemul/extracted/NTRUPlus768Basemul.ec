require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import Array4 WArray8.

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
  proc jade_ntruplus_ntruplus768_amd64_ref_basemul (rp:W16.t Array4.t,
                                                    ap:W16.t Array4.t,
                                                    bp:W16.t Array4.t,
                                                    zeta_0:W16.t) : W16.t Array4.t = {
    var a0:W16.t;
    var a1:W16.t;
    var a2:W16.t;
    var a3:W16.t;
    var b0:W16.t;
    var b1:W16.t;
    var b2:W16.t;
    var b3:W16.t;
    var acc:W32.t;
    var term:W32.t;
    var r0:W16.t;
    var r1:W16.t;
    var r2:W16.t;
    var r3:W16.t;
    var  _0:W64.t;
     _0 <- (init_msf);
    a0 <- ap.[0];
    a1 <- ap.[1];
    a2 <- ap.[2];
    a3 <- ap.[3];
    b0 <- bp.[0];
    b1 <- bp.[1];
    b2 <- bp.[2];
    b3 <- bp.[3];
    acc <@ __mul_i16 (a1, b3);
    term <@ __mul_i16 (a2, b2);
    acc <- (acc + term);
    term <@ __mul_i16 (a3, b1);
    acc <- (acc + term);
    r0 <@ __montgomery_reduce (acc);
    acc <@ __mul_i16 (a2, b3);
    term <@ __mul_i16 (a3, b2);
    acc <- (acc + term);
    r1 <@ __montgomery_reduce (acc);
    acc <@ __mul_i16 (a3, b3);
    r2 <@ __montgomery_reduce (acc);
    acc <@ __mul_i16 (r0, zeta_0);
    term <@ __mul_i16 (a0, b0);
    acc <- (acc + term);
    r0 <@ __montgomery_reduce (acc);
    acc <@ __mul_i16 (r1, zeta_0);
    term <@ __mul_i16 (a0, b1);
    acc <- (acc + term);
    term <@ __mul_i16 (a1, b0);
    acc <- (acc + term);
    r1 <@ __montgomery_reduce (acc);
    acc <@ __mul_i16 (r2, zeta_0);
    term <@ __mul_i16 (a0, b2);
    acc <- (acc + term);
    term <@ __mul_i16 (a1, b1);
    acc <- (acc + term);
    term <@ __mul_i16 (a2, b0);
    acc <- (acc + term);
    r2 <@ __montgomery_reduce (acc);
    acc <@ __mul_i16 (a0, b3);
    term <@ __mul_i16 (a1, b2);
    acc <- (acc + term);
    term <@ __mul_i16 (a2, b1);
    acc <- (acc + term);
    term <@ __mul_i16 (a3, b0);
    acc <- (acc + term);
    r3 <@ __montgomery_reduce (acc);
    acc <@ __mul_i16 (r0, (W16.of_int 867));
    r0 <@ __montgomery_reduce (acc);
    acc <@ __mul_i16 (r1, (W16.of_int 867));
    r1 <@ __montgomery_reduce (acc);
    acc <@ __mul_i16 (r2, (W16.of_int 867));
    r2 <@ __montgomery_reduce (acc);
    acc <@ __mul_i16 (r3, (W16.of_int 867));
    r3 <@ __montgomery_reduce (acc);
    rp.[0] <- r0;
    rp.[1] <- r1;
    rp.[2] <- r2;
    rp.[3] <- r3;
    return rp;
  }
}.
