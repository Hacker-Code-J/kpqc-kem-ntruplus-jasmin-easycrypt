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
  proc __fqmul (a:W16.t, b:W16.t) : W16.t = {
    var r:W16.t;
    var c:W32.t;
    c <@ __mul_i16 (a, b);
    r <@ __montgomery_reduce (c);
    return r;
  }
  proc __fqinv (a:W16.t) : W16.t = {
    var t2:W16.t;
    var t1:W16.t;
    var t3:W16.t;
    t1 <@ __fqmul (a, a);
    t2 <@ __fqmul (t1, t1);
    t2 <@ __fqmul (t2, t2);
    t3 <@ __fqmul (t2, t2);
    t1 <@ __fqmul (t1, t2);
    t2 <@ __fqmul (t1, t3);
    t2 <@ __fqmul (t2, t2);
    t2 <@ __fqmul (t2, a);
    t1 <@ __fqmul (t1, t2);
    t2 <@ __fqmul (t2, t2);
    t2 <@ __fqmul (t2, t2);
    t2 <@ __fqmul (t2, t2);
    t2 <@ __fqmul (t2, t2);
    t2 <@ __fqmul (t2, t2);
    t2 <@ __fqmul (t2, t2);
    t2 <@ __fqmul (t2, t1);
    t2 <@ __fqmul ((W16.of_int (- 682)), t2);
    return t2;
  }
  proc __baseinv_pretrace (a0:W16.t, a1:W16.t, a2:W16.t, a3:W16.t,
                           zeta_0:W16.t) : W16.t * W16.t * W16.t * W16.t = {
    var t0:W16.t;
    var t1:W16.t;
    var t2:W16.t;
    var t3:W16.t;
    var acc:W32.t;
    var term:W32.t;
    acc <@ __mul_i16 (a2, a2);
    term <@ __mul_i16 (a1, a3);
    term <- (term + term);
    acc <- (acc - term);
    t0 <@ __montgomery_reduce (acc);
    acc <@ __mul_i16 (a3, a3);
    t1 <@ __montgomery_reduce (acc);
    acc <@ __mul_i16 (a0, a0);
    term <@ __mul_i16 (t0, zeta_0);
    acc <- (acc + term);
    t0 <@ __montgomery_reduce (acc);
    acc <@ __mul_i16 (a1, a1);
    term <@ __mul_i16 (t1, zeta_0);
    acc <- (acc + term);
    term <@ __mul_i16 (a0, a2);
    term <- (term + term);
    acc <- (acc - term);
    t1 <@ __montgomery_reduce (acc);
    acc <@ __mul_i16 (t1, zeta_0);
    t2 <@ __montgomery_reduce (acc);
    acc <@ __mul_i16 (t0, t0);
    term <@ __mul_i16 (t1, t2);
    acc <- (acc - term);
    t3 <@ __montgomery_reduce (acc);
    return (t0, t1, t2, t3);
  }
  proc __baseinv_success (a0:W16.t, a1:W16.t, a2:W16.t, a3:W16.t, t0:W16.t,
                          t1:W16.t, t2:W16.t, determinant:W16.t) : W16.t *
                                                                   W16.t *
                                                                   W16.t *
                                                                   W16.t = {
    var r0:W16.t;
    var r1:W16.t;
    var r2:W16.t;
    var r3:W16.t;
    var acc:W32.t;
    var term:W32.t;
    var invword:W16.t;
    acc <@ __mul_i16 (a0, t0);
    term <@ __mul_i16 (a2, t2);
    acc <- (acc + term);
    r0 <@ __montgomery_reduce (acc);
    acc <@ __mul_i16 (a3, t2);
    term <@ __mul_i16 (a1, t0);
    acc <- (acc + term);
    r1 <@ __montgomery_reduce (acc);
    acc <@ __mul_i16 (a2, t0);
    term <@ __mul_i16 (a0, t1);
    acc <- (acc + term);
    r2 <@ __montgomery_reduce (acc);
    acc <@ __mul_i16 (a1, t1);
    term <@ __mul_i16 (a3, t0);
    acc <- (acc + term);
    r3 <@ __montgomery_reduce (acc);
    invword <@ __fqinv (determinant);
    acc <@ __mul_i16 (r0, invword);
    r0 <@ __montgomery_reduce (acc);
    acc <@ __mul_i16 (r1, invword);
    r1 <@ __montgomery_reduce (acc);
    acc <@ __mul_i16 (r2, invword);
    r2 <@ __montgomery_reduce (acc);
    acc <@ __mul_i16 (r3, invword);
    r3 <@ __montgomery_reduce (acc);
    return (r0, r1, r2, r3);
  }
  proc __baseinv_core (rp:W16.t Array4.t, ap:W16.t Array4.t, zeta_0:W16.t) : 
  W16.t Array4.t * W64.t = {
    var status:W64.t;
    var a0:W16.t;
    var a1:W16.t;
    var a2:W16.t;
    var a3:W16.t;
    var t0:W16.t;
    var t1:W16.t;
    var t2:W16.t;
    var t3:W16.t;
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
    (t0, t1, t2, t3) <@ __baseinv_pretrace (a0, a1, a2, a3, zeta_0);
    if ((t3 = (W16.of_int 0))) {
      status <- (W64.of_int 1);
    } else {
      (r0, r1, r2, r3) <@ __baseinv_success (a0, a1, a2, a3, t0, t1, t2, t3);
      r1 <- (- r1);
      r3 <- (- r3);
      rp.[0] <- r0;
      rp.[1] <- r1;
      rp.[2] <- r2;
      rp.[3] <- r3;
      status <- (W64.of_int 0);
    }
    return (rp, status);
  }
}.
