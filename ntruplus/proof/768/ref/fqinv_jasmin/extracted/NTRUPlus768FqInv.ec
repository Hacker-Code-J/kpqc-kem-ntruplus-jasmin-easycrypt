require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

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
  proc jade_ntruplus_ntruplus768_amd64_ref_fqinv (a:W16.t) : W16.t = {
    var t2:W16.t;
    var t1:W16.t;
    var t3:W16.t;
    var  _0:W64.t;
     _0 <- (init_msf);
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
}.
