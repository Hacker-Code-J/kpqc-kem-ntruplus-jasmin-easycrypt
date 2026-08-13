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
  proc __barrett_reduce (a:W16.t) : W16.t = {
    var t:W16.t;
    var v:W32.t;
    var td:W32.t;
    var q:W32.t;
    v <- (W32.of_int 19412);
    td <- (sigextu32 a);
    td <- (td * v);
    td <- (td + (W32.of_int 33554432));
    td <- (td `|>>` (W8.of_int 26));
    t <- (truncateu16 td);
    q <- (W32.of_int 3457);
    td <- (sigextu32 t);
    td <- (td * q);
    t <- (truncateu16 td);
    t <- (a - t);
    return t;
  }
  proc __invntt_radix2_64_block (rp:W16.t Array768.t, base:W64.t,
                                 zeta_0:W16.t) : W16.t Array768.t = {
    var i:W64.t;
    var stop:W64.t;
    var low:W16.t;
    var high:W16.t;
    var wd:W32.t;
    var td:W32.t;
    var sum:W16.t;
    var diff:W16.t;
    var acc:W32.t;
    var prod:W16.t;
    i <- base;
    stop <- base;
    stop <- (stop + (W64.of_int 64));
    while ((i \ult stop)) {
      low <- rp.[(W64.to_uint i)];
      high <- rp.[(W64.to_uint (i + (W64.of_int 64)))];
      wd <- (sigextu32 low);
      td <- (sigextu32 high);
      wd <- (wd + td);
      sum <- (truncateu16 wd);
      wd <- (sigextu32 high);
      td <- (sigextu32 low);
      wd <- (wd - td);
      diff <- (truncateu16 wd);
      sum <@ __barrett_reduce (sum);
      acc <@ __mul_i16 (zeta_0, diff);
      prod <@ __montgomery_reduce (acc);
      rp.[(W64.to_uint i)] <- sum;
      rp.[(W64.to_uint (i + (W64.of_int 64)))] <- prod;
      i <- (i + (W64.of_int 1));
    }
    return rp;
  }
  proc jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_64 (rp:W16.t Array768.t) : 
  W16.t Array768.t = {
    var  _0:W64.t;
     _0 <- (init_msf);
    rp <@ __invntt_radix2_64_block (rp, (W64.of_int 0),
    (W16.of_int (- 867)));
    rp <@ __invntt_radix2_64_block (rp, (W64.of_int 128),
    (W16.of_int (- 1124)));
    rp <@ __invntt_radix2_64_block (rp, (W64.of_int 256),
    (W16.of_int (- 257)));
    rp <@ __invntt_radix2_64_block (rp, (W64.of_int 384),
    (W16.of_int (- 723)));
    rp <@ __invntt_radix2_64_block (rp, (W64.of_int 512),
    (W16.of_int (- 722)));
    rp <@ __invntt_radix2_64_block (rp, (W64.of_int 640), (W16.of_int 1));
    return rp;
  }
}.
