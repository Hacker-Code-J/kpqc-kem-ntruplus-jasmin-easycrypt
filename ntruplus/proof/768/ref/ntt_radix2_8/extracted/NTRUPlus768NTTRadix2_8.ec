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
  proc __radix2_8_block (rp:W16.t Array768.t, base:W64.t, zeta_0:W16.t) : 
  W16.t Array768.t = {
    var aux:W16.t;
    var i:W64.t;
    var stop:W64.t;
    var low:W16.t;
    var high:W16.t;
    var acc:W32.t;
    var t:W16.t;
    var wd:W32.t;
    var td:W32.t;
    var diff:W16.t;
    var sum:W16.t;
    i <- base;
    stop <- base;
    stop <- (stop + (W64.of_int 8));
    while ((i \ult stop)) {
      low <- rp.[(W64.to_uint i)];
      high <- rp.[(W64.to_uint (i + (W64.of_int 8)))];
      acc <@ __mul_i16 (zeta_0, high);
      t <@ __montgomery_reduce (acc);
      wd <- (sigextu32 low);
      td <- (sigextu32 t);
      wd <- (wd - td);
      diff <- (truncateu16 wd);
      wd <- (sigextu32 low);
      td <- (sigextu32 t);
      wd <- (wd + td);
      sum <- (truncateu16 wd);
      aux <@ __barrett_reduce (diff);
      rp.[(W64.to_uint (i + (W64.of_int 8)))] <- aux;
      aux <@ __barrett_reduce (sum);
      rp.[(W64.to_uint i)] <- aux;
      i <- (i + (W64.of_int 1));
    }
    return rp;
  }
  proc jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_8 (rp:W16.t Array768.t) : 
  W16.t Array768.t = {
    var  _0:W64.t;
     _0 <- (init_msf);
    rp <@ __radix2_8_block (rp, (W64.of_int 0), (W16.of_int 1449));
    rp <@ __radix2_8_block (rp, (W64.of_int 16), (W16.of_int 837));
    rp <@ __radix2_8_block (rp, (W64.of_int 32), (W16.of_int 901));
    rp <@ __radix2_8_block (rp, (W64.of_int 48), (W16.of_int 1637));
    rp <@ __radix2_8_block (rp, (W64.of_int 64), (W16.of_int (- 569)));
    rp <@ __radix2_8_block (rp, (W64.of_int 80), (W16.of_int (- 1617)));
    rp <@ __radix2_8_block (rp, (W64.of_int 96), (W16.of_int (- 1530)));
    rp <@ __radix2_8_block (rp, (W64.of_int 112), (W16.of_int 1199));
    rp <@ __radix2_8_block (rp, (W64.of_int 128), (W16.of_int 50));
    rp <@ __radix2_8_block (rp, (W64.of_int 144), (W16.of_int (- 830)));
    rp <@ __radix2_8_block (rp, (W64.of_int 160), (W16.of_int (- 625)));
    rp <@ __radix2_8_block (rp, (W64.of_int 176), (W16.of_int 4));
    rp <@ __radix2_8_block (rp, (W64.of_int 192), (W16.of_int 176));
    rp <@ __radix2_8_block (rp, (W64.of_int 208), (W16.of_int (- 156)));
    rp <@ __radix2_8_block (rp, (W64.of_int 224), (W16.of_int 1257));
    rp <@ __radix2_8_block (rp, (W64.of_int 240), (W16.of_int (- 1507)));
    rp <@ __radix2_8_block (rp, (W64.of_int 256), (W16.of_int (- 380)));
    rp <@ __radix2_8_block (rp, (W64.of_int 272), (W16.of_int (- 606)));
    rp <@ __radix2_8_block (rp, (W64.of_int 288), (W16.of_int 1293));
    rp <@ __radix2_8_block (rp, (W64.of_int 304), (W16.of_int 661));
    rp <@ __radix2_8_block (rp, (W64.of_int 320), (W16.of_int 1428));
    rp <@ __radix2_8_block (rp, (W64.of_int 336), (W16.of_int (- 1580)));
    rp <@ __radix2_8_block (rp, (W64.of_int 352), (W16.of_int (- 565)));
    rp <@ __radix2_8_block (rp, (W64.of_int 368), (W16.of_int (- 992)));
    rp <@ __radix2_8_block (rp, (W64.of_int 384), (W16.of_int 548));
    rp <@ __radix2_8_block (rp, (W64.of_int 400), (W16.of_int (- 800)));
    rp <@ __radix2_8_block (rp, (W64.of_int 416), (W16.of_int 64));
    rp <@ __radix2_8_block (rp, (W64.of_int 432), (W16.of_int (- 371)));
    rp <@ __radix2_8_block (rp, (W64.of_int 448), (W16.of_int 961));
    rp <@ __radix2_8_block (rp, (W64.of_int 464), (W16.of_int 641));
    rp <@ __radix2_8_block (rp, (W64.of_int 480), (W16.of_int 87));
    rp <@ __radix2_8_block (rp, (W64.of_int 496), (W16.of_int 630));
    rp <@ __radix2_8_block (rp, (W64.of_int 512), (W16.of_int 675));
    rp <@ __radix2_8_block (rp, (W64.of_int 528), (W16.of_int (- 834)));
    rp <@ __radix2_8_block (rp, (W64.of_int 544), (W16.of_int 205));
    rp <@ __radix2_8_block (rp, (W64.of_int 560), (W16.of_int 54));
    rp <@ __radix2_8_block (rp, (W64.of_int 576), (W16.of_int (- 1081)));
    rp <@ __radix2_8_block (rp, (W64.of_int 592), (W16.of_int 1351));
    rp <@ __radix2_8_block (rp, (W64.of_int 608), (W16.of_int 1413));
    rp <@ __radix2_8_block (rp, (W64.of_int 624), (W16.of_int (- 1331)));
    rp <@ __radix2_8_block (rp, (W64.of_int 640), (W16.of_int (- 1673)));
    rp <@ __radix2_8_block (rp, (W64.of_int 656), (W16.of_int (- 1267)));
    rp <@ __radix2_8_block (rp, (W64.of_int 672), (W16.of_int (- 1558)));
    rp <@ __radix2_8_block (rp, (W64.of_int 688), (W16.of_int 281));
    rp <@ __radix2_8_block (rp, (W64.of_int 704), (W16.of_int (- 1464)));
    rp <@ __radix2_8_block (rp, (W64.of_int 720), (W16.of_int (- 588)));
    rp <@ __radix2_8_block (rp, (W64.of_int 736), (W16.of_int 1015));
    rp <@ __radix2_8_block (rp, (W64.of_int 752), (W16.of_int 436));
    return rp;
  }
}.
