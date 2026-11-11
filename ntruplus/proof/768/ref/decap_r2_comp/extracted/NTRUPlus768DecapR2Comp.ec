require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import Array4 Array96 Array768 WArray8 WArray192 WArray1536.

abbrev product__NTRUPLUS_ZETAS96 =
((Array96.of_list witness<:W16.t>)
[(W16.of_int 223); (W16.of_int 1138); (W16.of_int (-1059));
(W16.of_int (-397)); (W16.of_int (-183)); (W16.of_int 1655);
(W16.of_int 559); (W16.of_int (-1674)); (W16.of_int 277); (W16.of_int 933);
(W16.of_int 1723); (W16.of_int 437); (W16.of_int (-1514)); (W16.of_int 242);
(W16.of_int 1640); (W16.of_int 432); (W16.of_int (-1583)); (W16.of_int 696);
(W16.of_int 774); (W16.of_int 1671); (W16.of_int 927); (W16.of_int 514);
(W16.of_int 512); (W16.of_int 489); (W16.of_int 297); (W16.of_int 601);
(W16.of_int 1473); (W16.of_int 1130); (W16.of_int 1322); (W16.of_int 871);
(W16.of_int 760); (W16.of_int 1212); (W16.of_int (-312));
(W16.of_int (-352)); (W16.of_int 443); (W16.of_int 943); (W16.of_int 8);
(W16.of_int 1250); (W16.of_int (-100)); (W16.of_int 1660);
(W16.of_int (-31)); (W16.of_int 1206); (W16.of_int (-1341));
(W16.of_int (-1247)); (W16.of_int 444); (W16.of_int 235); (W16.of_int 1364);
(W16.of_int (-1209)); (W16.of_int 361); (W16.of_int 230); (W16.of_int 673);
(W16.of_int 582); (W16.of_int 1409); (W16.of_int 1501); (W16.of_int 1401);
(W16.of_int 251); (W16.of_int 1022); (W16.of_int (-1063)); (W16.of_int 1053);
(W16.of_int 1188); (W16.of_int 417); (W16.of_int (-1391));
(W16.of_int (-27)); (W16.of_int (-1626)); (W16.of_int 1685);
(W16.of_int (-315)); (W16.of_int 1408); (W16.of_int (-1248));
(W16.of_int 400); (W16.of_int 274); (W16.of_int (-1543)); (W16.of_int 32);
(W16.of_int (-1550)); (W16.of_int 1531); (W16.of_int (-1367));
(W16.of_int (-124)); (W16.of_int 1458); (W16.of_int 1379);
(W16.of_int (-940)); (W16.of_int (-1681)); (W16.of_int 22);
(W16.of_int 1709); (W16.of_int (-275)); (W16.of_int 1108); (W16.of_int 354);
(W16.of_int (-1728)); (W16.of_int (-968)); (W16.of_int 858);
(W16.of_int 1221); (W16.of_int (-218)); (W16.of_int 294);
(W16.of_int (-732)); (W16.of_int (-1095)); (W16.of_int 892);
(W16.of_int 1588); (W16.of_int (-779))]).

module M = {
  proc forward__Stage1____mul_i16 (a:W16.t, b:W16.t) : W32.t = {
    var c:W32.t;
    var ad:W32.t;
    var bd:W32.t;
    ad <- (sigextu32 a);
    bd <- (sigextu32 b);
    c <- (ad * bd);
    return c;
  }
  proc forward__Stage1____montgomery_reduce (a:W32.t) : W16.t = {
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
  proc forward__Stage1__jade_ntruplus_ntruplus768_amd64_ref_ntt_stage1 (
  rp:W16.t Array768.t, ap:W16.t Array768.t) : W16.t Array768.t = {
    var i:W64.t;
    var a0:W16.t;
    var a1:W16.t;
    var acc:W32.t;
    var t:W16.t;
    var lo:W16.t;
    var hi:W16.t;
    var  _0:W64.t;
     _0 <- (init_msf);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int (768 %/ 2)))) {
      a0 <- ap.[(W64.to_uint i)];
      a1 <- ap.[(W64.to_uint (i + (W64.of_int (768 %/ 2))))];
      acc <@ forward__Stage1____mul_i16 ((W16.of_int (- 1033)), a1);
      t <@ forward__Stage1____montgomery_reduce (acc);
      lo <- a0;
      lo <- (lo + t);
      hi <- a0;
      hi <- (hi + a1);
      hi <- (hi - t);
      rp.[(W64.to_uint i)] <- lo;
      rp.[(W64.to_uint (i + (W64.of_int (768 %/ 2))))] <- hi;
      i <- (i + (W64.of_int 1));
    }
    return rp;
  }
  proc forward__Radix3____mul_i16 (a:W16.t, b:W16.t) : W32.t = {
    var c:W32.t;
    var ad:W32.t;
    var bd:W32.t;
    ad <- (sigextu32 a);
    bd <- (sigextu32 b);
    c <- (ad * bd);
    return c;
  }
  proc forward__Radix3____montgomery_reduce (a:W32.t) : W16.t = {
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
  proc forward__Radix3__jade_ntruplus_ntruplus768_amd64_ref_ntt_radix3 (
  rp:W16.t Array768.t) : W16.t Array768.t = {
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
      acc <@ forward__Radix3____mul_i16 ((W16.of_int (- 682)), a1);
      t1 <@ forward__Radix3____montgomery_reduce (acc);
      acc <@ forward__Radix3____mul_i16 ((W16.of_int (- 248)), a2);
      t2 <@ forward__Radix3____montgomery_reduce (acc);
      td <- t1;
      td <- (td - t2);
      acc <@ forward__Radix3____mul_i16 ((W16.of_int (- 886)), td);
      t3 <@ forward__Radix3____montgomery_reduce (acc);
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
      acc <@ forward__Radix3____mul_i16 ((W16.of_int (- 708)), a1);
      t1 <@ forward__Radix3____montgomery_reduce (acc);
      acc <@ forward__Radix3____mul_i16 ((W16.of_int 682), a2);
      t2 <@ forward__Radix3____montgomery_reduce (acc);
      td <- t1;
      td <- (td - t2);
      acc <@ forward__Radix3____mul_i16 ((W16.of_int (- 886)), td);
      t3 <@ forward__Radix3____montgomery_reduce (acc);
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
  proc forward__Radix2_64____mul_i16 (a:W16.t, b:W16.t) : W32.t = {
    var c:W32.t;
    var ad:W32.t;
    var bd:W32.t;
    ad <- (sigextu32 a);
    bd <- (sigextu32 b);
    c <- (ad * bd);
    return c;
  }
  proc forward__Radix2_64____montgomery_reduce (a:W32.t) : W16.t = {
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
  proc forward__Radix2_64____barrett_reduce (a:W16.t) : W16.t = {
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
  proc forward__Radix2_64____radix2_64_block (rp:W16.t Array768.t,
                                              base:W64.t, zeta_0:W16.t) : 
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
    stop <- (stop + (W64.of_int 64));
    while ((i \ult stop)) {
      low <- rp.[(W64.to_uint i)];
      high <- rp.[(W64.to_uint (i + (W64.of_int 64)))];
      acc <@ forward__Radix2_64____mul_i16 (zeta_0, high);
      t <@ forward__Radix2_64____montgomery_reduce (acc);
      wd <- (sigextu32 low);
      td <- (sigextu32 t);
      wd <- (wd - td);
      diff <- (truncateu16 wd);
      wd <- (sigextu32 low);
      td <- (sigextu32 t);
      wd <- (wd + td);
      sum <- (truncateu16 wd);
      aux <@ forward__Radix2_64____barrett_reduce (diff);
      rp.[(W64.to_uint (i + (W64.of_int 64)))] <- aux;
      aux <@ forward__Radix2_64____barrett_reduce (sum);
      rp.[(W64.to_uint i)] <- aux;
      i <- (i + (W64.of_int 1));
    }
    return rp;
  }
  proc forward__Radix2_64__jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_64 (
  rp:W16.t Array768.t) : W16.t Array768.t = {
    var  _0:W64.t;
     _0 <- (init_msf);
    rp <@ forward__Radix2_64____radix2_64_block (rp, (W64.of_int 0),
    (W16.of_int 1));
    rp <@ forward__Radix2_64____radix2_64_block (rp, (W64.of_int 128),
    (W16.of_int (- 722)));
    rp <@ forward__Radix2_64____radix2_64_block (rp, (W64.of_int 256),
    (W16.of_int (- 723)));
    rp <@ forward__Radix2_64____radix2_64_block (rp, (W64.of_int 384),
    (W16.of_int (- 257)));
    rp <@ forward__Radix2_64____radix2_64_block (rp, (W64.of_int 512),
    (W16.of_int (- 1124)));
    rp <@ forward__Radix2_64____radix2_64_block (rp, (W64.of_int 640),
    (W16.of_int (- 867)));
    return rp;
  }
  proc forward__Radix2_32____mul_i16 (a:W16.t, b:W16.t) : W32.t = {
    var c:W32.t;
    var ad:W32.t;
    var bd:W32.t;
    ad <- (sigextu32 a);
    bd <- (sigextu32 b);
    c <- (ad * bd);
    return c;
  }
  proc forward__Radix2_32____montgomery_reduce (a:W32.t) : W16.t = {
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
  proc forward__Radix2_32____barrett_reduce (a:W16.t) : W16.t = {
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
  proc forward__Radix2_32____radix2_32_block (rp:W16.t Array768.t,
                                              base:W64.t, zeta_0:W16.t) : 
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
    stop <- (stop + (W64.of_int 32));
    while ((i \ult stop)) {
      low <- rp.[(W64.to_uint i)];
      high <- rp.[(W64.to_uint (i + (W64.of_int 32)))];
      acc <@ forward__Radix2_32____mul_i16 (zeta_0, high);
      t <@ forward__Radix2_32____montgomery_reduce (acc);
      wd <- (sigextu32 low);
      td <- (sigextu32 t);
      wd <- (wd - td);
      diff <- (truncateu16 wd);
      wd <- (sigextu32 low);
      td <- (sigextu32 t);
      wd <- (wd + td);
      sum <- (truncateu16 wd);
      aux <@ forward__Radix2_32____barrett_reduce (diff);
      rp.[(W64.to_uint (i + (W64.of_int 32)))] <- aux;
      aux <@ forward__Radix2_32____barrett_reduce (sum);
      rp.[(W64.to_uint i)] <- aux;
      i <- (i + (W64.of_int 1));
    }
    return rp;
  }
  proc forward__Radix2_32__jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_32 (
  rp:W16.t Array768.t) : W16.t Array768.t = {
    var  _0:W64.t;
     _0 <- (init_msf);
    rp <@ forward__Radix2_32____radix2_32_block (rp, (W64.of_int 0),
    (W16.of_int (- 256)));
    rp <@ forward__Radix2_32____radix2_32_block (rp, (W64.of_int 64),
    (W16.of_int 1484));
    rp <@ forward__Radix2_32____radix2_32_block (rp, (W64.of_int 128),
    (W16.of_int 1262));
    rp <@ forward__Radix2_32____radix2_32_block (rp, (W64.of_int 192),
    (W16.of_int (- 1590)));
    rp <@ forward__Radix2_32____radix2_32_block (rp, (W64.of_int 256),
    (W16.of_int 1611));
    rp <@ forward__Radix2_32____radix2_32_block (rp, (W64.of_int 320),
    (W16.of_int 222));
    rp <@ forward__Radix2_32____radix2_32_block (rp, (W64.of_int 384),
    (W16.of_int 1164));
    rp <@ forward__Radix2_32____radix2_32_block (rp, (W64.of_int 448),
    (W16.of_int (- 1346)));
    rp <@ forward__Radix2_32____radix2_32_block (rp, (W64.of_int 512),
    (W16.of_int 1716));
    rp <@ forward__Radix2_32____radix2_32_block (rp, (W64.of_int 576),
    (W16.of_int (- 1521)));
    rp <@ forward__Radix2_32____radix2_32_block (rp, (W64.of_int 640),
    (W16.of_int (- 357)));
    rp <@ forward__Radix2_32____radix2_32_block (rp, (W64.of_int 704),
    (W16.of_int 395));
    return rp;
  }
  proc forward__Radix2_16____mul_i16 (a:W16.t, b:W16.t) : W32.t = {
    var c:W32.t;
    var ad:W32.t;
    var bd:W32.t;
    ad <- (sigextu32 a);
    bd <- (sigextu32 b);
    c <- (ad * bd);
    return c;
  }
  proc forward__Radix2_16____montgomery_reduce (a:W32.t) : W16.t = {
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
  proc forward__Radix2_16____barrett_reduce (a:W16.t) : W16.t = {
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
  proc forward__Radix2_16____radix2_16_block (rp:W16.t Array768.t,
                                              base:W64.t, zeta_0:W16.t) : 
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
    stop <- (stop + (W64.of_int 16));
    while ((i \ult stop)) {
      low <- rp.[(W64.to_uint i)];
      high <- rp.[(W64.to_uint (i + (W64.of_int 16)))];
      acc <@ forward__Radix2_16____mul_i16 (zeta_0, high);
      t <@ forward__Radix2_16____montgomery_reduce (acc);
      wd <- (sigextu32 low);
      td <- (sigextu32 t);
      wd <- (wd - td);
      diff <- (truncateu16 wd);
      wd <- (sigextu32 low);
      td <- (sigextu32 t);
      wd <- (wd + td);
      sum <- (truncateu16 wd);
      aux <@ forward__Radix2_16____barrett_reduce (diff);
      rp.[(W64.to_uint (i + (W64.of_int 16)))] <- aux;
      aux <@ forward__Radix2_16____barrett_reduce (sum);
      rp.[(W64.to_uint i)] <- aux;
      i <- (i + (W64.of_int 1));
    }
    return rp;
  }
  proc forward__Radix2_16__jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_16 (
  rp:W16.t Array768.t) : W16.t Array768.t = {
    var  _0:W64.t;
     _0 <- (init_msf);
    rp <@ forward__Radix2_16____radix2_16_block (rp, (W64.of_int 0),
    (W16.of_int (- 455)));
    rp <@ forward__Radix2_16____radix2_16_block (rp, (W64.of_int 32),
    (W16.of_int 639));
    rp <@ forward__Radix2_16____radix2_16_block (rp, (W64.of_int 64),
    (W16.of_int 502));
    rp <@ forward__Radix2_16____radix2_16_block (rp, (W64.of_int 96),
    (W16.of_int 655));
    rp <@ forward__Radix2_16____radix2_16_block (rp, (W64.of_int 128),
    (W16.of_int (- 699)));
    rp <@ forward__Radix2_16____radix2_16_block (rp, (W64.of_int 160),
    (W16.of_int 541));
    rp <@ forward__Radix2_16____radix2_16_block (rp, (W64.of_int 192),
    (W16.of_int 95));
    rp <@ forward__Radix2_16____radix2_16_block (rp, (W64.of_int 224),
    (W16.of_int (- 1577)));
    rp <@ forward__Radix2_16____radix2_16_block (rp, (W64.of_int 256),
    (W16.of_int (- 1241)));
    rp <@ forward__Radix2_16____radix2_16_block (rp, (W64.of_int 288),
    (W16.of_int 550));
    rp <@ forward__Radix2_16____radix2_16_block (rp, (W64.of_int 320),
    (W16.of_int (- 44)));
    rp <@ forward__Radix2_16____radix2_16_block (rp, (W64.of_int 352),
    (W16.of_int 39));
    rp <@ forward__Radix2_16____radix2_16_block (rp, (W64.of_int 384),
    (W16.of_int (- 820)));
    rp <@ forward__Radix2_16____radix2_16_block (rp, (W64.of_int 416),
    (W16.of_int (- 216)));
    rp <@ forward__Radix2_16____radix2_16_block (rp, (W64.of_int 448),
    (W16.of_int (- 121)));
    rp <@ forward__Radix2_16____radix2_16_block (rp, (W64.of_int 480),
    (W16.of_int (- 757)));
    rp <@ forward__Radix2_16____radix2_16_block (rp, (W64.of_int 512),
    (W16.of_int (- 348)));
    rp <@ forward__Radix2_16____radix2_16_block (rp, (W64.of_int 544),
    (W16.of_int 937));
    rp <@ forward__Radix2_16____radix2_16_block (rp, (W64.of_int 576),
    (W16.of_int 893));
    rp <@ forward__Radix2_16____radix2_16_block (rp, (W64.of_int 608),
    (W16.of_int 387));
    rp <@ forward__Radix2_16____radix2_16_block (rp, (W64.of_int 640),
    (W16.of_int (- 603)));
    rp <@ forward__Radix2_16____radix2_16_block (rp, (W64.of_int 672),
    (W16.of_int 1713));
    rp <@ forward__Radix2_16____radix2_16_block (rp, (W64.of_int 704),
    (W16.of_int (- 1105)));
    rp <@ forward__Radix2_16____radix2_16_block (rp, (W64.of_int 736),
    (W16.of_int 1058));
    return rp;
  }
  proc forward__Radix2_8____mul_i16 (a:W16.t, b:W16.t) : W32.t = {
    var c:W32.t;
    var ad:W32.t;
    var bd:W32.t;
    ad <- (sigextu32 a);
    bd <- (sigextu32 b);
    c <- (ad * bd);
    return c;
  }
  proc forward__Radix2_8____montgomery_reduce (a:W32.t) : W16.t = {
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
  proc forward__Radix2_8____barrett_reduce (a:W16.t) : W16.t = {
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
  proc forward__Radix2_8____radix2_8_block (rp:W16.t Array768.t, base:W64.t,
                                            zeta_0:W16.t) : W16.t Array768.t = {
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
      acc <@ forward__Radix2_8____mul_i16 (zeta_0, high);
      t <@ forward__Radix2_8____montgomery_reduce (acc);
      wd <- (sigextu32 low);
      td <- (sigextu32 t);
      wd <- (wd - td);
      diff <- (truncateu16 wd);
      wd <- (sigextu32 low);
      td <- (sigextu32 t);
      wd <- (wd + td);
      sum <- (truncateu16 wd);
      aux <@ forward__Radix2_8____barrett_reduce (diff);
      rp.[(W64.to_uint (i + (W64.of_int 8)))] <- aux;
      aux <@ forward__Radix2_8____barrett_reduce (sum);
      rp.[(W64.to_uint i)] <- aux;
      i <- (i + (W64.of_int 1));
    }
    return rp;
  }
  proc forward__Radix2_8__jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_8 (
  rp:W16.t Array768.t) : W16.t Array768.t = {
    var  _0:W64.t;
     _0 <- (init_msf);
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 0),
    (W16.of_int 1449));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 16),
    (W16.of_int 837));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 32),
    (W16.of_int 901));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 48),
    (W16.of_int 1637));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 64),
    (W16.of_int (- 569)));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 80),
    (W16.of_int (- 1617)));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 96),
    (W16.of_int (- 1530)));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 112),
    (W16.of_int 1199));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 128),
    (W16.of_int 50));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 144),
    (W16.of_int (- 830)));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 160),
    (W16.of_int (- 625)));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 176),
    (W16.of_int 4));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 192),
    (W16.of_int 176));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 208),
    (W16.of_int (- 156)));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 224),
    (W16.of_int 1257));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 240),
    (W16.of_int (- 1507)));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 256),
    (W16.of_int (- 380)));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 272),
    (W16.of_int (- 606)));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 288),
    (W16.of_int 1293));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 304),
    (W16.of_int 661));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 320),
    (W16.of_int 1428));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 336),
    (W16.of_int (- 1580)));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 352),
    (W16.of_int (- 565)));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 368),
    (W16.of_int (- 992)));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 384),
    (W16.of_int 548));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 400),
    (W16.of_int (- 800)));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 416),
    (W16.of_int 64));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 432),
    (W16.of_int (- 371)));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 448),
    (W16.of_int 961));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 464),
    (W16.of_int 641));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 480),
    (W16.of_int 87));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 496),
    (W16.of_int 630));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 512),
    (W16.of_int 675));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 528),
    (W16.of_int (- 834)));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 544),
    (W16.of_int 205));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 560),
    (W16.of_int 54));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 576),
    (W16.of_int (- 1081)));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 592),
    (W16.of_int 1351));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 608),
    (W16.of_int 1413));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 624),
    (W16.of_int (- 1331)));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 640),
    (W16.of_int (- 1673)));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 656),
    (W16.of_int (- 1267)));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 672),
    (W16.of_int (- 1558)));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 688),
    (W16.of_int 281));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 704),
    (W16.of_int (- 1464)));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 720),
    (W16.of_int (- 588)));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 736),
    (W16.of_int 1015));
    rp <@ forward__Radix2_8____radix2_8_block (rp, (W64.of_int 752),
    (W16.of_int 436));
    return rp;
  }
  proc forward__Radix2_4____mul_i16 (a:W16.t, b:W16.t) : W32.t = {
    var c:W32.t;
    var ad:W32.t;
    var bd:W32.t;
    ad <- (sigextu32 a);
    bd <- (sigextu32 b);
    c <- (ad * bd);
    return c;
  }
  proc forward__Radix2_4____montgomery_reduce (a:W32.t) : W16.t = {
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
  proc forward__Radix2_4____barrett_reduce (a:W16.t) : W16.t = {
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
  proc forward__Radix2_4____radix2_4_block (rp:W16.t Array768.t, base:W64.t,
                                            zeta_0:W16.t) : W16.t Array768.t = {
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
    stop <- (stop + (W64.of_int 4));
    while ((i \ult stop)) {
      low <- rp.[(W64.to_uint i)];
      high <- rp.[(W64.to_uint (i + (W64.of_int 4)))];
      acc <@ forward__Radix2_4____mul_i16 (zeta_0, high);
      t <@ forward__Radix2_4____montgomery_reduce (acc);
      wd <- (sigextu32 low);
      td <- (sigextu32 t);
      wd <- (wd - td);
      diff <- (truncateu16 wd);
      wd <- (sigextu32 low);
      td <- (sigextu32 t);
      wd <- (wd + td);
      sum <- (truncateu16 wd);
      aux <@ forward__Radix2_4____barrett_reduce (diff);
      rp.[(W64.to_uint (i + (W64.of_int 4)))] <- aux;
      aux <@ forward__Radix2_4____barrett_reduce (sum);
      rp.[(W64.to_uint i)] <- aux;
      i <- (i + (W64.of_int 1));
    }
    return rp;
  }
  proc forward__Radix2_4__jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_4 (
  rp:W16.t Array768.t) : W16.t Array768.t = {
    var  _0:W64.t;
     _0 <- (init_msf);
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 0),
    (W16.of_int 223));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 8),
    (W16.of_int 1138));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 16),
    (W16.of_int (- 1059)));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 24),
    (W16.of_int (- 397)));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 32),
    (W16.of_int (- 183)));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 40),
    (W16.of_int 1655));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 48),
    (W16.of_int 559));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 56),
    (W16.of_int (- 1674)));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 64),
    (W16.of_int 277));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 72),
    (W16.of_int 933));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 80),
    (W16.of_int 1723));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 88),
    (W16.of_int 437));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 96),
    (W16.of_int (- 1514)));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 104),
    (W16.of_int 242));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 112),
    (W16.of_int 1640));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 120),
    (W16.of_int 432));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 128),
    (W16.of_int (- 1583)));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 136),
    (W16.of_int 696));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 144),
    (W16.of_int 774));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 152),
    (W16.of_int 1671));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 160),
    (W16.of_int 927));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 168),
    (W16.of_int 514));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 176),
    (W16.of_int 512));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 184),
    (W16.of_int 489));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 192),
    (W16.of_int 297));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 200),
    (W16.of_int 601));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 208),
    (W16.of_int 1473));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 216),
    (W16.of_int 1130));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 224),
    (W16.of_int 1322));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 232),
    (W16.of_int 871));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 240),
    (W16.of_int 760));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 248),
    (W16.of_int 1212));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 256),
    (W16.of_int (- 312)));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 264),
    (W16.of_int (- 352)));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 272),
    (W16.of_int 443));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 280),
    (W16.of_int 943));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 288),
    (W16.of_int 8));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 296),
    (W16.of_int 1250));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 304),
    (W16.of_int (- 100)));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 312),
    (W16.of_int 1660));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 320),
    (W16.of_int (- 31)));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 328),
    (W16.of_int 1206));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 336),
    (W16.of_int (- 1341)));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 344),
    (W16.of_int (- 1247)));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 352),
    (W16.of_int 444));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 360),
    (W16.of_int 235));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 368),
    (W16.of_int 1364));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 376),
    (W16.of_int (- 1209)));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 384),
    (W16.of_int 361));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 392),
    (W16.of_int 230));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 400),
    (W16.of_int 673));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 408),
    (W16.of_int 582));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 416),
    (W16.of_int 1409));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 424),
    (W16.of_int 1501));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 432),
    (W16.of_int 1401));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 440),
    (W16.of_int 251));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 448),
    (W16.of_int 1022));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 456),
    (W16.of_int (- 1063)));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 464),
    (W16.of_int 1053));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 472),
    (W16.of_int 1188));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 480),
    (W16.of_int 417));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 488),
    (W16.of_int (- 1391)));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 496),
    (W16.of_int (- 27)));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 504),
    (W16.of_int (- 1626)));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 512),
    (W16.of_int 1685));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 520),
    (W16.of_int (- 315)));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 528),
    (W16.of_int 1408));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 536),
    (W16.of_int (- 1248)));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 544),
    (W16.of_int 400));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 552),
    (W16.of_int 274));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 560),
    (W16.of_int (- 1543)));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 568),
    (W16.of_int 32));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 576),
    (W16.of_int (- 1550)));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 584),
    (W16.of_int 1531));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 592),
    (W16.of_int (- 1367)));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 600),
    (W16.of_int (- 124)));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 608),
    (W16.of_int 1458));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 616),
    (W16.of_int 1379));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 624),
    (W16.of_int (- 940)));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 632),
    (W16.of_int (- 1681)));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 640),
    (W16.of_int 22));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 648),
    (W16.of_int 1709));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 656),
    (W16.of_int (- 275)));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 664),
    (W16.of_int 1108));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 672),
    (W16.of_int 354));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 680),
    (W16.of_int (- 1728)));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 688),
    (W16.of_int (- 968)));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 696),
    (W16.of_int 858));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 704),
    (W16.of_int 1221));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 712),
    (W16.of_int (- 218)));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 720),
    (W16.of_int 294));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 728),
    (W16.of_int (- 732)));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 736),
    (W16.of_int (- 1095)));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 744),
    (W16.of_int 892));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 752),
    (W16.of_int 1588));
    rp <@ forward__Radix2_4____radix2_4_block (rp, (W64.of_int 760),
    (W16.of_int (- 779)));
    return rp;
  }
  proc forward__jade_ntruplus_ntruplus768_amd64_ref_ntt (rp:W16.t Array768.t,
                                                         ap:W16.t Array768.t) : 
  W16.t Array768.t = {
    
    rp <@ forward__Stage1__jade_ntruplus_ntruplus768_amd64_ref_ntt_stage1 (
    rp, ap);
    rp <@ forward__Radix3__jade_ntruplus_ntruplus768_amd64_ref_ntt_radix3 (
    rp);
    rp <@ forward__Radix2_64__jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_64 (
    rp);
    rp <@ forward__Radix2_32__jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_32 (
    rp);
    rp <@ forward__Radix2_16__jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_16 (
    rp);
    rp <@ forward__Radix2_8__jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_8 (
    rp);
    rp <@ forward__Radix2_4__jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_4 (
    rp);
    return rp;
  }
  proc difference__jade_ntruplus_ntruplus768_amd64_ref_poly_sub (rp:W16.t Array768.t,
                                                                 ap:W16.t Array768.t,
                                                                 bp:W16.t Array768.t) : 
  W16.t Array768.t = {
    var i:W64.t;
    var t:W16.t;
    var  _0:W64.t;
     _0 <- (init_msf);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 768))) {
      t <- ap.[(W64.to_uint i)];
      t <- (t - bp.[(W64.to_uint i)]);
      rp.[(W64.to_uint i)] <- t;
      i <- (i + (W64.of_int 1));
    }
    return rp;
  }
  proc product____mul_i16 (a:W16.t, b:W16.t) : W32.t = {
    var c:W32.t;
    var ad:W32.t;
    var bd:W32.t;
    ad <- (sigextu32 a);
    bd <- (sigextu32 b);
    c <- (ad * bd);
    return c;
  }
  proc product____montgomery_reduce (a:W32.t) : W16.t = {
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
  proc product____basemul4 (r:W16.t Array4.t, a:W16.t Array4.t,
                            b:W16.t Array4.t, zeta_0:W16.t) : W16.t Array4.t = {
    var aux:W16.t;
    var acc:W32.t;
    var term:W32.t;
    acc <@ product____mul_i16 (a.[1], b.[3]);
    term <@ product____mul_i16 (a.[2], b.[2]);
    acc <- (acc + term);
    term <@ product____mul_i16 (a.[3], b.[1]);
    acc <- (acc + term);
    aux <@ product____montgomery_reduce (acc);
    r.[0] <- aux;
    acc <@ product____mul_i16 (a.[2], b.[3]);
    term <@ product____mul_i16 (a.[3], b.[2]);
    acc <- (acc + term);
    aux <@ product____montgomery_reduce (acc);
    r.[1] <- aux;
    acc <@ product____mul_i16 (a.[3], b.[3]);
    aux <@ product____montgomery_reduce (acc);
    r.[2] <- aux;
    acc <@ product____mul_i16 (r.[0], zeta_0);
    term <@ product____mul_i16 (a.[0], b.[0]);
    acc <- (acc + term);
    aux <@ product____montgomery_reduce (acc);
    r.[0] <- aux;
    acc <@ product____mul_i16 (r.[1], zeta_0);
    term <@ product____mul_i16 (a.[0], b.[1]);
    acc <- (acc + term);
    term <@ product____mul_i16 (a.[1], b.[0]);
    acc <- (acc + term);
    aux <@ product____montgomery_reduce (acc);
    r.[1] <- aux;
    acc <@ product____mul_i16 (r.[2], zeta_0);
    term <@ product____mul_i16 (a.[0], b.[2]);
    acc <- (acc + term);
    term <@ product____mul_i16 (a.[1], b.[1]);
    acc <- (acc + term);
    term <@ product____mul_i16 (a.[2], b.[0]);
    acc <- (acc + term);
    aux <@ product____montgomery_reduce (acc);
    r.[2] <- aux;
    acc <@ product____mul_i16 (a.[0], b.[3]);
    term <@ product____mul_i16 (a.[1], b.[2]);
    acc <- (acc + term);
    term <@ product____mul_i16 (a.[2], b.[1]);
    acc <- (acc + term);
    term <@ product____mul_i16 (a.[3], b.[0]);
    acc <- (acc + term);
    aux <@ product____montgomery_reduce (acc);
    r.[3] <- aux;
    acc <@ product____mul_i16 (r.[0], (W16.of_int 867));
    aux <@ product____montgomery_reduce (acc);
    r.[0] <- aux;
    acc <@ product____mul_i16 (r.[1], (W16.of_int 867));
    aux <@ product____montgomery_reduce (acc);
    r.[1] <- aux;
    acc <@ product____mul_i16 (r.[2], (W16.of_int 867));
    aux <@ product____montgomery_reduce (acc);
    r.[2] <- aux;
    acc <@ product____mul_i16 (r.[3], (W16.of_int 867));
    aux <@ product____montgomery_reduce (acc);
    r.[3] <- aux;
    return r;
  }
  proc product__jade_ntruplus_ntruplus768_amd64_ref_poly_basemul (rp:W16.t Array768.t,
                                                                  ap:W16.t Array768.t,
                                                                  bp:W16.t Array768.t) : 
  W16.t Array768.t = {
    var zetasp:W16.t Array96.t;
    var i:W64.t;
    var zeta_0:W16.t;
    var off:W64.t;
    var ta:W16.t Array4.t;
    var tb:W16.t Array4.t;
    var tr:W16.t Array4.t;
    var  _0:W64.t;
    ta <- witness;
    tb <- witness;
    tr <- witness;
    zetasp <- witness;
     _0 <- (init_msf);
    zetasp <-
    (Array96.init (fun i_0 => product__NTRUPLUS_ZETAS96.[(0 + i_0)]));
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int (768 %/ 8)))) {
      zeta_0 <- zetasp.[(W64.to_uint i)];
      off <- i;
      off <- (off `<<` (W8.of_int 3));
      ta.[0] <- ap.[(W64.to_uint off)];
      ta.[1] <- ap.[(W64.to_uint (off + (W64.of_int 1)))];
      ta.[2] <- ap.[(W64.to_uint (off + (W64.of_int 2)))];
      ta.[3] <- ap.[(W64.to_uint (off + (W64.of_int 3)))];
      tb.[0] <- bp.[(W64.to_uint off)];
      tb.[1] <- bp.[(W64.to_uint (off + (W64.of_int 1)))];
      tb.[2] <- bp.[(W64.to_uint (off + (W64.of_int 2)))];
      tb.[3] <- bp.[(W64.to_uint (off + (W64.of_int 3)))];
      tr <@ product____basemul4 (tr, ta, tb, zeta_0);
      rp.[(W64.to_uint off)] <- tr.[0];
      rp.[(W64.to_uint (off + (W64.of_int 1)))] <- tr.[1];
      rp.[(W64.to_uint (off + (W64.of_int 2)))] <- tr.[2];
      rp.[(W64.to_uint (off + (W64.of_int 3)))] <- tr.[3];
      off <- (off + (W64.of_int 4));
      ta.[0] <- ap.[(W64.to_uint off)];
      ta.[1] <- ap.[(W64.to_uint (off + (W64.of_int 1)))];
      ta.[2] <- ap.[(W64.to_uint (off + (W64.of_int 2)))];
      ta.[3] <- ap.[(W64.to_uint (off + (W64.of_int 3)))];
      tb.[0] <- bp.[(W64.to_uint off)];
      tb.[1] <- bp.[(W64.to_uint (off + (W64.of_int 1)))];
      tb.[2] <- bp.[(W64.to_uint (off + (W64.of_int 2)))];
      tb.[3] <- bp.[(W64.to_uint (off + (W64.of_int 3)))];
      tr <@ product____basemul4 (tr, ta, tb, (- zeta_0));
      rp.[(W64.to_uint off)] <- tr.[0];
      rp.[(W64.to_uint (off + (W64.of_int 1)))] <- tr.[1];
      rp.[(W64.to_uint (off + (W64.of_int 2)))] <- tr.[2];
      rp.[(W64.to_uint (off + (W64.of_int 3)))] <- tr.[3];
      i <- (i + (W64.of_int 1));
    }
    return rp;
  }
  proc jade_ntruplus_ntruplus768_amd64_ref_decap_r2 (rp:W16.t Array768.t,
                                                     cp:W16.t Array768.t,
                                                     mp:W16.t Array768.t,
                                                     hp:W16.t Array768.t) : 
  W16.t Array768.t = {
    var i:int;
    var transformed:W16.t Array768.t;
    var difference:W16.t Array768.t;
    var transformedp:W16.t Array768.t;
    var differencep:W16.t Array768.t;
    var  _0:W64.t;
    difference <- witness;
    differencep <- witness;
    transformed <- witness;
    transformedp <- witness;
     _0 <- (init_msf);
    i <- 0;
    while ((i < 768)) {
      transformed.[i] <- (W16.of_int 0);
      difference.[i] <- (W16.of_int 0);
      i <- (i + 1);
    }
    transformedp <- (Array768.init (fun i_0 => transformed.[(0 + i_0)]));
    differencep <- (Array768.init (fun i_0 => difference.[(0 + i_0)]));
    transformedp <@ forward__jade_ntruplus_ntruplus768_amd64_ref_ntt (
    transformedp, mp);
    differencep <@ difference__jade_ntruplus_ntruplus768_amd64_ref_poly_sub (
    differencep, cp, transformedp);
    rp <@ product__jade_ntruplus_ntruplus768_amd64_ref_poly_basemul (
    rp, differencep, hp);
    return rp;
  }
}.
