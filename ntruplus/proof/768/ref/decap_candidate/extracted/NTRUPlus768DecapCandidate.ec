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
  proc inverse__Radix2_4____mul_i16 (a:W16.t, b:W16.t) : W32.t = {
    var c:W32.t;
    var ad:W32.t;
    var bd:W32.t;
    ad <- (sigextu32 a);
    bd <- (sigextu32 b);
    c <- (ad * bd);
    return c;
  }
  proc inverse__Radix2_4____montgomery_reduce (a:W32.t) : W16.t = {
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
  proc inverse__Radix2_4____barrett_reduce (a:W16.t) : W16.t = {
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
  proc inverse__Radix2_4____invntt_radix2_4_block (rp:W16.t Array768.t,
                                                   base:W64.t, zeta_0:W16.t) : 
  W16.t Array768.t = {
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
    stop <- (stop + (W64.of_int 4));
    while ((i \ult stop)) {
      low <- rp.[(W64.to_uint i)];
      high <- rp.[(W64.to_uint (i + (W64.of_int 4)))];
      wd <- (sigextu32 low);
      td <- (sigextu32 high);
      wd <- (wd + td);
      sum <- (truncateu16 wd);
      wd <- (sigextu32 high);
      td <- (sigextu32 low);
      wd <- (wd - td);
      diff <- (truncateu16 wd);
      sum <@ inverse__Radix2_4____barrett_reduce (sum);
      acc <@ inverse__Radix2_4____mul_i16 (zeta_0, diff);
      prod <@ inverse__Radix2_4____montgomery_reduce (acc);
      rp.[(W64.to_uint i)] <- sum;
      rp.[(W64.to_uint (i + (W64.of_int 4)))] <- prod;
      i <- (i + (W64.of_int 1));
    }
    return rp;
  }
  proc inverse__Radix2_4__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4 (
  rp:W16.t Array768.t) : W16.t Array768.t = {
    var  _0:W64.t;
     _0 <- (init_msf);
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 0),
    (W16.of_int (- 779)));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 8),
    (W16.of_int 1588));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 16),
    (W16.of_int 892));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 24),
    (W16.of_int (- 1095)));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 32),
    (W16.of_int (- 732)));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 40),
    (W16.of_int 294));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 48),
    (W16.of_int (- 218)));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 56),
    (W16.of_int 1221));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 64),
    (W16.of_int 858));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 72),
    (W16.of_int (- 968)));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 80),
    (W16.of_int (- 1728)));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 88),
    (W16.of_int 354));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 96),
    (W16.of_int 1108));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 104),
    (W16.of_int (- 275)));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 112),
    (W16.of_int 1709));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 120),
    (W16.of_int 22));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 128),
    (W16.of_int (- 1681)));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 136),
    (W16.of_int (- 940)));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 144),
    (W16.of_int 1379));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 152),
    (W16.of_int 1458));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 160),
    (W16.of_int (- 124)));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 168),
    (W16.of_int (- 1367)));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 176),
    (W16.of_int 1531));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 184),
    (W16.of_int (- 1550)));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 192),
    (W16.of_int 32));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 200),
    (W16.of_int (- 1543)));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 208),
    (W16.of_int 274));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 216),
    (W16.of_int 400));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 224),
    (W16.of_int (- 1248)));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 232),
    (W16.of_int 1408));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 240),
    (W16.of_int (- 315)));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 248),
    (W16.of_int 1685));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 256),
    (W16.of_int (- 1626)));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 264),
    (W16.of_int (- 27)));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 272),
    (W16.of_int (- 1391)));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 280),
    (W16.of_int 417));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 288),
    (W16.of_int 1188));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 296),
    (W16.of_int 1053));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 304),
    (W16.of_int (- 1063)));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 312),
    (W16.of_int 1022));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 320),
    (W16.of_int 251));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 328),
    (W16.of_int 1401));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 336),
    (W16.of_int 1501));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 344),
    (W16.of_int 1409));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 352),
    (W16.of_int 582));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 360),
    (W16.of_int 673));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 368),
    (W16.of_int 230));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 376),
    (W16.of_int 361));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 384),
    (W16.of_int (- 1209)));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 392),
    (W16.of_int 1364));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 400),
    (W16.of_int 235));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 408),
    (W16.of_int 444));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 416),
    (W16.of_int (- 1247)));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 424),
    (W16.of_int (- 1341)));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 432),
    (W16.of_int 1206));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 440),
    (W16.of_int (- 31)));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 448),
    (W16.of_int 1660));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 456),
    (W16.of_int (- 100)));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 464),
    (W16.of_int 1250));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 472),
    (W16.of_int 8));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 480),
    (W16.of_int 943));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 488),
    (W16.of_int 443));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 496),
    (W16.of_int (- 352)));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 504),
    (W16.of_int (- 312)));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 512),
    (W16.of_int 1212));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 520),
    (W16.of_int 760));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 528),
    (W16.of_int 871));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 536),
    (W16.of_int 1322));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 544),
    (W16.of_int 1130));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 552),
    (W16.of_int 1473));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 560),
    (W16.of_int 601));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 568),
    (W16.of_int 297));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 576),
    (W16.of_int 489));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 584),
    (W16.of_int 512));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 592),
    (W16.of_int 514));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 600),
    (W16.of_int 927));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 608),
    (W16.of_int 1671));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 616),
    (W16.of_int 774));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 624),
    (W16.of_int 696));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 632),
    (W16.of_int (- 1583)));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 640),
    (W16.of_int 432));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 648),
    (W16.of_int 1640));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 656),
    (W16.of_int 242));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 664),
    (W16.of_int (- 1514)));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 672),
    (W16.of_int 437));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 680),
    (W16.of_int 1723));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 688),
    (W16.of_int 933));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 696),
    (W16.of_int 277));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 704),
    (W16.of_int (- 1674)));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 712),
    (W16.of_int 559));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 720),
    (W16.of_int 1655));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 728),
    (W16.of_int (- 183)));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 736),
    (W16.of_int (- 397)));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 744),
    (W16.of_int (- 1059)));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 752),
    (W16.of_int 1138));
    rp <@ inverse__Radix2_4____invntt_radix2_4_block (rp, (W64.of_int 760),
    (W16.of_int 223));
    return rp;
  }
  proc inverse__Radix2_8____mul_i16 (a:W16.t, b:W16.t) : W32.t = {
    var c:W32.t;
    var ad:W32.t;
    var bd:W32.t;
    ad <- (sigextu32 a);
    bd <- (sigextu32 b);
    c <- (ad * bd);
    return c;
  }
  proc inverse__Radix2_8____montgomery_reduce (a:W32.t) : W16.t = {
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
  proc inverse__Radix2_8____barrett_reduce (a:W16.t) : W16.t = {
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
  proc inverse__Radix2_8____invntt_radix2_8_block (rp:W16.t Array768.t,
                                                   base:W64.t, zeta_0:W16.t) : 
  W16.t Array768.t = {
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
    stop <- (stop + (W64.of_int 8));
    while ((i \ult stop)) {
      low <- rp.[(W64.to_uint i)];
      high <- rp.[(W64.to_uint (i + (W64.of_int 8)))];
      wd <- (sigextu32 low);
      td <- (sigextu32 high);
      wd <- (wd + td);
      sum <- (truncateu16 wd);
      wd <- (sigextu32 high);
      td <- (sigextu32 low);
      wd <- (wd - td);
      diff <- (truncateu16 wd);
      sum <@ inverse__Radix2_8____barrett_reduce (sum);
      acc <@ inverse__Radix2_8____mul_i16 (zeta_0, diff);
      prod <@ inverse__Radix2_8____montgomery_reduce (acc);
      rp.[(W64.to_uint i)] <- sum;
      rp.[(W64.to_uint (i + (W64.of_int 8)))] <- prod;
      i <- (i + (W64.of_int 1));
    }
    return rp;
  }
  proc inverse__Radix2_8__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_8 (
  rp:W16.t Array768.t) : W16.t Array768.t = {
    var  _0:W64.t;
     _0 <- (init_msf);
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 0),
    (W16.of_int 436));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 16),
    (W16.of_int 1015));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 32),
    (W16.of_int (- 588)));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 48),
    (W16.of_int (- 1464)));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 64),
    (W16.of_int 281));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 80),
    (W16.of_int (- 1558)));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 96),
    (W16.of_int (- 1267)));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 112),
    (W16.of_int (- 1673)));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 128),
    (W16.of_int (- 1331)));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 144),
    (W16.of_int 1413));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 160),
    (W16.of_int 1351));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 176),
    (W16.of_int (- 1081)));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 192),
    (W16.of_int 54));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 208),
    (W16.of_int 205));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 224),
    (W16.of_int (- 834)));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 240),
    (W16.of_int 675));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 256),
    (W16.of_int 630));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 272),
    (W16.of_int 87));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 288),
    (W16.of_int 641));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 304),
    (W16.of_int 961));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 320),
    (W16.of_int (- 371)));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 336),
    (W16.of_int 64));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 352),
    (W16.of_int (- 800)));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 368),
    (W16.of_int 548));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 384),
    (W16.of_int (- 992)));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 400),
    (W16.of_int (- 565)));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 416),
    (W16.of_int (- 1580)));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 432),
    (W16.of_int 1428));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 448),
    (W16.of_int 661));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 464),
    (W16.of_int 1293));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 480),
    (W16.of_int (- 606)));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 496),
    (W16.of_int (- 380)));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 512),
    (W16.of_int (- 1507)));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 528),
    (W16.of_int 1257));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 544),
    (W16.of_int (- 156)));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 560),
    (W16.of_int 176));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 576),
    (W16.of_int 4));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 592),
    (W16.of_int (- 625)));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 608),
    (W16.of_int (- 830)));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 624),
    (W16.of_int 50));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 640),
    (W16.of_int 1199));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 656),
    (W16.of_int (- 1530)));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 672),
    (W16.of_int (- 1617)));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 688),
    (W16.of_int (- 569)));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 704),
    (W16.of_int 1637));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 720),
    (W16.of_int 901));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 736),
    (W16.of_int 837));
    rp <@ inverse__Radix2_8____invntt_radix2_8_block (rp, (W64.of_int 752),
    (W16.of_int 1449));
    return rp;
  }
  proc inverse__Radix2_16____mul_i16 (a:W16.t, b:W16.t) : W32.t = {
    var c:W32.t;
    var ad:W32.t;
    var bd:W32.t;
    ad <- (sigextu32 a);
    bd <- (sigextu32 b);
    c <- (ad * bd);
    return c;
  }
  proc inverse__Radix2_16____montgomery_reduce (a:W32.t) : W16.t = {
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
  proc inverse__Radix2_16____barrett_reduce (a:W16.t) : W16.t = {
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
  proc inverse__Radix2_16____invntt_radix2_16_block (rp:W16.t Array768.t,
                                                     base:W64.t, zeta_0:W16.t) : 
  W16.t Array768.t = {
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
    stop <- (stop + (W64.of_int 16));
    while ((i \ult stop)) {
      low <- rp.[(W64.to_uint i)];
      high <- rp.[(W64.to_uint (i + (W64.of_int 16)))];
      wd <- (sigextu32 low);
      td <- (sigextu32 high);
      wd <- (wd + td);
      sum <- (truncateu16 wd);
      wd <- (sigextu32 high);
      td <- (sigextu32 low);
      wd <- (wd - td);
      diff <- (truncateu16 wd);
      sum <@ inverse__Radix2_16____barrett_reduce (sum);
      acc <@ inverse__Radix2_16____mul_i16 (zeta_0, diff);
      prod <@ inverse__Radix2_16____montgomery_reduce (acc);
      rp.[(W64.to_uint i)] <- sum;
      rp.[(W64.to_uint (i + (W64.of_int 16)))] <- prod;
      i <- (i + (W64.of_int 1));
    }
    return rp;
  }
  proc inverse__Radix2_16__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_16 (
  rp:W16.t Array768.t) : W16.t Array768.t = {
    var  _0:W64.t;
     _0 <- (init_msf);
    rp <@ inverse__Radix2_16____invntt_radix2_16_block (rp, (W64.of_int 0),
    (W16.of_int 1058));
    rp <@ inverse__Radix2_16____invntt_radix2_16_block (rp, (W64.of_int 32),
    (W16.of_int (- 1105)));
    rp <@ inverse__Radix2_16____invntt_radix2_16_block (rp, (W64.of_int 64),
    (W16.of_int 1713));
    rp <@ inverse__Radix2_16____invntt_radix2_16_block (rp, (W64.of_int 96),
    (W16.of_int (- 603)));
    rp <@ inverse__Radix2_16____invntt_radix2_16_block (rp, (W64.of_int 128),
    (W16.of_int 387));
    rp <@ inverse__Radix2_16____invntt_radix2_16_block (rp, (W64.of_int 160),
    (W16.of_int 893));
    rp <@ inverse__Radix2_16____invntt_radix2_16_block (rp, (W64.of_int 192),
    (W16.of_int 937));
    rp <@ inverse__Radix2_16____invntt_radix2_16_block (rp, (W64.of_int 224),
    (W16.of_int (- 348)));
    rp <@ inverse__Radix2_16____invntt_radix2_16_block (rp, (W64.of_int 256),
    (W16.of_int (- 757)));
    rp <@ inverse__Radix2_16____invntt_radix2_16_block (rp, (W64.of_int 288),
    (W16.of_int (- 121)));
    rp <@ inverse__Radix2_16____invntt_radix2_16_block (rp, (W64.of_int 320),
    (W16.of_int (- 216)));
    rp <@ inverse__Radix2_16____invntt_radix2_16_block (rp, (W64.of_int 352),
    (W16.of_int (- 820)));
    rp <@ inverse__Radix2_16____invntt_radix2_16_block (rp, (W64.of_int 384),
    (W16.of_int 39));
    rp <@ inverse__Radix2_16____invntt_radix2_16_block (rp, (W64.of_int 416),
    (W16.of_int (- 44)));
    rp <@ inverse__Radix2_16____invntt_radix2_16_block (rp, (W64.of_int 448),
    (W16.of_int 550));
    rp <@ inverse__Radix2_16____invntt_radix2_16_block (rp, (W64.of_int 480),
    (W16.of_int (- 1241)));
    rp <@ inverse__Radix2_16____invntt_radix2_16_block (rp, (W64.of_int 512),
    (W16.of_int (- 1577)));
    rp <@ inverse__Radix2_16____invntt_radix2_16_block (rp, (W64.of_int 544),
    (W16.of_int 95));
    rp <@ inverse__Radix2_16____invntt_radix2_16_block (rp, (W64.of_int 576),
    (W16.of_int 541));
    rp <@ inverse__Radix2_16____invntt_radix2_16_block (rp, (W64.of_int 608),
    (W16.of_int (- 699)));
    rp <@ inverse__Radix2_16____invntt_radix2_16_block (rp, (W64.of_int 640),
    (W16.of_int 655));
    rp <@ inverse__Radix2_16____invntt_radix2_16_block (rp, (W64.of_int 672),
    (W16.of_int 502));
    rp <@ inverse__Radix2_16____invntt_radix2_16_block (rp, (W64.of_int 704),
    (W16.of_int 639));
    rp <@ inverse__Radix2_16____invntt_radix2_16_block (rp, (W64.of_int 736),
    (W16.of_int (- 455)));
    return rp;
  }
  proc inverse__Radix2_32____mul_i16 (a:W16.t, b:W16.t) : W32.t = {
    var c:W32.t;
    var ad:W32.t;
    var bd:W32.t;
    ad <- (sigextu32 a);
    bd <- (sigextu32 b);
    c <- (ad * bd);
    return c;
  }
  proc inverse__Radix2_32____montgomery_reduce (a:W32.t) : W16.t = {
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
  proc inverse__Radix2_32____barrett_reduce (a:W16.t) : W16.t = {
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
  proc inverse__Radix2_32____invntt_radix2_32_block (rp:W16.t Array768.t,
                                                     base:W64.t, zeta_0:W16.t) : 
  W16.t Array768.t = {
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
    stop <- (stop + (W64.of_int 32));
    while ((i \ult stop)) {
      low <- rp.[(W64.to_uint i)];
      high <- rp.[(W64.to_uint (i + (W64.of_int 32)))];
      wd <- (sigextu32 low);
      td <- (sigextu32 high);
      wd <- (wd + td);
      sum <- (truncateu16 wd);
      wd <- (sigextu32 high);
      td <- (sigextu32 low);
      wd <- (wd - td);
      diff <- (truncateu16 wd);
      sum <@ inverse__Radix2_32____barrett_reduce (sum);
      acc <@ inverse__Radix2_32____mul_i16 (zeta_0, diff);
      prod <@ inverse__Radix2_32____montgomery_reduce (acc);
      rp.[(W64.to_uint i)] <- sum;
      rp.[(W64.to_uint (i + (W64.of_int 32)))] <- prod;
      i <- (i + (W64.of_int 1));
    }
    return rp;
  }
  proc inverse__Radix2_32__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_32 (
  rp:W16.t Array768.t) : W16.t Array768.t = {
    var  _0:W64.t;
     _0 <- (init_msf);
    rp <@ inverse__Radix2_32____invntt_radix2_32_block (rp, (W64.of_int 0),
    (W16.of_int 395));
    rp <@ inverse__Radix2_32____invntt_radix2_32_block (rp, (W64.of_int 64),
    (W16.of_int (- 357)));
    rp <@ inverse__Radix2_32____invntt_radix2_32_block (rp, (W64.of_int 128),
    (W16.of_int (- 1521)));
    rp <@ inverse__Radix2_32____invntt_radix2_32_block (rp, (W64.of_int 192),
    (W16.of_int 1716));
    rp <@ inverse__Radix2_32____invntt_radix2_32_block (rp, (W64.of_int 256),
    (W16.of_int (- 1346)));
    rp <@ inverse__Radix2_32____invntt_radix2_32_block (rp, (W64.of_int 320),
    (W16.of_int 1164));
    rp <@ inverse__Radix2_32____invntt_radix2_32_block (rp, (W64.of_int 384),
    (W16.of_int 222));
    rp <@ inverse__Radix2_32____invntt_radix2_32_block (rp, (W64.of_int 448),
    (W16.of_int 1611));
    rp <@ inverse__Radix2_32____invntt_radix2_32_block (rp, (W64.of_int 512),
    (W16.of_int (- 1590)));
    rp <@ inverse__Radix2_32____invntt_radix2_32_block (rp, (W64.of_int 576),
    (W16.of_int 1262));
    rp <@ inverse__Radix2_32____invntt_radix2_32_block (rp, (W64.of_int 640),
    (W16.of_int 1484));
    rp <@ inverse__Radix2_32____invntt_radix2_32_block (rp, (W64.of_int 704),
    (W16.of_int (- 256)));
    return rp;
  }
  proc inverse__Radix2_64____mul_i16 (a:W16.t, b:W16.t) : W32.t = {
    var c:W32.t;
    var ad:W32.t;
    var bd:W32.t;
    ad <- (sigextu32 a);
    bd <- (sigextu32 b);
    c <- (ad * bd);
    return c;
  }
  proc inverse__Radix2_64____montgomery_reduce (a:W32.t) : W16.t = {
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
  proc inverse__Radix2_64____barrett_reduce (a:W16.t) : W16.t = {
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
  proc inverse__Radix2_64____invntt_radix2_64_block (rp:W16.t Array768.t,
                                                     base:W64.t, zeta_0:W16.t) : 
  W16.t Array768.t = {
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
      sum <@ inverse__Radix2_64____barrett_reduce (sum);
      acc <@ inverse__Radix2_64____mul_i16 (zeta_0, diff);
      prod <@ inverse__Radix2_64____montgomery_reduce (acc);
      rp.[(W64.to_uint i)] <- sum;
      rp.[(W64.to_uint (i + (W64.of_int 64)))] <- prod;
      i <- (i + (W64.of_int 1));
    }
    return rp;
  }
  proc inverse__Radix2_64__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_64 (
  rp:W16.t Array768.t) : W16.t Array768.t = {
    var  _0:W64.t;
     _0 <- (init_msf);
    rp <@ inverse__Radix2_64____invntt_radix2_64_block (rp, (W64.of_int 0),
    (W16.of_int (- 867)));
    rp <@ inverse__Radix2_64____invntt_radix2_64_block (rp, (W64.of_int 128),
    (W16.of_int (- 1124)));
    rp <@ inverse__Radix2_64____invntt_radix2_64_block (rp, (W64.of_int 256),
    (W16.of_int (- 257)));
    rp <@ inverse__Radix2_64____invntt_radix2_64_block (rp, (W64.of_int 384),
    (W16.of_int (- 723)));
    rp <@ inverse__Radix2_64____invntt_radix2_64_block (rp, (W64.of_int 512),
    (W16.of_int (- 722)));
    rp <@ inverse__Radix2_64____invntt_radix2_64_block (rp, (W64.of_int 640),
    (W16.of_int 1));
    return rp;
  }
  proc inverse__Radix3____mul_i16 (a:W16.t, b:W16.t) : W32.t = {
    var c:W32.t;
    var ad:W32.t;
    var bd:W32.t;
    ad <- (sigextu32 a);
    bd <- (sigextu32 b);
    c <- (ad * bd);
    return c;
  }
  proc inverse__Radix3____montgomery_reduce (a:W32.t) : W16.t = {
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
  proc inverse__Radix3__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix3 (
  rp:W16.t Array768.t) : W16.t Array768.t = {
    var i:W64.t;
    var a0:W16.t;
    var a1:W16.t;
    var a2:W16.t;
    var td:W16.t;
    var acc:W32.t;
    var t1:W16.t;
    var t2:W16.t;
    var t3:W16.t;
    var r0:W16.t;
    var  _0:W64.t;
     _0 <- (init_msf);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 128))) {
      a0 <- rp.[(W64.to_uint i)];
      a1 <- rp.[(W64.to_uint (i + (W64.of_int 128)))];
      a2 <- rp.[(W64.to_uint (i + (W64.of_int 256)))];
      td <- a1;
      td <- (td - a0);
      acc <@ inverse__Radix3____mul_i16 ((W16.of_int (- 886)), td);
      t1 <@ inverse__Radix3____montgomery_reduce (acc);
      td <- a2;
      td <- (td - a0);
      td <- (td + t1);
      acc <@ inverse__Radix3____mul_i16 ((W16.of_int (- 708)), td);
      t2 <@ inverse__Radix3____montgomery_reduce (acc);
      td <- a2;
      td <- (td - a1);
      td <- (td - t1);
      acc <@ inverse__Radix3____mul_i16 ((W16.of_int 682), td);
      t3 <@ inverse__Radix3____montgomery_reduce (acc);
      r0 <- a0;
      r0 <- (r0 + a1);
      r0 <- (r0 + a2);
      rp.[(W64.to_uint i)] <- r0;
      rp.[(W64.to_uint (i + (W64.of_int 128)))] <- t2;
      rp.[(W64.to_uint (i + (W64.of_int 256)))] <- t3;
      i <- (i + (W64.of_int 1));
    }
    i <- (W64.of_int 384);
    while ((i \ult (W64.of_int 512))) {
      a0 <- rp.[(W64.to_uint i)];
      a1 <- rp.[(W64.to_uint (i + (W64.of_int 128)))];
      a2 <- rp.[(W64.to_uint (i + (W64.of_int 256)))];
      td <- a1;
      td <- (td - a0);
      acc <@ inverse__Radix3____mul_i16 ((W16.of_int (- 886)), td);
      t1 <@ inverse__Radix3____montgomery_reduce (acc);
      td <- a2;
      td <- (td - a0);
      td <- (td + t1);
      acc <@ inverse__Radix3____mul_i16 ((W16.of_int (- 682)), td);
      t2 <@ inverse__Radix3____montgomery_reduce (acc);
      td <- a2;
      td <- (td - a1);
      td <- (td - t1);
      acc <@ inverse__Radix3____mul_i16 ((W16.of_int (- 248)), td);
      t3 <@ inverse__Radix3____montgomery_reduce (acc);
      r0 <- a0;
      r0 <- (r0 + a1);
      r0 <- (r0 + a2);
      rp.[(W64.to_uint i)] <- r0;
      rp.[(W64.to_uint (i + (W64.of_int 128)))] <- t2;
      rp.[(W64.to_uint (i + (W64.of_int 256)))] <- t3;
      i <- (i + (W64.of_int 1));
    }
    return rp;
  }
  proc inverse__Final____mul_i16 (a:W16.t, b:W16.t) : W32.t = {
    var c:W32.t;
    var ad:W32.t;
    var bd:W32.t;
    ad <- (sigextu32 a);
    bd <- (sigextu32 b);
    c <- (ad * bd);
    return c;
  }
  proc inverse__Final____montgomery_reduce (a:W32.t) : W16.t = {
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
  proc inverse__Final__jade_ntruplus_ntruplus768_amd64_ref_invntt_final (
  rp:W16.t Array768.t) : W16.t Array768.t = {
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
      acc <@ inverse__Final____mul_i16 ((W16.of_int (- 1665)), td);
      t2 <@ inverse__Final____montgomery_reduce (acc);
      td <- t1;
      td <- (td - t2);
      acc <@ inverse__Final____mul_i16 ((W16.of_int (- 811)), td);
      aux <@ inverse__Final____montgomery_reduce (acc);
      rp.[(W64.to_uint i)] <- aux;
      acc <@ inverse__Final____mul_i16 ((W16.of_int (- 1622)), t2);
      aux <@ inverse__Final____montgomery_reduce (acc);
      rp.[(W64.to_uint (i + (W64.of_int (768 %/ 2))))] <- aux;
      i <- (i + (W64.of_int 1));
    }
    return rp;
  }
  proc inverse____invntt_copy (rp:W16.t Array768.t, ap:W16.t Array768.t) : 
  W16.t Array768.t = {
    var i:W64.t;
    var  _0:W64.t;
     _0 <- (init_msf);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 768))) {
      rp.[(W64.to_uint i)] <- ap.[(W64.to_uint i)];
      i <- (i + (W64.of_int 1));
    }
    return rp;
  }
  proc inverse__jade_ntruplus_ntruplus768_amd64_ref_invntt (rp:W16.t Array768.t,
                                                            ap:W16.t Array768.t) : 
  W16.t Array768.t = {
    
    rp <@ inverse____invntt_copy (rp, ap);
    rp <@ inverse__Radix2_4__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4 (
    rp);
    rp <@ inverse__Radix2_8__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_8 (
    rp);
    rp <@ inverse__Radix2_16__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_16 (
    rp);
    rp <@ inverse__Radix2_32__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_32 (
    rp);
    rp <@ inverse__Radix2_64__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_64 (
    rp);
    rp <@ inverse__Radix3__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix3 (
    rp);
    rp <@ inverse__Final__jade_ntruplus_ntruplus768_amd64_ref_invntt_final (
    rp);
    return rp;
  }
  proc ternary____crepmod3 (a:W16.t) : W16.t = {
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
  proc ternary__jade_ntruplus_ntruplus768_amd64_ref_poly_crepmod3 (rp:W16.t Array768.t,
                                                                   ap:W16.t Array768.t) : 
  W16.t Array768.t = {
    var aux:W16.t;
    var i:W64.t;
    var  _0:W64.t;
     _0 <- (init_msf);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 768))) {
      aux <@ ternary____crepmod3 (ap.[(W64.to_uint i)]);
      rp.[(W64.to_uint i)] <- aux;
      i <- (i + (W64.of_int 1));
    }
    return rp;
  }
  proc jade_ntruplus_ntruplus768_amd64_ref_decap_candidate (rp:W16.t Array768.t,
                                                            cp:W16.t Array768.t,
                                                            fp:W16.t Array768.t) : 
  W16.t Array768.t = {
    var i:int;
    var product:W16.t Array768.t;
    var inverse:W16.t Array768.t;
    var productp:W16.t Array768.t;
    var inversep:W16.t Array768.t;
    var  _0:W64.t;
    inverse <- witness;
    inversep <- witness;
    product <- witness;
    productp <- witness;
     _0 <- (init_msf);
    i <- 0;
    while ((i < 768)) {
      product.[i] <- (W16.of_int 0);
      inverse.[i] <- (W16.of_int 0);
      i <- (i + 1);
    }
    productp <- (Array768.init (fun i_0 => product.[(0 + i_0)]));
    inversep <- (Array768.init (fun i_0 => inverse.[(0 + i_0)]));
    productp <@ product__jade_ntruplus_ntruplus768_amd64_ref_poly_basemul (
    productp, cp, fp);
    inversep <@ inverse__jade_ntruplus_ntruplus768_amd64_ref_invntt (
    inversep, productp);
    rp <@ ternary__jade_ntruplus_ntruplus768_amd64_ref_poly_crepmod3 (
    rp, inversep);
    return rp;
  }
}.
