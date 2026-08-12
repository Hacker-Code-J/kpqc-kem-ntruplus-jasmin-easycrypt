require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import Array4 Array96 Array768 WArray8 WArray192 WArray1536.

abbrev nTRUPLUS_ZETAS96 =
((Array96.of_list witness)
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
  proc __basemul4 (r:W16.t Array4.t, a:W16.t Array4.t, b:W16.t Array4.t,
                   zeta_0:W16.t) : W16.t Array4.t = {
    var aux:W16.t;
    var acc:W32.t;
    var term:W32.t;
    acc <@ __mul_i16 (a.[1], b.[3]);
    term <@ __mul_i16 (a.[2], b.[2]);
    acc <- (acc + term);
    term <@ __mul_i16 (a.[3], b.[1]);
    acc <- (acc + term);
    aux <@ __montgomery_reduce (acc);
    r.[0] <- aux;
    acc <@ __mul_i16 (a.[2], b.[3]);
    term <@ __mul_i16 (a.[3], b.[2]);
    acc <- (acc + term);
    aux <@ __montgomery_reduce (acc);
    r.[1] <- aux;
    acc <@ __mul_i16 (a.[3], b.[3]);
    aux <@ __montgomery_reduce (acc);
    r.[2] <- aux;
    acc <@ __mul_i16 (r.[0], zeta_0);
    term <@ __mul_i16 (a.[0], b.[0]);
    acc <- (acc + term);
    aux <@ __montgomery_reduce (acc);
    r.[0] <- aux;
    acc <@ __mul_i16 (r.[1], zeta_0);
    term <@ __mul_i16 (a.[0], b.[1]);
    acc <- (acc + term);
    term <@ __mul_i16 (a.[1], b.[0]);
    acc <- (acc + term);
    aux <@ __montgomery_reduce (acc);
    r.[1] <- aux;
    acc <@ __mul_i16 (r.[2], zeta_0);
    term <@ __mul_i16 (a.[0], b.[2]);
    acc <- (acc + term);
    term <@ __mul_i16 (a.[1], b.[1]);
    acc <- (acc + term);
    term <@ __mul_i16 (a.[2], b.[0]);
    acc <- (acc + term);
    aux <@ __montgomery_reduce (acc);
    r.[2] <- aux;
    acc <@ __mul_i16 (a.[0], b.[3]);
    term <@ __mul_i16 (a.[1], b.[2]);
    acc <- (acc + term);
    term <@ __mul_i16 (a.[2], b.[1]);
    acc <- (acc + term);
    term <@ __mul_i16 (a.[3], b.[0]);
    acc <- (acc + term);
    aux <@ __montgomery_reduce (acc);
    r.[3] <- aux;
    acc <@ __mul_i16 (r.[0], (W16.of_int 867));
    aux <@ __montgomery_reduce (acc);
    r.[0] <- aux;
    acc <@ __mul_i16 (r.[1], (W16.of_int 867));
    aux <@ __montgomery_reduce (acc);
    r.[1] <- aux;
    acc <@ __mul_i16 (r.[2], (W16.of_int 867));
    aux <@ __montgomery_reduce (acc);
    r.[2] <- aux;
    acc <@ __mul_i16 (r.[3], (W16.of_int 867));
    aux <@ __montgomery_reduce (acc);
    r.[3] <- aux;
    return r;
  }
  proc jade_ntruplus_ntruplus768_amd64_ref_poly_basemul (rp:W16.t Array768.t,
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
    zetasp <- (Array96.init (fun i_0 => nTRUPLUS_ZETAS96.[(0 + i_0)]));
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
      tr <@ __basemul4 (tr, ta, tb, zeta_0);
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
      tr <@ __basemul4 (tr, ta, tb, (- zeta_0));
      rp.[(W64.to_uint off)] <- tr.[0];
      rp.[(W64.to_uint (off + (W64.of_int 1)))] <- tr.[1];
      rp.[(W64.to_uint (off + (W64.of_int 2)))] <- tr.[2];
      rp.[(W64.to_uint (off + (W64.of_int 3)))] <- tr.[3];
      i <- (i + (W64.of_int 1));
    }
    return rp;
  }
}.
