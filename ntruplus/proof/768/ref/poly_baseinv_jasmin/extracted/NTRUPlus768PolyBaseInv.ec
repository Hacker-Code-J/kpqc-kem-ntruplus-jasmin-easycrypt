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
  proc baseInv____mul_i16 (a:W16.t, b:W16.t) : W32.t = {
    var c:W32.t;
    var ad:W32.t;
    var bd:W32.t;
    ad <- (sigextu32 a);
    bd <- (sigextu32 b);
    c <- (ad * bd);
    return c;
  }
  proc baseInv____montgomery_reduce (a:W32.t) : W16.t = {
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
  proc baseInv____fqmul (a:W16.t, b:W16.t) : W16.t = {
    var r:W16.t;
    var c:W32.t;
    c <@ baseInv____mul_i16 (a, b);
    r <@ baseInv____montgomery_reduce (c);
    return r;
  }
  proc baseInv____fqinv (a:W16.t) : W16.t = {
    var t2:W16.t;
    var t1:W16.t;
    var t3:W16.t;
    t1 <@ baseInv____fqmul (a, a);
    t2 <@ baseInv____fqmul (t1, t1);
    t2 <@ baseInv____fqmul (t2, t2);
    t3 <@ baseInv____fqmul (t2, t2);
    t1 <@ baseInv____fqmul (t1, t2);
    t2 <@ baseInv____fqmul (t1, t3);
    t2 <@ baseInv____fqmul (t2, t2);
    t2 <@ baseInv____fqmul (t2, a);
    t1 <@ baseInv____fqmul (t1, t2);
    t2 <@ baseInv____fqmul (t2, t2);
    t2 <@ baseInv____fqmul (t2, t2);
    t2 <@ baseInv____fqmul (t2, t2);
    t2 <@ baseInv____fqmul (t2, t2);
    t2 <@ baseInv____fqmul (t2, t2);
    t2 <@ baseInv____fqmul (t2, t2);
    t2 <@ baseInv____fqmul (t2, t1);
    t2 <@ baseInv____fqmul ((W16.of_int (- 682)), t2);
    return t2;
  }
  proc baseInv____baseinv_pretrace (a0:W16.t, a1:W16.t, a2:W16.t, a3:W16.t,
                                    zeta_0:W16.t) : W16.t * W16.t * W16.t *
                                                    W16.t = {
    var t0:W16.t;
    var t1:W16.t;
    var t2:W16.t;
    var t3:W16.t;
    var acc:W32.t;
    var term:W32.t;
    acc <@ baseInv____mul_i16 (a2, a2);
    term <@ baseInv____mul_i16 (a1, a3);
    term <- (term + term);
    acc <- (acc - term);
    t0 <@ baseInv____montgomery_reduce (acc);
    acc <@ baseInv____mul_i16 (a3, a3);
    t1 <@ baseInv____montgomery_reduce (acc);
    acc <@ baseInv____mul_i16 (a0, a0);
    term <@ baseInv____mul_i16 (t0, zeta_0);
    acc <- (acc + term);
    t0 <@ baseInv____montgomery_reduce (acc);
    acc <@ baseInv____mul_i16 (a1, a1);
    term <@ baseInv____mul_i16 (t1, zeta_0);
    acc <- (acc + term);
    term <@ baseInv____mul_i16 (a0, a2);
    term <- (term + term);
    acc <- (acc - term);
    t1 <@ baseInv____montgomery_reduce (acc);
    acc <@ baseInv____mul_i16 (t1, zeta_0);
    t2 <@ baseInv____montgomery_reduce (acc);
    acc <@ baseInv____mul_i16 (t0, t0);
    term <@ baseInv____mul_i16 (t1, t2);
    acc <- (acc - term);
    t3 <@ baseInv____montgomery_reduce (acc);
    return (t0, t1, t2, t3);
  }
  proc baseInv____baseinv_success (a0:W16.t, a1:W16.t, a2:W16.t, a3:W16.t,
                                   t0:W16.t, t1:W16.t, t2:W16.t,
                                   determinant:W16.t) : W16.t * W16.t *
                                                        W16.t * W16.t = {
    var r0:W16.t;
    var r1:W16.t;
    var r2:W16.t;
    var r3:W16.t;
    var acc:W32.t;
    var term:W32.t;
    var invword:W16.t;
    acc <@ baseInv____mul_i16 (a0, t0);
    term <@ baseInv____mul_i16 (a2, t2);
    acc <- (acc + term);
    r0 <@ baseInv____montgomery_reduce (acc);
    acc <@ baseInv____mul_i16 (a3, t2);
    term <@ baseInv____mul_i16 (a1, t0);
    acc <- (acc + term);
    r1 <@ baseInv____montgomery_reduce (acc);
    acc <@ baseInv____mul_i16 (a2, t0);
    term <@ baseInv____mul_i16 (a0, t1);
    acc <- (acc + term);
    r2 <@ baseInv____montgomery_reduce (acc);
    acc <@ baseInv____mul_i16 (a1, t1);
    term <@ baseInv____mul_i16 (a3, t0);
    acc <- (acc + term);
    r3 <@ baseInv____montgomery_reduce (acc);
    invword <@ baseInv____fqinv (determinant);
    acc <@ baseInv____mul_i16 (r0, invword);
    r0 <@ baseInv____montgomery_reduce (acc);
    acc <@ baseInv____mul_i16 (r1, invword);
    r1 <@ baseInv____montgomery_reduce (acc);
    acc <@ baseInv____mul_i16 (r2, invword);
    r2 <@ baseInv____montgomery_reduce (acc);
    acc <@ baseInv____mul_i16 (r3, invword);
    r3 <@ baseInv____montgomery_reduce (acc);
    return (r0, r1, r2, r3);
  }
  proc __poly_baseinv_block (tr:W16.t Array4.t, ta:W16.t Array4.t,
                             zeta_0:W16.t) : W16.t Array4.t * W64.t = {
    var status:W64.t;
    var t0:W16.t;
    var t1:W16.t;
    var t2:W16.t;
    var t3:W16.t;
    var r0:W16.t;
    var r1:W16.t;
    var r2:W16.t;
    var r3:W16.t;
    (t0, t1, t2, t3) <@ baseInv____baseinv_pretrace (ta.[0], ta.[1], 
    ta.[2], ta.[3], zeta_0);
    if ((t3 = (W16.of_int 0))) {
      status <- (W64.of_int 1);
    } else {
      (r0, r1, r2, r3) <@ baseInv____baseinv_success (ta.[0], ta.[1], 
      ta.[2], ta.[3], t0, t1, t2, t3);
      r1 <- (- r1);
      r3 <- (- r3);
      tr.[0] <- r0;
      tr.[1] <- r1;
      tr.[2] <- r2;
      tr.[3] <- r3;
      status <- (W64.of_int 0);
    }
    return (tr, status);
  }
  proc __poly_baseinv_apply (rp:W16.t Array768.t, ap:W16.t Array768.t,
                             block:W64.t, zeta_0:W16.t) : W16.t Array768.t *
                                                          W64.t = {
    var status:W64.t;
    var tr:W16.t Array4.t;
    var trp:W16.t Array4.t;
    var off:W64.t;
    var ta:W16.t Array4.t;
    ta <- witness;
    tr <- witness;
    trp <- witness;
    tr.[0] <- (W16.of_int 0);
    tr.[1] <- (W16.of_int 0);
    tr.[2] <- (W16.of_int 0);
    tr.[3] <- (W16.of_int 0);
    trp <- (Array4.init (fun i => tr.[(0 + i)]));
    off <- block;
    off <- (off `<<` (W8.of_int 2));
    ta.[0] <- ap.[(W64.to_uint off)];
    ta.[1] <- ap.[(W64.to_uint (off + (W64.of_int 1)))];
    ta.[2] <- ap.[(W64.to_uint (off + (W64.of_int 2)))];
    ta.[3] <- ap.[(W64.to_uint (off + (W64.of_int 3)))];
    (trp, status) <@ __poly_baseinv_block (trp, ta, zeta_0);
    if ((status = (W64.of_int 0))) {
      rp.[(W64.to_uint off)] <- trp.[0];
      rp.[(W64.to_uint (off + (W64.of_int 1)))] <- trp.[1];
      rp.[(W64.to_uint (off + (W64.of_int 2)))] <- trp.[2];
      rp.[(W64.to_uint (off + (W64.of_int 3)))] <- trp.[3];
    } else {
      
    }
    return (rp, status);
  }
  proc __poly_baseinv_pair (rp:W16.t Array768.t, ap:W16.t Array768.t,
                            i:W64.t, zeta_0:W16.t) : W16.t Array768.t * W64.t = {
    var status:W64.t;
    var block:W64.t;
    block <- i;
    block <- (block `<<` (W8.of_int 1));
    (rp, status) <@ __poly_baseinv_apply (rp, ap, block, zeta_0);
    if ((status <> (W64.of_int 1))) {
      block <- (block + (W64.of_int 1));
      zeta_0 <- (- zeta_0);
      (rp, status) <@ __poly_baseinv_apply (rp, ap, block, zeta_0);
    } else {
      
    }
    return (rp, status);
  }
  proc __poly_baseinv_zero (rp:W16.t Array768.t) : W16.t Array768.t = {
    var j:W64.t;
    j <- (W64.of_int 0);
    while ((j \ult (W64.of_int 768))) {
      rp.[(W64.to_uint j)] <- (W16.of_int 0);
      j <- (j + (W64.of_int 1));
    }
    return rp;
  }
  proc __poly_baseinv_core (rp:W16.t Array768.t, ap:W16.t Array768.t) : 
  W16.t Array768.t * W64.t = {
    var status:W64.t;
    var i:W64.t;
    var zetasp:W16.t Array96.t;
    var zeta_0:W16.t;
    var  _0:W64.t;
    zetasp <- witness;
     _0 <- (init_msf);
    i <- (W64.of_int 0);
    status <- (W64.of_int 0);
    zetasp <- (Array96.init (fun i_0 => nTRUPLUS_ZETAS96.[(0 + i_0)]));
    while ((i \ult (W64.of_int (768 %/ 8)))) {
      zeta_0 <- zetasp.[(W64.to_uint i)];
      (rp, status) <@ __poly_baseinv_pair (rp, ap, i, zeta_0);
      if ((status = (W64.of_int 1))) {
        i <- (W64.of_int (768 %/ 8));
      } else {
        i <- (i + (W64.of_int 1));
        status <- (W64.of_int 0);
      }
    }
    if ((status = (W64.of_int 1))) {
      rp <@ __poly_baseinv_zero (rp);
    } else {
      
    }
    return (rp, status);
  }
}.
