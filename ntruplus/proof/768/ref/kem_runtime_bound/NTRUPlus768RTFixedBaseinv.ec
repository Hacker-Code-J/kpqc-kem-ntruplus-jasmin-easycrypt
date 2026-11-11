require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import Array4 Array96 Array768 WArray8 WArray192 WArray1536.

abbrev nTRUPLUS_ZETAS96 =
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


require import NTRUPlus768PolyBaseInv.
(* Each rt_work update is a ghost charge for the preceding concrete instruction.
   Each array parameter is copied into an owned buffer (3N primitive events: allocation, load, store). Whole-array assignments/returns also pay 3N; Array.set updates this owned buffer. These procedures preserve the original data path; no global state is added. *)
module RTFixedBaseinv = {
  proc baseInv____mul_i16 (a:W16.t, b:W16.t) : (W32.t) * int = {
    var rt_work:int;
    var c:W32.t;
    var ad:W32.t;
    var bd:W32.t;
    rt_work <- 0;
    ad <- (sigextu32 a);
    rt_work <- rt_work + 2;
    bd <- (sigextu32 b);
    rt_work <- rt_work + 2;
    c <- (ad * bd);
    rt_work <- rt_work + 2;
    rt_work <- rt_work + 1;
    return (c,rt_work);
  }
  proc baseInv____montgomery_reduce (a:W32.t) : (W16.t) * int = {
    var rt_work:int;
    var t:W16.t;
    var q:W32.t;
    var td:W32.t;
    var r:W32.t;
    rt_work <- 0;
    q <- (W32.of_int 3457);
    rt_work <- rt_work + 1;
    td <- a;
    rt_work <- rt_work + 1;
    td <- (td * (W32.of_int 12929));
    rt_work <- rt_work + 2;
    t <- (truncateu16 td);
    rt_work <- rt_work + 2;
    td <- (sigextu32 t);
    rt_work <- rt_work + 2;
    r <- a;
    rt_work <- rt_work + 1;
    td <- (td * q);
    rt_work <- rt_work + 2;
    r <- (r - td);
    rt_work <- rt_work + 2;
    r <- (r `|>>` (W8.of_int 16));
    rt_work <- rt_work + 2;
    t <- (truncateu16 r);
    rt_work <- rt_work + 2;
    rt_work <- rt_work + 1;
    return (t,rt_work);
  }
  proc baseInv____fqmul (a:W16.t, b:W16.t) : (W16.t) * int = {
    var rt_work:int;
    var r:W16.t;
    var c:W32.t;
    var rt_call_baseInv____montgomery_reduce:(W16.t) * int;
    var rt_call_baseInv____mul_i16:(W32.t) * int;
    rt_work <- 0;
    rt_call_baseInv____mul_i16 <@ baseInv____mul_i16 (a, b);
    c <- rt_call_baseInv____mul_i16.`1;
    rt_work <- rt_work + rt_call_baseInv____mul_i16.`2 + 4;
    rt_call_baseInv____montgomery_reduce <@ baseInv____montgomery_reduce (c);
    r <- rt_call_baseInv____montgomery_reduce.`1;
    rt_work <- rt_work + rt_call_baseInv____montgomery_reduce.`2 + 3;
    rt_work <- rt_work + 1;
    return (r,rt_work);
  }
  proc baseInv____fqinv (a:W16.t) : (W16.t) * int = {
    var rt_work:int;
    var t2:W16.t;
    var t1:W16.t;
    var t3:W16.t;
    var rt_call_baseInv____fqmul:(W16.t) * int;
    rt_work <- 0;
    rt_call_baseInv____fqmul <@ baseInv____fqmul (a, a);
    t1 <- rt_call_baseInv____fqmul.`1;
    rt_work <- rt_work + rt_call_baseInv____fqmul.`2 + 4;
    rt_call_baseInv____fqmul <@ baseInv____fqmul (t1, t1);
    t2 <- rt_call_baseInv____fqmul.`1;
    rt_work <- rt_work + rt_call_baseInv____fqmul.`2 + 4;
    rt_call_baseInv____fqmul <@ baseInv____fqmul (t2, t2);
    t2 <- rt_call_baseInv____fqmul.`1;
    rt_work <- rt_work + rt_call_baseInv____fqmul.`2 + 4;
    rt_call_baseInv____fqmul <@ baseInv____fqmul (t2, t2);
    t3 <- rt_call_baseInv____fqmul.`1;
    rt_work <- rt_work + rt_call_baseInv____fqmul.`2 + 4;
    rt_call_baseInv____fqmul <@ baseInv____fqmul (t1, t2);
    t1 <- rt_call_baseInv____fqmul.`1;
    rt_work <- rt_work + rt_call_baseInv____fqmul.`2 + 4;
    rt_call_baseInv____fqmul <@ baseInv____fqmul (t1, t3);
    t2 <- rt_call_baseInv____fqmul.`1;
    rt_work <- rt_work + rt_call_baseInv____fqmul.`2 + 4;
    rt_call_baseInv____fqmul <@ baseInv____fqmul (t2, t2);
    t2 <- rt_call_baseInv____fqmul.`1;
    rt_work <- rt_work + rt_call_baseInv____fqmul.`2 + 4;
    rt_call_baseInv____fqmul <@ baseInv____fqmul (t2, a);
    t2 <- rt_call_baseInv____fqmul.`1;
    rt_work <- rt_work + rt_call_baseInv____fqmul.`2 + 4;
    rt_call_baseInv____fqmul <@ baseInv____fqmul (t1, t2);
    t1 <- rt_call_baseInv____fqmul.`1;
    rt_work <- rt_work + rt_call_baseInv____fqmul.`2 + 4;
    rt_call_baseInv____fqmul <@ baseInv____fqmul (t2, t2);
    t2 <- rt_call_baseInv____fqmul.`1;
    rt_work <- rt_work + rt_call_baseInv____fqmul.`2 + 4;
    rt_call_baseInv____fqmul <@ baseInv____fqmul (t2, t2);
    t2 <- rt_call_baseInv____fqmul.`1;
    rt_work <- rt_work + rt_call_baseInv____fqmul.`2 + 4;
    rt_call_baseInv____fqmul <@ baseInv____fqmul (t2, t2);
    t2 <- rt_call_baseInv____fqmul.`1;
    rt_work <- rt_work + rt_call_baseInv____fqmul.`2 + 4;
    rt_call_baseInv____fqmul <@ baseInv____fqmul (t2, t2);
    t2 <- rt_call_baseInv____fqmul.`1;
    rt_work <- rt_work + rt_call_baseInv____fqmul.`2 + 4;
    rt_call_baseInv____fqmul <@ baseInv____fqmul (t2, t2);
    t2 <- rt_call_baseInv____fqmul.`1;
    rt_work <- rt_work + rt_call_baseInv____fqmul.`2 + 4;
    rt_call_baseInv____fqmul <@ baseInv____fqmul (t2, t2);
    t2 <- rt_call_baseInv____fqmul.`1;
    rt_work <- rt_work + rt_call_baseInv____fqmul.`2 + 4;
    rt_call_baseInv____fqmul <@ baseInv____fqmul (t2, t1);
    t2 <- rt_call_baseInv____fqmul.`1;
    rt_work <- rt_work + rt_call_baseInv____fqmul.`2 + 4;
    rt_call_baseInv____fqmul <@ baseInv____fqmul ((W16.of_int (- 682)), t2);
    t2 <- rt_call_baseInv____fqmul.`1;
    rt_work <- rt_work + rt_call_baseInv____fqmul.`2 + 5;
    rt_work <- rt_work + 1;
    return (t2,rt_work);
  }
  proc baseInv____baseinv_pretrace (a0:W16.t, a1:W16.t, a2:W16.t, a3:W16.t,
                                    zeta_0:W16.t) : (W16.t * W16.t * W16.t *
                                                    W16.t) * int = {
    var rt_work:int;
    var t0:W16.t;
    var t1:W16.t;
    var t2:W16.t;
    var t3:W16.t;
    var acc:W32.t;
    var term:W32.t;
    var rt_call_baseInv____montgomery_reduce:(W16.t) * int;
    var rt_call_baseInv____mul_i16:(W32.t) * int;
    rt_work <- 0;
    rt_call_baseInv____mul_i16 <@ baseInv____mul_i16 (a2, a2);
    acc <- rt_call_baseInv____mul_i16.`1;
    rt_work <- rt_work + rt_call_baseInv____mul_i16.`2 + 4;
    rt_call_baseInv____mul_i16 <@ baseInv____mul_i16 (a1, a3);
    term <- rt_call_baseInv____mul_i16.`1;
    rt_work <- rt_work + rt_call_baseInv____mul_i16.`2 + 4;
    term <- (term + term);
    rt_work <- rt_work + 2;
    acc <- (acc - term);
    rt_work <- rt_work + 2;
    rt_call_baseInv____montgomery_reduce <@ baseInv____montgomery_reduce (acc);
    t0 <- rt_call_baseInv____montgomery_reduce.`1;
    rt_work <- rt_work + rt_call_baseInv____montgomery_reduce.`2 + 3;
    rt_call_baseInv____mul_i16 <@ baseInv____mul_i16 (a3, a3);
    acc <- rt_call_baseInv____mul_i16.`1;
    rt_work <- rt_work + rt_call_baseInv____mul_i16.`2 + 4;
    rt_call_baseInv____montgomery_reduce <@ baseInv____montgomery_reduce (acc);
    t1 <- rt_call_baseInv____montgomery_reduce.`1;
    rt_work <- rt_work + rt_call_baseInv____montgomery_reduce.`2 + 3;
    rt_call_baseInv____mul_i16 <@ baseInv____mul_i16 (a0, a0);
    acc <- rt_call_baseInv____mul_i16.`1;
    rt_work <- rt_work + rt_call_baseInv____mul_i16.`2 + 4;
    rt_call_baseInv____mul_i16 <@ baseInv____mul_i16 (t0, zeta_0);
    term <- rt_call_baseInv____mul_i16.`1;
    rt_work <- rt_work + rt_call_baseInv____mul_i16.`2 + 4;
    acc <- (acc + term);
    rt_work <- rt_work + 2;
    rt_call_baseInv____montgomery_reduce <@ baseInv____montgomery_reduce (acc);
    t0 <- rt_call_baseInv____montgomery_reduce.`1;
    rt_work <- rt_work + rt_call_baseInv____montgomery_reduce.`2 + 3;
    rt_call_baseInv____mul_i16 <@ baseInv____mul_i16 (a1, a1);
    acc <- rt_call_baseInv____mul_i16.`1;
    rt_work <- rt_work + rt_call_baseInv____mul_i16.`2 + 4;
    rt_call_baseInv____mul_i16 <@ baseInv____mul_i16 (t1, zeta_0);
    term <- rt_call_baseInv____mul_i16.`1;
    rt_work <- rt_work + rt_call_baseInv____mul_i16.`2 + 4;
    acc <- (acc + term);
    rt_work <- rt_work + 2;
    rt_call_baseInv____mul_i16 <@ baseInv____mul_i16 (a0, a2);
    term <- rt_call_baseInv____mul_i16.`1;
    rt_work <- rt_work + rt_call_baseInv____mul_i16.`2 + 4;
    term <- (term + term);
    rt_work <- rt_work + 2;
    acc <- (acc - term);
    rt_work <- rt_work + 2;
    rt_call_baseInv____montgomery_reduce <@ baseInv____montgomery_reduce (acc);
    t1 <- rt_call_baseInv____montgomery_reduce.`1;
    rt_work <- rt_work + rt_call_baseInv____montgomery_reduce.`2 + 3;
    rt_call_baseInv____mul_i16 <@ baseInv____mul_i16 (t1, zeta_0);
    acc <- rt_call_baseInv____mul_i16.`1;
    rt_work <- rt_work + rt_call_baseInv____mul_i16.`2 + 4;
    rt_call_baseInv____montgomery_reduce <@ baseInv____montgomery_reduce (acc);
    t2 <- rt_call_baseInv____montgomery_reduce.`1;
    rt_work <- rt_work + rt_call_baseInv____montgomery_reduce.`2 + 3;
    rt_call_baseInv____mul_i16 <@ baseInv____mul_i16 (t0, t0);
    acc <- rt_call_baseInv____mul_i16.`1;
    rt_work <- rt_work + rt_call_baseInv____mul_i16.`2 + 4;
    rt_call_baseInv____mul_i16 <@ baseInv____mul_i16 (t1, t2);
    term <- rt_call_baseInv____mul_i16.`1;
    rt_work <- rt_work + rt_call_baseInv____mul_i16.`2 + 4;
    acc <- (acc - term);
    rt_work <- rt_work + 2;
    rt_call_baseInv____montgomery_reduce <@ baseInv____montgomery_reduce (acc);
    t3 <- rt_call_baseInv____montgomery_reduce.`1;
    rt_work <- rt_work + rt_call_baseInv____montgomery_reduce.`2 + 3;
    rt_work <- rt_work + 4;
    return ((t0, t1, t2, t3),rt_work);
  }
  proc baseInv____baseinv_success (a0:W16.t, a1:W16.t, a2:W16.t, a3:W16.t,
                                   t0:W16.t, t1:W16.t, t2:W16.t,
                                   determinant:W16.t) : (W16.t * W16.t *
                                                        W16.t * W16.t) * int = {
    var rt_work:int;
    var r0:W16.t;
    var r1:W16.t;
    var r2:W16.t;
    var r3:W16.t;
    var acc:W32.t;
    var term:W32.t;
    var invword:W16.t;
    var rt_call_baseInv____fqinv:(W16.t) * int;
    var rt_call_baseInv____montgomery_reduce:(W16.t) * int;
    var rt_call_baseInv____mul_i16:(W32.t) * int;
    rt_work <- 0;
    rt_call_baseInv____mul_i16 <@ baseInv____mul_i16 (a0, t0);
    acc <- rt_call_baseInv____mul_i16.`1;
    rt_work <- rt_work + rt_call_baseInv____mul_i16.`2 + 4;
    rt_call_baseInv____mul_i16 <@ baseInv____mul_i16 (a2, t2);
    term <- rt_call_baseInv____mul_i16.`1;
    rt_work <- rt_work + rt_call_baseInv____mul_i16.`2 + 4;
    acc <- (acc + term);
    rt_work <- rt_work + 2;
    rt_call_baseInv____montgomery_reduce <@ baseInv____montgomery_reduce (acc);
    r0 <- rt_call_baseInv____montgomery_reduce.`1;
    rt_work <- rt_work + rt_call_baseInv____montgomery_reduce.`2 + 3;
    rt_call_baseInv____mul_i16 <@ baseInv____mul_i16 (a3, t2);
    acc <- rt_call_baseInv____mul_i16.`1;
    rt_work <- rt_work + rt_call_baseInv____mul_i16.`2 + 4;
    rt_call_baseInv____mul_i16 <@ baseInv____mul_i16 (a1, t0);
    term <- rt_call_baseInv____mul_i16.`1;
    rt_work <- rt_work + rt_call_baseInv____mul_i16.`2 + 4;
    acc <- (acc + term);
    rt_work <- rt_work + 2;
    rt_call_baseInv____montgomery_reduce <@ baseInv____montgomery_reduce (acc);
    r1 <- rt_call_baseInv____montgomery_reduce.`1;
    rt_work <- rt_work + rt_call_baseInv____montgomery_reduce.`2 + 3;
    rt_call_baseInv____mul_i16 <@ baseInv____mul_i16 (a2, t0);
    acc <- rt_call_baseInv____mul_i16.`1;
    rt_work <- rt_work + rt_call_baseInv____mul_i16.`2 + 4;
    rt_call_baseInv____mul_i16 <@ baseInv____mul_i16 (a0, t1);
    term <- rt_call_baseInv____mul_i16.`1;
    rt_work <- rt_work + rt_call_baseInv____mul_i16.`2 + 4;
    acc <- (acc + term);
    rt_work <- rt_work + 2;
    rt_call_baseInv____montgomery_reduce <@ baseInv____montgomery_reduce (acc);
    r2 <- rt_call_baseInv____montgomery_reduce.`1;
    rt_work <- rt_work + rt_call_baseInv____montgomery_reduce.`2 + 3;
    rt_call_baseInv____mul_i16 <@ baseInv____mul_i16 (a1, t1);
    acc <- rt_call_baseInv____mul_i16.`1;
    rt_work <- rt_work + rt_call_baseInv____mul_i16.`2 + 4;
    rt_call_baseInv____mul_i16 <@ baseInv____mul_i16 (a3, t0);
    term <- rt_call_baseInv____mul_i16.`1;
    rt_work <- rt_work + rt_call_baseInv____mul_i16.`2 + 4;
    acc <- (acc + term);
    rt_work <- rt_work + 2;
    rt_call_baseInv____montgomery_reduce <@ baseInv____montgomery_reduce (acc);
    r3 <- rt_call_baseInv____montgomery_reduce.`1;
    rt_work <- rt_work + rt_call_baseInv____montgomery_reduce.`2 + 3;
    rt_call_baseInv____fqinv <@ baseInv____fqinv (determinant);
    invword <- rt_call_baseInv____fqinv.`1;
    rt_work <- rt_work + rt_call_baseInv____fqinv.`2 + 3;
    rt_call_baseInv____mul_i16 <@ baseInv____mul_i16 (r0, invword);
    acc <- rt_call_baseInv____mul_i16.`1;
    rt_work <- rt_work + rt_call_baseInv____mul_i16.`2 + 4;
    rt_call_baseInv____montgomery_reduce <@ baseInv____montgomery_reduce (acc);
    r0 <- rt_call_baseInv____montgomery_reduce.`1;
    rt_work <- rt_work + rt_call_baseInv____montgomery_reduce.`2 + 3;
    rt_call_baseInv____mul_i16 <@ baseInv____mul_i16 (r1, invword);
    acc <- rt_call_baseInv____mul_i16.`1;
    rt_work <- rt_work + rt_call_baseInv____mul_i16.`2 + 4;
    rt_call_baseInv____montgomery_reduce <@ baseInv____montgomery_reduce (acc);
    r1 <- rt_call_baseInv____montgomery_reduce.`1;
    rt_work <- rt_work + rt_call_baseInv____montgomery_reduce.`2 + 3;
    rt_call_baseInv____mul_i16 <@ baseInv____mul_i16 (r2, invword);
    acc <- rt_call_baseInv____mul_i16.`1;
    rt_work <- rt_work + rt_call_baseInv____mul_i16.`2 + 4;
    rt_call_baseInv____montgomery_reduce <@ baseInv____montgomery_reduce (acc);
    r2 <- rt_call_baseInv____montgomery_reduce.`1;
    rt_work <- rt_work + rt_call_baseInv____montgomery_reduce.`2 + 3;
    rt_call_baseInv____mul_i16 <@ baseInv____mul_i16 (r3, invword);
    acc <- rt_call_baseInv____mul_i16.`1;
    rt_work <- rt_work + rt_call_baseInv____mul_i16.`2 + 4;
    rt_call_baseInv____montgomery_reduce <@ baseInv____montgomery_reduce (acc);
    r3 <- rt_call_baseInv____montgomery_reduce.`1;
    rt_work <- rt_work + rt_call_baseInv____montgomery_reduce.`2 + 3;
    rt_work <- rt_work + 4;
    return ((r0, r1, r2, r3),rt_work);
  }
  proc __poly_baseinv_block (tr:W16.t Array4.t, ta:W16.t Array4.t,
                             zeta_0:W16.t) : (W16.t Array4.t * W64.t) * int = {
    var rt_work:int;
    var status:W64.t;
    var t0:W16.t;
    var t1:W16.t;
    var t2:W16.t;
    var t3:W16.t;
    var r0:W16.t;
    var r1:W16.t;
    var r2:W16.t;
    var r3:W16.t;
    var rt_call_baseInv____baseinv_pretrace:(W16.t * W16.t * W16.t *
                                                    W16.t) * int;
    var rt_call_baseInv____baseinv_success:(W16.t * W16.t *
                                                        W16.t * W16.t) * int;
    rt_work <- 24;
    rt_call_baseInv____baseinv_pretrace <@ baseInv____baseinv_pretrace (ta.[0], ta.[1], ta.[2], ta.[3], zeta_0);
    (t0, t1, t2, t3) <- rt_call_baseInv____baseinv_pretrace.`1;
    rt_work <- rt_work + rt_call_baseInv____baseinv_pretrace.`2 + 11;
    rt_work <- rt_work + 2;
    if ((t3 = (W16.of_int 0))) {
      status <- (W64.of_int 1);
      rt_work <- rt_work + 1;
    } else {
      rt_call_baseInv____baseinv_success <@ baseInv____baseinv_success (ta.[0], ta.[1], ta.[2], ta.[3], t0, t1, t2, t3);
      (r0, r1, r2, r3) <- rt_call_baseInv____baseinv_success.`1;
      rt_work <- rt_work + rt_call_baseInv____baseinv_success.`2 + 14;
      r1 <- (- r1);
      rt_work <- rt_work + 2;
      r3 <- (- r3);
      rt_work <- rt_work + 2;
      tr.[0] <- r0;
      rt_work <- rt_work + 2;
      tr.[1] <- r1;
      rt_work <- rt_work + 2;
      tr.[2] <- r2;
      rt_work <- rt_work + 2;
      tr.[3] <- r3;
      rt_work <- rt_work + 2;
      status <- (W64.of_int 0);
      rt_work <- rt_work + 1;
    }
    rt_work <- rt_work + 14;
    return ((tr, status),rt_work);
  }
  proc __poly_baseinv_apply (rp:W16.t Array768.t, ap:W16.t Array768.t,
                             block:W64.t, zeta_0:W16.t) : (W16.t Array768.t *
                                                          W64.t) * int = {
    var rt_work:int;
    var status:W64.t;
    var tr:W16.t Array4.t;
    var trp:W16.t Array4.t;
    var off:W64.t;
    var ta:W16.t Array4.t;
    var rt_call___poly_baseinv_block:(W16.t Array4.t * W64.t) * int;
    rt_work <- 4608;
    ta <- witness;
    rt_work <- rt_work + 5;
    tr <- witness;
    rt_work <- rt_work + 5;
    trp <- witness;
    rt_work <- rt_work + 5;
    tr.[0] <- (W16.of_int 0);
    rt_work <- rt_work + 2;
    tr.[1] <- (W16.of_int 0);
    rt_work <- rt_work + 2;
    tr.[2] <- (W16.of_int 0);
    rt_work <- rt_work + 2;
    tr.[3] <- (W16.of_int 0);
    rt_work <- rt_work + 2;
    trp <- (Array4.init (fun i => tr.[(0 + i)]));
    rt_work <- rt_work + 35;
    off <- block;
    rt_work <- rt_work + 1;
    off <- (off `<<` (W8.of_int 2));
    rt_work <- rt_work + 2;
    ta.[0] <- ap.[(W64.to_uint off)];
    rt_work <- rt_work + 3;
    ta.[1] <- ap.[(W64.to_uint (off + (W64.of_int 1)))];
    rt_work <- rt_work + 4;
    ta.[2] <- ap.[(W64.to_uint (off + (W64.of_int 2)))];
    rt_work <- rt_work + 4;
    ta.[3] <- ap.[(W64.to_uint (off + (W64.of_int 3)))];
    rt_work <- rt_work + 4;
    rt_call___poly_baseinv_block <@ __poly_baseinv_block (trp, ta, zeta_0);
    (trp, status) <- rt_call___poly_baseinv_block.`1;
    rt_work <- rt_work + rt_call___poly_baseinv_block.`2 + 17;
    rt_work <- rt_work + 2;
    if ((status = (W64.of_int 0))) {
      rp.[(W64.to_uint off)] <- trp.[0];
      rt_work <- rt_work + 3;
      rp.[(W64.to_uint (off + (W64.of_int 1)))] <- trp.[1];
      rt_work <- rt_work + 4;
      rp.[(W64.to_uint (off + (W64.of_int 2)))] <- trp.[2];
      rt_work <- rt_work + 4;
      rp.[(W64.to_uint (off + (W64.of_int 3)))] <- trp.[3];
      rt_work <- rt_work + 4;
    } else {
    }
    rt_work <- rt_work + 2306;
    return ((rp, status),rt_work);
  }
  proc __poly_baseinv_pair (rp:W16.t Array768.t, ap:W16.t Array768.t,
                            i:W64.t, zeta_0:W16.t) : (W16.t Array768.t * W64.t) * int = {
    var rt_work:int;
    var status:W64.t;
    var block:W64.t;
    var rt_call___poly_baseinv_apply:(W16.t Array768.t *
                                                          W64.t) * int;
    rt_work <- 4608;
    block <- i;
    rt_work <- rt_work + 1;
    block <- (block `<<` (W8.of_int 1));
    rt_work <- rt_work + 2;
    rt_call___poly_baseinv_apply <@ __poly_baseinv_apply (rp, ap, block, zeta_0);
    (rp, status) <- rt_call___poly_baseinv_apply.`1;
    rt_work <- rt_work + rt_call___poly_baseinv_apply.`2 + 2310;
    rt_work <- rt_work + 2;
    if ((status <> (W64.of_int 1))) {
      block <- (block + (W64.of_int 1));
      rt_work <- rt_work + 2;
      zeta_0 <- (- zeta_0);
      rt_work <- rt_work + 2;
      rt_call___poly_baseinv_apply <@ __poly_baseinv_apply (rp, ap, block, zeta_0);
      (rp, status) <- rt_call___poly_baseinv_apply.`1;
      rt_work <- rt_work + rt_call___poly_baseinv_apply.`2 + 2310;
    } else {
    }
    rt_work <- rt_work + 2306;
    return ((rp, status),rt_work);
  }
  proc __poly_baseinv_zero (rp:W16.t Array768.t) : (W16.t Array768.t) * int = {
    var rt_work:int;
    var j:W64.t;
    rt_work <- 2304;
    j <- (W64.of_int 0);
    rt_work <- rt_work + 1;
    rt_work <- rt_work + 2;
    while ((j \ult (W64.of_int 768))) {
      rp.[(W64.to_uint j)] <- (W16.of_int 0);
      rt_work <- rt_work + 2;
      j <- (j + (W64.of_int 1));
      rt_work <- rt_work + 2;
      rt_work <- rt_work + 2;
    }
    rt_work <- rt_work + 2305;
    return (rp,rt_work);
  }
  proc __poly_baseinv_core (rp:W16.t Array768.t, ap:W16.t Array768.t) : (W16.t Array768.t * W64.t) * int = {
    var rt_work:int;
    var status:W64.t;
    var i:W64.t;
    var zetasp:W16.t Array96.t;
    var zeta_0:W16.t;
    var _0:W64.t;
    var rt_call___poly_baseinv_pair:(W16.t Array768.t * W64.t) * int;
    var rt_call___poly_baseinv_zero:(W16.t Array768.t) * int;
    rt_work <- 4608;
    zetasp <- witness;
    rt_work <- rt_work + 97;
    _0 <- (init_msf);
    rt_work <- rt_work + 1;
    i <- (W64.of_int 0);
    rt_work <- rt_work + 1;
    status <- (W64.of_int 0);
    rt_work <- rt_work + 1;
    zetasp <- (Array96.init (fun i_0 => nTRUPLUS_ZETAS96.[(0 + i_0)]));
    rt_work <- rt_work + 771;
    rt_work <- rt_work + 2;
    while ((i \ult (W64.of_int (768 %/ 8)))) {
      zeta_0 <- zetasp.[(W64.to_uint i)];
      rt_work <- rt_work + 2;
      rt_call___poly_baseinv_pair <@ __poly_baseinv_pair (rp, ap, i, zeta_0);
      (rp, status) <- rt_call___poly_baseinv_pair.`1;
      rt_work <- rt_work + rt_call___poly_baseinv_pair.`2 + 2310;
      rt_work <- rt_work + 2;
      if ((status = (W64.of_int 1))) {
        i <- (W64.of_int (768 %/ 8));
        rt_work <- rt_work + 2;
      } else {
        i <- (i + (W64.of_int 1));
        rt_work <- rt_work + 2;
        status <- (W64.of_int 0);
        rt_work <- rt_work + 1;
      }
      rt_work <- rt_work + 2;
    }
    rt_work <- rt_work + 2;
    if ((status = (W64.of_int 1))) {
      rt_call___poly_baseinv_zero <@ __poly_baseinv_zero (rp);
      rp <- rt_call___poly_baseinv_zero.`1;
      rt_work <- rt_work + rt_call___poly_baseinv_zero.`2 + 2307;
    } else {
    }
    rt_work <- rt_work + 2306;
    return ((rp, status),rt_work);
  }
}.

lemma rt_fixed_u64_next (i:W64.t) : W64.to_uint i<2048 => W64.to_uint(i+W64.one)=W64.to_uint i+1.
proof. move=>h;rewrite W64.to_uintD_small /=;smt(W64.to_uint_cmp). qed.
lemma rt_fixed_u64_add (i:W64.t)(n:int) : 0<=W64.to_uint i<=768 => 0<=n<=768 => W64.to_uint(i+W64.of_int n)=W64.to_uint i+n.
proof. move=>hi hn;have hnE:W64.to_uint(W64.of_int n)=n. + rewrite W64.to_uint_small;smt(). rewrite W64.to_uintD_small. + rewrite hnE;smt(). by rewrite hnE. qed.
lemma rt_fixed_ult (i:W64.t)(n:int) : 0<=n<2048 => (i \ult W64.of_int n)=(W64.to_uint i<n).
proof. move=>hn;rewrite W64.ultE W64.to_uint_small;smt(). qed.
lemma rt_fixed_exit (i:W64.t)(n:int) : 0<=n<2048 => !(i \ult W64.of_int n) => W64.to_uint i<=n => W64.to_uint i=n.
proof. move=>hn;rewrite(rt_fixed_ult i n hn);smt(). qed.

lemma rt_fixed_baseinv_baseInv____mul_i16_projection :
 equiv[RTFixedBaseinv.baseInv____mul_i16 ~ NTRUPlus768PolyBaseInv.M.baseInv____mul_i16 :
 ={a,b} ==> res{1}.`1=res{2}].
proof. proc.
 auto.
qed.
lemma rt_fixed_baseinv_baseInv____mul_i16_cost :
 hoare[RTFixedBaseinv.baseInv____mul_i16 : true ==> 0<=res.`2<=7].
proof. proc.
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_baseinv_baseInv____montgomery_reduce_projection :
 equiv[RTFixedBaseinv.baseInv____montgomery_reduce ~ NTRUPlus768PolyBaseInv.M.baseInv____montgomery_reduce :
 ={a} ==> res{1}.`1=res{2}].
proof. proc.
 auto.
qed.
lemma rt_fixed_baseinv_baseInv____montgomery_reduce_cost :
 hoare[RTFixedBaseinv.baseInv____montgomery_reduce : true ==> 0<=res.`2<=18].
proof. proc.
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_baseinv_baseInv____fqmul_projection :
 equiv[RTFixedBaseinv.baseInv____fqmul ~ NTRUPlus768PolyBaseInv.M.baseInv____fqmul :
 ={a,b} ==> res{1}.`1=res{2}].
proof. proc.
 wp;call rt_fixed_baseinv_baseInv____montgomery_reduce_projection.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_projection.
 auto.
qed.
lemma rt_fixed_baseinv_baseInv____fqmul_cost :
 hoare[RTFixedBaseinv.baseInv____fqmul : true ==> 0<=res.`2<=33].
proof. proc.
 wp;call rt_fixed_baseinv_baseInv____montgomery_reduce_cost.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_cost.
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_baseinv_baseInv____fqinv_projection :
 equiv[RTFixedBaseinv.baseInv____fqinv ~ NTRUPlus768PolyBaseInv.M.baseInv____fqinv :
 ={a} ==> res{1}.`1=res{2}].
proof. proc.
 wp;call rt_fixed_baseinv_baseInv____fqmul_projection.
 wp;call rt_fixed_baseinv_baseInv____fqmul_projection.
 wp;call rt_fixed_baseinv_baseInv____fqmul_projection.
 wp;call rt_fixed_baseinv_baseInv____fqmul_projection.
 wp;call rt_fixed_baseinv_baseInv____fqmul_projection.
 wp;call rt_fixed_baseinv_baseInv____fqmul_projection.
 wp;call rt_fixed_baseinv_baseInv____fqmul_projection.
 wp;call rt_fixed_baseinv_baseInv____fqmul_projection.
 wp;call rt_fixed_baseinv_baseInv____fqmul_projection.
 wp;call rt_fixed_baseinv_baseInv____fqmul_projection.
 wp;call rt_fixed_baseinv_baseInv____fqmul_projection.
 wp;call rt_fixed_baseinv_baseInv____fqmul_projection.
 wp;call rt_fixed_baseinv_baseInv____fqmul_projection.
 wp;call rt_fixed_baseinv_baseInv____fqmul_projection.
 wp;call rt_fixed_baseinv_baseInv____fqmul_projection.
 wp;call rt_fixed_baseinv_baseInv____fqmul_projection.
 wp;call rt_fixed_baseinv_baseInv____fqmul_projection.
 auto.
qed.
lemma rt_fixed_baseinv_baseInv____fqinv_cost :
 hoare[RTFixedBaseinv.baseInv____fqinv : true ==> 0<=res.`2<=631].
proof. proc.
 wp;call rt_fixed_baseinv_baseInv____fqmul_cost.
 wp;call rt_fixed_baseinv_baseInv____fqmul_cost.
 wp;call rt_fixed_baseinv_baseInv____fqmul_cost.
 wp;call rt_fixed_baseinv_baseInv____fqmul_cost.
 wp;call rt_fixed_baseinv_baseInv____fqmul_cost.
 wp;call rt_fixed_baseinv_baseInv____fqmul_cost.
 wp;call rt_fixed_baseinv_baseInv____fqmul_cost.
 wp;call rt_fixed_baseinv_baseInv____fqmul_cost.
 wp;call rt_fixed_baseinv_baseInv____fqmul_cost.
 wp;call rt_fixed_baseinv_baseInv____fqmul_cost.
 wp;call rt_fixed_baseinv_baseInv____fqmul_cost.
 wp;call rt_fixed_baseinv_baseInv____fqmul_cost.
 wp;call rt_fixed_baseinv_baseInv____fqmul_cost.
 wp;call rt_fixed_baseinv_baseInv____fqmul_cost.
 wp;call rt_fixed_baseinv_baseInv____fqmul_cost.
 wp;call rt_fixed_baseinv_baseInv____fqmul_cost.
 wp;call rt_fixed_baseinv_baseInv____fqmul_cost.
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_baseinv_baseInv____baseinv_pretrace_projection :
 equiv[RTFixedBaseinv.baseInv____baseinv_pretrace ~ NTRUPlus768PolyBaseInv.M.baseInv____baseinv_pretrace :
 ={a0,a1,a2,a3,zeta_0} ==> res{1}.`1=res{2}].
proof. proc.
 wp;call rt_fixed_baseinv_baseInv____montgomery_reduce_projection.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_projection.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_projection.
 wp;call rt_fixed_baseinv_baseInv____montgomery_reduce_projection.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_projection.
 wp;call rt_fixed_baseinv_baseInv____montgomery_reduce_projection.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_projection.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_projection.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_projection.
 wp;call rt_fixed_baseinv_baseInv____montgomery_reduce_projection.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_projection.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_projection.
 wp;call rt_fixed_baseinv_baseInv____montgomery_reduce_projection.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_projection.
 wp;call rt_fixed_baseinv_baseInv____montgomery_reduce_projection.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_projection.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_projection.
 auto.
qed.
lemma rt_fixed_baseinv_baseInv____baseinv_pretrace_cost :
 hoare[RTFixedBaseinv.baseInv____baseinv_pretrace : true ==> 0<=res.`2<=265].
proof. proc.
 wp;call rt_fixed_baseinv_baseInv____montgomery_reduce_cost.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_cost.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_cost.
 wp;call rt_fixed_baseinv_baseInv____montgomery_reduce_cost.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_cost.
 wp;call rt_fixed_baseinv_baseInv____montgomery_reduce_cost.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_cost.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_cost.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_cost.
 wp;call rt_fixed_baseinv_baseInv____montgomery_reduce_cost.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_cost.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_cost.
 wp;call rt_fixed_baseinv_baseInv____montgomery_reduce_cost.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_cost.
 wp;call rt_fixed_baseinv_baseInv____montgomery_reduce_cost.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_cost.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_cost.
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_baseinv_baseInv____baseinv_success_projection :
 equiv[RTFixedBaseinv.baseInv____baseinv_success ~ NTRUPlus768PolyBaseInv.M.baseInv____baseinv_success :
 ={a0,a1,a2,a3,t0,t1,t2,determinant} ==> res{1}.`1=res{2}].
proof. proc.
 wp;call rt_fixed_baseinv_baseInv____montgomery_reduce_projection.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_projection.
 wp;call rt_fixed_baseinv_baseInv____montgomery_reduce_projection.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_projection.
 wp;call rt_fixed_baseinv_baseInv____montgomery_reduce_projection.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_projection.
 wp;call rt_fixed_baseinv_baseInv____montgomery_reduce_projection.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_projection.
 wp;call rt_fixed_baseinv_baseInv____fqinv_projection.
 wp;call rt_fixed_baseinv_baseInv____montgomery_reduce_projection.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_projection.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_projection.
 wp;call rt_fixed_baseinv_baseInv____montgomery_reduce_projection.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_projection.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_projection.
 wp;call rt_fixed_baseinv_baseInv____montgomery_reduce_projection.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_projection.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_projection.
 wp;call rt_fixed_baseinv_baseInv____montgomery_reduce_projection.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_projection.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_projection.
 auto.
qed.
lemma rt_fixed_baseinv_baseInv____baseinv_success_cost :
 hoare[RTFixedBaseinv.baseInv____baseinv_success : true ==> 0<=res.`2<=946].
proof. proc.
 wp;call rt_fixed_baseinv_baseInv____montgomery_reduce_cost.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_cost.
 wp;call rt_fixed_baseinv_baseInv____montgomery_reduce_cost.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_cost.
 wp;call rt_fixed_baseinv_baseInv____montgomery_reduce_cost.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_cost.
 wp;call rt_fixed_baseinv_baseInv____montgomery_reduce_cost.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_cost.
 wp;call rt_fixed_baseinv_baseInv____fqinv_cost.
 wp;call rt_fixed_baseinv_baseInv____montgomery_reduce_cost.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_cost.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_cost.
 wp;call rt_fixed_baseinv_baseInv____montgomery_reduce_cost.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_cost.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_cost.
 wp;call rt_fixed_baseinv_baseInv____montgomery_reduce_cost.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_cost.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_cost.
 wp;call rt_fixed_baseinv_baseInv____montgomery_reduce_cost.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_cost.
 wp;call rt_fixed_baseinv_baseInv____mul_i16_cost.
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_baseinv___poly_baseinv_block_projection :
 equiv[RTFixedBaseinv.__poly_baseinv_block ~ NTRUPlus768PolyBaseInv.M.__poly_baseinv_block :
 ={tr,ta,zeta_0} ==> res{1}.`1=res{2}].
proof. proc;seq 5 1:(={tr,ta,zeta_0,t0,t1,t2,t3}).
 + wp;call rt_fixed_baseinv_baseInv____baseinv_pretrace_projection;auto.
 if;auto.
 wp;call rt_fixed_baseinv_baseInv____baseinv_success_projection;auto.
qed.
lemma rt_fixed_baseinv___poly_baseinv_block_cost :
 hoare[RTFixedBaseinv.__poly_baseinv_block : true ==> 0<=res.`2<=1289].
proof. proc;seq 5:(0<=rt_work<=302).
 + wp;call rt_fixed_baseinv_baseInv____baseinv_pretrace_cost;auto=> />;smt().
 if;first by auto=> />;smt().
 wp;call rt_fixed_baseinv_baseInv____baseinv_success_cost;auto=> />;smt().
qed.
lemma rt_fixed_baseinv___poly_baseinv_apply_projection :
 equiv[RTFixedBaseinv.__poly_baseinv_apply ~ NTRUPlus768PolyBaseInv.M.__poly_baseinv_apply :
 ={rp,ap,block,zeta_0} ==> res{1}.`1=res{2}].
proof. proc;seq 33 15:(={rp,ap,block,zeta_0,trp,status,off}).
 + wp;call rt_fixed_baseinv___poly_baseinv_block_projection;auto.
 if;auto.
qed.
lemma rt_fixed_baseinv___poly_baseinv_apply_cost :
 hoare[RTFixedBaseinv.__poly_baseinv_apply : true ==> 0<=res.`2<=8313].
proof. proc;seq 33:(0<=rt_work<=5992).
 + wp;call rt_fixed_baseinv___poly_baseinv_block_cost;auto=> />;smt().
 if;auto=> />;smt().
qed.
lemma rt_fixed_baseinv___poly_baseinv_pair_projection :
 equiv[RTFixedBaseinv.__poly_baseinv_pair ~ NTRUPlus768PolyBaseInv.M.__poly_baseinv_pair :
 ={rp,ap,i,zeta_0} ==> res{1}.`1=res{2}].
proof. proc;seq 9 3:(={rp,ap,i,zeta_0,status,block}).
 + wp;call rt_fixed_baseinv___poly_baseinv_apply_projection;auto.
 if;auto.
 wp;call rt_fixed_baseinv___poly_baseinv_apply_projection;auto.
qed.
lemma rt_fixed_baseinv___poly_baseinv_pair_cost :
 hoare[RTFixedBaseinv.__poly_baseinv_pair : true ==> 0<=res.`2<=28169].
proof. proc;seq 9:(0<=rt_work<=15236).
 + wp;call rt_fixed_baseinv___poly_baseinv_apply_cost;auto=> />;smt().
 if;last by auto=> />;smt().
 wp;call rt_fixed_baseinv___poly_baseinv_apply_cost;auto=> />;smt().
qed.
lemma rt_fixed_baseinv___poly_baseinv_zero_projection :
 equiv[RTFixedBaseinv.__poly_baseinv_zero ~ NTRUPlus768PolyBaseInv.M.__poly_baseinv_zero :
 ={rp} ==> res{1}.`1=res{2}].
proof. proc.
 wp;while(={rp,j}).
  + auto.
 auto.
qed.
lemma rt_fixed_baseinv___poly_baseinv_zero_cost :
 hoare[RTFixedBaseinv.__poly_baseinv_zero : true ==> 0<=res.`2<=9220].
proof. proc.
 wp;while(0<=W64.to_uint j<=768 /\ 0<=rt_work<=2307+6*(W64.to_uint j-(0))).
  + auto=> /> &hr;rewrite W64.ultE /=;move=>*;try (rewrite rt_fixed_u64_next 1:/#);smt().
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_baseinv___poly_baseinv_core_projection :
 equiv[RTFixedBaseinv.__poly_baseinv_core ~ NTRUPlus768PolyBaseInv.M.__poly_baseinv_core :
 ={rp,ap} ==> res{1}.`1=res{2}].
proof. proc;seq 14 6:(={rp,ap,status}).
 + wp;while(={rp,ap,i,zetasp,status}).
   - seq 6 2:(={rp,ap,i,zetasp,status,zeta_0}).
     + wp;call rt_fixed_baseinv___poly_baseinv_pair_projection;auto.
     if;auto.
   auto.
 if;auto.
 wp;call rt_fixed_baseinv___poly_baseinv_zero_projection;auto.
qed.
lemma rt_fixed_baseinv___poly_baseinv_core_cost :
 hoare[RTFixedBaseinv.__poly_baseinv_core : true ==> 0<=res.`2<=2946164].
proof. proc;seq 14:(0<=rt_work<=2932331).
 + wp;while(0<=W64.to_uint i<=96 /\ 0<=rt_work<=5481+30488*W64.to_uint i).
   - seq 6:(0<=W64.to_uint i<96 /\ 0<=rt_work<=5481+30488*W64.to_uint i+30483).
     + wp;call rt_fixed_baseinv___poly_baseinv_pair_cost.
       auto=> /> &hr;rewrite W64.ultE /=;smt().
     if;auto=> /> &hr;move=>*;try(rewrite rt_fixed_u64_next 1:/#);smt().
   auto=> />;smt(rt_fixed_exit).
 if;last by auto=> />;smt().
 wp;call rt_fixed_baseinv___poly_baseinv_zero_cost;auto=> />;smt().
qed.
op rt_fixed_baseinv_bound:int = 2946164.
lemma rt_fixed_baseinv_bound_cost : hoare[RTFixedBaseinv.__poly_baseinv_core : true ==>0<=res.`2<=rt_fixed_baseinv_bound].
proof. exact rt_fixed_baseinv___poly_baseinv_core_cost. qed.
