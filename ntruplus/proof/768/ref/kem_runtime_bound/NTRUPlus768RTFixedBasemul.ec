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


require import NTRUPlus768PolyBasemul.
(* Each rt_work update is a ghost charge for the preceding concrete instruction.
   Each array parameter is copied into an owned buffer (3N primitive events: allocation, load, store). Whole-array assignments/returns also pay 3N; Array.set updates this owned buffer. These procedures preserve the original data path; no global state is added. *)
module RTFixedBasemul = {
  proc __mul_i16 (a:W16.t, b:W16.t) : (W32.t) * int = {
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
  proc __montgomery_reduce (a:W32.t) : (W16.t) * int = {
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
  proc __basemul4 (r:W16.t Array4.t, a:W16.t Array4.t, b:W16.t Array4.t,
                   zeta_0:W16.t) : (W16.t Array4.t) * int = {
    var rt_work:int;
    var aux:W16.t;
    var acc:W32.t;
    var term:W32.t;
    var rt_call___montgomery_reduce:(W16.t) * int;
    var rt_call___mul_i16:(W32.t) * int;
    rt_work <- 36;
    rt_call___mul_i16 <@ __mul_i16 (a.[1], b.[3]);
    acc <- rt_call___mul_i16.`1;
    rt_work <- rt_work + rt_call___mul_i16.`2 + 6;
    rt_call___mul_i16 <@ __mul_i16 (a.[2], b.[2]);
    term <- rt_call___mul_i16.`1;
    rt_work <- rt_work + rt_call___mul_i16.`2 + 6;
    acc <- (acc + term);
    rt_work <- rt_work + 2;
    rt_call___mul_i16 <@ __mul_i16 (a.[3], b.[1]);
    term <- rt_call___mul_i16.`1;
    rt_work <- rt_work + rt_call___mul_i16.`2 + 6;
    acc <- (acc + term);
    rt_work <- rt_work + 2;
    rt_call___montgomery_reduce <@ __montgomery_reduce (acc);
    aux <- rt_call___montgomery_reduce.`1;
    rt_work <- rt_work + rt_call___montgomery_reduce.`2 + 3;
    r.[0] <- aux;
    rt_work <- rt_work + 2;
    rt_call___mul_i16 <@ __mul_i16 (a.[2], b.[3]);
    acc <- rt_call___mul_i16.`1;
    rt_work <- rt_work + rt_call___mul_i16.`2 + 6;
    rt_call___mul_i16 <@ __mul_i16 (a.[3], b.[2]);
    term <- rt_call___mul_i16.`1;
    rt_work <- rt_work + rt_call___mul_i16.`2 + 6;
    acc <- (acc + term);
    rt_work <- rt_work + 2;
    rt_call___montgomery_reduce <@ __montgomery_reduce (acc);
    aux <- rt_call___montgomery_reduce.`1;
    rt_work <- rt_work + rt_call___montgomery_reduce.`2 + 3;
    r.[1] <- aux;
    rt_work <- rt_work + 2;
    rt_call___mul_i16 <@ __mul_i16 (a.[3], b.[3]);
    acc <- rt_call___mul_i16.`1;
    rt_work <- rt_work + rt_call___mul_i16.`2 + 6;
    rt_call___montgomery_reduce <@ __montgomery_reduce (acc);
    aux <- rt_call___montgomery_reduce.`1;
    rt_work <- rt_work + rt_call___montgomery_reduce.`2 + 3;
    r.[2] <- aux;
    rt_work <- rt_work + 2;
    rt_call___mul_i16 <@ __mul_i16 (r.[0], zeta_0);
    acc <- rt_call___mul_i16.`1;
    rt_work <- rt_work + rt_call___mul_i16.`2 + 5;
    rt_call___mul_i16 <@ __mul_i16 (a.[0], b.[0]);
    term <- rt_call___mul_i16.`1;
    rt_work <- rt_work + rt_call___mul_i16.`2 + 6;
    acc <- (acc + term);
    rt_work <- rt_work + 2;
    rt_call___montgomery_reduce <@ __montgomery_reduce (acc);
    aux <- rt_call___montgomery_reduce.`1;
    rt_work <- rt_work + rt_call___montgomery_reduce.`2 + 3;
    r.[0] <- aux;
    rt_work <- rt_work + 2;
    rt_call___mul_i16 <@ __mul_i16 (r.[1], zeta_0);
    acc <- rt_call___mul_i16.`1;
    rt_work <- rt_work + rt_call___mul_i16.`2 + 5;
    rt_call___mul_i16 <@ __mul_i16 (a.[0], b.[1]);
    term <- rt_call___mul_i16.`1;
    rt_work <- rt_work + rt_call___mul_i16.`2 + 6;
    acc <- (acc + term);
    rt_work <- rt_work + 2;
    rt_call___mul_i16 <@ __mul_i16 (a.[1], b.[0]);
    term <- rt_call___mul_i16.`1;
    rt_work <- rt_work + rt_call___mul_i16.`2 + 6;
    acc <- (acc + term);
    rt_work <- rt_work + 2;
    rt_call___montgomery_reduce <@ __montgomery_reduce (acc);
    aux <- rt_call___montgomery_reduce.`1;
    rt_work <- rt_work + rt_call___montgomery_reduce.`2 + 3;
    r.[1] <- aux;
    rt_work <- rt_work + 2;
    rt_call___mul_i16 <@ __mul_i16 (r.[2], zeta_0);
    acc <- rt_call___mul_i16.`1;
    rt_work <- rt_work + rt_call___mul_i16.`2 + 5;
    rt_call___mul_i16 <@ __mul_i16 (a.[0], b.[2]);
    term <- rt_call___mul_i16.`1;
    rt_work <- rt_work + rt_call___mul_i16.`2 + 6;
    acc <- (acc + term);
    rt_work <- rt_work + 2;
    rt_call___mul_i16 <@ __mul_i16 (a.[1], b.[1]);
    term <- rt_call___mul_i16.`1;
    rt_work <- rt_work + rt_call___mul_i16.`2 + 6;
    acc <- (acc + term);
    rt_work <- rt_work + 2;
    rt_call___mul_i16 <@ __mul_i16 (a.[2], b.[0]);
    term <- rt_call___mul_i16.`1;
    rt_work <- rt_work + rt_call___mul_i16.`2 + 6;
    acc <- (acc + term);
    rt_work <- rt_work + 2;
    rt_call___montgomery_reduce <@ __montgomery_reduce (acc);
    aux <- rt_call___montgomery_reduce.`1;
    rt_work <- rt_work + rt_call___montgomery_reduce.`2 + 3;
    r.[2] <- aux;
    rt_work <- rt_work + 2;
    rt_call___mul_i16 <@ __mul_i16 (a.[0], b.[3]);
    acc <- rt_call___mul_i16.`1;
    rt_work <- rt_work + rt_call___mul_i16.`2 + 6;
    rt_call___mul_i16 <@ __mul_i16 (a.[1], b.[2]);
    term <- rt_call___mul_i16.`1;
    rt_work <- rt_work + rt_call___mul_i16.`2 + 6;
    acc <- (acc + term);
    rt_work <- rt_work + 2;
    rt_call___mul_i16 <@ __mul_i16 (a.[2], b.[1]);
    term <- rt_call___mul_i16.`1;
    rt_work <- rt_work + rt_call___mul_i16.`2 + 6;
    acc <- (acc + term);
    rt_work <- rt_work + 2;
    rt_call___mul_i16 <@ __mul_i16 (a.[3], b.[0]);
    term <- rt_call___mul_i16.`1;
    rt_work <- rt_work + rt_call___mul_i16.`2 + 6;
    acc <- (acc + term);
    rt_work <- rt_work + 2;
    rt_call___montgomery_reduce <@ __montgomery_reduce (acc);
    aux <- rt_call___montgomery_reduce.`1;
    rt_work <- rt_work + rt_call___montgomery_reduce.`2 + 3;
    r.[3] <- aux;
    rt_work <- rt_work + 2;
    rt_call___mul_i16 <@ __mul_i16 (r.[0], (W16.of_int 867));
    acc <- rt_call___mul_i16.`1;
    rt_work <- rt_work + rt_call___mul_i16.`2 + 5;
    rt_call___montgomery_reduce <@ __montgomery_reduce (acc);
    aux <- rt_call___montgomery_reduce.`1;
    rt_work <- rt_work + rt_call___montgomery_reduce.`2 + 3;
    r.[0] <- aux;
    rt_work <- rt_work + 2;
    rt_call___mul_i16 <@ __mul_i16 (r.[1], (W16.of_int 867));
    acc <- rt_call___mul_i16.`1;
    rt_work <- rt_work + rt_call___mul_i16.`2 + 5;
    rt_call___montgomery_reduce <@ __montgomery_reduce (acc);
    aux <- rt_call___montgomery_reduce.`1;
    rt_work <- rt_work + rt_call___montgomery_reduce.`2 + 3;
    r.[1] <- aux;
    rt_work <- rt_work + 2;
    rt_call___mul_i16 <@ __mul_i16 (r.[2], (W16.of_int 867));
    acc <- rt_call___mul_i16.`1;
    rt_work <- rt_work + rt_call___mul_i16.`2 + 5;
    rt_call___montgomery_reduce <@ __montgomery_reduce (acc);
    aux <- rt_call___montgomery_reduce.`1;
    rt_work <- rt_work + rt_call___montgomery_reduce.`2 + 3;
    r.[2] <- aux;
    rt_work <- rt_work + 2;
    rt_call___mul_i16 <@ __mul_i16 (r.[3], (W16.of_int 867));
    acc <- rt_call___mul_i16.`1;
    rt_work <- rt_work + rt_call___mul_i16.`2 + 5;
    rt_call___montgomery_reduce <@ __montgomery_reduce (acc);
    aux <- rt_call___montgomery_reduce.`1;
    rt_work <- rt_work + rt_call___montgomery_reduce.`2 + 3;
    r.[3] <- aux;
    rt_work <- rt_work + 2;
    rt_work <- rt_work + 13;
    return (r,rt_work);
  }
  proc jade_ntruplus_ntruplus768_amd64_ref_poly_basemul (rp:W16.t Array768.t,
                                                         ap:W16.t Array768.t,
                                                         bp:W16.t Array768.t) : (W16.t Array768.t) * int = {
    var rt_work:int;
    var zetasp:W16.t Array96.t;
    var i:W64.t;
    var zeta_0:W16.t;
    var off:W64.t;
    var ta:W16.t Array4.t;
    var tb:W16.t Array4.t;
    var tr:W16.t Array4.t;
    var _0:W64.t;
    var rt_call___basemul4:(W16.t Array4.t) * int;
    rt_work <- 6912;
    ta <- witness;
    rt_work <- rt_work + 5;
    tb <- witness;
    rt_work <- rt_work + 5;
    tr <- witness;
    rt_work <- rt_work + 5;
    zetasp <- witness;
    rt_work <- rt_work + 97;
    _0 <- (init_msf);
    rt_work <- rt_work + 1;
    zetasp <- (Array96.init (fun i_0 => nTRUPLUS_ZETAS96.[(0 + i_0)]));
    rt_work <- rt_work + 771;
    i <- (W64.of_int 0);
    rt_work <- rt_work + 1;
    rt_work <- rt_work + 2;
    while ((i \ult (W64.of_int (768 %/ 8)))) {
      zeta_0 <- zetasp.[(W64.to_uint i)];
      rt_work <- rt_work + 2;
      off <- i;
      rt_work <- rt_work + 1;
      off <- (off `<<` (W8.of_int 3));
      rt_work <- rt_work + 2;
      ta.[0] <- ap.[(W64.to_uint off)];
      rt_work <- rt_work + 3;
      ta.[1] <- ap.[(W64.to_uint (off + (W64.of_int 1)))];
      rt_work <- rt_work + 4;
      ta.[2] <- ap.[(W64.to_uint (off + (W64.of_int 2)))];
      rt_work <- rt_work + 4;
      ta.[3] <- ap.[(W64.to_uint (off + (W64.of_int 3)))];
      rt_work <- rt_work + 4;
      tb.[0] <- bp.[(W64.to_uint off)];
      rt_work <- rt_work + 3;
      tb.[1] <- bp.[(W64.to_uint (off + (W64.of_int 1)))];
      rt_work <- rt_work + 4;
      tb.[2] <- bp.[(W64.to_uint (off + (W64.of_int 2)))];
      rt_work <- rt_work + 4;
      tb.[3] <- bp.[(W64.to_uint (off + (W64.of_int 3)))];
      rt_work <- rt_work + 4;
      rt_call___basemul4 <@ __basemul4 (tr, ta, tb, zeta_0);
      tr <- rt_call___basemul4.`1;
      rt_work <- rt_work + rt_call___basemul4.`2 + 18;
      rp.[(W64.to_uint off)] <- tr.[0];
      rt_work <- rt_work + 3;
      rp.[(W64.to_uint (off + (W64.of_int 1)))] <- tr.[1];
      rt_work <- rt_work + 4;
      rp.[(W64.to_uint (off + (W64.of_int 2)))] <- tr.[2];
      rt_work <- rt_work + 4;
      rp.[(W64.to_uint (off + (W64.of_int 3)))] <- tr.[3];
      rt_work <- rt_work + 4;
      off <- (off + (W64.of_int 4));
      rt_work <- rt_work + 2;
      ta.[0] <- ap.[(W64.to_uint off)];
      rt_work <- rt_work + 3;
      ta.[1] <- ap.[(W64.to_uint (off + (W64.of_int 1)))];
      rt_work <- rt_work + 4;
      ta.[2] <- ap.[(W64.to_uint (off + (W64.of_int 2)))];
      rt_work <- rt_work + 4;
      ta.[3] <- ap.[(W64.to_uint (off + (W64.of_int 3)))];
      rt_work <- rt_work + 4;
      tb.[0] <- bp.[(W64.to_uint off)];
      rt_work <- rt_work + 3;
      tb.[1] <- bp.[(W64.to_uint (off + (W64.of_int 1)))];
      rt_work <- rt_work + 4;
      tb.[2] <- bp.[(W64.to_uint (off + (W64.of_int 2)))];
      rt_work <- rt_work + 4;
      tb.[3] <- bp.[(W64.to_uint (off + (W64.of_int 3)))];
      rt_work <- rt_work + 4;
      rt_call___basemul4 <@ __basemul4 (tr, ta, tb, (- zeta_0));
      tr <- rt_call___basemul4.`1;
      rt_work <- rt_work + rt_call___basemul4.`2 + 19;
      rp.[(W64.to_uint off)] <- tr.[0];
      rt_work <- rt_work + 3;
      rp.[(W64.to_uint (off + (W64.of_int 1)))] <- tr.[1];
      rt_work <- rt_work + 4;
      rp.[(W64.to_uint (off + (W64.of_int 2)))] <- tr.[2];
      rt_work <- rt_work + 4;
      rp.[(W64.to_uint (off + (W64.of_int 3)))] <- tr.[3];
      rt_work <- rt_work + 4;
      i <- (i + (W64.of_int 1));
      rt_work <- rt_work + 2;
      rt_work <- rt_work + 2;
    }
    rt_work <- rt_work + 2305;
    return (rp,rt_work);
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

lemma rt_fixed_basemul___mul_i16_projection :
 equiv[RTFixedBasemul.__mul_i16 ~ NTRUPlus768PolyBasemul.M.__mul_i16 :
 ={a,b} ==> res{1}.`1=res{2}].
proof. proc.
 auto.
qed.
lemma rt_fixed_basemul___mul_i16_cost :
 hoare[RTFixedBasemul.__mul_i16 : true ==> 0<=res.`2<=7].
proof. proc.
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_basemul___montgomery_reduce_projection :
 equiv[RTFixedBasemul.__montgomery_reduce ~ NTRUPlus768PolyBasemul.M.__montgomery_reduce :
 ={a} ==> res{1}.`1=res{2}].
proof. proc.
 auto.
qed.
lemma rt_fixed_basemul___montgomery_reduce_cost :
 hoare[RTFixedBasemul.__montgomery_reduce : true ==> 0<=res.`2<=18].
proof. proc.
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_basemul___basemul4_projection :
 equiv[RTFixedBasemul.__basemul4 ~ NTRUPlus768PolyBasemul.M.__basemul4 :
 ={r,a,b,zeta_0} ==> res{1}.`1=res{2}].
proof. proc.
 wp;call rt_fixed_basemul___montgomery_reduce_projection.
 wp;call rt_fixed_basemul___mul_i16_projection.
 wp;call rt_fixed_basemul___montgomery_reduce_projection.
 wp;call rt_fixed_basemul___mul_i16_projection.
 wp;call rt_fixed_basemul___montgomery_reduce_projection.
 wp;call rt_fixed_basemul___mul_i16_projection.
 wp;call rt_fixed_basemul___montgomery_reduce_projection.
 wp;call rt_fixed_basemul___mul_i16_projection.
 wp;call rt_fixed_basemul___montgomery_reduce_projection.
 wp;call rt_fixed_basemul___mul_i16_projection.
 wp;call rt_fixed_basemul___mul_i16_projection.
 wp;call rt_fixed_basemul___mul_i16_projection.
 wp;call rt_fixed_basemul___mul_i16_projection.
 wp;call rt_fixed_basemul___montgomery_reduce_projection.
 wp;call rt_fixed_basemul___mul_i16_projection.
 wp;call rt_fixed_basemul___mul_i16_projection.
 wp;call rt_fixed_basemul___mul_i16_projection.
 wp;call rt_fixed_basemul___mul_i16_projection.
 wp;call rt_fixed_basemul___montgomery_reduce_projection.
 wp;call rt_fixed_basemul___mul_i16_projection.
 wp;call rt_fixed_basemul___mul_i16_projection.
 wp;call rt_fixed_basemul___mul_i16_projection.
 wp;call rt_fixed_basemul___montgomery_reduce_projection.
 wp;call rt_fixed_basemul___mul_i16_projection.
 wp;call rt_fixed_basemul___mul_i16_projection.
 wp;call rt_fixed_basemul___montgomery_reduce_projection.
 wp;call rt_fixed_basemul___mul_i16_projection.
 wp;call rt_fixed_basemul___montgomery_reduce_projection.
 wp;call rt_fixed_basemul___mul_i16_projection.
 wp;call rt_fixed_basemul___mul_i16_projection.
 wp;call rt_fixed_basemul___montgomery_reduce_projection.
 wp;call rt_fixed_basemul___mul_i16_projection.
 wp;call rt_fixed_basemul___mul_i16_projection.
 wp;call rt_fixed_basemul___mul_i16_projection.
 auto.
qed.
lemma rt_fixed_basemul___basemul4_cost :
 hoare[RTFixedBasemul.__basemul4 : true ==> 0<=res.`2<=618].
proof. proc.
 wp;call rt_fixed_basemul___montgomery_reduce_cost.
 wp;call rt_fixed_basemul___mul_i16_cost.
 wp;call rt_fixed_basemul___montgomery_reduce_cost.
 wp;call rt_fixed_basemul___mul_i16_cost.
 wp;call rt_fixed_basemul___montgomery_reduce_cost.
 wp;call rt_fixed_basemul___mul_i16_cost.
 wp;call rt_fixed_basemul___montgomery_reduce_cost.
 wp;call rt_fixed_basemul___mul_i16_cost.
 wp;call rt_fixed_basemul___montgomery_reduce_cost.
 wp;call rt_fixed_basemul___mul_i16_cost.
 wp;call rt_fixed_basemul___mul_i16_cost.
 wp;call rt_fixed_basemul___mul_i16_cost.
 wp;call rt_fixed_basemul___mul_i16_cost.
 wp;call rt_fixed_basemul___montgomery_reduce_cost.
 wp;call rt_fixed_basemul___mul_i16_cost.
 wp;call rt_fixed_basemul___mul_i16_cost.
 wp;call rt_fixed_basemul___mul_i16_cost.
 wp;call rt_fixed_basemul___mul_i16_cost.
 wp;call rt_fixed_basemul___montgomery_reduce_cost.
 wp;call rt_fixed_basemul___mul_i16_cost.
 wp;call rt_fixed_basemul___mul_i16_cost.
 wp;call rt_fixed_basemul___mul_i16_cost.
 wp;call rt_fixed_basemul___montgomery_reduce_cost.
 wp;call rt_fixed_basemul___mul_i16_cost.
 wp;call rt_fixed_basemul___mul_i16_cost.
 wp;call rt_fixed_basemul___montgomery_reduce_cost.
 wp;call rt_fixed_basemul___mul_i16_cost.
 wp;call rt_fixed_basemul___montgomery_reduce_cost.
 wp;call rt_fixed_basemul___mul_i16_cost.
 wp;call rt_fixed_basemul___mul_i16_cost.
 wp;call rt_fixed_basemul___montgomery_reduce_cost.
 wp;call rt_fixed_basemul___mul_i16_cost.
 wp;call rt_fixed_basemul___mul_i16_cost.
 wp;call rt_fixed_basemul___mul_i16_cost.
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_basemul_jade_ntruplus_ntruplus768_amd64_ref_poly_basemul_projection :
 equiv[RTFixedBasemul.jade_ntruplus_ntruplus768_amd64_ref_poly_basemul ~ NTRUPlus768PolyBasemul.M.jade_ntruplus_ntruplus768_amd64_ref_poly_basemul :
 ={rp,ap,bp} ==> res{1}.`1=res{2}].
proof. proc.
 wp;while(={rp,ap,bp,i,zetasp,ta,tb,tr}).
  + wp;call rt_fixed_basemul___basemul4_projection.
    wp;call rt_fixed_basemul___basemul4_projection.
    auto.
 auto.
qed.
lemma rt_fixed_basemul_jade_ntruplus_ntruplus768_amd64_ref_poly_basemul_cost :
 hoare[RTFixedBasemul.jade_ntruplus_ntruplus768_amd64_ref_poly_basemul : true ==> 0<=res.`2<=142008].
proof. proc.
 wp;while(0<=W64.to_uint i<=96 /\ 0<=rt_work<=7799+1374*(W64.to_uint i-(0))).
  + wp;call rt_fixed_basemul___basemul4_cost.
    wp;call rt_fixed_basemul___basemul4_cost.
    auto=> /> &hr;rewrite W64.ultE /=;move=>*;try (rewrite rt_fixed_u64_next 1:/#);smt().
 auto=> />;smt(rt_fixed_exit).
qed.
op rt_fixed_basemul_bound:int = 142008.
lemma rt_fixed_basemul_bound_cost : hoare[RTFixedBasemul.jade_ntruplus_ntruplus768_amd64_ref_poly_basemul : true ==>0<=res.`2<=rt_fixed_basemul_bound].
proof. exact rt_fixed_basemul_jade_ntruplus_ntruplus768_amd64_ref_poly_basemul_cost. qed.
