require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import Array768 Array1152 WArray1152 WArray1536.


require import NTRUPlus768PolyToBytes.
(* Each rt_work update is a ghost charge for the preceding concrete instruction.
   Each array parameter is copied into an owned buffer (3N primitive events: allocation, load, store). Whole-array assignments/returns also pay 3N; Array.set updates this owned buffer. These procedures preserve the original data path; no global state is added. *)
module RTFixedToBytes = {
  proc jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes (rp:W8.t Array1152.t,
                                                         ap:W16.t Array768.t) : (W8.t Array1152.t) * int = {
    var rt_work:int;
    var i:W64.t;
    var off:W64.t;
    var t0:W16.t;
    var mask:W16.t;
    var t1:W16.t;
    var t:W16.t;
    var _0:W64.t;
    rt_work <- 5760;
    _0 <- (init_msf);
    rt_work <- rt_work + 1;
    i <- (W64.of_int 0);
    rt_work <- rt_work + 1;
    rt_work <- rt_work + 2;
    while ((i \ult (W64.of_int (768 %/ 2)))) {
      off <- i;
      rt_work <- rt_work + 1;
      off <- (off `<<` (W8.of_int 1));
      rt_work <- rt_work + 2;
      t0 <- ap.[(W64.to_uint ((W64.of_int 2) * i))];
      rt_work <- rt_work + 3;
      mask <- t0;
      rt_work <- rt_work + 1;
      mask <- (mask `|>>` (W8.of_int 15));
      rt_work <- rt_work + 2;
      mask <- (mask `&` (W16.of_int 3457));
      rt_work <- rt_work + 2;
      t0 <- (t0 + mask);
      rt_work <- rt_work + 2;
      t1 <- ap.[(W64.to_uint (((W64.of_int 2) * i) + (W64.of_int 1)))];
      rt_work <- rt_work + 4;
      mask <- t1;
      rt_work <- rt_work + 1;
      mask <- (mask `|>>` (W8.of_int 15));
      rt_work <- rt_work + 2;
      mask <- (mask `&` (W16.of_int 3457));
      rt_work <- rt_work + 2;
      t1 <- (t1 + mask);
      rt_work <- rt_work + 2;
      off <- (off + i);
      rt_work <- rt_work + 2;
      rp.[(W64.to_uint off)] <- (truncateu8 t0);
      rt_work <- rt_work + 3;
      t <- t0;
      rt_work <- rt_work + 1;
      t <- (t `>>` (W8.of_int 8));
      rt_work <- rt_work + 2;
      mask <- t1;
      rt_work <- rt_work + 1;
      mask <- (mask `<<` (W8.of_int 4));
      rt_work <- rt_work + 2;
      t <- (t `|` mask);
      rt_work <- rt_work + 2;
      rp.[(W64.to_uint (off + (W64.of_int 1)))] <- (truncateu8 t);
      rt_work <- rt_work + 4;
      t <- t1;
      rt_work <- rt_work + 1;
      t <- (t `>>` (W8.of_int 4));
      rt_work <- rt_work + 2;
      rp.[(W64.to_uint (off + (W64.of_int 2)))] <- (truncateu8 t);
      rt_work <- rt_work + 4;
      i <- (i + (W64.of_int 1));
      rt_work <- rt_work + 2;
      rt_work <- rt_work + 2;
    }
    rt_work <- rt_work + 3457;
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

lemma rt_fixed_tobytes_jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes_projection :
 equiv[RTFixedToBytes.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes ~ NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes :
 ={rp,ap} ==> res{1}.`1=res{2}].
proof. proc.
 wp;while(={rp,ap,i}).
  + auto.
 auto.
qed.
lemma rt_fixed_tobytes_jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes_cost :
 hoare[RTFixedToBytes.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes : true ==> 0<=res.`2<=29189].
proof. proc.
 wp;while(0<=W64.to_uint i<=384 /\ 0<=rt_work<=5764+52*(W64.to_uint i-(0))).
  + auto=> /> &hr;rewrite W64.ultE /=;move=>*;try (rewrite rt_fixed_u64_next 1:/#);smt().
 auto=> />;smt(rt_fixed_exit).
qed.
op rt_fixed_tobytes_bound:int = 29189.
lemma rt_fixed_tobytes_bound_cost : hoare[RTFixedToBytes.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes : true ==>0<=res.`2<=rt_fixed_tobytes_bound].
proof. exact rt_fixed_tobytes_jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes_cost. qed.
