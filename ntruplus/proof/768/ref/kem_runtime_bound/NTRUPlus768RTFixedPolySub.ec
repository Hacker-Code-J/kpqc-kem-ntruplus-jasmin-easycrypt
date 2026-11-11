require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import Array768 WArray1536.


require import NTRUPlus768PolySub.
(* Each rt_work update is a ghost charge for the preceding concrete instruction.
   Each array parameter is copied into an owned buffer (3N primitive events: allocation, load, store). Whole-array assignments/returns also pay 3N; Array.set updates this owned buffer. These procedures preserve the original data path; no global state is added. *)
module RTFixedPolySub = {
  proc jade_ntruplus_ntruplus768_amd64_ref_poly_sub (rp:W16.t Array768.t,
                                                     ap:W16.t Array768.t,
                                                     bp:W16.t Array768.t) : (W16.t Array768.t) * int = {
    var rt_work:int;
    var i:W64.t;
    var t:W16.t;
    var _0:W64.t;
    rt_work <- 6912;
    _0 <- (init_msf);
    rt_work <- rt_work + 1;
    i <- (W64.of_int 0);
    rt_work <- rt_work + 1;
    rt_work <- rt_work + 2;
    while ((i \ult (W64.of_int 768))) {
      t <- ap.[(W64.to_uint i)];
      rt_work <- rt_work + 2;
      t <- (t - bp.[(W64.to_uint i)]);
      rt_work <- rt_work + 3;
      rp.[(W64.to_uint i)] <- t;
      rt_work <- rt_work + 2;
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

lemma rt_fixed_polysub_jade_ntruplus_ntruplus768_amd64_ref_poly_sub_projection :
 equiv[RTFixedPolySub.jade_ntruplus_ntruplus768_amd64_ref_poly_sub ~ NTRUPlus768PolySub.M.jade_ntruplus_ntruplus768_amd64_ref_poly_sub :
 ={rp,ap,bp} ==> res{1}.`1=res{2}].
proof. proc.
 wp;while(={rp,ap,bp,i}).
  + auto.
 auto.
qed.
lemma rt_fixed_polysub_jade_ntruplus_ntruplus768_amd64_ref_poly_sub_cost :
 hoare[RTFixedPolySub.jade_ntruplus_ntruplus768_amd64_ref_poly_sub : true ==> 0<=res.`2<=17669].
proof. proc.
 wp;while(0<=W64.to_uint i<=768 /\ 0<=rt_work<=6916+11*(W64.to_uint i-(0))).
  + auto=> /> &hr;rewrite W64.ultE /=;move=>*;try (rewrite rt_fixed_u64_next 1:/#);smt().
 auto=> />;smt(rt_fixed_exit).
qed.
op rt_fixed_polysub_bound:int = 17669.
lemma rt_fixed_polysub_bound_cost : hoare[RTFixedPolySub.jade_ntruplus_ntruplus768_amd64_ref_poly_sub : true ==>0<=res.`2<=rt_fixed_polysub_bound].
proof. exact rt_fixed_polysub_jade_ntruplus_ntruplus768_amd64_ref_poly_sub_cost. qed.
