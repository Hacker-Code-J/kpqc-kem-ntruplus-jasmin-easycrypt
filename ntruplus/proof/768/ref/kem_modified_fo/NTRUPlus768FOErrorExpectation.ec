require import AllCore List Distr RealSeries StdOrder.
from Jasmin require import JWord.
require import Array192 Array14466.
require import NTRUPlus768FOError NTRUPlus768StoppedKeygenModel.
require import NTRUPlus768FOModel NTRUPlus768ACWC2Oracle NTRUPlus768ACWC2BaseModel.
require import NTRUPlus768ACWC2WorstCase.
require import NTRUPlus768ACWC2KeyMean NTRUPlus768ACWC2Numerical.
require import NTRUPlus768KEMProposalContext NTRUPlus768FreshRetryLaw.
import RealOrder RField.

op [opaque] fo_expected_error (dk:keygen_output distr) =
 E dk(fun (out:keygen_output)=>E acwc2_eager_g_law (fo_error out.`1)).

lemma fo_expected_error_range (dk:keygen_output distr) :
 0%r<=fo_expected_error dk<=1%r.
proof.
 rewrite /fo_expected_error; apply acwc2_expectation_unit_range=>out.
 exact(fo_error_expectation_range out.`1 acwc2_eager_g_law).
qed.

lemma fo_key_error_hasE (dk:keygen_output distr) :
 hasE dk(fun (out:keygen_output)=>E acwc2_eager_g_law (fo_error out.`1)).
proof.
 apply(acwc2_bounded_hasE dk _ 1%r)=> // out.
 exact(fo_error_expectation_range out.`1 acwc2_eager_g_law).
qed.

(* The stronger base-error concentration theorem holds for every witness.
   The only normalization needed to average its constant overhead is dk LL. *)
lemma fo_expected_error_bound (dk:keygen_output distr) : is_lossless dk =>
 fo_expected_error dk<=E dk(fun (out:keygen_output)=>acwc2_base_mean out.`1)+
 acwc2_epsilon+acwc2_union_tail.
proof.
 move=>hll; pose overhead:=acwc2_epsilon+acwc2_union_tail.
 have h0:0%r<=overhead by exact acwc2_overhead_nonnegative.
 have hm:hasE dk(fun (out:keygen_output)=>acwc2_base_mean out.`1).
 + apply(acwc2_bounded_hasE dk _ 1%r)=> // out; exact(acwc2_base_mean_range out.`1).
 have hr:hasE dk(fun (out:keygen_output)=>acwc2_base_mean out.`1+overhead).
 + apply(acwc2_bounded_hasE dk _ (1%r+overhead)); first smt().
   move=>out; have h:=acwc2_base_mean_range out.`1; smt().
 have hb:fo_expected_error dk<=E dk(fun (out:keygen_output)=>acwc2_base_mean out.`1+overhead).
 + rewrite /fo_expected_error; apply(in_ler_exp dk _ _ (fo_key_error_hasE dk) hr).
   move=>out ho; have h:=fo_eager_error_bound out.`1.
   rewrite /overhead; smt().
 have he:E dk(fun (out:keygen_output)=>acwc2_base_mean out.`1+overhead)=
   E dk(fun (out:keygen_output)=>acwc2_base_mean out.`1)+acwc2_epsilon+acwc2_union_tail.
 + rewrite expD 1:hm 1:(hasEC dk overhead) expC hll /overhead; ring.
 by move:hb; rewrite he.
qed.

lemma fo_expected_error_pads (dk:keygen_output distr) :
 E dk(fun (out:keygen_output)=>E acwc2_gpads_law
   (fun (pads:W8.t Array192.t list)=>fo_error out.`1 (acwc2_gfun pads)))=
 fo_expected_error dk.
proof.
 rewrite /fo_expected_error; apply eq_exp=>out hout /=.
 rewrite /acwc2_eager_g_law (exp_dmap _ _ _ (fo_error_hasE out.`1 _)) /(\o).
 done.
qed.

lemma fo_fresh_expected_error &m :
 fo_expected_error (mk(fun z=>Pr[KeygenSource(FreshExpand).guess(witness) @ &m:res=z]))
 <1%r/(2%r^353).
proof.
 pose dk:=mk(fun z=>Pr[KeygenSource(FreshExpand).guess(witness) @ &m:res=z]).
 have hb:=fo_expected_error_bound dk (acwc2_fresh_key_law_lossless &m).
 have ha:=acwc2_fresh_key_mean_bound &m.
 exact(acwc2_numerical_combination _ _ ha hb).
qed.

(* Both independent draws are explicit. In particular, no pointwise bound
   of 2^-353 on an individual key or fixed G is asserted. *)
lemma fo_fresh_expected_error_pads &m :
 E (mk(fun z=>Pr[KeygenSource(FreshExpand).guess(witness) @ &m:res=z]))
   (fun (out:keygen_output)=>E acwc2_gpads_law
     (fun (pads:W8.t Array192.t list)=>fo_error out.`1 (acwc2_gfun pads)))
 <1%r/(2%r^353).
proof. rewrite fo_expected_error_pads; exact(fo_fresh_expected_error &m). qed.

lemma fo_fresh_expected_error_scaled &m (Q:real) : 0%r<=Q =>
 Q*fo_expected_error (mk(fun z=>Pr[KeygenSource(FreshExpand).guess(witness) @ &m:res=z]))
 <=Q/(2%r^353).
proof.
 move=>hQ; have h:=fo_fresh_expected_error &m.
 have he:Q*(1%r/(2%r^353))=Q/(2%r^353) by ring.
 have hm:=ler_wpmul2l Q hQ _ _ (ltrW _ _ h).
 by move:hm; rewrite he.
qed.

(* A partial adaptive kernel retains its missing mass. A pointwise
   bound is averaged without assuming that the kernel terminates. *)
lemma fo_kernel_average ['a 'b] (d:'a distr) (K:'a->'b distr) bad (bound:'a->real) :
 hasE d bound =>(forall x,x \in d=>mu(K x)bad<=bound x) =>
 mu(dlet d K)bad<=E d bound.
proof.
 move=>hb hpoint.
 have hm:hasE d(fun x=>mu(K x)bad).
 + apply(acwc2_bounded_hasE d _ 1%r)=> // x; exact(mu_bounded (K x) bad).
 have he:mu(dlet d K)bad=E d(fun x=>mu(K x)bad).
 + rewrite dletE /E; apply eq_sum=>x /=; ring.
 rewrite he; exact(in_ler_exp d _ _ hm hb hpoint).
qed.
