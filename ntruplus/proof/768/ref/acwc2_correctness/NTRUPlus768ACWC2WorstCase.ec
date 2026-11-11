require import AllCore List Distr DProd Finite StdBigop StdOrder.
from Jasmin require import JWord.
require import Array96 Array192 Array768 Array14466.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768PKEModel.
require import NTRUPlus768ACWC2BaseModel NTRUPlus768ACWC2Domains.
require import NTRUPlus768ACWC2Oracle NTRUPlus768ACWC2Mean.
require import NTRUPlus768ACWC2Collision NTRUPlus768ACWC2Concentration NTRUPlus768ACWC2Numerical.
import RealOrder RField.

(* Concentration is applied to the single-entry underlying-PKE envelope.
   The actual decoder's failure indicators need not be independent. *)
lemma acwc2_eager_weighted_max_bound w :
 E acwc2_eager_g_law(fun g=>acwc2_finite_max acwc2_message_enum
   (fun msg=>acwc2_weighted_bad w msg g)) <=
 acwc2_base_mean w+acwc2_epsilon+acwc2_union_tail.
proof.
 have hc:0%r<=acwc2_collision_mass.
 + rewrite /acwc2_collision_mass; apply expr_ge0; smt().
 have h4:0%r<=acwc2_collision_mass^4 by apply expr_ge0.
 have hK:0%r<=65536%r*acwc2_collision_mass^4 by smt().
 have hbase:=acwc2_base_mean_range w.
 have hb:=acwc2_finite_max_concentration acwc2_eager_g_law acwc2_message_enum
  (fun msg g=>acwc2_weighted_bad w msg g) (acwc2_base_mean w) acwc2_epsilon
  (65536%r*acwc2_collision_mass^4) acwc2_eager_g_finite acwc2_eager_g_lossless
  _ acwc2_epsilon_positive hK _ _; first smt().
 + move=>msg g hmsg hg; exact(acwc2_weighted_bad_range w msg g).
 + move=>msg hmsg.
   have h:=acwc2_eager_eighth_bound w msg.
   move:h; rewrite acwc2_r_weight_collision -/acwc2_collision_mass=>h.
   have hscale:105%r*acwc2_collision_mass^4<=65536%r*acwc2_collision_mass^4 by smt().
   exact(ler_trans _ _ _ h hscale).
 have hn:(size acwc2_message_enum)%r=2%r^768.
 + by rewrite acwc2_message_cardinality fromintXn.
 have he:acwc2_base_mean w+acwc2_epsilon+
   (size acwc2_message_enum)%r*(65536%r*acwc2_collision_mass^4)/(acwc2_epsilon^8)=
   acwc2_base_mean w+acwc2_epsilon+acwc2_union_tail.
 + rewrite hn /acwc2_union_tail; ring.
 by move:hb; rewrite he.
qed.

(* Bounded expectations allow the actual reified key distribution to be
   used directly, without assuming or computing a finite key enumeration. *)
lemma acwc2_bounded_hasE ['a] (d:'a distr) (f:'a->real) B :
 0%r<=B => (forall x,0%r<=f x<=B) =>hasE d f.
proof.
 move=>hB hf.
 apply(hasE_le d f (fun _=>B)); first exact(hasEC d B).
 move=>x; have h:=hf x; smt(RealOrder.ger0_norm).
qed.
lemma acwc2_expectation_unit_range ['a] (d:'a distr) (f:'a->real) :
 (forall x,0%r<=f x<=1%r) =>0%r<=E d f<=1%r.
proof.
 move=>hf.
 have h0:0%r<=E d f by apply exp_ge0; move=>x; have h:=hf x; smt().
 have he:E d f<=E d (fun _=>1%r).
 + apply ler_exp; first by apply(acwc2_bounded_hasE d f 1%r); smt().
   - exact(hasEC d 1%r).
   move=>x; have h:=hf x; smt().
 rewrite expC in he; have hm:=mu_bounded d predT; smt().
qed.

require import NTRUPlus768ACWC2Error NTRUPlus768StoppedKeygenModel.
op [opaque] acwc2_expected_worst_error (dk:keygen_output distr) =
 E dk(fun (out:keygen_output)=>E acwc2_eager_g_law(fun g=>acwc2_worst_error out.`1 g)).

lemma acwc2_eager_worst_range w :
 0%r<=E acwc2_eager_g_law(fun g=>acwc2_worst_error w g)<=1%r.
proof.
 apply acwc2_expectation_unit_range=>g; exact(acwc2_worst_error_range w g).
qed.
lemma acwc2_eager_worst_bound w : pke_key_relation w =>
 E acwc2_eager_g_law(fun g=>acwc2_worst_error w g)<=
 acwc2_base_mean w+acwc2_epsilon+acwc2_union_tail.
proof.
 move=>hk.
 have h:E acwc2_eager_g_law(fun g=>acwc2_worst_error w g)<=
 E acwc2_eager_g_law(fun g=>acwc2_finite_max acwc2_message_enum
   (fun msg=>acwc2_weighted_bad w msg g)).
 + apply in_ler_exp; first 2 by apply hasE_finite; exact acwc2_eager_g_finite.
   move=>g hg; exact(acwc2_worst_error_bound w g hk).
 exact(ler_trans _ _ _ h (acwc2_eager_weighted_max_bound w)).
qed.
lemma acwc2_overhead_nonnegative : 0%r<=acwc2_epsilon+acwc2_union_tail.
proof.
 have he:=acwc2_epsilon_positive.
 have hc:0%r<=acwc2_collision_mass by rewrite /acwc2_collision_mass; apply expr_ge0; smt().
 have h2:0%r<=2%r^768 by apply expr_ge0; smt().
 have h4:0%r<=acwc2_collision_mass^4 by apply expr_ge0.
 have h8:0%r<acwc2_epsilon^8 by apply expr_gt0.
 have h:0%r<=acwc2_union_tail.
 + rewrite /acwc2_union_tail; apply divr_ge0; smt().
 smt().
qed.
lemma acwc2_expected_worst_bound (dk:keygen_output distr) :
 is_lossless dk => (forall (out:keygen_output),out \in dk=>pke_key_relation out.`1) =>
 acwc2_expected_worst_error dk <=
 E dk(fun (out:keygen_output)=>acwc2_base_mean out.`1)+acwc2_epsilon+acwc2_union_tail.
proof.
 move=>hll hk.
 pose overhead:=acwc2_epsilon+acwc2_union_tail.
 have h0:0%r<=overhead by exact acwc2_overhead_nonnegative.
 have hmean:hasE dk(fun (out:keygen_output)=>acwc2_base_mean out.`1).
 + apply(acwc2_bounded_hasE dk _ 1%r)=> // out; exact(acwc2_base_mean_range out.`1).
 have hleft:hasE dk(fun (out:keygen_output)=>E acwc2_eager_g_law(fun g=>acwc2_worst_error out.`1 g)).
 + apply(acwc2_bounded_hasE dk _ 1%r)=> // out; exact(acwc2_eager_worst_range out.`1).
 have hright:hasE dk(fun (out:keygen_output)=>acwc2_base_mean out.`1+overhead).
 + apply(acwc2_bounded_hasE dk _ (1%r+overhead)); first smt().
   move=>out; have hr:=acwc2_base_mean_range out.`1; smt().
 have hb:acwc2_expected_worst_error dk<=E dk(fun (out:keygen_output)=>acwc2_base_mean out.`1+overhead).
 + rewrite /acwc2_expected_worst_error; apply(in_ler_exp dk _ _ hleft hright).
   move=>out ho.
   have h:=acwc2_eager_worst_bound out.`1 (hk out ho).
   move:h; rewrite /overhead; smt().
 have he:E dk(fun (out:keygen_output)=>acwc2_base_mean out.`1+overhead)=
   E dk(fun (out:keygen_output)=>acwc2_base_mean out.`1)+acwc2_epsilon+acwc2_union_tail.
 + rewrite expD 1:hmean 1:(hasEC dk overhead) expC hll /overhead; ring.
 by move:hb; rewrite he.
qed.

require import NTRUPlus768ACWC2KeyMean NTRUPlus768KEMProposalContext NTRUPlus768FreshRetryLaw.

(* The key law is the actual accepted-key procedure, reified at the
   specified initial memory. There is no per-key small-error premise. *)
lemma acwc2_fresh_worst_correctness &m :
 acwc2_expected_worst_error
   (mk(fun z=>Pr[KeygenSource(FreshExpand).guess(witness) @ &m:res=z]))
 <1%r/(2%r^353).
proof.
 pose dk:=mk(fun z=>Pr[KeygenSource(FreshExpand).guess(witness) @ &m:res=z]).
 have hll:is_lossless dk by exact(acwc2_fresh_key_law_lossless &m).
 have hk:forall (out:keygen_output),out \in dk=>pke_key_relation out.`1.
 + move=>out ho; exact(acwc2_fresh_key_law_supported &m out ho).
 have ha:=acwc2_fresh_key_mean_bound &m.
 have hb:=acwc2_expected_worst_bound dk hll hk.
 exact(acwc2_numerical_combination _ _ ha hb).
qed.

require import NTRUPlus768ACWC2Execution.

(* Every counterfactual message uses the same previously selected pads.
   The fixed-oracle trial installs those answers deterministically, then
   samples a fresh buffer and calls the actual CBD and Enc/Dec kernels. *)
lemma acwc2_expected_worst_as_calls &m (dk:keygen_output distr) :
 E dk(fun (out:keygen_output)=>E acwc2_gpads_law
   (fun (pads:W8.t Array192.t list)=>acwc2_finite_max acwc2_message_enum
     (fun (msg:W8.t Array96.t)=>
       Pr[ACWC2FixedOracleTrial.run(pads,out.`1.`kg_pk,out.`1.`kg_sk,msg) @ &m:res])))
 =acwc2_expected_worst_error dk.
proof.
 rewrite /acwc2_expected_worst_error; apply eq_exp=>out hout /=.
 have hf:hasE (dmap acwc2_gpads_law acwc2_gfun)(fun g=>acwc2_worst_error out.`1 g).
 + apply hasE_finite; apply acwc2_dmap_finite; exact acwc2_gpads_finite.
 rewrite /acwc2_eager_g_law (exp_dmap _ _ _ hf) /(\o).
 apply eq_exp=>pads hp /=; rewrite /acwc2_worst_error.
 have he:(fun (msg:W8.t Array96.t)=>
     Pr[ACWC2FixedOracleTrial.run(pads,out.`1.`kg_pk,out.`1.`kg_sk,msg) @ &m:res])=
     (fun msg=>acwc2_message_error out.`1 (acwc2_gfun pads) msg).
 + apply fun_ext=>msg; exact(acwc2_fixed_oracle_trial_error &m out.`1 pads msg).
 by rewrite he.
qed.

(* Concrete endpoint: actual fresh KeyGen, a single sampled finite random
   oracle, maximum over all messages, and actual randomized array calls.
   No average-error, concentration, validity, or independence premise is
   left to instantiate. This is not an IND-CCA advantage bound. *)
lemma acwc2_fresh_worst_actual_calls &m :
 E (mk(fun z=>Pr[KeygenSource(FreshExpand).guess(witness) @ &m:res=z]))
  (fun (out:keygen_output)=>E acwc2_gpads_law
   (fun (pads:W8.t Array192.t list)=>acwc2_finite_max acwc2_message_enum
    (fun (msg:W8.t Array96.t)=>
      Pr[ACWC2FixedOracleTrial.run(pads,out.`1.`kg_pk,out.`1.`kg_sk,msg) @ &m:res])))
 <1%r/(2%r^353).
proof.
 rewrite acwc2_expected_worst_as_calls.
 exact(acwc2_fresh_worst_correctness &m).
qed.
