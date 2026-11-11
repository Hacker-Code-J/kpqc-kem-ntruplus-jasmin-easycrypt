require import AllCore Distr.
from Jasmin require import JWord.
require import Array192.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteProof.
require import NTRUPlus768FreshRetryLaw NTRUPlus768FreshBoundedLaw NTRUPlus768FreshKeyPairLaw.
require import NTRUPlus768StoppedKeygenModel NTRUPlus768ROMOracles NTRUPlus768ROMDistributions.
require import NTRUPlus768AcceptanceRoots NTRUPlus768AcceptanceAlgebra NTRUPlus768AcceptanceInput.
require import NTRUPlus768AcceptanceCover.
require import NTRUPlus768AcceptanceMasks NTRUPlus768UniformOrbitBound.
require import NTRUPlus768EvaluationSemantics.

op acceptance_bad (is_f:bool) (j:int) (buf:W8.t Array192.t) =
 quadratic_divides (lift_int(acceptance_root j)) (acceptance_input is_f buf).

lemma acceptance_bad_probability is_f j :
 0<=j<384 => mu uniform192 (acceptance_bad is_f j)<=1%r/1024%r.
proof.
 move=>hj.
 apply(xor1024_disjoint_event_bound (acceptance_masks (acceptance_root j))
  (acceptance_bad is_f j)).
 exact (acceptance_bad_translates_disjoint is_f j hj).
qed.

lemma keygen_f_failure_covered buf :
 !keygen_f_accept buf => indexed_event_union 384 (acceptance_bad true) buf.
proof.
 move=>hf; have [j [hj hd]]:=keygen_f_rejected_quadratic buf hf.
 rewrite /indexed_event_union; exists j; split; first exact hj.
 by rewrite /acceptance_bad /acceptance_input /acceptance_shape.
qed.
lemma keygen_g_failure_covered buf :
 !keygen_g_accept buf => indexed_event_union 384 (acceptance_bad false) buf.
proof.
 move=>hg; have [j [hj hd]]:=keygen_g_rejected_quadratic buf hg.
 rewrite /indexed_event_union; exists j; split; first exact hj.
 by rewrite /acceptance_bad /acceptance_input /acceptance_shape.
qed.

(* The final lower bounds have no probabilistic or algebraic premises:
   every actual failure is covered by the checked quadratic events. *)
lemma fresh_f_accept_lower : 5%r/8%r<=fresh_f_accept_mass.
proof.
 apply(uniform192_acceptance_from_384_bad keygen_f_accept (acceptance_bad true)).
 + exact (acceptance_bad_probability true).
 exact keygen_f_failure_covered.
qed.
lemma fresh_g_accept_lower : 5%r/8%r<=fresh_g_accept_mass.
proof.
 apply(uniform192_acceptance_from_384_bad keygen_g_accept (acceptance_bad false)).
 + exact (acceptance_bad_probability false).
 exact keygen_g_failure_covered.
qed.
lemma fresh_f_accept_positive : 0%r<fresh_f_accept_mass.
proof. have h:=fresh_f_accept_lower; smt(). qed.
lemma fresh_g_accept_positive : 0%r<fresh_g_accept_mass.
proof. have h:=fresh_g_accept_lower; smt(). qed.

lemma fresh_keygen_instrumented_lossless_unconditional :
 islossless KeygenInstrumented(UniformSeedRNG,FreshExpand,SHAKEFROM).run.
proof. exact (fresh_keygen_instrumented_ll fresh_f_accept_positive fresh_g_accept_positive). qed.
lemma fresh_keygen_lossless_unconditional :
 islossless Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run.
proof. exact (fresh_keygen_ll fresh_f_accept_positive fresh_g_accept_positive). qed.
lemma fresh_counted_keygen_lossless_unconditional :
 islossless CountedKeygen(UniformSeedRNG,FreshExpand).run.
proof. exact (fresh_counted_keygen_ll fresh_f_accept_positive fresh_g_accept_positive). qed.

(* Normalization of the already-proved joint accepted-buffer law.  The
   conditioning in each factor retains dependencies among its coefficients. *)
lemma fresh_accepted_pair_normalized : is_lossless fresh_accepted_pair_law.
proof.
 rewrite /fresh_accepted_pair_law dprod_ll; split.
 + exact (dcond_ll uniform192 keygen_f_accept fresh_f_accept_positive).
 exact (dcond_ll uniform192 keygen_g_accept fresh_g_accept_positive).
qed.
