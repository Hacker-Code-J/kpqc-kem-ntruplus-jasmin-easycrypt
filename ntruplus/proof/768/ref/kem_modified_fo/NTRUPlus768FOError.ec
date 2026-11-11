require import AllCore Distr DProd StdOrder.
from Jasmin require import JWord.
require import Array96 Array192 Array224.
require import NTRUPlus768FOModel NTRUPlus768ROMDistributions.
require import NTRUPlus768HashPayloadSampling NTRUPlus768PKEKeyDistribution.
require import NTRUPlus768ACWC2Oracle NTRUPlus768ACWC2Mean NTRUPlus768ACWC2Domains.
require import NTRUPlus768ACWC2BaseModel NTRUPlus768ACWC2Concentration NTRUPlus768ACWC2Numerical.
require import NTRUPlus768ACWC2Error NTRUPlus768ACWC2WorstCase.
import RealOrder.

(* This is underlying PKE decryption failure at the single entry G(r).
   No transformed-decoder failure bound is used in either direction. *)
lemma fo_randomness_law : dmap uniform224 fo_randomness=pke_psi1.
proof.
 rewrite /fo_randomness -dmap_comp uniform224_tail_law.
 exact pke_cbd1_uniform.
qed.

lemma fo_base_bad_probability w g msg :
 mu uniform224 (fo_base_bad w g msg)=acwc2_weighted_bad w msg g.
proof.
 rewrite acwc2_weighted_bad_probability -fo_randomness_law
   (dmapE uniform224 fo_randomness (fun r=>acwc2_pad_bad w msg r(g r))).
 apply mu_eq=>hout; by rewrite /fo_base_bad /(\o).
qed.

lemma fo_error_range w g : 0%r<=fo_error w g<=1%r.
proof.
 rewrite /fo_error; split; first exact(acwc2_max_nonnegative _ _).
 move=>_; apply acwc2_max_upper=> // msg hm.
 have [_ h]:=acwc2_weighted_bad_range w msg g; exact h.
qed.

lemma fo_message_error_bound w g msg : acwc2_weighted_bad w msg g<=fo_error w g.
proof.
 rewrite /fo_error.
 apply(acwc2_finite_max_member acwc2_message_enum (fun m=>acwc2_weighted_bad w m g) msg).
 exact(acwc2_message_enum_full msg).
qed.

lemma fo_base_bad_bound w g msg : mu uniform224 (fo_base_bad w g msg)<=fo_error w g.
proof. rewrite fo_base_bad_probability; exact(fo_message_error_bound w g msg). qed.

lemma fo_error_hasE w (d:acwc2_g_function distr) : hasE d (fo_error w).
proof. apply(acwc2_bounded_hasE d _ 1%r)=> // g; exact(fo_error_range w g). qed.

lemma fo_error_expectation_range w (d:acwc2_g_function distr) :
 0%r<=E d (fo_error w)<=1%r.
proof. apply acwc2_expectation_unit_range=>g; exact(fo_error_range w g). qed.

lemma fo_eager_error_bound w :
 E acwc2_eager_g_law (fo_error w)<=acwc2_base_mean w+acwc2_epsilon+acwc2_union_tail.
proof. rewrite /fo_error; exact(acwc2_eager_weighted_max_bound w). qed.
