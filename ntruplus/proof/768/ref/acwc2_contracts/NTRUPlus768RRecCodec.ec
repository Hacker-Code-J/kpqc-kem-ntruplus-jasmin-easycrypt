require import AllCore IntDiv List.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array768 Array1152 Array1153.
require import NTRUPlus768RRecWordChecks NTRUPlus768PKEModel NTRUPlus768PKEAlgebra.
require import NTRUPlus768PolyCBD1Algebra.
require import NTRUPlus768BasemulAlgebra NTRUPlus768Crepmod3Algebra NTRUPlus768PolySubAlgebra.
require import NTRUPlus768KeygenPublicKeyBridge NTRUPlus768KeygenSecretFBridge.
require import NTRUPlus768TerminalRepresentation NTRUPlus768ForwardNTTStage1Semantics NTRUPlus768ForwardNTTSemantics.
require import NTRUPlus768NTTProof NTRUPlus768NTTAlgebra NTRUPlus768NTTStage1Algebra.
require import NTRUPlus768InverseNTTSemantics NTRUPlus768InvNTTAlgebra NTRUPlus768InvNTTRadix2_4Algebra.
require import NTRUPlus768NTTRoundtripSemantics NTRUPlus768ValidKeyM1Recovery NTRUPlus768CoefficientRecovery.
require import NTRUPlus768Crepmod3Recovery NTRUPlus768R2Serialization NTRUPlus768PolyToBytesAlgebra.

(* No message-recovery/no-wrap premise: this codec recovers a small
   randomness polynomial from any congruent, in-range transform. *)
lemma rrec_center_unique x y : -1728<=y<=1728 =>
 x %% q=y %% q => rrec_center x=y.
proof.
 move=>hy hm; apply centered_representative_unique.
 + exact(rrec_center_range x).
 + exact hy.
 by rewrite /q rrec_center_mod; exact hm.
qed.
lemma rrec_normalize_coeff a j : 0<=j<768 =>
 coeff(rrec_normalize a).[j]=rrec_center(coeff a.[j]).
proof.
 move=>hj; rewrite /rrec_normalize Array768.initiE //.
 apply coeff_of_word_small; have h:=rrec_center_range(coeff a.[j]); smt().
qed.
lemma rrec_normalize_recovers_small b r :
 pke_domain r => eqm_global (input_poly r) (input_poly b) => rrec_normalize b=r.
proof.
 move=>hr hg; apply Array768.tP=>j hj.
 have heq: eqm_global (int_poly(integer_coefficients r)) (int_poly(integer_coefficients b))
  by rewrite !integer_coefficients_poly; exact hg.
 have hcon:=eqm_global_int_poly_coeff (integer_coefficients r) (integer_coefficients b) j heq hj.
 rewrite (integer_coefficients_get r j hj) (integer_coefficients_get b j hj) in hcon.
 have ht:is_trit(coeff r.[j]) by move:hr; rewrite /pke_domain /poly_cbd1_trit_output=>hr; exact(hr j hj).
 have he : rrec_center(coeff b.[j])=coeff r.[j].
 + apply rrec_center_unique; first by move:ht; rewrite /is_trit; smt().
   smt().
 rewrite (word_from_coeff (rrec_normalize b).[j]) (word_from_coeff r.[j]).
 by rewrite rrec_normalize_coeff // he.
qed.

lemma rrec_normalized_inverse_recovers a r :
 qrange_input_shape a => pke_domain r =>
 poly_coeff_eq_mod_q a (pke_rhat r) =>
 rrec_normalize(inverse_invntt_spec a)=r.
proof.
 move=>ha hr he; apply rrec_normalize_recovers_small; first exact hr.
 have hrep:terminal_represents (pke_rhat r) (input_poly r).
 + rewrite /pke_rhat ntt_specE.
   exact(forward_ntt_spec_terminal_represents r (pke_domain_qrange r hr)).
 have ha_rep:=terminal_represents_mod_q_replacement (pke_rhat r) a (input_poly r) he hrep.
 exact(inverse_invntt_spec_semantics (input_poly r) a ha_rep ha).
qed.
lemma rrec_ntt_shape r : pke_domain r => qrange_input_shape(pke_rhat r).
proof.
 move=>hr; rewrite /pke_rhat ntt_specE.
 exact(forward_ntt_spec_invntt_input_shape r (pke_domain_qrange r hr)).
qed.
lemma rrec_transform_roundtrip r : pke_domain r =>
 rrec_normalize(inverse_invntt_spec(pke_rhat r))=r.
proof.
 move=>hr; apply(rrec_normalized_inverse_recovers (pke_rhat r) r (rrec_ntt_shape r hr) hr).
 by rewrite /poly_coeff_eq_mod_q.
qed.

op [opaque] rr_G_input (r:pke_poly) : W8.t Array1152.t =
 NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec(pke_rhat r).
lemma rr_G_inputE r : rr_G_input r=NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec(pke_rhat r).
proof. by rewrite /rr_G_input. qed.
lemma rr_G_input_serializer r : pke_domain r => poly_tobytes_input_qrange(pke_rhat r).
proof.
 move=>hr j hj; have h:=pke_rhat_range r hr j hj.
 move:h; rewrite /poly_tobytes_input_qrange /input_qrange /in_qrange /q; smt().
qed.
lemma rr_G_decode_mod r : pke_domain r =>
 poly_coeff_eq_mod_q (r2_serialized_decode(pke_rhat r)) (pke_rhat r).
proof. move=>hr; exact(r2_serialized_decode_mod_q _ (rr_G_input_serializer r hr)). qed.
lemma rr_G_input_injective r s : pke_domain r => pke_domain s => rr_G_input r=rr_G_input s => r=s.
proof.
 move=>hr hs he.
 have hd:r2_serialized_decode(pke_rhat r)=r2_serialized_decode(pke_rhat s).
 + by rewrite /r2_serialized_decode -!rr_G_inputE he.
 have hm:poly_coeff_eq_mod_q (pke_rhat r) (pke_rhat s).
 + have h1:=rr_G_decode_mod r hr; have h2:=rr_G_decode_mod s hs.
   rewrite -hd in h2; move=>j hj.
   by rewrite -(h1 j hj) (h2 j hj).
 have hrr:=rrec_transform_roundtrip r hr.
 have hrs:=rrec_normalized_inverse_recovers (pke_rhat r) s (rrec_ntt_shape r hr) hs hm.
 by rewrite -hrr hrs.
qed.
