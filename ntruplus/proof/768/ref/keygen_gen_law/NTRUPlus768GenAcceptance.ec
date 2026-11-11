require import AllCore Distr Ring.
from Jasmin require import JWord.
require import Array192 Array768.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteInverse.
require import NTRUPlus768KeygenSamplerAlgebra NTRUPlus768KeygenSamplerBridge.
require import NTRUPlus768KeygenInverseBridge NTRUPlus768KeygenSecretFBridge.
require import NTRUPlus768PKEKeyDistribution NTRUPlus768PolyCBD1Algebra.
require import NTRUPlus768CyclotomicFactorization NTRUPlus768EvaluationSemantics.
require import NTRUPlus768TerminalRepresentation NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768ForwardNTTSemantics.
require import NTRUPlus768KeygenTerminalUnit NTRUPlus768KeygenGlobalUnit.

abbrev ( + ) = NTRUPoly.PolyComRing.( + ).
abbrev ( * ) = NTRUPoly.PolyComRing.( * ).

lemma gen_f_ntt_represents buf :
 terminal_represents (keygen_f_ntt_spec buf)
  (input_poly(keygen_f_pre_ntt_spec buf)).
proof. exact(keygen_sampled_secret_f_terminal_represents buf). qed.

lemma gen_g_ntt_represents buf :
 terminal_represents (keygen_g_ntt_spec buf)
  (input_poly(keygen_g_pre_ntt_spec buf)).
proof.
 rewrite /keygen_g_ntt_spec.
 exact(forward_ntt_spec_terminal_represents _ (keygen_g_pre_ntt_input_qrange buf)).
qed.

(* These equalities cover every typed byte buffer. CBD1 supplies the trit
   range needed for word shaping; no overflow premise is left to a caller. *)
lemma gen_f_accept_shaped_unit buf :
 keygen_f_accept buf=pke_rq_unit(input_poly(keygen_f_pre_ntt_spec buf)).
proof.
 have hi:=gen_inverse_status_iff (keygen_f_ntt_spec buf) (keygen_f_ntt_qrange buf).
 have hu:=gen_terminal_unit_iff_rq (keygen_f_ntt_spec buf)
  (input_poly(keygen_f_pre_ntt_spec buf)) (keygen_f_ntt_qrange buf)
  (gen_f_ntt_represents buf).
 have hs:=keygen_f_attempt_accept buf.
 rewrite /keygen_f_attempt_result /= in hs.
 apply eq_iff_imp; split.
 + move=>ha; exact(iffLR _ _ hu (iffLR _ _ hi (iffRL _ _ hs ha))).
 move=>hu0; exact(iffLR _ _ hs (iffRL _ _ hi (iffRL _ _ hu hu0))).
qed.

lemma gen_g_accept_shaped_unit buf :
 keygen_g_accept buf=pke_rq_unit(input_poly(keygen_g_pre_ntt_spec buf)).
proof.
 have hi:=gen_inverse_status_iff (keygen_g_ntt_spec buf) (keygen_g_ntt_qrange buf).
 have hu:=gen_terminal_unit_iff_rq (keygen_g_ntt_spec buf)
  (input_poly(keygen_g_pre_ntt_spec buf)) (keygen_g_ntt_qrange buf)
  (gen_g_ntt_represents buf).
 have hs:=keygen_g_attempt_accept buf.
 rewrite /keygen_g_attempt_result /= in hs.
 apply eq_iff_imp; split.
 + move=>ha; exact(iffLR _ _ hu (iffLR _ _ hi (iffRL _ _ hs ha))).
 move=>hu0; exact(iffLR _ _ hs (iffRL _ _ hi (iffRL _ _ hu hu0))).
qed.

lemma gen_f_accept_unit buf :
 keygen_f_accept buf=
 pke_rq_unit(NTRUPoly.poly1+NTRUPoly.polyC(lift_int 3)*pke_cbd_field buf).
proof. by rewrite gen_f_accept_shaped_unit pke_f_field_shape. qed.

lemma gen_g_accept_unit buf :
 keygen_g_accept buf=pke_rq_unit(pke_cbd_field buf).
proof.
 rewrite gen_g_accept_shaped_unit.
 have h:=pke_g_unscaled_unit buf; exact(eq_iff_imp _ _ h).
qed.

lemma gen_f_attempt_unit buf :
 (keygen_f_attempt_result buf).`4=W64.zero <=>
 pke_rq_unit(NTRUPoly.poly1+NTRUPoly.polyC(lift_int 3)*pke_cbd_field buf).
proof. by rewrite keygen_f_attempt_accept gen_f_accept_unit. qed.

lemma gen_g_attempt_unit buf :
 (keygen_g_attempt_result buf).`4=W64.zero <=>pke_rq_unit(pke_cbd_field buf).
proof. by rewrite keygen_g_attempt_accept gen_g_accept_unit. qed.
