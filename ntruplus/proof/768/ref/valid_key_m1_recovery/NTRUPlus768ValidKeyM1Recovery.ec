require import AllCore IntDiv List Ring StdOrder.
from Jasmin require import JWord.

require import Array96 Array192 Array768 Array1152.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768CyclotomicFactorization.
require import NTRUPlus768EvaluationSemantics.
require import NTRUPlus768TerminalRepresentation.
require import NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768ForwardNTTSemantics.
require import NTRUPlus768InverseNTTSemantics.
require import NTRUPlus768NTTAlgebra NTRUPlus768NTTStage1Algebra.
require import NTRUPlus768InvNTTAlgebra.
require import NTRUPlus768PolyBasemulAlgebra.
require import NTRUPlus768PolyBasemulInvNTTAlgebra.
require import NTRUPlus768EncapPolyBasemulAddAlgebra.
require import NTRUPlus768PolyCBD1Algebra.
require import NTRUPlus768KeygenSamplerAlgebra.
require import NTRUPlus768KeygenSamplerBridge.
require import NTRUPlus768KeygenSecretFBridge.
require import NTRUPlus768ValidKeyDecapM1Semantics.
require import NTRUPlus768Crepmod3Proof NTRUPlus768Crepmod3Algebra.
require import NTRUPlus768Crepmod3DecapBridge.
require import NTRUPlus768PolySOTPEncodeAlgebra.
require import NTRUPlus768PolySOTPDecodeAlgebra.
require import NTRUPlus768PolySOTPRoundTrip.
require import NTRUPlus768CoefficientRecovery.
require import NTRUPlus768IntegerConvolution.
require import NTRUPlus768Crepmod3Recovery.

import Ring.IntID IntOrder.

abbrev ( + ) = NTRUPoly.PolyComRing.( + ).
abbrev ( * ) = NTRUPoly.PolyComRing.( * ).

(* Conditional recovery at the array-value boundary. The no-wrap predicate
   is a bound on an explicit INTEGER convolution, before reduction modulo q.
   It is not asserted for all sampler inputs. No failure-probability bound,
   actual decapsulation-pad agreement, formal production-C equivalence, or
   full-KEM correctness is established by this theory. *)

op integer_coefficients (a : W16.t Array768.t) : int Array768.t =
  Array768.map coeff a.

op sampled_m1_noise
    (fbuf gbuf : W8.t Array192.t)
    (r m : W16.t Array768.t) : int Array768.t =
  integer_add
    (integer_product
      (integer_coefficients (poly_cbd1_spec gbuf)) (integer_coefficients r))
    (integer_product
      (integer_coefficients m) (integer_coefficients (poly_cbd1_spec fbuf))).

op sampled_m1_integer_lift
    (fbuf gbuf : W8.t Array192.t)
    (r m : W16.t Array768.t) : int Array768.t =
  integer_add (integer_coefficients m)
    (integer_scale 3 (sampled_m1_noise fbuf gbuf r m)).

op sampled_m1_no_wrap
    (fbuf gbuf : W8.t Array192.t)
    (r m : W16.t Array768.t) : bool =
  forall j, 0 <= j < 768 =>
    -1728 <= (sampled_m1_integer_lift fbuf gbuf r m).[j] <= 1728.

lemma integer_coefficients_get (a : W16.t Array768.t) (j : int) :
  0 <= j < 768 => (integer_coefficients a).[j] = coeff a.[j].
proof. by move=> Hj; rewrite /integer_coefficients Array768.mapiE 1:Hj. qed.

lemma integer_coefficients_poly (a : W16.t Array768.t) :
  int_poly (integer_coefficients a) = input_poly a.
proof. by rewrite /integer_coefficients int_poly_words. qed.

lemma keygen_f_integer_shape (buf : W8.t Array192.t) :
  integer_coefficients (keygen_f_pre_ntt_spec buf) =
  integer_add (integer_unit 0)
    (integer_scale 3 (integer_coefficients (poly_cbd1_spec buf))).
proof.
  apply Array768.tP => j Hj.
  rewrite integer_coefficients_get 1:Hj.
  rewrite integer_add_get 1:Hj integer_unit_get 1:Hj.
  rewrite integer_scale_get 1:Hj integer_coefficients_get 1:Hj.
  rewrite keygen_f_pre_ntt_coeff 1:Hj poly_cbd1_spec_coeff 1:Hj.
  by rewrite /keygen_delta0; smt().
qed.

lemma keygen_g_integer_shape (buf : W8.t Array192.t) :
  integer_coefficients (keygen_g_pre_ntt_spec buf) =
  integer_scale 3 (integer_coefficients (poly_cbd1_spec buf)).
proof.
  apply Array768.tP => j Hj.
  rewrite integer_coefficients_get 1:Hj integer_scale_get 1:Hj.
  rewrite integer_coefficients_get 1:Hj.
  by rewrite keygen_g_pre_ntt_coeff 1:Hj poly_cbd1_spec_coeff 1:Hj.
qed.

lemma keygen_f_input_poly_shape (buf : W8.t Array192.t) :
  input_poly (keygen_f_pre_ntt_spec buf) =
    poly1 + polyC (lift_int 3) * input_poly (poly_cbd1_spec buf).
proof.
  rewrite -integer_coefficients_poly keygen_f_integer_shape.
  rewrite int_poly_add int_poly_scale int_poly_unit 1:/#.
  by rewrite integer_coefficients_poly NTRUPoly.PolyComRing.expr0.
qed.

lemma keygen_g_input_poly_shape (buf : W8.t Array192.t) :
  input_poly (keygen_g_pre_ntt_spec buf) =
    polyC (lift_int 3) * input_poly (poly_cbd1_spec buf).
proof.
  rewrite -integer_coefficients_poly keygen_g_integer_shape.
  by rewrite int_poly_scale integer_coefficients_poly.
qed.

lemma sampled_m1_integer_lift_coeff
    (fbuf gbuf : W8.t Array192.t)
    (r m : W16.t Array768.t) (j : int) :
  0 <= j < 768 =>
  (sampled_m1_integer_lift fbuf gbuf r m).[j] =
    coeff m.[j] + 3 * (sampled_m1_noise fbuf gbuf r m).[j].
proof.
  move=> Hj.
  by rewrite /sampled_m1_integer_lift integer_add_get 1:Hj
    integer_scale_get 1:Hj integer_coefficients_get 1:Hj.
qed.

lemma sampled_m1_integer_lift_mod3
    (fbuf gbuf : W8.t Array192.t)
    (r m : W16.t Array768.t) (j : int) :
  0 <= j < 768 =>
  (sampled_m1_integer_lift fbuf gbuf r m).[j] %% 3 = coeff m.[j] %% 3.
proof.
  move=> Hj.
  rewrite sampled_m1_integer_lift_coeff 1:Hj.
  smt().
qed.

lemma sampled_m1_integer_lift_semantics
    (fbuf gbuf : W8.t Array192.t) (r m : W16.t Array768.t) :
  eqm_global
    (input_poly (keygen_g_pre_ntt_spec gbuf) * input_poly r +
     input_poly m * input_poly (keygen_f_pre_ntt_spec fbuf))
    (int_poly (sampled_m1_integer_lift fbuf gbuf r m)).
proof.
  have Hgr := integer_product_eqm_global
    (integer_coefficients (poly_cbd1_spec gbuf)) (integer_coefficients r).
  have Hmf := integer_product_eqm_global
    (integer_coefficients m) (integer_coefficients (poly_cbd1_spec fbuf)).
  rewrite !integer_coefficients_poly in Hgr.
  rewrite !integer_coefficients_poly in Hmf.
  have Hnoise := eqm_global_add _ _ _ _ Hgr Hmf.
  have Hscaled := eqm_global_mul _ _ _ _
    (eqm_global_refl (polyC (lift_int 3))) Hnoise.
  have Htotal := eqm_global_add _ _ _ _
    (eqm_global_refl (input_poly m)) Hscaled.
  rewrite /sampled_m1_integer_lift /sampled_m1_noise.
  rewrite !int_poly_add int_poly_scale int_poly_add integer_coefficients_poly.
  rewrite keygen_f_input_poly_shape keygen_g_input_poly_shape.
  have -> :
    (polyC (lift_int 3) * input_poly (poly_cbd1_spec gbuf)) * input_poly r +
    input_poly m * (poly1 + polyC (lift_int 3) * input_poly (poly_cbd1_spec fbuf)) =
    input_poly m + polyC (lift_int 3) *
      (input_poly (poly_cbd1_spec gbuf) * input_poly r +
       input_poly m * input_poly (poly_cbd1_spec fbuf)) by ring.
  exact Htotal.
qed.

lemma sampled_m1_centered_integer_witness
    (fbuf gbuf : W8.t Array192.t) (r m output : W16.t Array768.t) :
  invntt_semantics
    (input_poly (keygen_g_pre_ntt_spec gbuf) * input_poly r +
     input_poly m * input_poly (keygen_f_pre_ntt_spec fbuf)) output =>
  input_qrange output =>
  sampled_m1_no_wrap fbuf gbuf r m =>
  centered_integer_witness output (sampled_m1_integer_lift fbuf gbuf r m).
proof.
  move=> Hsem Hrange Hnowrap.
  have Hlift := sampled_m1_integer_lift_semantics fbuf gbuf r m.
  have Hcongr := eqm_global_trans _ _ _ (eqm_global_sym _ _ Hlift) Hsem.
  rewrite -integer_coefficients_poly in Hcongr.
  split; first exact Hrange.
  move=> j Hj.
  split; first exact (Hnowrap j Hj).
  have Hcoeff := eqm_global_int_poly_coeff
    (sampled_m1_integer_lift fbuf gbuf r m)
    (integer_coefficients output) j Hcongr Hj.
  by rewrite integer_coefficients_get 1:Hj in Hcoeff.
qed.

lemma sampled_m1_message_mod3_witness
    (fbuf gbuf : W8.t Array192.t) (r m : W16.t Array768.t) :
  poly_cbd1_trit_output m =>
  message_mod3_witness (sampled_m1_integer_lift fbuf gbuf r m) m.
proof.
  move=> Hm j Hj.
  split; first exact (Hm j Hj).
  exact (sampled_m1_integer_lift_mod3 fbuf gbuf r m j Hj).
qed.

lemma sampled_m1_no_wrap_spec_recovery
    (fbuf gbuf : W8.t Array192.t) (r m output : W16.t Array768.t) :
  invntt_semantics
    (input_poly (keygen_g_pre_ntt_spec gbuf) * input_poly r +
     input_poly m * input_poly (keygen_f_pre_ntt_spec fbuf)) output =>
  input_qrange output =>
  poly_cbd1_trit_output m =>
  sampled_m1_no_wrap fbuf gbuf r m =>
  poly_crepmod3_spec output = m.
proof.
  move=> Hsem Hrange Hm Hnowrap.
  exact (poly_crepmod3_exact_recovery output m
    (sampled_m1_integer_lift fbuf gbuf r m)
    (sampled_m1_centered_integer_witness fbuf gbuf r m output Hsem Hrange Hnowrap)
    (sampled_m1_message_mod3_witness fbuf gbuf r m Hm)).
qed.

lemma trit_polynomial_input_qrange (m : W16.t Array768.t) :
  poly_cbd1_trit_output m => input_qrange m.
proof.
  move=> Hm j Hj.
  have Htrit := Hm j Hj.
  rewrite /in_qrange /q.
  by move: Htrit; rewrite /is_trit; smt().
qed.

lemma keygen_secret_f_no_wrap_m1_recovery
    (fbuf gbuf : W8.t Array192.t)
    (finv ginv h hinv decoded_h decoded_f r m c product_ntt : W16.t Array768.t)
    (pk sk_f : W8.t Array1152.t) :
  keygen_secret_f_serialization_relation
    (keygen_f_ntt_spec fbuf) finv (keygen_g_ntt_spec gbuf) ginv
    h hinv decoded_h decoded_f pk sk_f
    (input_poly (keygen_f_pre_ntt_spec fbuf)) =>
  input_qrange r =>
  poly_cbd1_trit_output m =>
  poly_basemul_add_qring decoded_h (forward_ntt_spec r) (forward_ntt_spec m) c 192 =>
  poly_basemul_qring c decoded_f product_ntt 192 =>
  sampled_m1_no_wrap fbuf gbuf r m =>
  inverse_invntt_crepmod3_spec product_ntt = m.
proof.
  move=> Hkey Hr Hm Hcipher Hproduct Hnowrap.
  have Hg_rep := forward_ntt_spec_terminal_represents
    (keygen_g_pre_ntt_spec gbuf) (keygen_g_pre_ntt_input_qrange gbuf).
  have Hr_rep := forward_ntt_spec_terminal_represents r Hr.
  have Hm_rep := forward_ntt_spec_terminal_represents m
    (trit_polynomial_input_qrange m Hm).
  have Hsem := keygen_secret_f_valid_key_m1_spec_semantics
    (keygen_f_ntt_spec fbuf) finv (keygen_g_ntt_spec gbuf) ginv
    h hinv decoded_h decoded_f (forward_ntt_spec r) (forward_ntt_spec m)
    c product_ntt pk sk_f
    (input_poly (keygen_f_pre_ntt_spec fbuf))
    (input_poly (keygen_g_pre_ntt_spec gbuf)) (input_poly r) (input_poly m)
    Hkey Hg_rep Hr_rep Hm_rep Hcipher Hproduct.
  have Hready := poly_basemul_qring_implies_invntt_ready c decoded_f product_ntt Hproduct.
  move: Hready => [_ Hshape].
  have Hrange := inverse_invntt_spec_ntt_input_qrange product_ntt Hshape.
  rewrite /inverse_invntt_crepmod3_spec.
  exact (sampled_m1_no_wrap_spec_recovery fbuf gbuf r m
    (inverse_invntt_spec product_ntt) Hsem Hrange Hm Hnowrap).
qed.

(* The same pad is explicit: r2 recovery and the actual hash_g pad agreement
   are subsequent obligations, not premises silently discharged here. *)
lemma recovered_m1_sotp_same_pad
    (msg : W8.t Array96.t) (pad : W8.t Array192.t)
    (m1 : W16.t Array768.t) :
  m1 = poly_sotp_encode_spec msg pad =>
  poly_sotp_decode_spec m1 pad = (msg, false).
proof.
  move=> ->.
  exact (poly_sotp_encode_decode_roundtrip msg pad).
qed.

lemma keygen_secret_f_no_wrap_sotp_recovery
    (fbuf gbuf : W8.t Array192.t)
    (finv ginv h hinv decoded_h decoded_f r c product_ntt : W16.t Array768.t)
    (pk sk_f : W8.t Array1152.t)
    (msg : W8.t Array96.t) (pad : W8.t Array192.t) :
  keygen_secret_f_serialization_relation
    (keygen_f_ntt_spec fbuf) finv (keygen_g_ntt_spec gbuf) ginv
    h hinv decoded_h decoded_f pk sk_f
    (input_poly (keygen_f_pre_ntt_spec fbuf)) =>
  input_qrange r =>
  poly_basemul_add_qring decoded_h (forward_ntt_spec r)
    (forward_ntt_spec (poly_sotp_encode_spec msg pad)) c 192 =>
  poly_basemul_qring c decoded_f product_ntt 192 =>
  sampled_m1_no_wrap fbuf gbuf r (poly_sotp_encode_spec msg pad) =>
  inverse_invntt_crepmod3_spec product_ntt = poly_sotp_encode_spec msg pad /\
  poly_sotp_decode_spec (inverse_invntt_crepmod3_spec product_ntt) pad = (msg, false).
proof.
  move=> Hkey Hr Hcipher Hproduct Hnowrap.
  have Htrit : poly_cbd1_trit_output (poly_sotp_encode_spec msg pad).
  + exact (poly_cbd1_spec_trit_output (poly_sotp_encode_input msg pad)).
  have Hrecovery := keygen_secret_f_no_wrap_m1_recovery
    fbuf gbuf finv ginv h hinv decoded_h decoded_f r
    (poly_sotp_encode_spec msg pad) c product_ntt pk sk_f
    Hkey Hr Htrit Hcipher Hproduct Hnowrap.
  split; first exact Hrecovery.
  exact (recovered_m1_sotp_same_pad msg pad
    (inverse_invntt_crepmod3_spec product_ntt) Hrecovery).
qed.
