require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord.

require import Array96 Array192 Array768 Array1152.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768EvaluationSemantics.
require import NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768NTTAlgebra NTRUPlus768NTTStage1Algebra.
require import NTRUPlus768PolyBasemulAlgebra.
require import NTRUPlus768PolyToBytesAlgebra.
require import NTRUPlus768PolyFromBytesAlgebra.
require import NTRUPlus768PolySubProof NTRUPlus768PolySubAlgebra.
require import NTRUPlus768PolySubDecapBridge.
require import NTRUPlus768PolyCBD1Algebra.
require import NTRUPlus768PolySOTPEncodeAlgebra.
require import NTRUPlus768PolySOTPDecodeAlgebra.
require import NTRUPlus768PolySOTPRoundTrip.
require import NTRUPlus768KeygenSamplerAlgebra.
require import NTRUPlus768KeygenSamplerBridge.
require import NTRUPlus768KeygenHBridge.
require import NTRUPlus768KeygenPublicKeyBridge.
require import NTRUPlus768KeygenSecretFBridge.
require import NTRUPlus768EncapPolyBasemulAddAlgebra.
require import NTRUPlus768Crepmod3DecapBridge.
require import NTRUPlus768DecapR2Bridge.
require import NTRUPlus768DecapHashGBridge.
require import NTRUPlus768ValidKeyM1Recovery.
require import NTRUPlus768R2Serialization.
require import NTRUPlus768ValidKeyR2Algebra NTRUPlus768ValidKeyR2Recovery.

require import NTRUPlus768KEMPayloadSpec NTRUPlus768KEMAgreementContext.
require import NTRUPlus768CanonicalDecoder NTRUPlus768DecapCompleteSpec NTRUPlus768DecapCandidateSpec NTRUPlus768DecapCandidateAlgebra.
require import NTRUPlus768DecapR2CompAlgebra NTRUPlus768DecapR2CompSpec NTRUPlus768DecapMessageAlgebra NTRUPlus768DecapGuardSpec.

(* Arbitrary SOTP pad and arbitrary realized HashH output. No fixed SHAKE
   function occurs in the relation or in the integer no-wrap event. *)
lemma payload_serialized_recovery
    (fbuf gbuf : W8.t Array192.t)
    (finv ginv h hinv decoded_h decoded_f decoded_c decoded_hinv r m c product_ntt r2 : W16.t Array768.t)
    (pk sk_f ct sk_hinv : W8.t Array1152.t) :
  keygen_secret_f_serialization_relation
    (keygen_f_ntt_spec fbuf) finv (keygen_g_ntt_spec gbuf) ginv h hinv
    decoded_h decoded_f pk sk_f (input_poly (keygen_f_pre_ntt_spec fbuf)) =>
  r2_serialization_relation c hinv decoded_c decoded_hinv ct sk_hinv =>
  input_qrange r => poly_cbd1_trit_output m =>
  poly_basemul_add_qring decoded_h (forward_ntt_spec r) (forward_ntt_spec m) c 192 =>
  poly_basemul_qring decoded_c decoded_f product_ntt 192 =>
  poly_basemul_qring (decap_sub_spec decoded_c product_ntt) decoded_hinv r2 192 =>
  sampled_m1_no_wrap fbuf gbuf r m =>
  inverse_invntt_crepmod3_spec product_ntt=m /\
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec r2 =
    NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec (forward_ntt_spec r).
proof.
  move=> Hkey Hser Hr Hm Henc Hfirst Hsecond Hnowrap.
  have Hcr := encap_cipher_tobytes_input_qrange _ _ _ _ Henc.
  have [Hcd _] := r2_serialization_relation_decode c hinv decoded_c decoded_hinv ct sk_hinv Hser.
  have Hp : poly_basemul_qring c decoded_f product_ntt 192.
  + apply (decoded_cipher_product_transfer c decoded_f product_ntt Hcr).
    by rewrite -Hcd.
  have Hm1 : inverse_invntt_crepmod3_spec product_ntt=m.
  + apply(keygen_secret_f_no_wrap_m1_recovery fbuf gbuf finv ginv h hinv
      decoded_h decoded_f r m c product_ntt pk sk_f).
    - exact Hkey.
    - exact Hr.
    - exact Hm.
    - exact Henc.
    - exact Hp.
    exact Hnowrap.
  have [Hkp Hh] := secret_f_relation_keypair_and_public_congruence
    (keygen_f_ntt_spec fbuf) finv (keygen_g_ntt_spec gbuf) ginv h hinv
    decoded_h decoded_f pk sk_f (input_poly (keygen_f_pre_ntt_spec fbuf)) Hkey.
  have Hhir := keygen_hinv_tobytes_input_qrange _ _ _ _ _ _ Hkp.
  have [Hcmod Hhimod] := r2_serialization_relation_mod_q
    c hinv decoded_c decoded_hinv ct sk_hinv Hcr Hhir Hser.
  have Hdec : decoder_range decoded_c.
  + rewrite Hcd /r2_serialized_decode.
    exact (poly_frombytes_spec_decoder_range (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c)).
  have Hmr := trit_polynomial_input_qrange m Hm.
  have Hmnr : input_qrange (forward_ntt_spec m).
  + move=> j Hj; exact (forward_ntt_centered_coeff_range m j Hmr Hj).
  have Hsub : poly_sub_algebra decoded_c (forward_ntt_spec m) (decap_sub_spec decoded_c product_ntt).
  + rewrite /decap_sub_spec Hm1.
    exact (poly_sub_spec_algebra decoded_c (forward_ntt_spec m) Hdec Hmnr).
  have Hmod := valid_key_r2_mod_q (keygen_f_ntt_spec fbuf) finv (keygen_g_ntt_spec gbuf) ginv
    h hinv decoded_h decoded_hinv (forward_ntt_spec r) (forward_ntt_spec m)
    c decoded_c (decap_sub_spec decoded_c product_ntt) r2
    Hkp Hh Hhimod Henc Hcmod Hsub Hsecond.
  split; first exact Hm1.
  exact (poly_tobytes_mod_q_congr r2 (forward_ntt_spec r)
    (basemul_output_tobytes_input_qrange _ _ _ Hsecond)
    (forward_ntt_tobytes_input_qrange r Hr) Hmod).
qed.

lemma payload_actual_prefix_recovery fbuf gbuf finv ginv h hinv pk sk r m c :
  payload_key_relation fbuf gbuf finv ginv h hinv pk sk =>
  input_qrange r => poly_cbd1_trit_output m =>
  poly_basemul_add_qring (decoded_poly pk) (forward_ntt_spec r) (forward_ntt_spec m) c 192 =>
  sampled_m1_no_wrap fbuf gbuf r m =>
  let ct=NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c in
  complete_entry_accepts ct sk /\
  message_candidate ct (complete_sk_poly sk)=m /\
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec (message_r2 ct (complete_sk_poly sk)) =
    NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec (forward_ntt_spec r).
proof.
  move=> Hkey Hr Hm Henc Hnowrap; simplify.
  have Hcr := encap_cipher_tobytes_input_qrange _ _ _ _ Henc.
  have Ha := payload_entry_accepts fbuf gbuf finv ginv h hinv pk sk c Hkey Hcr.
  have Hsecret := payload_secret_relation fbuf gbuf finv ginv h hinv pk sk Hkey.
  have Hser : r2_serialization_relation c hinv
    (decoded_poly (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c))
    (decoded_poly (decap_hbytes (complete_sk_poly sk)))
    (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c) (decap_hbytes (complete_sk_poly sk)).
  + rewrite /r2_serialization_relation.
    split; first done.
    split; first exact (payload_hinv_encoding fbuf gbuf finv ginv h hinv pk sk Hkey).
    by split.
  have Hca := candidate_decoded_spec_algebra (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c) (decap_fbytes (complete_sk_poly sk)).
  have Hfirst : poly_basemul_qring
    (decoded_poly (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c))
    (decoded_poly (decap_fbytes (complete_sk_poly sk)))
    (candidate_product_spec (decoded_poly (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c))
      (decoded_poly (decap_fbytes (complete_sk_poly sk)))) 192.
  + move: Hca; rewrite /decap_candidate_algebra; move=> [H _]; exact H.
  have [Hd [Hm0 Hhi]] := r2_guard_candidate_inputs (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c) (complete_sk_poly sk) Ha.
  have H2 := r2_spec_algebra (decoded_poly (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c))
    (message_candidate (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c) (complete_sk_poly sk))
    (decoded_poly (decap_hbytes (complete_sk_poly sk))) Hd Hm0 Hhi.
  have Hsecond : poly_basemul_qring
    (decap_sub_spec (decoded_poly (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c))
      (candidate_product_spec (decoded_poly (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c))
        (decoded_poly (decap_fbytes (complete_sk_poly sk)))))
    (decoded_poly (decap_hbytes (complete_sk_poly sk)))
    (message_r2 (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c) (complete_sk_poly sk)) 192.
  + rewrite -agreement_difference_value.
    move: H2; rewrite /decap_r2_algebra /message_r2; move=> [_ [_ [_ [H _]]]]; exact H.
  have [Hmsg Hbytes] := payload_serialized_recovery fbuf gbuf finv ginv h hinv
    (decoded_poly pk) (decoded_poly (decap_fbytes (complete_sk_poly sk)))
    (decoded_poly (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c))
    (decoded_poly (decap_hbytes (complete_sk_poly sk))) r m c
    (candidate_product_spec (decoded_poly (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c))
      (decoded_poly (decap_fbytes (complete_sk_poly sk))))
    (message_r2 (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c) (complete_sk_poly sk))
    pk (decap_fbytes (complete_sk_poly sk)) (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c)
    (decap_hbytes (complete_sk_poly sk)) Hsecret Hser Hr Hm Henc Hfirst Hsecond Hnowrap.
  split; first exact Ha.
  split; last exact Hbytes.
  by rewrite agreement_candidate_value.
qed.
