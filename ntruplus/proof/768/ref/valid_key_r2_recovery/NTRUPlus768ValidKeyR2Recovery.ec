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
require import NTRUPlus768ValidKeyR2Algebra.

import Ring.IntID IntOrder.

(* The pad is computed from the recovered r2 bytes, not supplied as an
   equality premise. All conclusions concern array values under successful
   key/arithmetic contracts and explicit no-wrap. This is not a formal C
   memory theorem, full-KEM/shared-secret theorem, or failure-probability
   estimate. sk_hinv names the separate 1152-byte secret-key block. *)

op serialized_hash_g_pad (r_ntt : W16.t Array768.t) : W8.t Array192.t =
  hash_g_spec (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec r_ntt).

op r2_encap_message
    (r : W16.t Array768.t) (msg : W8.t Array96.t) : W16.t Array768.t =
  poly_sotp_encode_spec msg (serialized_hash_g_pad (forward_ntt_spec r)).

op r2_pad_message_recovery
    (r : W16.t Array768.t) (msg : W8.t Array96.t)
    (product_ntt r2 : W16.t Array768.t) : bool =
  inverse_invntt_crepmod3_spec product_ntt = r2_encap_message r msg /\
  poly_coeff_eq_mod_q r2 (forward_ntt_spec r) /\
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec r2 =
    NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec (forward_ntt_spec r) /\
  serialized_hash_g_pad r2 = serialized_hash_g_pad (forward_ntt_spec r) /\
  poly_sotp_decode_spec (inverse_invntt_crepmod3_spec product_ntt)
    (serialized_hash_g_pad r2) = (msg, false).

lemma forward_ntt_tobytes_input_qrange (r : W16.t Array768.t) :
  NTRUPlus768NTTStage1Algebra.input_qrange r =>
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange (forward_ntt_spec r).
proof.
  move=> Hr j Hj.
  exact (forward_ntt_centered_coeff_range r j Hr Hj).
qed.

lemma basemul_output_tobytes_input_qrange (a b r2 : W16.t Array768.t) :
  poly_basemul_qring a b r2 192 =>
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange r2.
proof.
  move=> Hproduct.
  exact (NTRUPlus768KeygenPublicKeyBridge.in_qrange768_poly_tobytes_input_qrange r2
    (NTRUPlus768KeygenPublicKeyBridge.poly_basemul_qring_output_in_qrange768
      a b r2 Hproduct)).
qed.

lemma r2_congruent_bytes_and_pad (r2 r_ntt : W16.t Array768.t) :
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange r2 =>
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange r_ntt =>
  poly_coeff_eq_mod_q r2 r_ntt =>
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec r2 =
    NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec r_ntt /\
  serialized_hash_g_pad r2 = serialized_hash_g_pad r_ntt.
proof.
  move=> H2 Hr Hcongr.
  have Hbytes := poly_tobytes_mod_q_congr r2 r_ntt H2 Hr Hcongr.
  split; first exact Hbytes.
  by rewrite /serialized_hash_g_pad Hbytes.
qed.

lemma secret_f_relation_keypair_and_public_congruence
    (f finv g ginv h hinv decoded_h decoded_f : W16.t Array768.t)
    (pk sk_f : W8.t Array1152.t) (F : poly) :
  keygen_secret_f_serialization_relation
    f finv g ginv h hinv decoded_h decoded_f pk sk_f F =>
  keygen_keypair_ntt_relation f finv g ginv h hinv /\
  poly_coeff_eq_mod_q decoded_h h.
proof.
  rewrite /keygen_secret_f_serialization_relation
    /keygen_public_key_serialization_relation.
  smt().
qed.

lemma r2_encap_message_trit
    (r : W16.t Array768.t) (msg : W8.t Array96.t) :
  poly_cbd1_trit_output (r2_encap_message r msg).
proof.
  exact (poly_cbd1_spec_trit_output
    (poly_sotp_encode_input msg (serialized_hash_g_pad (forward_ntt_spec r)))).
qed.

lemma serialized_cipher_no_wrap_m1_recovery
    (fbuf gbuf : W8.t Array192.t)
    (finv ginv h hinv decoded_h decoded_f decoded_c decoded_hinv r c_enc product_ntt :
      W16.t Array768.t)
    (pk sk_f ct sk_hinv : W8.t Array1152.t) (msg : W8.t Array96.t) :
  keygen_secret_f_serialization_relation
    (keygen_f_ntt_spec fbuf) finv (keygen_g_ntt_spec gbuf) ginv
    h hinv decoded_h decoded_f pk sk_f
    (input_poly (keygen_f_pre_ntt_spec fbuf)) =>
  r2_serialization_relation c_enc hinv decoded_c decoded_hinv ct sk_hinv =>
  NTRUPlus768NTTStage1Algebra.input_qrange r =>
  poly_basemul_add_qring decoded_h (forward_ntt_spec r)
    (forward_ntt_spec (r2_encap_message r msg)) c_enc 192 =>
  poly_basemul_qring decoded_c decoded_f product_ntt 192 =>
  sampled_m1_no_wrap fbuf gbuf r (r2_encap_message r msg) =>
  inverse_invntt_crepmod3_spec product_ntt = r2_encap_message r msg.
proof.
  move=> Hkey Hser Hr Henc Hproduct Hnowrap.
  have Hc_range := encap_cipher_tobytes_input_qrange
    decoded_h (forward_ntt_spec r) (forward_ntt_spec (r2_encap_message r msg)) c_enc Henc.
  have [Hc_decode _] := r2_serialization_relation_decode
    c_enc hinv decoded_c decoded_hinv ct sk_hinv Hser.
  have Hfirst : poly_basemul_qring c_enc decoded_f product_ntt 192.
  + apply (decoded_cipher_product_transfer c_enc decoded_f product_ntt Hc_range).
    by rewrite -Hc_decode.
  exact (keygen_secret_f_no_wrap_m1_recovery fbuf gbuf
    finv ginv h hinv decoded_h decoded_f r (r2_encap_message r msg) c_enc product_ntt
    pk sk_f Hkey Hr (r2_encap_message_trit r msg) Henc Hfirst Hnowrap).
qed.

lemma serialized_r2_pad_agreement
    (f finv g ginv h hinv decoded_h decoded_hinv r_ntt m_ntt c_enc decoded_c sub r2 :
      W16.t Array768.t) (ct sk_hinv : W8.t Array1152.t) :
  keygen_keypair_ntt_relation f finv g ginv h hinv =>
  poly_coeff_eq_mod_q decoded_h h =>
  r2_serialization_relation c_enc hinv decoded_c decoded_hinv ct sk_hinv =>
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange r_ntt =>
  poly_basemul_add_qring decoded_h r_ntt m_ntt c_enc 192 =>
  poly_sub_algebra decoded_c m_ntt sub =>
  poly_basemul_qring sub decoded_hinv r2 192 =>
  poly_coeff_eq_mod_q r2 r_ntt /\
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec r2 =
    NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec r_ntt /\
  serialized_hash_g_pad r2 = serialized_hash_g_pad r_ntt.
proof.
  move=> Hkey Hh_mod Hser Hr Henc Hsub Hproduct.
  have Hc_range := encap_cipher_tobytes_input_qrange decoded_h r_ntt m_ntt c_enc Henc.
  have Hhinv_range := keygen_hinv_tobytes_input_qrange f finv g ginv h hinv Hkey.
  have [Hc_mod Hhinv_mod] := r2_serialization_relation_mod_q
    c_enc hinv decoded_c decoded_hinv ct sk_hinv Hc_range Hhinv_range Hser.
  have Hcongr := valid_key_r2_mod_q f finv g ginv h hinv
    decoded_h decoded_hinv r_ntt m_ntt c_enc decoded_c sub r2
    Hkey Hh_mod Hhinv_mod Henc Hc_mod Hsub Hproduct.
  split; first exact Hcongr.
  exact (r2_congruent_bytes_and_pad r2 r_ntt
    (basemul_output_tobytes_input_qrange sub decoded_hinv r2 Hproduct) Hr Hcongr).
qed.

lemma no_wrap_serialized_message_recovery
    (fbuf gbuf : W8.t Array192.t)
    (finv ginv h hinv decoded_h decoded_f decoded_c decoded_hinv r c_enc product_ntt r2 :
      W16.t Array768.t)
    (pk sk_f ct sk_hinv : W8.t Array1152.t) (msg : W8.t Array96.t) :
  keygen_secret_f_serialization_relation
    (keygen_f_ntt_spec fbuf) finv (keygen_g_ntt_spec gbuf) ginv
    h hinv decoded_h decoded_f pk sk_f
    (input_poly (keygen_f_pre_ntt_spec fbuf)) =>
  r2_serialization_relation c_enc hinv decoded_c decoded_hinv ct sk_hinv =>
  NTRUPlus768NTTStage1Algebra.input_qrange r =>
  poly_basemul_add_qring decoded_h (forward_ntt_spec r)
    (forward_ntt_spec (r2_encap_message r msg)) c_enc 192 =>
  poly_basemul_qring decoded_c decoded_f product_ntt 192 =>
  poly_basemul_qring (decap_sub_spec decoded_c product_ntt) decoded_hinv r2 192 =>
  sampled_m1_no_wrap fbuf gbuf r (r2_encap_message r msg) =>
  r2_pad_message_recovery r msg product_ntt r2.
proof.
  move=> Hkey Hser Hr Henc Hfirst Hsecond Hnowrap.
  have Hm1 := serialized_cipher_no_wrap_m1_recovery
    fbuf gbuf finv ginv h hinv decoded_h decoded_f decoded_c decoded_hinv
    r c_enc product_ntt pk sk_f ct sk_hinv msg
    Hkey Hser Hr Henc Hfirst Hnowrap.
  have Hkey_context := secret_f_relation_keypair_and_public_congruence
    (keygen_f_ntt_spec fbuf) finv (keygen_g_ntt_spec gbuf) ginv
    h hinv decoded_h decoded_f pk sk_f (input_poly (keygen_f_pre_ntt_spec fbuf)) Hkey.
  have Hkeypair : keygen_keypair_ntt_relation
      (keygen_f_ntt_spec fbuf) finv (keygen_g_ntt_spec gbuf) ginv h hinv by smt().
  have Hh_mod : poly_coeff_eq_mod_q decoded_h h by smt().
  have [Hdecoded_c _] := r2_serialization_relation_decode
    c_enc hinv decoded_c decoded_hinv ct sk_hinv Hser.
  have Hdecoder : decoder_range decoded_c.
  + rewrite Hdecoded_c /r2_serialized_decode.
    exact (poly_frombytes_spec_decoder_range
      (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c_enc)).
  have Hmessage_range := trit_polynomial_input_qrange (r2_encap_message r msg)
    (r2_encap_message_trit r msg).
  have Hm_ntt_range :
      NTRUPlus768NTTStage1Algebra.input_qrange (forward_ntt_spec (r2_encap_message r msg)).
  + move=> j Hj.
    exact (forward_ntt_centered_coeff_range (r2_encap_message r msg) j Hmessage_range Hj).
  have Hsub : poly_sub_algebra decoded_c (forward_ntt_spec (r2_encap_message r msg))
      (decap_sub_spec decoded_c product_ntt).
  + rewrite /decap_sub_spec Hm1.
    exact (poly_sub_spec_algebra decoded_c
      (forward_ntt_spec (r2_encap_message r msg)) Hdecoder Hm_ntt_range).
  have [Hr2 [Hbytes Hpad]] := serialized_r2_pad_agreement
    (keygen_f_ntt_spec fbuf) finv (keygen_g_ntt_spec gbuf) ginv
    h hinv decoded_h decoded_hinv (forward_ntt_spec r)
    (forward_ntt_spec (r2_encap_message r msg)) c_enc decoded_c
    (decap_sub_spec decoded_c product_ntt) r2 ct sk_hinv
    Hkeypair Hh_mod Hser (forward_ntt_tobytes_input_qrange r Hr) Henc Hsub Hsecond.
  rewrite /r2_pad_message_recovery.
  split; first exact Hm1.
  split; first exact Hr2.
  split; first exact Hbytes.
  split; first exact Hpad.
  rewrite Hm1 Hpad /r2_encap_message.
  exact (poly_sotp_encode_decode_roundtrip msg
    (serialized_hash_g_pad (forward_ntt_spec r))).
qed.
