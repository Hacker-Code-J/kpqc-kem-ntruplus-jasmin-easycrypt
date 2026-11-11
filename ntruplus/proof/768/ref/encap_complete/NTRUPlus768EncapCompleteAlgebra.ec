require import AllCore IntDiv.
from Jasmin require import JWord JModel_x86.
require import Array4 Array768 Array1152 Array96.
require import NTRUPlus768EncapCompleteSpec NTRUPlus768EncapGuardSpec NTRUPlus768CanonicalDecoder.
require import NTRUPlus768DecapCompleteSpec NTRUPlus768PolyCBD1Algebra NTRUPlus768PolySOTPEncodeAlgebra.
require import NTRUPlus768NTTProof NTRUPlus768NTTAlgebra NTRUPlus768NTTStage1Algebra NTRUPlus768NTTRadix2_4Algebra.
require import NTRUPlus768PolyBasemulAlgebra NTRUPlus768BasemulAlgebra NTRUPlus768DecapCandidateSpec NTRUPlus768DecapCandidateAlgebra.
require import NTRUPlus768EncapPolyBasemulAddAlgebra NTRUPlus768DecapR2Bridge NTRUPlus768PolyToBytesProof.

lemma encap_pointwise_blocks p : input_qrange p => in_qrange768 p.
proof.
  move=> hp k hk; rewrite /in_qrange4 /block4 !Array4.initiE //=.
  have h0 := hp (4*k) _; first smt().
  have h1 := hp (4*k+1) _; first smt().
  have h2 := hp (4*k+2) _; first smt().
  have h3 := hp (4*k+3) _; first smt().
  smt().
qed.
lemma encap_full_r_input_qrange pk coins : input_qrange (encap_full_r pk coins).
proof. exact (poly_cbd1_spec_input_qrange _). qed.
lemma encap_full_rhat_qrange pk coins : input_qrange (encap_full_rhat pk coins).
proof.
  move=> j hj; rewrite /encap_full_rhat ntt_specE.
  exact (forward_ntt_centered_coeff_range _ j (encap_full_r_input_qrange pk coins) hj).
qed.
lemma encap_full_rhat_serializer pk coins : poly_tobytes_input_qrange (encap_full_rhat pk coins).
proof. exact (encap_full_rhat_qrange pk coins). qed.
lemma encap_full_m_input_qrange pk coins : input_qrange (encap_full_m pk coins).
proof. rewrite /encap_full_m /poly_sotp_encode_spec; apply poly_cbd1_spec_input_qrange. qed.
lemma encap_full_mhat_centered pk coins : centered_input_shape (encap_full_mhat pk coins).
proof.
  rewrite /encap_full_mhat ntt_specE.
  exact (forward_ntt_centered_output_shape _ (encap_full_m_input_qrange pk coins)).
qed.
lemma encap_full_product_qring pk coins : encap_key_canonical pk =>
  poly_basemul_qring (decoded_poly pk) (encap_full_rhat pk coins) (encap_full_product pk coins) 192.
proof.
  move=> hk; apply poly_basemul_word_to_qring.
  + apply encap_pointwise_blocks; exact (candidate_canonical_decoder_qrange pk hk).
  + apply encap_pointwise_blocks; exact (encap_full_rhat_qrange pk coins).
  exact (candidate_product_word _ _).
qed.
lemma encap_full_product_range pk coins : encap_key_canonical pk => in_qrange768 (encap_full_product pk coins).
proof. move=> hk; exact (poly_basemul_qring_product_in_qrange768 _ _ _ (encap_full_product_qring pk coins hk)). qed.
lemma encap_full_cipher_qring pk coins : encap_key_canonical pk =>
  poly_basemul_add_qring (decoded_poly pk) (encap_full_rhat pk coins) (encap_full_mhat pk coins)
    (encap_full_cipher pk coins) 192.
proof.
  move=> hk; exact (poly_basemul_add_spec_qring _ _ _ _
    (encap_full_product_qring pk coins hk) (encap_full_mhat_centered pk coins)).
qed.
lemma encap_full_cipher_serializer pk coins : encap_key_canonical pk =>
  poly_tobytes_input_qrange (encap_full_cipher pk coins).
proof.
  move=> hk; apply in_qrange768_poly_tobytes_input_qrange.
  have h := poly_centered_add_spec_qring _ _ (encap_full_product_range pk coins hk) (encap_full_mhat_centered pk coins).
  move: h => [hr _]; exact hr.
qed.
