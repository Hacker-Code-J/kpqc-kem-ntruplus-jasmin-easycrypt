require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.
require import Array768 Array1152 Array2304.
require import NTRUPlus768DecapCandidate NTRUPlus768DecapCandidateSpec NTRUPlus768DecapCandidateProof.
require import NTRUPlus768BasemulAlgebra NTRUPlus768PolyBasemulAlgebra.
require import NTRUPlus768PolyBasemulInvNTTAlgebra.
require import NTRUPlus768InvNTTAlgebra NTRUPlus768Crepmod3Algebra NTRUPlus768Crepmod3DecapBridge.
require import NTRUPlus768NTTStage1Algebra NTRUPlus768PolyFromBytesAlgebra.
require import NTRUPlus768CanonicalDecoder NTRUPlus768EncapGuardSpec NTRUPlus768DecapGuardSpec.

(* This is the candidate computation. Algebraic key validity and the
   message-recovery/no-wrap conditions are not asserted here. *)
op decap_candidate_algebra (cp fp rp : W16.t Array768.t) : bool =
  poly_basemul_qring cp fp (candidate_product_spec cp fp) 192 /\
  decap_m1_crepmod3_value_flow (candidate_product_spec cp fp) rp.

op candidate_ternary (rp : W16.t Array768.t) : bool =
  forall j, 0 <= j < 768 => is_trit (coeff rp.[j]).

lemma candidate_spec_algebra_s12 cp fp :
  in_s12range768 cp => in_s12range768 fp =>
  decap_candidate_algebra cp fp (decap_candidate_spec cp fp).
proof.
  move=> hc hf.
  have hb := poly_basemul_word_to_qring_s12 cp fp (candidate_product_spec cp fp)
    hc hf (candidate_product_word cp fp).
  split; first exact hb.
  rewrite /decap_candidate_spec invntt_specE.
  exact (poly_basemul_qring_decap_m1_crepmod3_value_flow cp fp
    (candidate_product_spec cp fp) hb).
qed.

lemma candidate_algebra_ternary cp fp rp :
  decap_candidate_algebra cp fp rp => candidate_ternary rp.
proof.
  rewrite /decap_candidate_algebra /decap_m1_crepmod3_value_flow.
  move=> h.
  have hc : poly_crepmod3_algebra
      (inverse_invntt_spec (candidate_product_spec cp fp)) rp by smt().
  rewrite /candidate_ternary.
  rewrite /poly_crepmod3_algebra in hc.
  smt().
qed.

lemma candidate_decoded_spec_algebra ct fb :
  decap_candidate_algebra (decoded_poly ct) (decoded_poly fb)
    (decap_candidate_spec (decoded_poly ct) (decoded_poly fb)).
proof.
  apply candidate_spec_algebra_s12;
    apply NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec_in_s12range768.
qed.

lemma candidate_canonical_decoder_qrange bs : encap_key_canonical bs =>
  NTRUPlus768NTTStage1Algebra.input_qrange (decoded_poly bs).
proof.
  move=> hb j hj.
  have h := hb j hj.
  have hu := W16.to_uint_cmp (decoded_poly bs).[j].
  have he : W16.to_sint (decoded_poly bs).[j] = W16.to_uint (decoded_poly bs).[j].
  + apply NTRUPlus768PolyFromBytesAlgebra.coeff_uint_small; smt().
  rewrite /in_qrange /coeff /q he; smt().
qed.

lemma candidate_guard_accepts_ranges ct sk :
  decap_guard_accepts ct (decap_fbytes sk) (decap_hbytes sk) =>
  NTRUPlus768NTTStage1Algebra.input_qrange (decoded_poly ct) /\
  NTRUPlus768NTTStage1Algebra.input_qrange (decoded_poly (decap_fbytes sk)) /\
  in_s12range768 (decoded_poly ct) /\
  in_s12range768 (decoded_poly (decap_fbytes sk)).
proof.
  move=> [hc [hf _]].
  split; first exact (candidate_canonical_decoder_qrange ct hc).
  split; first exact (candidate_canonical_decoder_qrange (decap_fbytes sk) hf).
  split; apply NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec_in_s12range768.
qed.

