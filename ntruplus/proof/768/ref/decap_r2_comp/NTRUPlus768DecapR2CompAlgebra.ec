require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.
require import Array4 Array768 Array1152 Array2304.
require import NTRUPlus768BasemulAlgebra NTRUPlus768Crepmod3Algebra.
require import NTRUPlus768NTTProof NTRUPlus768PolySubProof NTRUPlus768PolyFromBytesAlgebra.
require import NTRUPlus768DecapR2Comp NTRUPlus768DecapR2CompSpec NTRUPlus768DecapR2CompProof.
require import NTRUPlus768DecapCandidateSpec NTRUPlus768DecapCandidateAlgebra.
require import NTRUPlus768NTTAlgebra NTRUPlus768NTTStage1Algebra.
require import NTRUPlus768PolySubAlgebra NTRUPlus768PolySubDecapBridge.
require import NTRUPlus768PolyBasemulAlgebra NTRUPlus768DecapR2Bridge.
require import NTRUPlus768CanonicalDecoder NTRUPlus768EncapGuardSpec NTRUPlus768DecapGuardSpec.

(* This is a computation theorem: it does not assert recovery of the
   encapsulator's randomness or algebraic validity of the secret key. *)
op decap_r2_algebra (cp mp hp rp : W16.t Array768.t) : bool =
  candidate_ternary mp /\
  forward_ntt_algebra mp (ntt_spec mp) /\
  poly_sub_algebra cp (ntt_spec mp) (r2_difference_spec cp mp) /\
  poly_basemul_qring (r2_difference_spec cp mp) hp rp 192 /\
  in_qrange768 rp.

lemma r2_ternary_input_qrange mp : candidate_ternary mp => input_qrange mp.
proof.
  move=> ht j hj; have h := ht j hj.
  move: h; rewrite /is_trit /in_qrange /q; smt().
qed.

lemma r2_forward_qrange mp : candidate_ternary mp => input_qrange (ntt_spec mp).
proof.
  move=> ht j hj; rewrite ntt_specE.
  exact (forward_ntt_centered_coeff_range mp j (r2_ternary_input_qrange mp ht) hj).
qed.

lemma r2_difference_asym cp mp : decoder_range cp => candidate_ternary mp =>
  in_asymrange768 (r2_difference_spec cp mp).
proof.
  move=> hc hm; rewrite /r2_difference_spec.
  exact (poly_sub_spec_in_asymrange768 cp (ntt_spec mp) hc (r2_forward_qrange mp hm)).
qed.

lemma r2_canonical_decoded bs : encap_key_canonical bs =>
  in_canonical_range768 (decoded_poly bs).
proof.
  move=> hb.
  have hj : forall j, 0 <= j < 768 => 0 <= coeff (decoded_poly bs).[j] < q.
  + move=> j hj.
    have h := hb j hj.
    have hu := W16.to_uint_cmp (decoded_poly bs).[j].
    have he : W16.to_sint (decoded_poly bs).[j] = W16.to_uint (decoded_poly bs).[j].
    - apply NTRUPlus768PolyFromBytesAlgebra.coeff_uint_small; smt().
    rewrite /coeff he; smt().
  move=> k hk.
  rewrite /in_canonical_range4 /block4 /in_canonical_range !Array4.initiE //=.
  smt().
qed.

lemma r2_spec_algebra cp mp hp : decoder_range cp => candidate_ternary mp =>
  in_canonical_range768 hp => decap_r2_algebra cp mp hp (decap_r2_spec cp mp hp).
proof.
  move=> hc hm hh.
  have hf := r2_forward_qrange mp hm.
  have hs := r2_difference_asym cp mp hc hm.
  have hb := poly_basemul_word_to_qring_asym (r2_difference_spec cp mp) hp
    (decap_r2_spec cp mp hp) hs hh (decap_r2_word cp mp hp).
  split; first exact hm.
  split.
  + rewrite ntt_specE; exact (forward_ntt_spec_algebra mp (r2_ternary_input_qrange mp hm)).
  split.
  + exact (poly_sub_spec_algebra cp (ntt_spec mp) hc hf).
  split; first exact hb.
  exact (poly_basemul_qring_output_in_qrange768 _ _ _ hb).
qed.

lemma r2_guard_candidate_inputs ct sk :
  decap_guard_accepts ct (decap_fbytes sk) (decap_hbytes sk) =>
  decoder_range (decoded_poly ct) /\
  candidate_ternary (decap_candidate_spec (decoded_poly ct) (decoded_poly (decap_fbytes sk))) /\
  in_canonical_range768 (decoded_poly (decap_hbytes sk)).
proof.
  move=> [_ [_ hh]].
  split; first exact (poly_frombytes_spec_decoder_range ct).
  split.
  + exact (candidate_algebra_ternary _ _ _ (candidate_decoded_spec_algebra ct (decap_fbytes sk))).
  exact (r2_canonical_decoded (decap_hbytes sk) hh).
qed.

