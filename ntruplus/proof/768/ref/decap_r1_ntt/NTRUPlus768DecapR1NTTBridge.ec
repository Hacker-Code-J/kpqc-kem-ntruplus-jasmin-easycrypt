require import AllCore Distr.
from Jasmin require import JWord.

require import Array192 Array224 Array768.
require import NTRUPlus768DecapPolyCBD1Bridge.
require import NTRUPlus768PolyCBD1Algebra.
require import NTRUPlus768NTTProof.
require import NTRUPlus768NTTAlgebra.
require import NTRUPlus768PolyToBytesAlgebra.

(* Keccak-free value composition for the decapsulation r1 transform.  The
   predecessor predicate is applied to the same hash-output prefix by the
   typed CBD bridge.  The procedure lemmas below specialize the verified
   old-array Jasmin model to equal input/output array values; they do not claim
   a C pointer-alias or shared-memory theorem. *)

op decap_r1_ntt_value_flow
    (predecessor_flow : W8.t Array224.t -> bool)
    (buf3_prefix : W8.t Array224.t)
    (cbd1_input : W8.t Array192.t)
    (r1_pre r1_post : W16.t Array768.t) : bool =
  NTRUPlus768DecapPolyCBD1Bridge.decap_poly_cbd1_value_flow
    predecessor_flow buf3_prefix cbd1_input r1_pre /\
  r1_post = NTRUPlus768NTTProof.ntt_spec r1_pre.

lemma decap_poly_cbd1_to_r1_ntt_value_flow
    (predecessor_flow : W8.t Array224.t -> bool)
    (buf3_prefix : W8.t Array224.t) :
  predecessor_flow buf3_prefix =>
  decap_r1_ntt_value_flow
    predecessor_flow
    buf3_prefix
    (NTRUPlus768DecapPolyCBD1Bridge.hash_h_cbd1_input_from_prefix
      buf3_prefix)
    (NTRUPlus768PolyCBD1Algebra.poly_cbd1_spec
      (NTRUPlus768DecapPolyCBD1Bridge.hash_h_cbd1_input_from_prefix
        buf3_prefix))
    (NTRUPlus768NTTProof.ntt_spec
      (NTRUPlus768PolyCBD1Algebra.poly_cbd1_spec
        (NTRUPlus768DecapPolyCBD1Bridge.hash_h_cbd1_input_from_prefix
          buf3_prefix))).
proof.
  move=> Hpredecessor.
  rewrite /decap_r1_ntt_value_flow.
  split.
  + exact
      (NTRUPlus768DecapPolyCBD1Bridge.decap_terminal_poly_cbd1_value_flow
        predecessor_flow buf3_prefix Hpredecessor).
  done.
qed.

lemma decap_terminal_r1_ntt_value_flow
    (predecessor_flow : W8.t Array224.t -> bool)
    (buf3_prefix : W8.t Array224.t) :
  predecessor_flow buf3_prefix =>
  decap_r1_ntt_value_flow
    predecessor_flow
    buf3_prefix
    (NTRUPlus768DecapPolyCBD1Bridge.hash_h_cbd1_input_from_prefix
      buf3_prefix)
    (NTRUPlus768PolyCBD1Algebra.poly_cbd1_spec
      (NTRUPlus768DecapPolyCBD1Bridge.hash_h_cbd1_input_from_prefix
        buf3_prefix))
    (NTRUPlus768NTTProof.ntt_spec
      (NTRUPlus768PolyCBD1Algebra.poly_cbd1_spec
        (NTRUPlus768DecapPolyCBD1Bridge.hash_h_cbd1_input_from_prefix
          buf3_prefix))).
proof. exact (decap_poly_cbd1_to_r1_ntt_value_flow predecessor_flow buf3_prefix). qed.

lemma decap_r1_ntt_input_qrange
    (predecessor_flow : W8.t Array224.t -> bool)
    (buf3_prefix : W8.t Array224.t)
    (cbd1_input : W8.t Array192.t)
    (r1_pre r1_post : W16.t Array768.t) :
  decap_r1_ntt_value_flow
    predecessor_flow buf3_prefix cbd1_input r1_pre r1_post =>
  NTRUPlus768NTTStage1Algebra.input_qrange r1_pre.
proof.
  move=> [Hcbd _].
  exact
    (NTRUPlus768DecapPolyCBD1Bridge.decap_poly_cbd1_r1_input_qrange
      predecessor_flow buf3_prefix cbd1_input r1_pre Hcbd).
qed.

lemma decap_r1_ntt_inplace_functional (r1_pre : W16.t Array768.t) :
  hoare [NTRUPlus768NTT.M.jade_ntruplus_ntruplus768_amd64_ref_ntt :
    rp = r1_pre /\ ap = r1_pre ==>
    res = NTRUPlus768NTTProof.ntt_spec r1_pre].
proof. exact (NTRUPlus768NTTProof.ntt_functional r1_pre r1_pre). qed.

lemma decap_r1_ntt_inplace_lossless :
  islossless NTRUPlus768NTT.M.jade_ntruplus_ntruplus768_amd64_ref_ntt.
proof. exact NTRUPlus768NTTProof.ntt_lossless. qed.

lemma decap_r1_ntt_inplace_correct (r1_pre : W16.t Array768.t) :
  phoare [NTRUPlus768NTT.M.jade_ntruplus_ntruplus768_amd64_ref_ntt :
    rp = r1_pre /\ ap = r1_pre ==>
    res = NTRUPlus768NTTProof.ntt_spec r1_pre] = 1%r.
proof. exact (NTRUPlus768NTTProof.ntt_correct r1_pre r1_pre). qed.

lemma decap_r1_ntt_value_flow_inplace_functional
    (predecessor_flow : W8.t Array224.t -> bool)
    (buf3_prefix : W8.t Array224.t)
    (cbd1_input : W8.t Array192.t)
    (r1_pre r1_post : W16.t Array768.t) :
  decap_r1_ntt_value_flow
    predecessor_flow buf3_prefix cbd1_input r1_pre r1_post =>
  hoare [NTRUPlus768NTT.M.jade_ntruplus_ntruplus768_amd64_ref_ntt :
    rp = r1_pre /\ ap = r1_pre ==> res = r1_post].
proof.
  move=> [_ Hr1_post].
  rewrite Hr1_post.
  exact (decap_r1_ntt_inplace_functional r1_pre).
qed.

lemma decap_r1_ntt_value_flow_inplace_correct
    (predecessor_flow : W8.t Array224.t -> bool)
    (buf3_prefix : W8.t Array224.t)
    (cbd1_input : W8.t Array192.t)
    (r1_pre r1_post : W16.t Array768.t) :
  decap_r1_ntt_value_flow
    predecessor_flow buf3_prefix cbd1_input r1_pre r1_post =>
  phoare [NTRUPlus768NTT.M.jade_ntruplus_ntruplus768_amd64_ref_ntt :
    rp = r1_pre /\ ap = r1_pre ==> res = r1_post] = 1%r.
proof.
  move=> [_ Hr1_post].
  rewrite Hr1_post.
  exact (decap_r1_ntt_inplace_correct r1_pre).
qed.

lemma decap_r1_ntt_algebra
    (predecessor_flow : W8.t Array224.t -> bool)
    (buf3_prefix : W8.t Array224.t)
    (cbd1_input : W8.t Array192.t)
    (r1_pre r1_post : W16.t Array768.t) :
  decap_r1_ntt_value_flow
    predecessor_flow buf3_prefix cbd1_input r1_pre r1_post =>
  NTRUPlus768NTTAlgebra.forward_ntt_algebra r1_pre r1_post.
proof.
  move=> Hflow.
  have Hinput :=
    decap_r1_ntt_input_qrange
      predecessor_flow buf3_prefix cbd1_input r1_pre r1_post Hflow.
  move: Hflow => [_ ->].
  rewrite NTRUPlus768NTTAlgebra.ntt_specE.
  exact (NTRUPlus768NTTAlgebra.forward_ntt_spec_algebra r1_pre Hinput).
qed.

lemma decap_r1_ntt_centered_output
    (predecessor_flow : W8.t Array224.t -> bool)
    (buf3_prefix : W8.t Array224.t)
    (cbd1_input : W8.t Array192.t)
    (r1_pre r1_post : W16.t Array768.t) :
  decap_r1_ntt_value_flow
    predecessor_flow buf3_prefix cbd1_input r1_pre r1_post =>
  NTRUPlus768NTTRadix2_4Algebra.centered_input_shape r1_post.
proof.
  move=> Hflow.
  have Hinput :=
    decap_r1_ntt_input_qrange
      predecessor_flow buf3_prefix cbd1_input r1_pre r1_post Hflow.
  move: Hflow => [_ ->].
  rewrite NTRUPlus768NTTAlgebra.ntt_specE.
  exact (NTRUPlus768NTTAlgebra.forward_ntt_centered_output_shape r1_pre Hinput).
qed.

lemma decap_r1_ntt_poly_tobytes_ready
    (predecessor_flow : W8.t Array224.t -> bool)
    (buf3_prefix : W8.t Array224.t)
    (cbd1_input : W8.t Array192.t)
    (r1_pre r1_post : W16.t Array768.t) :
  decap_r1_ntt_value_flow
    predecessor_flow buf3_prefix cbd1_input r1_pre r1_post =>
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange r1_post.
proof.
  move=> Hflow.
  have Hinput :=
    decap_r1_ntt_input_qrange
      predecessor_flow buf3_prefix cbd1_input r1_pre r1_post Hflow.
  move: Hflow => [_ ->].
  rewrite /NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange.
  move=> j Hj.
  rewrite NTRUPlus768NTTAlgebra.ntt_specE.
  exact
    (NTRUPlus768NTTAlgebra.forward_ntt_centered_coeff_range
      r1_pre j Hinput Hj).
qed.
