require import AllCore Distr.
from Jasmin require import JWord.

require import Array192 Array224 Array768 Array1152.
require import NTRUPlus768DecapPolyCBD1Bridge.
require import NTRUPlus768PolyCBD1Algebra.
require import NTRUPlus768DecapR1NTTBridge.
require import NTRUPlus768NTTProof.
require import NTRUPlus768PolyToBytes.
require import NTRUPlus768PolyToBytesProof.
require import NTRUPlus768PolyToBytesAlgebra.

(* Keccak-free serialization boundary for the decapsulation reencryption
   candidate.  It composes the verified r1 NTT value with the existing
   poly_tobytes procedure/specification and stops before verify semantics.
   No C pointer identity, overlap, or shared-memory theorem is claimed. *)

op decap_r1_cbd_input_spec
    (buf3_prefix : W8.t Array224.t) : W8.t Array192.t =
  NTRUPlus768DecapPolyCBD1Bridge.hash_h_cbd1_input_from_prefix buf3_prefix.

op decap_r1_pre_ntt_spec
    (buf3_prefix : W8.t Array224.t) : W16.t Array768.t =
  NTRUPlus768PolyCBD1Algebra.poly_cbd1_spec
    (decap_r1_cbd_input_spec buf3_prefix).

op decap_r1_post_ntt_spec
    (buf3_prefix : W8.t Array224.t) : W16.t Array768.t =
  NTRUPlus768NTTProof.ntt_spec (decap_r1_pre_ntt_spec buf3_prefix).

op decap_r1_buf2_spec
    (buf3_prefix : W8.t Array224.t) : W8.t Array1152.t =
  NTRUPlus768PolyToBytesProof.poly_tobytes_spec
    (decap_r1_post_ntt_spec buf3_prefix).

op decap_r1_tobytes_value_flow
    (predecessor_flow : W8.t Array224.t -> bool)
    (buf3_prefix : W8.t Array224.t)
    (cbd1_input : W8.t Array192.t)
    (r1_pre r1_post : W16.t Array768.t)
    (buf2 : W8.t Array1152.t) : bool =
  NTRUPlus768DecapR1NTTBridge.decap_r1_ntt_value_flow
    predecessor_flow buf3_prefix cbd1_input r1_pre r1_post /\
  buf2 = NTRUPlus768PolyToBytesProof.poly_tobytes_spec r1_post.

lemma decap_r1_ntt_to_tobytes_value_flow
    (predecessor_flow : W8.t Array224.t -> bool)
    (buf3_prefix : W8.t Array224.t)
    (cbd1_input : W8.t Array192.t)
    (r1_pre r1_post : W16.t Array768.t) :
  NTRUPlus768DecapR1NTTBridge.decap_r1_ntt_value_flow
    predecessor_flow buf3_prefix cbd1_input r1_pre r1_post =>
  decap_r1_tobytes_value_flow
    predecessor_flow buf3_prefix cbd1_input r1_pre r1_post
    (NTRUPlus768PolyToBytesProof.poly_tobytes_spec r1_post).
proof. by move=> Hflow; rewrite /decap_r1_tobytes_value_flow. qed.

lemma decap_terminal_r1_tobytes_value_flow
    (predecessor_flow : W8.t Array224.t -> bool)
    (buf3_prefix : W8.t Array224.t) :
  predecessor_flow buf3_prefix =>
  decap_r1_tobytes_value_flow
    predecessor_flow buf3_prefix
    (decap_r1_cbd_input_spec buf3_prefix)
    (decap_r1_pre_ntt_spec buf3_prefix)
    (decap_r1_post_ntt_spec buf3_prefix)
    (decap_r1_buf2_spec buf3_prefix).
proof.
  move=> Hpredecessor.
  rewrite /decap_r1_tobytes_value_flow /decap_r1_buf2_spec.
  split; last done.
  rewrite /decap_r1_cbd_input_spec /decap_r1_pre_ntt_spec
    /decap_r1_post_ntt_spec.
  exact
    (NTRUPlus768DecapR1NTTBridge.decap_terminal_r1_ntt_value_flow
      predecessor_flow buf3_prefix Hpredecessor).
qed.

lemma decap_r1_tobytes_input_qrange
    (predecessor_flow : W8.t Array224.t -> bool)
    (buf3_prefix : W8.t Array224.t)
    (cbd1_input : W8.t Array192.t)
    (r1_pre r1_post : W16.t Array768.t)
    (buf2 : W8.t Array1152.t) :
  decap_r1_tobytes_value_flow
    predecessor_flow buf3_prefix cbd1_input r1_pre r1_post buf2 =>
  NTRUPlus768PolyToBytesProof.poly_tobytes_input_qrange r1_post.
proof.
  move=> [Hntt _].
  rewrite NTRUPlus768PolyToBytesAlgebra.poly_tobytes_procedure_input_qrangeE.
  exact
    (NTRUPlus768DecapR1NTTBridge.decap_r1_ntt_poly_tobytes_ready
      predecessor_flow buf3_prefix cbd1_input r1_pre r1_post Hntt).
qed.

lemma decap_r1_tobytes_algebra_spec
    (predecessor_flow : W8.t Array224.t -> bool)
    (buf3_prefix : W8.t Array224.t)
    (cbd1_input : W8.t Array192.t)
    (r1_pre r1_post : W16.t Array768.t)
    (buf2 : W8.t Array1152.t) :
  decap_r1_tobytes_value_flow
    predecessor_flow buf3_prefix cbd1_input r1_pre r1_post buf2 =>
  buf2 = NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec r1_post.
proof.
  move=> [_ ->].
  exact (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_procedure_specE r1_post).
qed.

lemma decap_r1_tobytes_functional
    (predecessor_flow : W8.t Array224.t -> bool)
    (buf3_prefix : W8.t Array224.t)
    (cbd1_input : W8.t Array192.t)
    (r1_pre r1_post : W16.t Array768.t)
    (buf2 rp0 : W8.t Array1152.t) :
  decap_r1_tobytes_value_flow
    predecessor_flow buf3_prefix cbd1_input r1_pre r1_post buf2 =>
  hoare [NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes :
    rp = rp0 /\ ap = r1_post ==>
    res = NTRUPlus768PolyToBytesProof.poly_tobytes_spec r1_post].
proof.
  move=> Hflow.
  exact
    (NTRUPlus768PolyToBytesProof.poly_tobytes_functional rp0 r1_post
      (decap_r1_tobytes_input_qrange
        predecessor_flow buf3_prefix cbd1_input r1_pre r1_post buf2 Hflow)).
qed.

lemma decap_r1_tobytes_lossless :
  islossless
    NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes.
proof. exact NTRUPlus768PolyToBytesProof.poly_tobytes_lossless. qed.

lemma decap_r1_tobytes_correct
    (predecessor_flow : W8.t Array224.t -> bool)
    (buf3_prefix : W8.t Array224.t)
    (cbd1_input : W8.t Array192.t)
    (r1_pre r1_post : W16.t Array768.t)
    (buf2 rp0 : W8.t Array1152.t) :
  decap_r1_tobytes_value_flow
    predecessor_flow buf3_prefix cbd1_input r1_pre r1_post buf2 =>
  phoare [NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes :
    rp = rp0 /\ ap = r1_post ==>
    res = NTRUPlus768PolyToBytesProof.poly_tobytes_spec r1_post] = 1%r.
proof.
  move=> Hflow.
  exact
    (NTRUPlus768PolyToBytesProof.poly_tobytes_correct rp0 r1_post
      (decap_r1_tobytes_input_qrange
        predecessor_flow buf3_prefix cbd1_input r1_pre r1_post buf2 Hflow)).
qed.

lemma decap_r1_tobytes_value_flow_functional
    (predecessor_flow : W8.t Array224.t -> bool)
    (buf3_prefix : W8.t Array224.t)
    (cbd1_input : W8.t Array192.t)
    (r1_pre r1_post : W16.t Array768.t)
    (buf2 rp0 : W8.t Array1152.t) :
  decap_r1_tobytes_value_flow
    predecessor_flow buf3_prefix cbd1_input r1_pre r1_post buf2 =>
  hoare [NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes :
    rp = rp0 /\ ap = r1_post ==> res = buf2].
proof.
  move=> Hflow.
  have Hfunctional :=
    decap_r1_tobytes_functional
      predecessor_flow buf3_prefix cbd1_input r1_pre r1_post buf2 rp0 Hflow.
  move: Hflow => [_ ->].
  exact Hfunctional.
qed.

lemma decap_r1_tobytes_value_flow_correct
    (predecessor_flow : W8.t Array224.t -> bool)
    (buf3_prefix : W8.t Array224.t)
    (cbd1_input : W8.t Array192.t)
    (r1_pre r1_post : W16.t Array768.t)
    (buf2 rp0 : W8.t Array1152.t) :
  decap_r1_tobytes_value_flow
    predecessor_flow buf3_prefix cbd1_input r1_pre r1_post buf2 =>
  phoare [NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes :
    rp = rp0 /\ ap = r1_post ==> res = buf2] = 1%r.
proof.
  move=> Hflow.
  have Hcorrect :=
    decap_r1_tobytes_correct
      predecessor_flow buf3_prefix cbd1_input r1_pre r1_post buf2 rp0 Hflow.
  move: Hflow => [_ ->].
  exact Hcorrect.
qed.

lemma decap_terminal_r1_tobytes_functional
    (predecessor_flow : W8.t Array224.t -> bool)
    (buf3_prefix : W8.t Array224.t)
    (rp0 : W8.t Array1152.t) :
  predecessor_flow buf3_prefix =>
  hoare [NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes :
    rp = rp0 /\ ap = decap_r1_post_ntt_spec buf3_prefix ==>
    res = decap_r1_buf2_spec buf3_prefix].
proof.
  move=> Hpredecessor.
  exact
    (decap_r1_tobytes_value_flow_functional
      predecessor_flow buf3_prefix
      (decap_r1_cbd_input_spec buf3_prefix)
      (decap_r1_pre_ntt_spec buf3_prefix)
      (decap_r1_post_ntt_spec buf3_prefix)
      (decap_r1_buf2_spec buf3_prefix) rp0
      (decap_terminal_r1_tobytes_value_flow
        predecessor_flow buf3_prefix Hpredecessor)).
qed.

lemma decap_terminal_r1_tobytes_correct
    (predecessor_flow : W8.t Array224.t -> bool)
    (buf3_prefix : W8.t Array224.t)
    (rp0 : W8.t Array1152.t) :
  predecessor_flow buf3_prefix =>
  phoare [NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes :
    rp = rp0 /\ ap = decap_r1_post_ntt_spec buf3_prefix ==>
    res = decap_r1_buf2_spec buf3_prefix] = 1%r.
proof.
  move=> Hpredecessor.
  exact
    (decap_r1_tobytes_value_flow_correct
      predecessor_flow buf3_prefix
      (decap_r1_cbd_input_spec buf3_prefix)
      (decap_r1_pre_ntt_spec buf3_prefix)
      (decap_r1_post_ntt_spec buf3_prefix)
      (decap_r1_buf2_spec buf3_prefix) rp0
      (decap_terminal_r1_tobytes_value_flow
        predecessor_flow buf3_prefix Hpredecessor)).
qed.
