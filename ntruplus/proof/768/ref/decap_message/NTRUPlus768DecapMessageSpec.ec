require import AllCore IntDiv List Distr.
from Jasmin require import JWord JModel_x86.
require import Array768 Array1152 Array1153 Array192 Array96.
require import NTRUPlus768DecapMessagePrepareProof NTRUPlus768DecapHashGBridge.
require import NTRUPlus768PolySOTPDecodeAlgebra Keccak1600_Spec EclibExtra.

op message_shake_spec (input : W8.t Array1153.t) : W8.t Array192.t =
  Array192.of_list W8.zero (SHAKE256 (Array1153.to_list input) 192).

op decap_message_spec (r2 m1 : W16.t Array768.t) :
    W8.t Array1152.t * W8.t Array96.t * W32.t =
  let bs = NTRUPlus768PolyToBytesProof.poly_tobytes_spec r2 in
  let pad = hash_g_spec bs in
  (bs, poly_sotp_decode_msg_spec m1 pad,
    W32.of_int (b2i (poly_sotp_decode_fail_spec m1 pad))).

lemma message_hash_input_list bs :
  Array1153.to_list (message_hash_input bs) = hash_g_input bs.
proof.
  apply (eq_from_nth witness).
  + by rewrite Array1153.size_to_list hash_g_input_size.
  move=> j; rewrite Array1153.size_to_list => hj.
  rewrite Array1153.get_to_list /message_hash_input Array1153.initiE //.
  rewrite /hash_g_input /=.
  case (j = 0) => hz; first done.
  smt(Array1152.get_to_list).
qed.

lemma message_shake_hash_g bs :
  message_shake_spec (message_hash_input bs) = hash_g_spec bs.
proof.
  by rewrite /message_shake_spec message_hash_input_list /hash_g_spec /hash_g_output_list.
qed.

lemma decap_message_flag_boolean r2 m1 :
  (decap_message_spec r2 m1).`3 = W32.zero \/
  (decap_message_spec r2 m1).`3 = W32.one.
proof.
  rewrite /decap_message_spec /=; case (poly_sotp_decode_fail_spec m1
    (hash_g_spec (NTRUPlus768PolyToBytesProof.poly_tobytes_spec r2))) => hf.
  + by rewrite /b2i.
  by rewrite /b2i.
qed.

lemma decap_message_failure_zero r2 m1 :
  (decap_message_spec r2 m1).`3 = W32.one =>
  (decap_message_spec r2 m1).`2 = poly_sotp_zero_msg_spec.
proof.
  rewrite /decap_message_spec /=.
  case (poly_sotp_decode_fail_spec m1
    (hash_g_spec (NTRUPlus768PolyToBytesProof.poly_tobytes_spec r2))) => hf /=.
  + move=> _; exact (poly_sotp_decode_failure_zero _ _ hf).
  smt(W32.to_uint0 W32.to_uint1).
qed.

(* The contract below is an explicit external assumption for the native C
   SHAKE256 call. The mathematical implementation discharges it only for its
   own model; no theorem here identifies the C primitive with that model. *)
module type MessageSHAKE = {
  proc shake(input : W8.t Array1153.t) : W8.t Array192.t
}.

module MathematicalSHAKE = {
  proc shake(input : W8.t Array1153.t) : W8.t Array192.t = {
    var out;
    out <@ Keccak1600Bytes.shake256(Array1153.to_list input,192);
    return Array192.of_list W8.zero out;
  }
}.

lemma mathematical_shake_functional input0 :
  hoare [MathematicalSHAKE.shake : input = input0 ==> res = message_shake_spec input0].
proof.
  proc; ecall (SHAKE256_h (Array1153.to_list input0) 192); by auto => />.
qed.

lemma mathematical_shake_lossless : islossless MathematicalSHAKE.shake.
proof. proc; call SHAKE256_ll; by auto. qed.

lemma mathematical_shake_correct input0 :
  phoare [MathematicalSHAKE.shake : input = input0 ==> res = message_shake_spec input0] = 1%r.
proof. by conseq mathematical_shake_lossless (mathematical_shake_functional input0). qed.
