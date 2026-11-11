require import AllCore List Distr.
from Jasmin require import JWord.
require import Array129 Array224 Array96 Array32.
require import NTRUPlus768DecapHashHPrepareProof NTRUPlus768DecapHashHBridge.
require import Keccak1600_Spec EclibExtra.

(* External ABI contract for the native SHAKE256 call. The mathematical
   instance below proves the contract only for Keccak1600Bytes, not for C. *)
module type CompleteSHAKEH = {
  proc shake(input : W8.t Array129.t) : W8.t Array224.t
}.
op complete_shake_h_spec (input : W8.t Array129.t) : W8.t Array224.t =
  Array224.of_list W8.zero (SHAKE256 (Array129.to_list input) 224).

lemma complete_shake_h_agreement msg suffix :
  complete_shake_h_spec (hash_h_prepare_spec msg suffix) = hash_h_spec msg suffix.
proof.
  by rewrite /complete_shake_h_spec hash_h_prepare_to_list /hash_h_spec /hash_h_output_list /hash_h_input /hash_h_payload_list.
qed.

module MathematicalSHAKEH = {
  proc shake(input : W8.t Array129.t) : W8.t Array224.t = {
    var out;
    out <@ Keccak1600Bytes.shake256(Array129.to_list input,224);
    return Array224.of_list W8.zero out;
  }
}.
lemma complete_mathematical_h_functional input0 :
  hoare [MathematicalSHAKEH.shake : input=input0 ==> res=complete_shake_h_spec input0].
proof.
  proc; ecall (SHAKE256_h (Array129.to_list input0) 224); by auto => />.
qed.
lemma complete_mathematical_h_lossless : islossless MathematicalSHAKEH.shake.
proof. proc; call SHAKE256_ll; by auto. qed.
lemma complete_mathematical_h_correct input0 :
  phoare [MathematicalSHAKEH.shake : input=input0 ==> res=complete_shake_h_spec input0]=1%r.
proof. by conseq complete_mathematical_h_lossless (complete_mathematical_h_functional input0). qed.
