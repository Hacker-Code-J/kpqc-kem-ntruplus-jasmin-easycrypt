require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.
require import Array768 Array1152 Array1153 Array192 Array96.
require import NTRUPlus768DecapMessagePrepare NTRUPlus768DecapMessagePrepareProof.
require import NTRUPlus768DecapMessageSpec NTRUPlus768PolyToBytesProof.
require import NTRUPlus768PolySOTPDecodeChecked NTRUPlus768PolySOTPDecodeAlgebra.
require import NTRUPlus768PolySOTPDecodeCheckedProof NTRUPlus768PolySOTPDecodeCheckedLossless.

(* Array-level composition of two actual extracted Jasmin procedures with an
   explicit external hash module. This models the native C glue's value flow;
   it is not a C-AST, shared-memory, or complete-Decaps refinement theorem. *)
module DecapMessage(H : MessageSHAKE) = {
  proc run(serialized : W8.t Array1152.t, input : W8.t Array1153.t,
      msg : W8.t Array96.t, r2 m1 : W16.t Array768.t) :
      W8.t Array1152.t * W8.t Array96.t * W32.t = {
    var pad : W8.t Array192.t;
    var status : W32.t;
    (serialized,input) <@ NTRUPlus768DecapMessagePrepare.M.jade_ntruplus_ntruplus768_amd64_ref_decap_message_prepare(serialized,input,r2);
    pad <@ H.shake(input);
    (msg,status) <@ NTRUPlus768PolySOTPDecodeChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_decode(msg,m1,pad);
    return (serialized,msg,status);
  }
}.

lemma decap_message_functional (H <: MessageSHAKE) bs0 input0 msg0 r20 m10 :
  (forall input0, hoare [H.shake : input = input0 ==> res = message_shake_spec input0]) =>
  poly_tobytes_input_qrange r20 => poly_sotp_trit_input m10 =>
  hoare [DecapMessage(H).run :
    serialized = bs0 /\ input = input0 /\ msg = msg0 /\ r2 = r20 /\ m1 = m10 ==>
    res = decap_message_spec r20 m10].
proof.
  move=> hh hr hm; proc.
  call (poly_sotp_decode_functional msg0 m10
    (message_shake_spec (message_hash_input (poly_tobytes_spec r20)))).
  call (hh (message_hash_input (poly_tobytes_spec r20))).
  call (message_prepare_functional bs0 input0 r20 hr).
  auto => />; by rewrite message_shake_hash_g /decap_message_spec.
qed.

lemma decap_message_lossless (H <: MessageSHAKE) :
  islossless H.shake => islossless DecapMessage(H).run.
proof.
  move=> hl; proc; call poly_sotp_decode_lossless; call hl;
    call message_prepare_lossless; by auto.
qed.

lemma decap_message_correct (H <: MessageSHAKE) bs0 input0 msg0 r20 m10 :
  (forall input0, hoare [H.shake : input = input0 ==> res = message_shake_spec input0]) =>
  islossless H.shake =>
  poly_tobytes_input_qrange r20 => poly_sotp_trit_input m10 =>
  phoare [DecapMessage(H).run :
    serialized = bs0 /\ input = input0 /\ msg = msg0 /\ r2 = r20 /\ m1 = m10 ==>
    res = decap_message_spec r20 m10] = 1%r.
proof.
  move=> hh hl hr hm; by conseq (decap_message_lossless H hl)
    (decap_message_functional H bs0 input0 msg0 r20 m10 hh hr hm).
qed.

lemma decap_message_mathematical_correct bs0 input0 msg0 r20 m10 :
  poly_tobytes_input_qrange r20 => poly_sotp_trit_input m10 =>
  phoare [DecapMessage(MathematicalSHAKE).run :
    serialized = bs0 /\ input = input0 /\ msg = msg0 /\ r2 = r20 /\ m1 = m10 ==>
    res = decap_message_spec r20 m10] = 1%r.
proof.
  move=> hr hm; exact (decap_message_correct MathematicalSHAKE bs0 input0 msg0 r20 m10
    mathematical_shake_functional mathematical_shake_lossless hr hm).
qed.
