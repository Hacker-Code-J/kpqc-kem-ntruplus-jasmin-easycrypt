require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.
require import Array129 Array224 Array192 Array768 Array1152 Array96 Array32.
require import NTRUPlus768DecapCompleteSpec NTRUPlus768DecapCompleteHash.
require import NTRUPlus768DecapHashHPrepare NTRUPlus768DecapHashHPrepareProof NTRUPlus768DecapHashHBridge.
require import NTRUPlus768PolyCBD1Checked NTRUPlus768PolyCBD1CheckedProof NTRUPlus768PolyCBD1Algebra.
require import NTRUPlus768NTT NTRUPlus768NTTProof.
require import NTRUPlus768PolyToBytes NTRUPlus768PolyToBytesProof.
require import NTRUPlus768DecapFinish NTRUPlus768DecapFinishCorrectness.
require import NTRUPlus768EncapGuardSpec NTRUPlus768DecapMaskBridge.

(* Model the remaining native glue's array values. The SOTP flag is an
   argument to finish; it does not suppress HashH or regeneration. *)
module CompleteTail(H : CompleteSHAKEH) = {
  proc run(recovered : W8.t Array1152.t, msg : W8.t Array96.t,
      decode_fail : W32.t, suffix : W8.t Array32.t) : W8.t Array32.t * W32.t = {
    var input : W8.t Array129.t;
    var hashout : W8.t Array224.t;
    var r1, r1ntt : W16.t Array768.t;
    var regenerated : W8.t Array1152.t;
    var ss : W8.t Array32.t;
    var status : W32.t;
    input <@ NTRUPlus768DecapHashHPrepare.M.jade_ntruplus_ntruplus768_amd64_ref_decap_hash_h_prepare(witness,msg,suffix);
    hashout <@ H.shake(input);
    r1 <@ NTRUPlus768PolyCBD1Checked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(witness,complete_hash_tail hashout);
    r1ntt <@ NTRUPlus768NTT.M.jade_ntruplus_ntruplus768_amd64_ref_ntt(witness,r1);
    regenerated <@ NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes(witness,r1ntt);
    (ss,status) <@ NTRUPlus768DecapFinish.M.jade_ntruplus_ntruplus768_amd64_ref_decap_finish(witness,hashout,recovered,regenerated,decode_fail);
    return (ss,status);
  }
}.

lemma complete_tail_functional (H <: CompleteSHAKEH) bs0 msg0 df suffix0 :
  (forall input0, hoare [H.shake : input=input0 ==> res=complete_shake_h_spec input0]) =>
  hoare [CompleteTail(H).run : recovered=bs0 /\ msg=msg0 /\
    decode_fail=W32.of_int (b2i df) /\ suffix=suffix0 ==>
    res=complete_tail_spec bs0 msg0 df suffix0].
proof.
  move=> hh; proc.
  call (finish_functional witness (hash_h_spec msg0 suffix0) bs0
    (complete_regenerated (hash_h_spec msg0 suffix0)) df).
  call (poly_tobytes_functional witness
    (ntt_spec (poly_cbd1_spec (complete_hash_tail (hash_h_spec msg0 suffix0))))
    (complete_regeneration_qrange (hash_h_spec msg0 suffix0))).
  call (ntt_functional witness (poly_cbd1_spec (complete_hash_tail (hash_h_spec msg0 suffix0)))).
  call (poly_cbd1_functional witness (complete_hash_tail (hash_h_spec msg0 suffix0))).
  call (hh (hash_h_prepare_spec msg0 suffix0)).
  call (hash_h_prepare_functional witness msg0 suffix0).
  auto => />.
  rewrite complete_shake_h_agreement.
  done.
qed.

lemma complete_tail_lossless (H <: CompleteSHAKEH) :
  islossless H.shake => islossless CompleteTail(H).run.
proof.
  move=> hl; proc; call finish_ll; call poly_tobytes_lossless; call ntt_lossless;
    call poly_cbd1_lossless; call hl; call hash_h_prepare_lossless; by auto.
qed.

lemma complete_tail_correct (H <: CompleteSHAKEH) bs0 msg0 df suffix0 :
  (forall input0, hoare [H.shake : input=input0 ==> res=complete_shake_h_spec input0]) =>
  islossless H.shake =>
  phoare [CompleteTail(H).run : recovered=bs0 /\ msg=msg0 /\
    decode_fail=W32.of_int (b2i df) /\ suffix=suffix0 ==>
    res=complete_tail_spec bs0 msg0 df suffix0]=1%r.
proof.
  move=> hh hl; by conseq (complete_tail_lossless H hl)
    (complete_tail_functional H bs0 msg0 df suffix0 hh).
qed.
