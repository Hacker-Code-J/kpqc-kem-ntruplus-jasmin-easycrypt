require import AllCore List Distr.
from Jasmin require import JWord.
require import Array1153 Array1152 Array32 Array96 Array224.
require import NTRUPlus768EncapCompleteSpec NTRUPlus768HashFProof NTRUPlus768EncapHashFPrepare NTRUPlus768EncapHashFPrepareProof.
require import NTRUPlus768DecapCompleteHash NTRUPlus768DecapHashHPrepare NTRUPlus768DecapHashHPrepareProof NTRUPlus768DecapHashHBridge.
require import Keccak1600_Spec EclibExtra.
module type EncapSHAKEF = { proc shake(input : W8.t Array1153.t) : W8.t Array32.t }.
op encap_shake_f_spec (input : W8.t Array1153.t) : W8.t Array32.t =
  Array32.of_list W8.zero (SHAKE256 (Array1153.to_list input) 32).
lemma encap_shake_f_agreement pk : encap_shake_f_spec(encap_hash_f_input_spec pk)=hash_f_spec pk.
proof. by rewrite /encap_shake_f_spec encap_hash_f_input_to_list /hash_f_spec /hash_f_output_list /hash_f_input /hash_f_payload_list. qed.
module MathematicalSHAKEF = {
  proc shake(input : W8.t Array1153.t) : W8.t Array32.t = {
    var out; out <@ Keccak1600Bytes.shake256(Array1153.to_list input,32);
    return Array32.of_list W8.zero out;
  }
}.
lemma encap_mathematical_f_functional input0 :
  hoare [MathematicalSHAKEF.shake : input=input0 ==> res=encap_shake_f_spec input0].
proof. proc; ecall (SHAKE256_h (Array1153.to_list input0) 32); by auto => />. qed.
lemma encap_mathematical_f_lossless : islossless MathematicalSHAKEF.shake.
proof. proc; call SHAKE256_ll; by auto. qed.
module EncapSeed(F:EncapSHAKEF,H:CompleteSHAKEH) = {
  proc run(pk : W8.t Array1152.t, coins : W8.t Array96.t) : W8.t Array224.t = {
    var inputf : W8.t Array1153.t; var inputh : W8.t Array129.Array129.t;
    var suffix : W8.t Array32.t; var hashout : W8.t Array224.t;
    inputf <@ NTRUPlus768EncapHashFPrepare.M.jade_ntruplus_ntruplus768_amd64_ref_encap_hash_f_prepare(witness,pk);
    suffix <@ F.shake(inputf);
    inputh <@ NTRUPlus768DecapHashHPrepare.M.jade_ntruplus_ntruplus768_amd64_ref_decap_hash_h_prepare(witness,coins,suffix);
    hashout <@ H.shake(inputh); return hashout;
  }
}.
lemma encap_seed_functional (F<:EncapSHAKEF) (H<:CompleteSHAKEH) pk0 coins0 :
  (forall x, hoare [F.shake : input=x ==> res=encap_shake_f_spec x]) =>
  (forall x, hoare [H.shake : input=x ==> res=complete_shake_h_spec x]) =>
  hoare [EncapSeed(F,H).run : pk=pk0 /\ coins=coins0 ==> res=encap_full_hash pk0 coins0].
proof.
  move=> hf hh; proc; call(hh(hash_h_prepare_spec coins0(hash_f_spec pk0)));
    call(hash_h_prepare_functional witness coins0(hash_f_spec pk0));
    call(hf(encap_hash_f_input_spec pk0)); call(encap_hash_f_prepare_functional witness pk0);
    auto => />; by rewrite encap_shake_f_agreement complete_shake_h_agreement.
qed.
lemma encap_seed_lossless (F<:EncapSHAKEF) (H<:CompleteSHAKEH) :
  islossless F.shake => islossless H.shake => islossless EncapSeed(F,H).run.
proof. move=> fl hl; proc; call hl; call hash_h_prepare_lossless; call fl; call encap_hash_f_prepare_lossless; by auto. qed.
