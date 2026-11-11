require import AllCore Distr FMap.
from Jasmin require import JWord.
require import Array32 Array192 Array768 Array1152 Array1153 Array2336 Array14466.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768KeygenCompleteFinish.
require import NTRUPlus768KeygenCompleteRetry NTRUPlus768FreshRetryLaw NTRUPlus768AcceptanceProbability.
require import NTRUPlus768KeygenHBridge NTRUPlus768PolyToBytesProof.
require import NTRUPlus768EncapHashFPrepareProof NTRUPlus768KeygenPackSKProof NTRUPlus768KeygenClearProof.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDomains NTRUPlus768ROMPayloadHash.

(* F contributes only to the unused KEM secret-key suffix. The base
   collision and one-wayness experiments need only the public key. *)
module SecZeroF = {
 proc shake(input:W8.t Array1153.t) : W8.t Array32.t = {
  return Array32.init(fun _=>W8.zero);
 }
}.
module SecBaseKeygen = {
 proc run() : W8.t Array1152.t = {
  var pk:W8.t Array1152.t;var sk:W8.t Array2336.t;
  (pk,sk)<@Keygen(UniformSeedRNG,FreshExpand,SecZeroF).run();
  return pk;
 }
}.
module SecPublicROMKeygen = {
 proc run() : W8.t Array1152.t = {
  var pk:W8.t Array1152.t;var sk:W8.t Array2336.t;
  (pk,sk)<@Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run();
  return pk;
 }
}.
module SecFinishCore = {
 proc run(f finv g ginv:W16.t Array768.t) : W8.t Array1152.t = {
  var h,hinv:W16.t Array768.t;var pk:W8.t Array1152.t;
  (h,hinv)<@KeygenHComposition.derive_products(f,finv,g,ginv,witness,witness);
  pk<@NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes(witness,h);
  return pk;
 }
}.
module SecFinishROM = {
 proc run(f finv g ginv:W16.t Array768.t) : W8.t Array1152.t = {
  var pk:W8.t Array1152.t;var ignored:W8.t Array32.t;
  pk<@SecFinishCore.run(f,finv,g,ginv);
  ignored<@ROF.get(pk);
  return pk;
 }
}.
module SecCoreKeygen = {
 proc run() : W8.t Array1152.t = {
  var fbuf,gbuf:W8.t Array192.t;var f,finv,g,ginv:W16.t Array768.t;var pk:W8.t Array1152.t;
  (fbuf,f,finv)<@KeygenRetry(UniformSeedRNG,FreshExpand).f();
  (gbuf,g,ginv)<@KeygenRetry(UniformSeedRNG,FreshExpand).g();
  pk<@SecFinishCore.run(f,finv,g,ginv);
  return pk;
 }
}.
module SecROMCoreKeygen = {
 proc run() : W8.t Array1152.t = {
  var fbuf,gbuf:W8.t Array192.t;var f,finv,g,ginv:W16.t Array768.t;var pk:W8.t Array1152.t;
  (fbuf,f,finv)<@KeygenRetry(UniformSeedRNG,FreshExpand).f();
  (gbuf,g,ginv)<@KeygenRetry(UniformSeedRNG,FreshExpand).g();
  pk<@SecFinishROM.run(f,finv,g,ginv);
  return pk;
 }
}.
module SecCoreLateF = {
 proc run() : W8.t Array1152.t = {
  var pk:W8.t Array1152.t;var ignored:W8.t Array32.t;
  pk<@SecCoreKeygen.run();ignored<@ROF.get(pk);return pk;
 }
}.
module SecBaseLateF = {
 proc run() : W8.t Array1152.t = {
  var pk:W8.t Array1152.t;var ignored:W8.t Array32.t;
  pk<@SecBaseKeygen.run();ignored<@ROF.get(pk);return pk;
 }
}.

lemma sec_zero_f_ll : islossless SecZeroF.shake.
proof. proc;auto. qed.

lemma sec_finish_zero :
 equiv[KeygenFinish(SecZeroF).run ~ SecFinishCore.run:
 ={arg} ==> res{1}.`1=res{2}].
proof.
 proc;wp;call{1} keygen_pack_sk_lossless.
 inline{1} SecZeroF.shake;wp.
 call{1} encap_hash_f_prepare_lossless.
 call{1} poly_tobytes_lossless;call{1} poly_tobytes_lossless.
 call(_: ={arg} ==> ={res});first by sim.
 call(_: ={arg} ==> ={res});first by sim.
 auto.
qed.

lemma sec_finish_rom :
 equiv[KeygenFinish(SHAKEFROM).run ~ SecFinishROM.run:
 ={arg,ROF.m} ==> res{1}.`1=res{2} /\ ={ROF.m}].
proof.
 proc;inline{2} SecFinishCore.run;wp;call{1} keygen_pack_sk_lossless.
 inline{1} SHAKEFROM.shake;wp.
 call(_: ={input,ROF.m} ==> ={res,ROF.m});first by sim.
 wp;ecall{1}(encap_hash_f_prepare_correct witness pk{1}).
 call{1} poly_tobytes_lossless;call{1} poly_tobytes_lossless.
 call(_: ={arg} ==> ={res});first by sim.
 call(_: ={arg} ==> ={res});first by sim.
 auto=> />;smt(payload_f_preparation peel_encode_f).
qed.

lemma sec_base_keygen_core :
 equiv[SecBaseKeygen.run ~ SecCoreKeygen.run:true ==> ={res}].
proof.
 proc;inline{1} Keygen(UniformSeedRNG,FreshExpand,SecZeroF).run
  KeygenInstrumented(UniformSeedRNG,FreshExpand,SecZeroF).run.
 wp;call{1} keygen_clear_lossless.
 call sec_finish_zero.
 call(_: true ==> ={res});first by sim.
 call(_: true ==> ={res});first by sim.
 auto.
qed.

lemma sec_public_rom_core :
 equiv[SecPublicROMKeygen.run ~ SecROMCoreKeygen.run:
 ={ROF.m} ==> ={res,ROF.m}].
proof.
 proc;inline{1} Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run
  KeygenInstrumented(UniformSeedRNG,FreshExpand,SHAKEFROM).run.
 wp;call{1} keygen_clear_lossless.
 call sec_finish_rom.
 call(_: true ==> ={res});first by sim.
 call(_: true ==> ={res});first by sim.
 auto.
qed.

lemma sec_rom_core_late :
 equiv[SecROMCoreKeygen.run ~ SecCoreLateF.run:
 ={ROF.m} ==> ={res,ROF.m}].
proof.
 proc;inline{1} SecFinishROM.run;inline{2} SecCoreKeygen.run;wp.
 call(_: ={arg,ROF.m} ==> ={res,ROF.m});first by sim.
 wp;call(_: ={arg} ==> ={res});first by sim.
 wp;call(_: true ==> ={res});first by sim.
 call(_: true ==> ={res});first by sim.
 auto.
qed.

lemma sec_core_late_base :
 equiv[SecCoreLateF.run ~ SecBaseLateF.run:
 ={ROF.m} ==> ={res,ROF.m}].
proof.
 proc;call(_: ={arg,ROF.m} ==> ={res,ROF.m});first by sim.
 symmetry;call sec_base_keygen_core;auto.
qed.

lemma sec_keygen_hoist :
 equiv[SecPublicROMKeygen.run ~ SecBaseLateF.run:
 ={ROF.m} ==> ={res,ROF.m}].
proof.
 transitivity SecROMCoreKeygen.run (={ROF.m} ==> ={res,ROF.m}) (={ROF.m} ==> ={res,ROF.m})=> //;first by smt().
 + exact sec_public_rom_core.
 transitivity SecCoreLateF.run (={ROF.m} ==> ={res,ROF.m}) (={ROF.m} ==> ={res,ROF.m})=> //;first by smt().
 + exact sec_rom_core_late.
 exact sec_core_late_base.
qed.

lemma sec_base_keygen_ll : islossless SecBaseKeygen.run.
proof.
 proc;call(keygen_public_lossless UniformSeedRNG FreshExpand SecZeroF
  (fresh_retry_f_ll fresh_f_accept_positive)
  (fresh_retry_g_ll fresh_g_accept_positive) sec_zero_f_ll);auto.
qed.
