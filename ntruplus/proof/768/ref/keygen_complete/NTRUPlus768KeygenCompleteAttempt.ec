require import AllCore Distr.
from Jasmin require import JWord.
require import Array32 Array192 Array768.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteInverse.
require import NTRUPlus768KeygenShapeF NTRUPlus768KeygenShapeG NTRUPlus768KeygenShapeProof.
require import NTRUPlus768PolyCBD1Checked NTRUPlus768PolyCBD1CheckedProof NTRUPlus768PolyCBD1Algebra.
require import NTRUPlus768NTT NTRUPlus768NTTProof NTRUPlus768NTTAlgebra.
require import NTRUPlus768KeygenSamplerAlgebra NTRUPlus768KeygenSamplerBridge NTRUPlus768KeygenInverseBridge.
require import NTRUPlus768PolyBaseInv NTRUPlus768PolyBaseInvProof.

module KeygenAttempt(E : KeygenExpand) = {
 proc f(seed : W8.t Array32.t) : W8.t Array192.t * W16.t Array768.t * W16.t Array768.t * W64.t = {
  var buf:W8.t Array192.t; var pre,ntt,inverse:W16.t Array768.t; var status:W64.t;
  buf <@ E.shake(seed);
  pre <@ NTRUPlus768PolyCBD1Checked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(witness,buf);
  pre <@ NTRUPlus768KeygenShapeF.M.jade_ntruplus_ntruplus768_amd64_ref_keygen_shape_f(pre);
  ntt <@ NTRUPlus768NTT.M.jade_ntruplus_ntruplus768_amd64_ref_ntt(witness,pre);
  (inverse,status) <@ NTRUPlus768PolyBaseInv.M.__poly_baseinv_core(witness,ntt);
  return (buf,ntt,inverse,status);
 }
 proc g(seed : W8.t Array32.t) : W8.t Array192.t * W16.t Array768.t * W16.t Array768.t * W64.t = {
  var buf:W8.t Array192.t; var pre,ntt,inverse:W16.t Array768.t; var status:W64.t;
  buf <@ E.shake(seed);
  pre <@ NTRUPlus768PolyCBD1Checked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(witness,buf);
  pre <@ NTRUPlus768KeygenShapeG.M.jade_ntruplus_ntruplus768_amd64_ref_keygen_shape_g(pre);
  ntt <@ NTRUPlus768NTT.M.jade_ntruplus_ntruplus768_amd64_ref_ntt(witness,pre);
  (inverse,status) <@ NTRUPlus768PolyBaseInv.M.__poly_baseinv_core(witness,ntt);
  return (buf,ntt,inverse,status);
 }
}.

lemma keygen_attempt_f_functional (E <: KeygenExpand) (expand : W8.t Array32.t -> W8.t Array192.t) seed0 :
 (forall x, hoare [E.shake : seed=x ==> res=expand x]) =>
 hoare [KeygenAttempt(E).f : seed=seed0 ==> res=keygen_f_attempt_result(expand seed0)].
proof.
 move=> he; proc.
 call(keygen_inverse_functional witness(keygen_f_ntt_spec(expand seed0))).
 call(ntt_functional witness(keygen_f_pre_ntt_spec(expand seed0))).
 call(keygen_shape_f_functional(poly_cbd1_spec(expand seed0))).
 call(poly_cbd1_functional witness(expand seed0)).
 call(he seed0); auto => />.
 by rewrite keygen_shape_f_sampled_spec ntt_specE /keygen_f_ntt_spec.
qed.
lemma keygen_attempt_g_functional (E <: KeygenExpand) (expand : W8.t Array32.t -> W8.t Array192.t) seed0 :
 (forall x, hoare [E.shake : seed=x ==> res=expand x]) =>
 hoare [KeygenAttempt(E).g : seed=seed0 ==> res=keygen_g_attempt_result(expand seed0)].
proof.
 move=> he; proc.
 call(keygen_inverse_functional witness(keygen_g_ntt_spec(expand seed0))).
 call(ntt_functional witness(keygen_g_pre_ntt_spec(expand seed0))).
 call(keygen_shape_g_functional(poly_cbd1_spec(expand seed0))).
 call(poly_cbd1_functional witness(expand seed0)).
 call(he seed0); auto => />.
 by rewrite keygen_shape_g_sampled_spec ntt_specE /keygen_g_ntt_spec.
qed.

lemma keygen_attempt_f_accepted (E <: KeygenExpand) :
 hoare [KeygenAttempt(E).f : true ==> res.`4=W64.zero => keygen_f_accepted res.`1 res.`2 res.`3].
proof.
 proc.
 seq 1 : (true); first by call (_:true ==> true); auto.
 seq 3 : (ntt=keygen_f_ntt_spec buf).
 + ecall (ntt_functional witness(keygen_f_pre_ntt_spec buf)).
   ecall (keygen_shape_f_functional(poly_cbd1_spec buf)).
   ecall (poly_cbd1_functional witness buf).
   auto => /> &hr.
   rewrite keygen_shape_f_sampled_spec ntt_specE /keygen_f_ntt_spec; done.
 ecall (keygen_f_inverse_success_bridge buf witness).
 by auto => />; rewrite /keygen_f_accepted; smt().
qed.
lemma keygen_attempt_g_accepted (E <: KeygenExpand) :
 hoare [KeygenAttempt(E).g : true ==> res.`4=W64.zero => keygen_g_accepted res.`1 res.`2 res.`3].
proof.
 proc.
 seq 1 : (true); first by call (_:true ==> true); auto.
 seq 3 : (ntt=keygen_g_ntt_spec buf).
 + ecall (ntt_functional witness(keygen_g_pre_ntt_spec buf)).
   ecall (keygen_shape_g_functional(poly_cbd1_spec buf)).
   ecall (poly_cbd1_functional witness buf).
   auto => /> &hr.
   rewrite keygen_shape_g_sampled_spec ntt_specE /keygen_g_ntt_spec; done.
 ecall (keygen_g_inverse_success_bridge buf witness).
 by auto => />; rewrite /keygen_g_accepted; smt().
qed.
lemma keygen_attempt_f_lossless (E <: KeygenExpand) : islossless E.shake => islossless KeygenAttempt(E).f.
proof. move=> he; proc; call keygen_inverse_lossless; call ntt_lossless; call keygen_shape_f_lossless;
 call poly_cbd1_lossless; call he; auto. qed.
lemma keygen_attempt_g_lossless (E <: KeygenExpand) : islossless E.shake => islossless KeygenAttempt(E).g.
proof. move=> he; proc; call keygen_inverse_lossless; call ntt_lossless; call keygen_shape_g_lossless;
 call poly_cbd1_lossless; call he; auto. qed.
