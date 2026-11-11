require import AllCore Distr.
from Jasmin require import JWord.
require import Array32 Array192 Array768.
require import NTRUPlus768KeygenCompleteAttempt NTRUPlus768KeygenCompleteSpec.
require import NTRUPlus768KeygenCompleteInverse NTRUPlus768KeygenShapeProof.
require import NTRUPlus768PolyCBD1CheckedProof NTRUPlus768PolyCBD1Algebra.
require import NTRUPlus768NTTProof NTRUPlus768NTTAlgebra.
require import NTRUPlus768KeygenSamplerAlgebra NTRUPlus768KeygenSamplerBridge.

module AttemptResult(E:KeygenExpand) = {
 proc f(seed:W8.t Array32.t) : W8.t Array192.t * W16.t Array768.t * W16.t Array768.t * W64.t = {
  var buf; buf <@ E.shake(seed); return keygen_f_attempt_result buf;
 }
 proc g(seed:W8.t Array32.t) : W8.t Array192.t * W16.t Array768.t * W16.t Array768.t * W64.t = {
  var buf; buf <@ E.shake(seed); return keygen_g_attempt_result buf;
 }
}.

lemma keygen_inverse_total rp0 ap0 :
 phoare [NTRUPlus768PolyBaseInv.M.__poly_baseinv_core : rp=rp0 /\ ap=ap0 ==>
    res=(keygen_inverse_value ap0,keygen_inverse_status ap0)]=1%r.
proof. by conseq keygen_inverse_lossless (keygen_inverse_functional rp0 ap0). qed.

lemma keygen_attempt_f_realized_equiv (E <: KeygenExpand) :
 equiv [KeygenAttempt(E).f ~ AttemptResult(E).f : ={seed,glob E} ==> ={res,glob E}].
proof.
 proc; wp.
 ecall{1}(keygen_inverse_total witness(keygen_f_ntt_spec buf{1})).
 ecall{1}(ntt_correct witness(keygen_f_pre_ntt_spec buf{1})).
 ecall{1}(keygen_shape_f_correct(poly_cbd1_spec buf{1})).
 ecall{1}(poly_cbd1_correct witness buf{1}).
 call (_: ={seed,glob E} ==> ={res,glob E}); first by sim.
 auto => /> result.
 by rewrite keygen_shape_f_sampled_spec ntt_specE /keygen_f_ntt_spec.
qed.

lemma keygen_attempt_g_realized_equiv (E <: KeygenExpand) :
 equiv [KeygenAttempt(E).g ~ AttemptResult(E).g : ={seed,glob E} ==> ={res,glob E}].
proof.
 proc; wp.
 ecall{1}(keygen_inverse_total witness(keygen_g_ntt_spec buf{1})).
 ecall{1}(ntt_correct witness(keygen_g_pre_ntt_spec buf{1})).
 ecall{1}(keygen_shape_g_correct(poly_cbd1_spec buf{1})).
 ecall{1}(poly_cbd1_correct witness buf{1}).
 call (_: ={seed,glob E} ==> ={res,glob E}); first by sim.
 auto => /> result.
 by rewrite keygen_shape_g_sampled_spec ntt_specE /keygen_g_ntt_spec.
qed.

(* E may be stateful and randomized.  These contracts refer to its actual
   returned expansion, including on rejected attempts. *)
lemma keygen_attempt_f_realized (E <: KeygenExpand) :
 hoare [KeygenAttempt(E).f : true ==> res=keygen_f_attempt_result res.`1].
proof.
 proc; seq 1 : (true); first by call (_:true ==> true); auto.
 ecall(keygen_inverse_functional witness(keygen_f_ntt_spec buf)).
 ecall(ntt_functional witness(keygen_f_pre_ntt_spec buf)).
 ecall(keygen_shape_f_functional(poly_cbd1_spec buf)).
 ecall(poly_cbd1_functional witness buf).
 auto => /> &hr.
 by rewrite keygen_shape_f_sampled_spec ntt_specE /keygen_f_ntt_spec.
qed.

lemma keygen_attempt_g_realized (E <: KeygenExpand) :
 hoare [KeygenAttempt(E).g : true ==> res=keygen_g_attempt_result res.`1].
proof.
 proc; seq 1 : (true); first by call (_:true ==> true); auto.
 ecall(keygen_inverse_functional witness(keygen_g_ntt_spec buf)).
 ecall(ntt_functional witness(keygen_g_pre_ntt_spec buf)).
 ecall(keygen_shape_g_functional(poly_cbd1_spec buf)).
 ecall(poly_cbd1_functional witness buf).
 auto => /> &hr.
 by rewrite keygen_shape_g_sampled_spec ntt_specE /keygen_g_ntt_spec.
qed.

lemma keygen_attempt_f_realized_total (E <: KeygenExpand) :
 islossless E.shake =>
 phoare [KeygenAttempt(E).f : true ==> res=keygen_f_attempt_result res.`1]=1%r.
proof. move=> el; by conseq (keygen_attempt_f_lossless E el) (keygen_attempt_f_realized E). qed.

lemma keygen_attempt_g_realized_total (E <: KeygenExpand) :
 islossless E.shake =>
 phoare [KeygenAttempt(E).g : true ==> res=keygen_g_attempt_result res.`1]=1%r.
proof. move=> el; by conseq (keygen_attempt_g_lossless E el) (keygen_attempt_g_realized E). qed.
