require import AllCore Distr DProd.
from Jasmin require import JWord.
require import Array768 Array1152.
require import NTRUPlus768PKEModel NTRUPlus768PKEKeyDistribution.
require import NTRUPlus768CoefficientRecovery NTRUPlus768CyclotomicFactorization NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768SecModel NTRUPlus768SecBaseGames.
require import NTRUPlus768GenDistribution NTRUPlus768GenModel.
require import NTRUPlus768OWUniform NTRUPlus768OWCodec NTRUPlus768OWKeyAlgebra NTRUPlus768OWKeyConditioning.

(* The hardness challenges are canonical polynomial representatives.
   The existing OW attacker still receives the actual serialized bytes. *)
module type OWNTRUAdversary = {proc run(h:NTRUPoly.poly):bool}.
module type OWRLWEAdversary = {proc run(a b:NTRUPoly.poly):NTRUPoly.poly}.
module OWKernel(B:SecOWAdversary) = {
 proc run(pk:W8.t Array1152.t):bool = {
  var code,r,answer:pke_poly;var ct:W8.t Array1152.t;
  code<$pke_psi1;r<$pke_psi1;ct<-pke_ciphertext pk code r;
  answer<@B.run(pk,ct);return answer=code;
 }
}.
module OWFieldKernel(B:SecOWAdversary) = {
 proc guess(a:NTRUPoly.poly):bool = {
  var win:bool;win<-false;
  if(ow_unit_test a){win<@OWKernel(B).run(ow_encode a);}
  return win;
 }
}.
module OWNTRUReduction(B:SecOWAdversary) : OWNTRUAdversary = {
 proc run(h:NTRUPoly.poly):bool = {
  var win;win<@OWFieldKernel(B).guess(ow_scale3 h);return win;
 }
}.
(* f is the conditioned 1+3*f0 law, required for the quotient to be
   defined. g has the unconditioned CBD1 law; its acceptance is accounted
   for by the explicit alpha_g factor in the exact reduction identity. *)
module OWNTRURealGame(D:OWNTRUAdversary) = {
 proc run():bool = {
  var fg:NTRUPoly.poly*NTRUPoly.poly;var win:bool;
  fg<$ow_raw_fg_law;
  win<@D.run(ow_ntru_key fg.`1 fg.`2);return win;
 }
}.
module OWNTRUUniformGame(D:OWNTRUAdversary) = {
 proc run():bool = {
  var h:NTRUPoly.poly;var win:bool;
  h<$ow_uniform_rq;win<@D.run(h);return win;
 }
}.
module OWUniformTest(B:SecOWAdversary) = {
 proc run():bool = {
  var a:NTRUPoly.poly;var win:bool;
  a<$ow_uniform_rq;win<@OWFieldKernel(B).guess(a);return win;
 }
}.
(* On a nonunit the distinguisher returns false, but the uniform
   distribution itself is never conditioned on invertibility. *)
module OWUniformSource(B:SecOWAdversary) = {
 proc run():bool = {
  var a:NTRUPoly.poly;var code,r,answer:pke_poly;
  var pk,ct:W8.t Array1152.t;var win:bool;
  a<$ow_uniform_rq;code<$pke_psi1;r<$pke_psi1;win<-false;
  if(ow_unit_test a){
   pk<-ow_encode a;ct<-pke_ciphertext pk code r;
   answer<@B.run(pk,ct);win<-answer=code;
  }
  return win;
 }
}.
module OWRLWESolver(B:SecOWAdversary) : OWRLWEAdversary = {
 proc run(a b:NTRUPoly.poly):NTRUPoly.poly = {
  var code:pke_poly;var answer:NTRUPoly.poly;
  answer<-NTRUPoly.poly0;
  if(ow_unit_test a){
   code<@B.run(ow_encode a,ow_encode b);
   answer<-ow_recover a b code;
  }
  return answer;
 }
}.
(* ow_rlwe_value is certified to be the unique reduced representative of
   a*input_poly(secret)+input_poly(error) in R_q. Auxiliary random oracles,
   if required by B, remain entirely inside the concrete solver. *)
module OWRLWEGame(C:OWRLWEAdversary) = {
 proc run():bool = {
  var a,b,answer:NTRUPoly.poly;var error,secret:pke_poly;
  a<$ow_uniform_rq;error<$pke_psi1;secret<$pke_psi1;
  b<-ow_rlwe_value a secret error;
  answer<@C.run(a,b);return answer=input_poly secret;
 }
}.

module type OWBoolPolyPort = {proc guess(a:NTRUPoly.poly):bool}.
module type OWByteKernelPort = {proc run(pk:W8.t Array1152.t):bool}.
lemma ow_poly_same(K<:OWBoolPolyPort):equiv[K.guess ~ K.guess: ={arg,glob K} ==> ={res,glob K}].
proof. proc true;auto. qed.
lemma ow_kernel_same(K<:OWByteKernelPort):equiv[K.run ~ K.run: ={arg,glob K} ==> ={res,glob K}].
proof. proc true;auto. qed.
