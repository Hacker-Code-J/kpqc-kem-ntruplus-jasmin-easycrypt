require import AllCore Distr List StdOrder.
from Jasmin require import JWord.
require import Array768 Array1152.
require import NTRUPlus768PKEModel NTRUPlus768SecModel NTRUPlus768SecExtractModel.
require import NTRUPlus768OWCodec NTRUPlus768OWCodecProof NTRUPlus768OWUniform.
require import NTRUPlus768OWGames NTRUPlus768INJGames NTRUPlus768OWCodecCalls.
require import NTRUPlus768CyclotomicFactorization NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768RTKernelTypes NTRUPlus768RTKernels NTRUPlus768RTWordCodec.

(* Executable hardness inputs are 768 words. Polynomial reification is
   used only in the specification/projection and in the challenger-side
   representation bridge, never read by these reduction procedures. *)
module RTWordINJNTRUReduction(B:SecINJAdversary) = {
 proc run(h:pke_poly):bool*rt_kernel_profile = {
  var a:pke_poly;var pk:W8.t Array1152.t;var collision:sec_collision;
  var accept,win:bool;var checked:bool*rt_kernel_profile;
  var scales,units,encodes,calls:int;var profile:rt_kernel_profile;
  scales<-0;units<-0;encodes<-0;calls<-0;win<-false;
  profile<-rtk_profile 0 0 0 0 0 0 0 0 0 0;
  a<@RTWordScale3.run(h);scales<-scales+1;
  accept<@RTWordUnit.run(a);units<-units+1;
  if(accept){
   pk<@RTWordEncode.run(a);encodes<-encodes+1;
   collision<@B.run(pk);calls<-calls+1;
   checked<@RTINJCheck.run(pk,collision);win<-checked.`1;profile<-checked.`2;
  }
  return(win,rtk_add profile(rtk_profile scales units encodes 0 0 0 0 0 0 calls));
 }
}.
module RTWordOWNTRUReduction(B:SecOWAdversary) = {
 proc run(h:pke_poly):bool*rt_kernel_profile = {
  var a:pke_poly;var pk:W8.t Array1152.t;
  var accept,win:bool;var checked:bool*rt_kernel_profile;
  var scales,units,encodes:int;var profile:rt_kernel_profile;
  scales<-0;units<-0;encodes<-0;win<-false;
  profile<-rtk_profile 0 0 0 0 0 0 0 0 0 0;
  a<@RTWordScale3.run(h);scales<-scales+1;
  accept<@RTWordUnit.run(a);units<-units+1;
  if(accept){
   pk<@RTWordEncode.run(a);encodes<-encodes+1;
   checked<@RTOWKernel(B).run(pk);win<-checked.`1;profile<-checked.`2;
  }
  return(win,rtk_add profile(rtk_profile scales units encodes 0 0 0 0 0 0 0));
 }
}.
module RTWordOWRLWESolver(B:SecOWAdversary) = {
 proc run(a b:pke_poly):pke_poly*rt_kernel_profile = {
  var pk,ct:W8.t Array1152.t;var code,answer:pke_poly;var recovered:pke_poly option;var accept:bool;
  var units,encodes,recovers,calls:int;
  units<-0;encodes<-0;recovers<-0;calls<-0;answer<-Array768.init(fun _=>W16.zero);
  accept<@RTWordUnit.run(a);units<-units+1;
  if(accept){
   pk<@RTWordEncode.run(a);encodes<-encodes+1;
   ct<@RTWordEncode.run(b);encodes<-encodes+1;
   code<@B.run(pk,ct);calls<-calls+1;
   recovered<@RTWordRecover.run(a,b,code);recovers<-recovers+1;
   if(recovered<>None){answer<-oget recovered;}
  }
  return(answer,rtk_profile 0 units encodes recovers 0 0 0 0 0 calls);
 }
}.

lemma rt_word_zero_poly : input_poly(Array768.init(fun _=>W16.zero))=NTRUPoly.poly0.
proof.
 have hz:ow_coeff_words NTRUPoly.poly0=Array768.init(fun _=>W16.zero).
 + apply Array768.tP=>i hi.
   rewrite /ow_coeff_words !Array768.initiE //=.
   rewrite NTRUPoly.poly0E CycloFq.zeroE /=;done.
 rewrite -hz;apply ow_coeff_words_poly;rewrite /ow_rq_domain NTRUPoly.deg0;done.
qed.

lemma rt_word_inj_projection (B<:SecINJAdversary) :
 equiv[RTWordINJNTRUReduction(B).run ~ RTINJNTRUReduction(B).run:
 h{1}=ow_coeff_words h{2} /\ ={glob B} ==> ={res,glob B}].
proof.
 proc;seq 10 10:(a{1}=ow_coeff_words a{2} /\
 ={scales,units,encodes,calls,win,profile,accept,glob B}).
 + wp;call rt_word_unit_projection;wp.
   ecall{1}(rt_word_scale3_correct h{2});auto.
 if;first by auto.
 + wp;call(_: ={arg} ==> ={res});first by sim.
   wp;call(_: ={arg,glob B} ==> ={res,glob B});first by proc true;auto.
   wp;call rt_word_encode_projection;auto.
 auto.
qed.
lemma rt_word_ow_projection (B<:SecOWAdversary) :
 equiv[RTWordOWNTRUReduction(B).run ~ RTOWNTRUReduction(B).run:
 h{1}=ow_coeff_words h{2} /\ ={glob B} ==> ={res,glob B}].
proof.
 proc;seq 9 9:(a{1}=ow_coeff_words a{2} /\
 ={scales,units,encodes,win,profile,accept,glob B}).
 + wp;call rt_word_unit_projection;wp.
   ecall{1}(rt_word_scale3_correct h{2});auto.
 if;first by auto.
 + wp;call(_: ={arg,glob B} ==> ={res,glob B});first by sim.
   wp;call rt_word_encode_projection;auto.
 auto.
qed.
lemma rt_word_rlwe_projection (B<:SecOWAdversary) :
 equiv[RTWordOWRLWESolver(B).run ~ RTOWRLWESolver(B).run:
 a{1}=ow_coeff_words a{2} /\ b{1}=ow_coeff_words b{2} /\ ={glob B} ==>
 input_poly res{1}.`1=res{2}.`1 /\ res{1}.`2=res{2}.`2 /\ ={glob B}].
proof.
 proc;seq 7 7:(a{1}=ow_coeff_words a{2} /\ b{1}=ow_coeff_words b{2} /\
 ={units,encodes,recovers,calls,accept,glob B} /\
 answer{1}=Array768.init(fun _=>W16.zero) /\ answer{2}=NTRUPoly.poly0).
 + wp;call rt_word_unit_projection;auto=> />;smt(rt_word_zero_poly).
 if;first by auto.
 + wp;call rt_word_recover_projection.
   wp;call(_: ={arg,glob B} ==> ={res,glob B});first by proc true;auto.
   wp;call rt_word_encode_projection;wp;call rt_word_encode_projection;auto=> />;smt(rt_word_zero_poly).
 auto=> />;smt(rt_word_zero_poly).
qed.
