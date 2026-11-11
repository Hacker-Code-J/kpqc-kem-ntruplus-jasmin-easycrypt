require import AllCore Distr DProd SDist.
from Jasmin require import JWord.
require import Array192 Array768 Array1152 Array14466.
require import NTRUPlus768ACWC2BaseModel.
require import NTRUPlus768PKEModel NTRUPlus768PKEAlgebra NTRUPlus768PKECallProof.
require import NTRUPlus768PKEAverageModel NTRUPlus768PKEAverageCorrectness.
require import NTRUPlus768PKEKeyDistribution NTRUPlus768PolyCBD1Algebra.
require import NTRUPlus768PolyCBD1CheckedProof.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteProof.
require import NTRUPlus768ROMDistributions NTRUPlus768ROMOracles NTRUPlus768ROMKeygen.
require import NTRUPlus768FreshRetryLaw NTRUPlus768KEMProposalContext.
require import NTRUPlus768StoppedKeygenModel.

lemma acwc2_pke_trial_value (x0:kem_keygen_observation) :
 hoare[PKEAverageTrial.run:x=x0 ==>
 res=acwc2_base_failure x0.`1.`1 (poly_cbd1_spec x0.`3) (poly_cbd1_spec x0.`2)].
proof.
 proc; seq 4:(x=x0 /\ r=poly_cbd1_spec x0.`2 /\ m=poly_cbd1_spec x0.`3 /\
 ct=pke_enc_spec x0.`1.`1.`kg_pk (poly_cbd1_spec x0.`3) (poly_cbd1_spec x0.`2) /\ failed).
 + wp; call(pke_enc_functional x0.`1.`1.`kg_pk (poly_cbd1_spec x0.`3)
      (poly_cbd1_spec x0.`2) (pke_domain_cbd x0.`3) (pke_domain_cbd x0.`2)).
   call(poly_cbd1_functional witness x0.`3); call(poly_cbd1_functional witness x0.`2); auto.
 if.
 + wp; call(pke_dec_functional
      (oget(pke_enc_spec x0.`1.`1.`kg_pk (poly_cbd1_spec x0.`3) (poly_cbd1_spec x0.`2)))
      (pke_secret_bytes x0.`1.`1)); auto=> />.
   move=> &hr hf hct.
   by rewrite acwc2_base_failureE (negbTE _ hct).
 auto=> /> &hr hf hct.
 by rewrite acwc2_base_failureE hct.
qed.
lemma acwc2_pke_trial_correct (x0:kem_keygen_observation) :
 phoare[PKEAverageTrial.run:x=x0 ==>
 res=acwc2_base_failure x0.`1.`1 (poly_cbd1_spec x0.`3) (poly_cbd1_spec x0.`2)]=1%r.
proof. by conseq pke_average_trial_lossless (acwc2_pke_trial_value x0). qed.

lemma acwc2_pke_failure_projection (E<:KeygenExpand {-ROF}) :
 equiv[PKEAverage(E).run ~ KeygenThenUniform(E).run:
 ={glob E,glob ROF} ==>
 res{1}=acwc2_base_failure res.`1.`1{2} (poly_cbd1_spec res.`3{2})
   (poly_cbd1_spec res.`2{2})].
proof.
 proc*; inline{1} PKEAverage(E).run; wp.
 ecall{1}(acwc2_pke_trial_correct x{1}).
 call(_: ={glob E,glob ROF} ==> ={res}); first by sim.
 auto.
qed.

module ACWC2BaseObserver = {
 proc guess(out:keygen_output) : bool = {
  var bs:W8.t Array192.t*W8.t Array192.t;
  bs <$ uniform192 `*` uniform192;
  return acwc2_base_failure out.`1 (poly_cbd1_spec bs.`2) (poly_cbd1_spec bs.`1);
 }
}.
lemma acwc2_base_observer_probability &m out0 :
 Pr[ACWC2BaseObserver.guess(out0) @ &m:res]=acwc2_base_mean out0.`1.
proof.
 rewrite acwc2_base_meanE -pke_independent_cbd_pair dmapE /pke_buffer_cbd_pair.
 byphoare(_:out=out0 ==>res)=> //; proc; rnd; auto.
qed.
lemma acwc2_reified_base_observer :
 equiv[ReifiedKeygenThenUniform.run ~ NoWrapDist.Sample(ACWC2BaseObserver).main:
 ={d} ==> acwc2_base_failure res.`1.`1{1} (poly_cbd1_spec res.`3{1})
 (poly_cbd1_spec res.`2{1})=res{2}].
proof.
 proc; inline KeygenDist.S.sample ACWC2BaseObserver.guess; wp.
 seq 3 2:(out{1}=out{2}); first by wp; rnd; auto.
 rnd : *0 *0 => /=; auto=> />.
 by rewrite dprod_dlet dmap_id.
qed.

require import RealSeries StdOrder NTRUPlus768AcceptanceProbability.
import RealOrder RField.

lemma acwc2_base_observer_expectation &m (d:keygen_output distr) :
 Pr[NoWrapDist.Sample(ACWC2BaseObserver).main(d) @ &m:res]=
 E d (fun (out:keygen_output)=>acwc2_base_mean out.`1).
proof.
 rewrite (NoWrapDist.Sample_dlet ACWC2BaseObserver &m d) dletE /E.
 apply eq_sum=>out /=.
 have hv:mu1(mk(fun b=>Pr[ACWC2BaseObserver.guess(out) @ &m:res=b])) true=acwc2_base_mean out.`1.
 + rewrite -(NoWrapDist.GenDist.adv_mu1 ACWC2BaseObserver &m true out).
   have he:Pr[ACWC2BaseObserver.guess(out) @ &m:res=true]=
     Pr[ACWC2BaseObserver.guess(out) @ &m:res] by rewrite Pr[mu_eq]; smt().
   rewrite he; exact(acwc2_base_observer_probability &m out).
 rewrite hv; ring.
qed.
lemma acwc2_reified_base_expectation &m (d:keygen_output distr) :
 Pr[ReifiedKeygenThenUniform.run(d) @ &m:
 acwc2_base_failure res.`1.`1 (poly_cbd1_spec res.`3) (poly_cbd1_spec res.`2)]=
 E d (fun (out:keygen_output)=>acwc2_base_mean out.`1).
proof.
 rewrite -(acwc2_base_observer_expectation &m d).
 byequiv acwc2_reified_base_observer=> //.
qed.

lemma acwc2_key_base_mean_integrable (d:keygen_output distr) :
 hasE d (fun (out:keygen_output)=>acwc2_base_mean out.`1).
proof.
 apply(hasE_le d (fun (out:keygen_output)=>acwc2_base_mean out.`1)
   (fun (_:keygen_output)=>1%r) (hasEC d 1%r)).
 move=>out; have [h0 h1]:=acwc2_base_mean_range out.`1.
 by rewrite (ger0_norm _ h0) normr1.
qed.

lemma acwc2_fresh_key_source_lossless : islossless KeygenSource(FreshExpand).guess.
proof.
 proc; call(fresh_keygen_instrumented_ll fresh_f_accept_positive fresh_g_accept_positive); auto.
qed.
lemma acwc2_fresh_key_source_valid :
 hoare[KeygenSource(FreshExpand).guess:true ==>pke_key_relation res.`1].
proof.
 proc; call(rom_keygen_instrumented UniformSeedRNG FreshExpand); auto=> />; smt(pke_key_from_rom).
qed.

(* This reification preserves the actual fresh KeyGen output law at the
   specified initial memory, including its accepted key and cleared array.
   It is a probability distribution by the already proved fresh retry LL. *)
lemma acwc2_fresh_key_law_lossless &m :
 is_lossless(mk(fun z=>Pr[KeygenSource(FreshExpand).guess(witness) @ &m:res=z])).
proof.
 rewrite /is_lossless -(keygen_source_mu FreshExpand &m witness predT).
 by byphoare acwc2_fresh_key_source_lossless.
qed.
lemma acwc2_fresh_key_law_supported &m out :
 out \in mk(fun z=>Pr[KeygenSource(FreshExpand).guess(witness) @ &m:res=z]) =>
 pke_key_relation out.`1.
proof.
 move=>hout.
 have hz:Pr[KeygenSource(FreshExpand).guess(witness) @ &m:!pke_key_relation res.`1]=0%r.
 + byphoare(_:true ==> !pke_key_relation res.`1)=> //; hoare.
   conseq acwc2_fresh_key_source_valid=> />; smt().
 have hd:mu (mk(fun z=>Pr[KeygenSource(FreshExpand).guess(witness) @ &m:res=z]))
   (fun (x:keygen_output)=>!pke_key_relation x.`1)=0%r.
 + rewrite -(keygen_source_mu FreshExpand &m witness (fun (x:keygen_output)=>!pke_key_relation x.`1)); exact hz.
 have h:=eq0_mu _ _ hd out hout; smt().
qed.

lemma acwc2_fresh_key_mean_identity &m :
 E (mk(fun z=>Pr[KeygenSource(FreshExpand).guess(witness) @ &m:res=z]))
   (fun (out:keygen_output)=>acwc2_base_mean out.`1)=Pr[PKEAverage(FreshExpand).run() @ &m:res].
proof.
 have hp:Pr[PKEAverage(FreshExpand).run() @ &m:res]=
   Pr[KeygenThenUniform(FreshExpand).run() @ &m:
   acwc2_base_failure res.`1.`1 (poly_cbd1_spec res.`3) (poly_cbd1_spec res.`2)].
 + byequiv(acwc2_pke_failure_projection FreshExpand)=> //.
 rewrite hp (keygen_then_uniform_reified FreshExpand &m
   (fun (x:kem_keygen_observation)=>acwc2_base_failure x.`1.`1 (poly_cbd1_spec x.`3) (poly_cbd1_spec x.`2))).
 by rewrite acwc2_reified_base_expectation.
qed.
lemma acwc2_fresh_key_mean_bound &m :
 E (mk(fun z=>Pr[KeygenSource(FreshExpand).guess(witness) @ &m:res=z]))
   (fun (out:keygen_output)=>acwc2_base_mean out.`1)<1%r/(2%r^354).
proof. rewrite acwc2_fresh_key_mean_identity; exact(pke_fresh_average_correctness &m). qed.
