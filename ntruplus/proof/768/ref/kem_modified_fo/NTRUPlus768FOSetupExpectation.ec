require import AllCore List Distr FMap SDist RealSeries StdOrder.
from Jasmin require import JWord.
require import Array192 Array14466.
require import NTRUPlus768FOModel NTRUPlus768FOError NTRUPlus768FOErrorExpectation.
require import NTRUPlus768FOSetupDistribution NTRUPlus768StoppedKeygenModel.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768FreshRetryLaw NTRUPlus768ROMOracles.
require import NTRUPlus768ACWC2Oracle NTRUPlus768ACWC2BaseModel NTRUPlus768ACWC2KeyMean.
require import NTRUPlus768ACWC2Numerical NTRUPlus768ACWC2WorstCase NTRUPlus768KEMProposalContext.
import RealOrder RField.

op fo_setup_error (x:fo_setup_observation) = fo_error x.`1.`1 (acwc2_gfun x.`3).

lemma fo_setup_error_range x : 0%r<=fo_setup_error x<=1%r.
proof. rewrite /fo_setup_error; exact(fo_error_range _ _). qed.
lemma fo_setup_error_hasE (d:fo_setup_observation distr) : hasE d fo_setup_error.
proof. apply(acwc2_bounded_hasE d _ 1%r)=> // x; exact(fo_setup_error_range x). qed.

clone SDist.Dist as FOSetupBaseDist with type a <- fo_setup_key_observation proof *.
module FOSetupBaseObserver = {
 proc guess(key:fo_setup_key_observation) : bool = {
  var failed:bool;
  failed <@ ACWC2BaseObserver.guess(key.`1);
  return failed;
 }
}.
module FOSetupBaseExperiment = {
 proc run() : bool = {
  var key:fo_setup_key_observation; var failed:bool;
  key <@ FOSetupKeySource.guess(witness);
  failed <@ FOSetupBaseObserver.guess(key);
  return failed;
 }
}.
module FOBaseUninitialized = {
 proc run() : bool = {
  var out:keygen_output; var failed:bool;
  out <@ KeygenSource(FreshExpand).guess(witness);
  failed <@ ACWC2BaseObserver.guess(out);
  return failed;
 }
}.
module FOBaseInitialized = {
 proc run() : bool = {
  var failed:bool;
  ROF.init();
  failed <@ FOBaseUninitialized.run();
  return failed;
 }
}.

lemma fo_setup_base_observer_probability &m (key0:fo_setup_key_observation) :
 Pr[FOSetupBaseObserver.guess(key0) @ &m:res]=acwc2_base_mean key0.`1.`1.
proof.
 rewrite -(acwc2_base_observer_probability &m key0.`1).
 byequiv(_:key{1}=key0 /\ out{2}=key0.`1 ==> ={res})=> //.
 proc; inline{1} ACWC2BaseObserver.guess; wp; rnd; auto.
qed.
lemma fo_setup_base_observer_expectation &m (d:fo_setup_key_observation distr) :
 Pr[FOSetupBaseDist.Sample(FOSetupBaseObserver).main(d) @ &m:res]=
 E d(fun (key:fo_setup_key_observation)=>acwc2_base_mean key.`1.`1).
proof.
 rewrite(FOSetupBaseDist.Sample_dlet FOSetupBaseObserver &m d) dletE /E.
 apply eq_sum=>key /=.
 have hv:mu1(mk(fun b=>Pr[FOSetupBaseObserver.guess(key) @ &m:res=b]))true=
   acwc2_base_mean key.`1.`1.
 + rewrite -(FOSetupBaseDist.GenDist.adv_mu1 FOSetupBaseObserver &m true key).
   have he:Pr[FOSetupBaseObserver.guess(key) @ &m:res=true]=
     Pr[FOSetupBaseObserver.guess(key) @ &m:res] by rewrite Pr[mu_eq]; smt().
   rewrite he; exact(fo_setup_base_observer_probability &m key).
 rewrite hv; ring.
qed.
lemma fo_setup_base_expectation &m :
 Pr[FOSetupBaseExperiment.run() @ &m:res]=
 E(mk(fun (key:fo_setup_key_observation)=>Pr[FOSetupKeySource.guess(witness) @ &m:res=key]))
   (fun (key:fo_setup_key_observation)=>acwc2_base_mean key.`1.`1).
proof.
 rewrite -(fo_setup_base_observer_expectation &m _).
 byequiv(_: (glob FOSetupKeySource){1}=(glob FOSetupKeySource){m} /\
   d{2}=mk(fun (key:fo_setup_key_observation)=>Pr[FOSetupKeySource.guess(witness) @ &m:res=key]) ==> ={res})=> //.
 proc; call(_: ={key} ==> ={res}); first by sim.
 outline{2} 1 ~ FOSetupKeyDist.S.sample.
 call(fo_setup_key_sample FOSetupKeySource &m witness); auto.
qed.
lemma fo_base_uninitialized_probability &m :
 Pr[FOBaseUninitialized.run() @ &m:res]=
 E(mk(fun out=>Pr[KeygenSource(FreshExpand).guess(witness) @ &m:res=out]))
   (fun (out:keygen_output)=>acwc2_base_mean out.`1).
proof.
 rewrite -(acwc2_base_observer_expectation &m _).
 byequiv(_: (glob KeygenSource(FreshExpand)){1}=(glob KeygenSource(FreshExpand)){m} /\
   d{2}=mk(fun out=>Pr[KeygenSource(FreshExpand).guess(witness) @ &m:res=out]) ==> ={res})=> //.
 proc; call(_: ={out} ==> ={res}); first by sim.
 outline{2} 1 ~ KeygenDist.S.sample.
 call(source_sample_equiv (KeygenSource(FreshExpand)) &m witness); auto.
qed.
lemma fo_base_uninitialized_bound :
 phoare[FOBaseUninitialized.run:true ==>res] <=(1%r/(2%r^354)).
proof.
 bypr=> &m _; rewrite fo_base_uninitialized_probability.
 exact(ltrW _ _ (acwc2_fresh_key_mean_bound &m)).
qed.
lemma fo_base_initialized_bound :
 phoare[FOBaseInitialized.run:true ==>res] <=(1%r/(2%r^354)).
proof. proc; inline ROF.init; call fo_base_uninitialized_bound; auto. qed.
lemma fo_setup_base_initialized_equiv :
 equiv[FOSetupBaseExperiment.run ~ FOBaseInitialized.run:true ==> ={res}].
proof.
 proc; inline FOSetupKeySource.guess FOSetupBaseObserver.guess
   FOBaseUninitialized.run KeygenSource(FreshExpand).guess; wp.
 call(_: ={out} ==> ={res}); first by sim.
 wp; call(_: ={workspace,glob ROF} ==> ={res}); first by sim.
 inline ROF.init; auto.
qed.

(* The uniform numerical upper bound is first proved for every initial
   memory, then composed with ROF.init. No arbitrary-F law is substituted. *)
lemma fo_setup_key_base_mean_bound &m :
 E(mk(fun (key:fo_setup_key_observation)=>Pr[FOSetupKeySource.guess(witness) @ &m:res=key]))
   (fun (key:fo_setup_key_observation)=>acwc2_base_mean key.`1.`1)<=1%r/(2%r^354).
proof.
 rewrite -fo_setup_base_expectation.
 have he:Pr[FOSetupBaseExperiment.run() @ &m:res]=Pr[FOBaseInitialized.run() @ &m:res]
  by byequiv fo_setup_base_initialized_equiv=> //.
 rewrite he; by byphoare fo_base_initialized_bound.
qed.

lemma fo_setup_joint_error (dk:fo_setup_key_observation distr) :
 E(fo_setup_joint_law dk)fo_setup_error=
 E dk(fun (key:fo_setup_key_observation)=>E acwc2_gpads_law(fun pads=>fo_error key.`1.`1(acwc2_gfun pads))).
proof.
 rewrite /fo_setup_joint_law (exp_dlet _ _ _ (fo_setup_error_hasE _)).
 apply eq_exp=>key hk /=.
 rewrite(exp_dmap _ _ _ (fo_setup_error_hasE _)) /(\o) /fo_setup_error; done.
qed.
lemma fo_setup_pads_error_bound (key:fo_setup_key_observation) :
 E acwc2_gpads_law(fun pads=>fo_error key.`1.`1(acwc2_gfun pads))<=
 acwc2_base_mean key.`1.`1+acwc2_epsilon+acwc2_union_tail.
proof.
 have h:=fo_eager_error_bound key.`1.`1.
 move:h; rewrite /acwc2_eager_g_law(exp_dmap _ _ _ (fo_error_hasE _ _)) /(\o); done.
qed.
lemma fo_setup_joint_error_bound (dk:fo_setup_key_observation distr) : is_lossless dk =>
 E(fo_setup_joint_law dk)fo_setup_error<=
 E dk(fun (key:fo_setup_key_observation)=>acwc2_base_mean key.`1.`1)+acwc2_epsilon+acwc2_union_tail.
proof.
 move=>hll; rewrite fo_setup_joint_error.
 pose overhead:=acwc2_epsilon+acwc2_union_tail.
 have h0:0%r<=overhead by exact acwc2_overhead_nonnegative.
 have hm:hasE dk(fun (key:fo_setup_key_observation)=>acwc2_base_mean key.`1.`1).
 + apply(acwc2_bounded_hasE dk _ 1%r)=> // key; exact(acwc2_base_mean_range key.`1.`1).
 have hl:hasE dk(fun (key:fo_setup_key_observation)=>E acwc2_gpads_law(fun pads=>fo_error key.`1.`1(acwc2_gfun pads))).
 + apply(acwc2_bounded_hasE dk _ 1%r)=> // key.
   apply acwc2_expectation_unit_range=>pads; exact(fo_error_range _ _).
 have hr:hasE dk(fun (key:fo_setup_key_observation)=>acwc2_base_mean key.`1.`1+overhead).
 + apply(acwc2_bounded_hasE dk _ (1%r+overhead)); first smt().
   move=>key; have h:=acwc2_base_mean_range key.`1.`1; smt().
 have hb:=in_ler_exp dk _ _ hl hr _.
 + move=>key hk; have h:=fo_setup_pads_error_bound key; rewrite /overhead; smt().
 have he:E dk(fun (key:fo_setup_key_observation)=>acwc2_base_mean key.`1.`1+overhead)=
  E dk(fun (key:fo_setup_key_observation)=>acwc2_base_mean key.`1.`1)+acwc2_epsilon+acwc2_union_tail.
 + rewrite expD 1:hm 1:(hasEC dk overhead) expC hll /overhead; ring.
 by move:hb; rewrite he.
qed.

lemma fo_setup_error_expectation &m :
 E(mk(fun x=>Pr[FOSetupSource.guess(witness) @ &m:res=x]))fo_setup_error<1%r/(2%r^353).
proof.
 rewrite fo_setup_joint_distribution.
 have hb:=fo_setup_joint_error_bound _ (fo_setup_key_law_lossless &m witness).
 have hm:=fo_setup_key_base_mean_bound &m.
 have hn:=acwc2_error_scales.
 apply(ler_lt_trans _ _ _ hb).
 apply(ler_lt_trans _ _ _ _ hn).
 apply ler_add; last exact(lerr _).
 apply ler_add; first exact hm.
 exact(lerr _).
qed.

lemma fo_setup_kernel_bound ['a] &m (K:fo_setup_observation->'a distr) bad (Q:real) :
 0%r<=Q =>
 (forall x,x \in mk(fun z=>Pr[FOSetupSource.guess(witness) @ &m:res=z]) =>
   mu(K x)bad<=Q*fo_setup_error x) =>
 mu(dlet(mk(fun z=>Pr[FOSetupSource.guess(witness) @ &m:res=z]))K)bad<=Q/(2%r^353).
proof.
 move=>hQ hpoint.
 have hh:hasE(mk(fun z=>Pr[FOSetupSource.guess(witness) @ &m:res=z]))
   (fun x=>Q*fo_setup_error x).
 + apply(acwc2_bounded_hasE _ _ Q)=> // x.
   have [h0 h1]:=fo_setup_error_range x.
   split; first by apply mulr_ge0.
   move=>_; have h:=ler_wpmul2l Q hQ _ _ h1.
   by move:h; rewrite mulr1.
 have hb:=fo_kernel_average _ K bad (fun x=>Q*fo_setup_error x) hh hpoint.
 rewrite expZ in hb.
 have hn:=fo_setup_error_expectation &m.
 have hs:=ler_wpmul2l Q hQ _ _ (ltrW _ _ hn).
 have he:Q*(1%r/(2%r^353))=Q/(2%r^353) by ring.
 move:hs; rewrite he=>hs; exact(ler_trans _ _ _ hb hs).
qed.
