require import AllCore List Distr FMap SDist StdOrder.
from Jasmin require import JWord.
require import Array192 Array1152.
require import NTRUPlus768FOModel NTRUPlus768FOSetupDistribution.
require import NTRUPlus768FOSetupExpectation NTRUPlus768SimAverage.
require import NTRUPlus768HistBound NTRUPlus768CCAStatusAdapter.
require import NTRUPlus768ACWC2Oracle NTRUPlus768PKEModel.
require import NTRUPlus768ROMOracles NTRUPlus768SimModel.
import RealOrder.

type hist_average_input =
 fo_setup_observation * fo_h_input list * W8.t Array1152.t * bool * (cca_reply->bool).

(* The arguments qs and ct are fixed before the setup is sampled.
   This observes one actual finite-query build and one actual lookup. *)
module HistAverageKernel = {
 proc guess(input:hist_average_input):bool = {
  var out:cca_reply*bool;
  out<@HistLookupAfterBuild.run(input.`1.`1.`1,acwc2_gfun input.`1.`3,
   acwc2_g_cache input.`1.`3,input.`2,input.`3,input.`4);
  return input.`5 out.`1;
 }
}.

clone SDist.Dist as HistAverageDist with type a<-hist_average_input proof *.

lemma hist_average_kernel_ll : islossless HistAverageKernel.guess.
proof. proc;call hist_lookup_after_build_ll;auto. qed.

lemma hist_average_kernel_probability s qs ct which event &m :
 Pr[HistAverageKernel.guess((s,qs,ct,which,event))@&m:res=true]=
 Pr[HistLookupAfterBuild.run(s.`1.`1,acwc2_gfun s.`3,acwc2_g_cache s.`3,
  qs,ct,which)@&m:event res.`1].
proof.
 byequiv(_: input{1}=(s,qs,ct,which,event) /\
 arg{2}=(s.`1.`1,acwc2_gfun s.`3,acwc2_g_cache s.`3,qs,ct,which) /\
 ={glob ROG,glob ROH,glob SimPublic,glob SimHistory} ==>
 (res{1}=true <=> event res{2}.`1))=> //.
 proc*;inline{1} HistAverageKernel.guess;wp.
 call(_: ={arg,glob ROG,glob ROH,glob SimPublic,glob SimHistory} ==> ={res});first by sim.
 auto=> />;smt().
qed.

lemma hist_average_kernel_distance (s:fo_setup_observation) qs ct event &m :
 fo_setup_valid s=>
 `|Pr[HistAverageKernel.guess((s,qs,ct,true,event))@&m:res=true]-
   Pr[HistAverageKernel.guess((s,qs,ct,false,event))@&m:res=true]|
 <=(size qs)%r*fo_setup_error s.
proof.
 move=>hv;rewrite !hist_average_kernel_probability /fo_setup_error.
 have hk:pke_key_relation s.`1.`1 by move:hv;rewrite /fo_setup_valid;smt().
 have hg:acwc2_cache_matches(acwc2_gfun s.`3)(acwc2_g_cache s.`3)
  by move:hv;rewrite /fo_setup_valid;smt().
 exact(hist_lookup_after_build_distance s.`1.`1 (acwc2_gfun s.`3)
  (acwc2_g_cache s.`3) qs ct &m event hk hg).
qed.

(* Every pointwise premise of the setup average is discharged for the
   concrete kernels above. No arbitrary-kernel distance is assumed. *)
lemma hist_lookup_setup_average qs ct event &m :
 `|mu1(dlet(mk(fun s=>Pr[FOSetupSource.guess(witness)@&m:res=s]))
    (fun s=>mk(fun b=>Pr[HistAverageKernel.guess((s,qs,ct,true,event))@&m:res=b])))true-
   mu1(dlet(mk(fun s=>Pr[FOSetupSource.guess(witness)@&m:res=s]))
    (fun s=>mk(fun b=>Pr[HistAverageKernel.guess((s,qs,ct,false,event))@&m:res=b])))true|
 <=(size qs)%r/(2%r^353).
proof.
 have hQ:0%r<=(size qs)%r by smt(size_ge0).
 pose K0:=fun s=>mk(fun b=>Pr[HistAverageKernel.guess((s,qs,ct,true,event))@&m:res=b]).
 pose K1:=fun s=>mk(fun b=>Pr[HistAverageKernel.guess((s,qs,ct,false,event))@&m:res=b]).
 have hp:forall s,s \in mk(fun z=>Pr[FOSetupSource.guess(witness)@&m:res=z])=>
  `|mu1(K0 s)true-mu1(K1 s)true|<=0%r+(size qs)%r*fo_setup_error s.
 + move=>s hs;rewrite /K0 /K1
    -(HistAverageDist.GenDist.adv_mu1 HistAverageKernel &m true (s,qs,ct,true,event))
    -(HistAverageDist.GenDist.adv_mu1 HistAverageKernel &m true (s,qs,ct,false,event)) /=.
   exact(hist_average_kernel_distance s qs ct event &m (fo_setup_law_support &m witness s hs)).
 have hzero:0%r<=0%r by done.
 have ha:=sim_setup_distance_average &m K0 K1 (pred1 true) 0%r (size qs)%r hzero hQ hp.
 by move:ha;rewrite /K0 /K1 /=.
qed.

require import NTRUPlus768HistBuild.

lemma hist_average_after_build_initial :
 equiv[HistLookupAfterBuild.run ~ HistLookupAfterBuild.run:
 ={arg} ==> ={res}].
proof. proc;inline HistBuild.run ROH.init;sim. qed.

lemma hist_average_kernel_initial :
 equiv[HistAverageKernel.guess ~ HistAverageKernel.guess:
 ={input} ==> ={res}].
proof. proc;call hist_average_after_build_initial;auto. qed.

module HistAverageExperiment = {
 proc run(qs:fo_h_input list,ct:W8.t Array1152.t,which:bool,event:cca_reply->bool):bool = {
  var s:fo_setup_observation;var win:bool;
  s<@FOSetupSource.guess(witness);
  win<@HistAverageKernel.guess((s,qs,ct,which,event));
  return win;
 }
}.
module HistAverageReified = {
 proc run(d:fo_setup_observation distr,qs:fo_h_input list,
          ct:W8.t Array1152.t,which:bool,event:cca_reply->bool):bool = {
  var s:fo_setup_observation;var input:hist_average_input;var win:bool;
  s<$d;input<-(s,qs,ct,which,event);
  win<@HistAverageKernel.guess(input);
  return win;
 }
}.

lemma hist_average_experiment_reified qs0 ct0 which0 event0 &m :
 Pr[HistAverageExperiment.run(qs0,ct0,which0,event0)@&m:res]=
 Pr[HistAverageReified.run(mk(fun s=>Pr[FOSetupSource.guess(witness)@&m:res=s]),
  qs0,ct0,which0,event0)@&m:res].
proof.
 byequiv(_: ={qs,ct,which,event} /\ ROF.m{1}=ROF.m{m} /\
 d{2}=mk(fun s=>Pr[FOSetupSource.guess(witness)@&m:res=s]) ==> ={res})=> //.
 proc;call hist_average_kernel_initial;wp.
 outline{2} 1 ~ FOSetupDist.S.sample.
 call(fo_setup_source_sample FOSetupSource &m witness);auto.
qed.

lemma hist_average_reified_sample d0 qs0 ct0 which0 event0 &m :
 Pr[HistAverageReified.run(d0,qs0,ct0,which0,event0)@&m:res]=
 Pr[HistAverageDist.Sample(HistAverageKernel).main
  (dmap d0(fun s=>(s,qs0,ct0,which0,event0)))@&m:res].
proof.
 byequiv(_: d{1}=d0 /\ qs{1}=qs0 /\ ct{1}=ct0 /\ which{1}=which0 /\ event{1}=event0 /\
 d{2}=dmap d0(fun s=>(s,qs0,ct0,which0,event0)) ==> ={res})=> //.
 proc;call hist_average_kernel_initial;rndsem*{1} 0;rnd;auto.
qed.

lemma hist_average_experiment_mu qs ct which event &m :
 Pr[HistAverageExperiment.run(qs,ct,which,event)@&m:res]=
 mu1(dlet(mk(fun s=>Pr[FOSetupSource.guess(witness)@&m:res=s]))
  (fun s=>mk(fun b=>Pr[HistAverageKernel.guess((s,qs,ct,which,event))@&m:res=b])))true.
proof.
 rewrite hist_average_experiment_reified hist_average_reified_sample
  (HistAverageDist.Sample_dlet HistAverageKernel &m _) dlet_dmap.
 done.
qed.

lemma hist_lookup_setup_experiment_distance qs ct event &m :
 `|Pr[HistAverageExperiment.run(qs,ct,true,event)@&m:res]-
   Pr[HistAverageExperiment.run(qs,ct,false,event)@&m:res]|
 <=(size qs)%r/(2%r^353).
proof.
 rewrite !hist_average_experiment_mu.
 exact(hist_lookup_setup_average qs ct event &m).
qed.

require import NTRUPlus768HistCosts NTRUPlus768DecapCompleteSpec.

type hist_public_average_input =
 fo_setup_observation * fo_h_input list * W8.t Array1152.t * (cca_reply->bool).

(* Prepared G is installed only by this proof experiment. The invoked
   public procedure accepts pk, suffix, qs and ct, with no secret witness. *)
module HistAveragePublicKernel = {
 proc guess(input:hist_public_average_input):bool = {
  var out:cca_reply*int*int*int*int;
  ROG.m<-acwc2_g_cache input.`1.`3;
  out<@HistPublicLookup.run(input.`1.`1.`1.`kg_pk,
   complete_sk_suffix input.`1.`1.`1.`kg_sk,input.`2,input.`3);
  return input.`4 out.`1;
 }
}.
module HistAveragePublicExperiment = {
 proc run(qs:fo_h_input list,ct:W8.t Array1152.t,event:cca_reply->bool):bool = {
  var s:fo_setup_observation;var win:bool;
  s<@FOSetupSource.guess(witness);
  win<@HistAveragePublicKernel.guess((s,qs,ct,event));
  return win;
 }
}.

lemma hist_average_public_kernel_ll : islossless HistAveragePublicKernel.guess.
proof. proc;call hist_public_lookup_lossless;auto. qed.

lemma hist_average_public_kernel_projection :
 equiv[HistAveragePublicKernel.guess ~ HistAverageKernel.guess:
 input{1}.`1=input{2}.`1 /\ input{1}.`2=input{2}.`2 /\
 input{1}.`3=input{2}.`3 /\ input{1}.`4=input{2}.`5 /\ input{2}.`4 ==>
 ={res}].
proof.
 proc;wp;call hist_public_lookup_projection;auto.
 move=> &1 &2 [hs [hq [hc [he hw]]]].
 rewrite hs hq hc he hw /=.
 move=> rl rr ml hl mr hr [hreply _].
 by rewrite hreply.
qed.

lemma hist_average_public_experiment_projection qs0 ct0 event0 &m :
 Pr[HistAveragePublicExperiment.run(qs0,ct0,event0)@&m:res]=
 Pr[HistAverageExperiment.run(qs0,ct0,true,event0)@&m:res].
proof.
 byequiv(_: ={qs,ct,event} /\ which{2} ==> ={res})=> //.
 proc;call hist_average_public_kernel_projection.
 call fo_setup_source_initial_state;auto.
qed.

(* Actual setup, actual finite public H-history construction, and one
   public list lookup versus the original map-based lookup. This theorem
   concerns fixed qs/ct and an output event, not a full adaptive CCA game. *)
lemma hist_public_lookup_setup_distance qs ct event &m :
 `|Pr[HistAveragePublicExperiment.run(qs,ct,event)@&m:res]-
   Pr[HistAverageExperiment.run(qs,ct,false,event)@&m:res]|
 <=(size qs)%r/(2%r^353).
proof.
 rewrite hist_average_public_experiment_projection.
 exact(hist_lookup_setup_experiment_distance qs ct event &m).
qed.
