require import AllCore Distr FMap StdOrder.
from Jasmin require import JWord.
require import Array32 Array224.
require import NTRUPlus768SimModel NTRUPlus768SimSampling NTRUPlus768SimAnswer.
require import NTRUPlus768SimSpreadHash NTRUPlus768SimAnswerErasure.
require import NTRUPlus768SimPorts NTRUPlus768SimHybrid.
require import NTRUPlus768SimPortContracts.
require import NTRUPlus768FOModel NTRUPlus768FOError NTRUPlus768FOEagerG.
require import NTRUPlus768FOGAdapters NTRUPlus768PKEModel NTRUPlus768PKEAlgebra.
require import NTRUPlus768ROMOracles NTRUPlus768ACWC2Oracle NTRUPlus768SpreadCBD.
require import NTRUPlus768CCAGame NTRUPlus768FOSetupDistribution NTRUPlus768FOQueryBudget.
import RealOrder.

lemma sim_cover_unknown_fresh history table challenge q :
 sim_h_cover history table challenge=>sim_h_input q \notin history=>
 Some(sim_h_input q)<>challenge=>sim_h_input q \notin table.
proof. rewrite /sim_h_cover; smt(). qed.

module SimAnswerMarkReal(G:FOGPort,H:SimHPort) : SimAnswer = {
 proc answer(q:sim_request) : W8.t Array32.t option = {
  var result:W8.t Array32.t option;
  result<@SimAnswerReal(G,H).answer(q);
  SimBad.hidden<-SimBad.hidden \/ result<>None;
  SimBad.selected_calls<-SimBad.selected_calls+1;
  return result;
 }
}.

lemma sim_mark_real_ll (G<:FOGPort)(H<:SimHPort) :
 islossless G.get=>islossless H.get=>islossless SimAnswerMarkReal(G,H).answer.
proof. move=>hg hh;proc;wp;call(sim_answer_real_ll G H hg hh);auto. qed.

lemma sim_mark_real_projection :
 equiv[SimAnswerMarkReal(FOGActual,SimHActual).answer ~ SimAnswerReal(FOGActual,SimHActual).answer:
 ={q,ROG.m,ROH.m} ==> ={res,ROG.m,ROH.m}].
proof. proc*;inline{1} SimAnswerMarkReal(FOGActual,SimHActual).answer;sim. qed.

lemma sim_mark_reject_step :
 equiv[SimAnswerMarkReal(FOGActual,SimHActual).answer ~ SimAnswerRejectGet(FOGActual,SimHActual).answer:
 ={q,ROG.m,ROH.m,glob SimBad} ==>
 ={ROG.m,ROH.m,glob SimBad} /\ (!SimBad.hidden{2}=> ={res})].
proof.
 proc;wp.
 call(_: ={arg,ROG.m,ROH.m} ==> ={res,ROG.m,ROH.m});first by sim.
 auto;smt().
qed.

lemma sim_mark_latched (G<:FOGPort {-SimBad})(H<:SimHPort {-SimBad}) :
 hoare[SimAnswerMarkReal(G,H).answer:SimBad.hidden ==>SimBad.hidden].
proof. proc;wp;call(_:true ==>true);first by trivial. auto;smt(). qed.
lemma sim_reject_latched (G<:FOGPort {-SimBad})(H<:SimHPort {-SimBad}) :
 hoare[SimAnswerRejectGet(G,H).answer:SimBad.hidden ==>SimBad.hidden].
proof. proc;wp;call(_:true ==>true);first by trivial. auto;smt(). qed.
lemma sim_mark_count (G<:FOGPort {-SimBad})(H<:SimHPort {-SimBad}) n0 :
 hoare[SimAnswerMarkReal(G,H).answer:SimBad.selected_calls=n0 ==>SimBad.selected_calls=n0+1].
proof. proc;wp;call(_:true ==>true);first by trivial. auto;smt(). qed.
lemma sim_reject_count (G<:FOGPort {-SimBad})(H<:SimHPort {-SimBad}) n0 :
 hoare[SimAnswerRejectGet(G,H).answer:SimBad.selected_calls=n0 ==>SimBad.selected_calls=n0+1].
proof. proc;wp;call(_:true ==>true);first by trivial. auto;smt(). qed.

lemma sim_selected_fresh_bad w g q0 gm0 hm0 :
 pke_key_relation w=>q0.`sr_pk=w.`kg_pk=>acwc2_cache_matches g gm0=>
 sim_h_input q0 \notin hm0=>
 phoare[SimAnswerRejectGet(FOGActual,SimHActual).answer:
 q=q0 /\ ROG.m=gm0 /\ ROH.m=hm0 /\ !SimBad.hidden ==>SimBad.hidden]
 <=(1%r/(2%r^768)+fo_error w g).
proof.
 move=>hk hp hg hf;proc;wp.
 call(sim_answer_actual_fresh_bound w g q0 gm0 hm0 hk hp hg hf);auto;smt().
qed.

lemma sim_actual_fresh_uniform_pre w g : pke_key_relation w=>
 phoare[SimAnswerReal(FOGActual,SimHActual).answer:
 q.`sr_pk=w.`kg_pk /\ acwc2_cache_matches g ROG.m /\ sim_h_input q \notin ROH.m ==>
 res<>None] <=(1%r/(2%r^768)+fo_error w g).
proof.
 move=>hk;bypr=> &m [hp [hg hf]].
 byphoare(sim_answer_actual_fresh_bound w g q{m} ROG.m{m} ROH.m{m} hk hp hg hf)=> //.
qed.

(* These fields and the guard belong only to the diagnostic experiment.
   The concrete selected-query invariant later proves the guard true. *)
module SimSelectedFixed = {
 var key:NTRUPlus768KeygenCompleteProof.keygen_witness
 var g:acwc2_g_function
}.
module SimGuardedReject : SimAnswer = {
 proc answer(q:sim_request) : W8.t Array32.t option = {
  var result:W8.t Array32.t option;
  if(q.`sr_pk=SimSelectedFixed.key.`kg_pk /\ sim_h_input q \notin ROH.m){
   result<@SimAnswerReal(FOGActual,SimHActual).answer(q);
   SimBad.hidden<-SimBad.hidden \/ result<>None;
  }
  SimBad.selected_calls<-SimBad.selected_calls+1;
  return None;
 }
}.
module SimGuardedExperiment(C:SimAnswerContext) = {
 proc run(w:NTRUPlus768KeygenCompleteProof.keygen_witness,g:acwc2_g_function,
  s:fo_setup_observation) : bool = {
  var b;
  SimSelectedFixed.key<-w;SimSelectedFixed.g<-g;SimBad.init();
  b<@C(FOGActual,SimHActual,SimGuardedReject).distinguish(s);
  return b;
 }
}.
lemma sim_guarded_ll : islossless SimGuardedReject.answer.
proof.
 proc;wp;sp;if;last by auto.
 wp;call(sim_answer_real_ll FOGActual SimHActual rog_get_ll roh_get_ll);auto.
qed.
lemma sim_guarded_bad w g : pke_key_relation w=>
 phoare[SimGuardedReject.answer:
 SimSelectedFixed.key=w /\ acwc2_cache_matches g ROG.m /\ !SimBad.hidden ==>SimBad.hidden]
 <=(1%r/(2%r^768)+fo_error w g).
proof.
 move=>hk.
 have hp:=ltrW _ _ spread_cbd_bound_positive.
 have [he _]:=fo_error_range w g.
 have hge:0%r<=1%r/(2%r^768)+fo_error w g by exact(addr_ge0 _ _ hp he).
 proc;wp;sp;if.
 + by wp;call(sim_actual_fresh_uniform_pre w g hk);skip=> />.
 conseq (_: !SimBad.hidden ==>false : =0%r)=> //.
qed.

lemma sim_guarded_count n0 : hoare[SimGuardedReject.answer:
 SimBad.selected_calls=n0 ==>SimBad.selected_calls=n0+1].
proof.
 proc;wp;if;last by auto.
 wp;call(_:true ==>true);first by trivial. auto.
qed.
lemma sim_guarded_latched : hoare[SimGuardedReject.answer:SimBad.hidden ==>SimBad.hidden].
proof.
 proc;wp;if;last by auto.
 wp;call(_:true ==>true);first by trivial. auto;smt().
qed.
lemma sim_reject_guarded_step w :
 equiv[SimAnswerRejectGet(FOGActual,SimHActual).answer ~ SimGuardedReject.answer:
 ={q,ROG.m,ROH.m,glob SimBad} /\ SimSelectedFixed.key{2}=w /\
 q{1}.`sr_pk=w.`kg_pk /\ sim_h_input q{1} \notin ROH.m{1} ==>
 ={res,ROG.m,ROH.m,glob SimBad}].
proof.
 proc;rcondt{2} 1;first by auto=> />;smt().
 wp;call(_: ={arg,ROG.m,ROH.m} ==> ={res,ROG.m,ROH.m});first by sim.
 auto.
qed.

lemma sim_guarded_context_bad
 (C<:SimAnswerContext {-ROG,-ROH,-SimSelectedFixed,-SimBad}) w0 g0 s0 &m :
 pke_key_relation w0=>acwc2_cache_matches g0 ROG.m{m}=>
 Pr[SimGuardedExperiment(C).run(w0,g0,s0) @ &m:SimBad.hidden /\ SimBad.selected_calls<=1]
 <=(1%r/(2%r^768)+fo_error w0 g0).
proof.
 move=>hk hg.
 fel 3 SimBad.selected_calls (fun _=>1%r/(2%r^768)+fo_error w0 g0) 1 SimBad.hidden
  [FOGActual.get:false;SimHActual.get:false;SimGuardedReject.answer:true]
  (SimSelectedFixed.key=w0 /\ SimSelectedFixed.g=g0 /\ acwc2_cache_matches g0 ROG.m)=> //.
 + by rewrite StdBigop.Bigreal.BRA.big_int1.
 + inline SimBad.init;auto.
 + conseq(sim_guarded_bad w0 g0 hk);smt().
 + move=>c;proc;wp;sp;if;last by auto;smt().
   wp;call(sim_answer_cache g0);auto;smt().
 move=>b c;proc*;call(sim_g_cache_preserves g0);auto=> />.
qed.

(* A concrete namespace exposes one shared instance to downstream files.
   budget remains an uninterpreted integer parameter; no security or
   positivity axiom is attached to it. SH normalizes it with max 0. *)
theory SimSelectedBudget.
op budget : int.
clone import SimHybridBudget as SH with
 type leak_input <- sim_leak_input,
 type leak_output <- sim_leak_output,
 op budget <- budget.

module SimBackend(G:FOGPort,H:SimHPort) : SH.HB.Orclb = {
 proc leaks=SimLeaksBackend(G,H).leaks
 proc orclL=SimAnswerReal(G,H).answer
 proc orclR=SimAnswerNever.answer
}.
module SimCaller(A:CCAExtendedAdversary,B:SH.HB.Orclb,O:SH.HB.Orcl) : SH.HB.Adv = {
 proc main() : bool = {
  var guess;
  FOBudgetState.configure(0);
  guess<@FOCountedA(A,SimLeakHashes(B),SimLeakDecaps(B,SH.SimAnswerOfOracle(O))).guess(
   SimPhaseInput.pk,SimPhaseInput.ct,SimPhaseInput.key);
  return guess=SimPhaseInput.bit;
 }
}.
module SimSelectedContext(A:CCAExtendedAdversary,G:FOGPort,H:SimHPort,D:SimAnswer) = {
 proc distinguish(s:fo_setup_observation) : bool = {
  var win;
  win<@SH.HB.HybGame(SimCaller(A),SimBackend(G,H),SH.SimOracleOfAnswer(D)).main();
  return win;
 }
}.
module SimSelectedExperiment(A:CCAExtendedAdversary,G:FOGPort,H:SimHPort,D:SimAnswer) = {
 proc distinguish(s:fo_setup_observation) : bool = {
  var win;SimBad.init();
  win<@SimSelectedContext(A,G,H,D).distinguish(s);
  return win;
 }
}.
module SimSelectedReal(A:CCAExtendedAdversary) =
 SimSelectedExperiment(A,FOGActual,SimHActual,SimAnswerReal(FOGActual,SimHActual)).
module SimSelectedMark(A:CCAExtendedAdversary) =
 SimSelectedExperiment(A,FOGActual,SimHActual,SimAnswerMarkReal(FOGActual,SimHActual)).
module SimSelectedReject(A:CCAExtendedAdversary) =
 SimSelectedExperiment(A,FOGActual,SimHActual,SimAnswerRejectGet(FOGActual,SimHActual)).
module SimSelectedNever(A:CCAExtendedAdversary) =
 SimSelectedExperiment(A,FOGActual,SimHActual,SimAnswerNever).

module SimSelectedGuarded(A:CCAExtendedAdversary) =
 SimGuardedExperiment(SimSelectedContext(A)).

end SimSelectedBudget.
