require import AllCore Distr FMap StdOrder.
require import NTRUPlus768SimModel NTRUPlus768SimSampling NTRUPlus768SimAnswer NTRUPlus768SimAnswerErasure NTRUPlus768SimSelected.
require import NTRUPlus768FOEagerG NTRUPlus768FOGAdapters NTRUPlus768FOSetupDistribution NTRUPlus768ACWC2Oracle NTRUPlus768ROMOracles.
import RealOrder.

module SimMarkContext(C:SimAnswerContext) = {
 proc run(s:fo_setup_observation) : bool = {
  var b;SimBad.init();
  b<@C(FOGActual,SimHActual,SimAnswerMarkReal(FOGActual,SimHActual)).distinguish(s);
  return b;
 }
}.
module SimRejectContext(C:SimAnswerContext) = {
 proc run(s:fo_setup_observation) : bool = {
  var b;SimBad.init();
  b<@C(FOGActual,SimHActual,SimAnswerRejectGet(FOGActual,SimHActual)).distinguish(s);
  return b;
 }
}.
module SimRealContext(C:SimAnswerContext) = {
 proc run(s:fo_setup_observation) : bool = {
  var b;SimBad.init();
  b<@C(FOGActual,SimHActual,SimAnswerReal(FOGActual,SimHActual)).distinguish(s);
  return b;
 }
}.
module SimNeverContext(C:SimAnswerContext) = {
 proc run(s:fo_setup_observation) : bool = {
  var b;SimBad.init();
  b<@C(FOGActual,SimHActual,SimAnswerNever).distinguish(s);
  return b;
 }
}.

lemma sim_context_mark_real (C<:SimAnswerContext {-ROG,-ROH,-SimBad}) :
 equiv[SimMarkContext(C).run ~ SimRealContext(C).run:
 ={s,glob C,ROG.m,ROH.m} ==> ={res,glob C,ROG.m,ROH.m}].
proof.
 proc;call(_: ={ROG.m,ROH.m});first 2 by sim.
 + conseq sim_mark_real_projection=> //.
 inline SimBad.init;auto.
qed.

lemma sim_context_mark_reject
 (C<:SimAnswerContext {-ROG,-ROH,-SimBad}) :
 (forall(G<:FOGPort {-C})(H<:SimHPort {-C})(D<:SimAnswer {-C}),
 islossless G.get=>islossless H.get=>islossless D.answer=>islossless C(G,H,D).distinguish)=>
 equiv[SimMarkContext(C).run ~ SimRejectContext(C).run:
 ={s,glob C,ROG.m,ROH.m} ==>
 ={SimBad.hidden} /\ (!SimBad.hidden{2}=> ={res,glob C,ROG.m,ROH.m})].
proof.
 move=>all.
 have ml:=sim_mark_real_ll FOGActual SimHActual rog_get_ll roh_get_ll.
 have rl:=sim_answer_reject_ll FOGActual SimHActual rog_get_ll roh_get_ll.
 have al:=all FOGActual SimHActual (SimAnswerMarkReal(FOGActual,SimHActual)) rog_get_ll roh_get_ll ml.
 have ar:=all FOGActual SimHActual (SimAnswerRejectGet(FOGActual,SimHActual)) rog_get_ll roh_get_ll rl.
 proc;call(_:SimBad.hidden, ={ROG.m,ROH.m,glob SimBad}, ={SimBad.hidden}).
 + conseq(_: ={arg,ROG.m,ROH.m,glob SimBad} ==> ={res,ROG.m,ROH.m,glob SimBad})=> //;by sim.
 + move=> &2 h;conseq rog_get_ll (_:SimBad.hidden ==>SimBad.hidden);first 2 by smt().
   proc*;call(_:true ==>true);first by trivial. auto.
 + move=> &1;conseq rog_get_ll (_:SimBad.hidden ==>SimBad.hidden);first 2 by smt().
   proc*;call(_:true ==>true);first by trivial. auto.
 + conseq(_: ={arg,ROG.m,ROH.m,glob SimBad} ==> ={res,ROG.m,ROH.m,glob SimBad})=> //;by sim.
 + move=> &2 h;conseq roh_get_ll (_:SimBad.hidden ==>SimBad.hidden);first 2 by smt().
   proc*;call(_:true ==>true);first by trivial. auto.
 + move=> &1;conseq roh_get_ll (_:SimBad.hidden ==>SimBad.hidden);first 2 by smt().
   proc*;call(_:true ==>true);first by trivial. auto.
 + conseq sim_mark_reject_step;smt().
 + move=> &2 h;conseq ml (sim_mark_latched FOGActual SimHActual);smt().
 + move=> &1;conseq rl (sim_reject_latched FOGActual SimHActual);smt().
 inline SimBad.init;auto;smt().
qed.

lemma sim_context_real_reject_distance
 (C<:SimAnswerContext {-ROG,-ROH,-SimBad}) s0 &m :
 (forall(G<:FOGPort {-C})(H<:SimHPort {-C})(D<:SimAnswer {-C}),
 islossless G.get=>islossless H.get=>islossless D.answer=>islossless C(G,H,D).distinguish)=>
 `|Pr[SimRealContext(C).run(s0) @ &m:res]-Pr[SimRejectContext(C).run(s0) @ &m:res]|
 <=Pr[SimRejectContext(C).run(s0) @ &m:SimBad.hidden].
proof.
 move=>all.
 have he:Pr[SimRealContext(C).run(s0) @ &m:res]=Pr[SimMarkContext(C).run(s0) @ &m:res]
  by apply/eq_sym;byequiv(sim_context_mark_real C)=> //.
 rewrite he.
 have hg:Pr[SimMarkContext(C).run(s0) @ &m:res /\ !SimBad.hidden]=
 Pr[SimRejectContext(C).run(s0) @ &m:res /\ !SimBad.hidden]
  by byequiv(sim_context_mark_reject C all)=> //;smt().
 have hb:Pr[SimMarkContext(C).run(s0) @ &m:SimBad.hidden]=
 Pr[SimRejectContext(C).run(s0) @ &m:SimBad.hidden]
  by byequiv(sim_context_mark_reject C all)=> //;smt().
 have h0:Pr[SimMarkContext(C).run(s0) @ &m:res /\ SimBad.hidden]<=Pr[SimMarkContext(C).run(s0) @ &m:SimBad.hidden]
  by rewrite Pr[mu_sub].
 have h1:Pr[SimRejectContext(C).run(s0) @ &m:res /\ SimBad.hidden]<=Pr[SimRejectContext(C).run(s0) @ &m:SimBad.hidden]
  by rewrite Pr[mu_sub].
 rewrite Pr[mu_split SimBad.hidden].
 have ->:Pr[SimRejectContext(C).run(s0) @ &m:res]=
 Pr[SimRejectContext(C).run(s0) @ &m:res /\ SimBad.hidden]+
 Pr[SimRejectContext(C).run(s0) @ &m:res /\ !SimBad.hidden]
  by rewrite Pr[mu_split SimBad.hidden].
 clear all.
 smt(mu_bounded).
qed.

module SimRejectHQuery(C:SimAnswerContext,H:SimHPort) = {
 proc distinguish=C(FOGActual,H,SimAnswerRejectGet(FOGActual,H)).distinguish
}.
module SimNeverHQuery(C:SimAnswerContext,H:SimHPort) = {
 proc distinguish=C(FOGActual,H,SimAnswerNever).distinguish
}.
module SimHRejectInitialized(C:SimAnswerContext) = {
 proc run(s:fo_setup_observation) : bool = {
  var b;SimBad.init();SimHRO.RO.m<-ROH.m;
  b<@SimRejectWorld(C,SimHRO.RO).distinguish(s);return b;
 }
}.
module SimHSampleInitialized(C:SimAnswerContext,H:SimHRO.RO) = {
 proc run(s:fo_setup_observation) : bool = {
  var b;SimBad.init();SimHRO.RO.m<-ROH.m;
  b<@SimSampleWorld(C,H).distinguish(s);return b;
 }
}.
module SimHNeverInitialized(C:SimAnswerContext) = {
 proc run(s:fo_setup_observation) : bool = {
  var b;SimBad.init();SimHRO.RO.m<-ROH.m;
  b<@SimNeverWorld(C,SimHRO.RO).distinguish(s);return b;
 }
}.

lemma sim_reject_initialize
 (C<:SimAnswerContext {-ROG,-ROH,-SimGRO.RO,-SimGRO.FRO,-SimHRO.RO,-SimHRO.FRO,-SimBad}) :
 equiv[SimRejectContext(C).run ~ SimHRejectInitialized(C).run:
 ={s,glob C,ROG.m,ROH.m} ==> ={res,glob C,ROG.m}].
proof.
 proc;inline{2} SimRejectWorld(C,SimHRO.RO).distinguish;wp.
 call(sim_h_query_context_adapter (SimRejectHQuery(C))).
 inline SimBad.init;auto.
qed.
lemma sim_never_initialize
 (C<:SimAnswerContext {-ROG,-ROH,-SimGRO.RO,-SimGRO.FRO,-SimHRO.RO,-SimHRO.FRO,-SimBad}) :
 equiv[SimNeverContext(C).run ~ SimHNeverInitialized(C).run:
 ={s,glob C,ROG.m,ROH.m} ==> ={res,glob C,ROG.m}].
proof.
 proc;inline{2} SimNeverWorld(C,SimHRO.RO).distinguish;wp.
 call(sim_h_query_context_adapter (SimNeverHQuery(C))).
 inline SimBad.init;auto.
qed.
lemma sim_reject_initialized_sample
 (C<:SimAnswerContext {-ROG,-ROH,-SimGRO.RO,-SimGRO.FRO,-SimHRO.RO,-SimHRO.FRO,-SimBad})
 g &m s0 (event:bool->bool) : acwc2_cache_matches g ROG.m{m}=>
 Pr[SimHRejectInitialized(C).run(s0) @ &m:event res]=
 Pr[SimHSampleInitialized(C,SimHRO.RO).run(s0) @ &m:event res].
proof.
 move=>hg;byequiv(_: ={arg,glob C,ROG.m,ROH.m} /\ acwc2_cache_matches g ROG.m{1} ==> ={res})=> //.
 proc;call(sim_reject_sample_context C g);inline SimBad.init;auto.
qed.
lemma sim_sample_initialized_erase
 (C<:SimAnswerContext {-ROG,-ROH,-SimGRO.RO,-SimGRO.FRO,-SimHRO.RO,-SimHRO.FRO,-SimBad})
 &m s0 (event:bool->bool) :
 Pr[SimHSampleInitialized(C,SimHRO.RO).run(s0) @ &m:event res]=
 Pr[SimHSampleInitialized(C,SimHRO.LRO).run(s0) @ &m:event res].
proof.
 byequiv(_: ={arg,glob C,ROG.m,ROH.m} ==> ={res})=> //.
 proc;call(sim_sample_world_erase C);inline SimBad.init;auto.
qed.
lemma sim_sample_initialized_never
 (C<:SimAnswerContext {-ROG,-ROH,-SimGRO.RO,-SimGRO.FRO,-SimHRO.RO,-SimHRO.FRO,-SimBad})
 &m s0 (event:bool->bool) :
 Pr[SimHSampleInitialized(C,SimHRO.LRO).run(s0) @ &m:event res]=
 Pr[SimHNeverInitialized(C).run(s0) @ &m:event res].
proof.
 byequiv(_: ={arg,glob C,ROG.m,ROH.m} ==> ={res})=> //.
 proc;call(sim_sample_lazy_never C);inline SimBad.init;auto.
qed.
lemma sim_context_reject_never
 (C<:SimAnswerContext {-ROG,-ROH,-SimGRO.RO,-SimGRO.FRO,-SimHRO.RO,-SimHRO.FRO,-SimBad})
 g &m s0 (event:bool->bool) : acwc2_cache_matches g ROG.m{m}=>
 Pr[SimRejectContext(C).run(s0) @ &m:event res]=
 Pr[SimNeverContext(C).run(s0) @ &m:event res].
proof.
 move=>hg.
 have hr:Pr[SimRejectContext(C).run(s0) @ &m:event res]=Pr[SimHRejectInitialized(C).run(s0) @ &m:event res]
  by byequiv(sim_reject_initialize C)=> //.
 have hn:Pr[SimNeverContext(C).run(s0) @ &m:event res]=Pr[SimHNeverInitialized(C).run(s0) @ &m:event res]
  by byequiv(sim_never_initialize C)=> //.
 rewrite hr hn (sim_reject_initialized_sample C g &m s0 event hg)
  (sim_sample_initialized_erase C &m s0 event).
 exact(sim_sample_initialized_never C &m s0 event).
qed.

lemma sim_context_real_never_distance
 (C<:SimAnswerContext {-ROG,-ROH,-SimGRO.RO,-SimGRO.FRO,-SimHRO.RO,-SimHRO.FRO,-SimBad})
 g &m s0 : acwc2_cache_matches g ROG.m{m}=>
 (forall(G<:FOGPort {-C})(H<:SimHPort {-C})(D<:SimAnswer {-C}),
 islossless G.get=>islossless H.get=>islossless D.answer=>islossless C(G,H,D).distinguish)=>
 `|Pr[SimRealContext(C).run(s0) @ &m:res]-Pr[SimNeverContext(C).run(s0) @ &m:res]|
 <=Pr[SimRejectContext(C).run(s0) @ &m:SimBad.hidden].
proof.
 move=>hg all;rewrite -(sim_context_reject_never C g &m s0 (fun b=>b) hg).
 exact(sim_context_real_reject_distance C s0 &m all).
qed.
