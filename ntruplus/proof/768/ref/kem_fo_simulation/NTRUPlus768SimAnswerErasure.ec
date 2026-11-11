require import AllCore Distr FMap.
from Jasmin require import JWord.
require import Array32 Array192 Array224 Array1152.
require import NTRUPlus768FOModel NTRUPlus768FOSetupDistribution NTRUPlus768PKEModel.
require import NTRUPlus768ACWC2Oracle NTRUPlus768ROMOracles NTRUPlus768ROMDistributions.
require import NTRUPlus768FOEagerG NTRUPlus768FOGAdapters NTRUPlus768FOProcedures NTRUPlus768FONativeBridge.
require import NTRUPlus768SimModel NTRUPlus768SimSampling NTRUPlus768SimAnswer NTRUPlus768SimSpreadHash.
require import NTRUPlus768PolyCBD1CheckedProof NTRUPlus768PolyCBD1Algebra NTRUPlus768DecapCompleteSpec.

(* No public-key canonicity or decode-status premise is needed when the
   regeneration result is discarded. Its only G input is sampled CBD1. *)
lemma sim_regenerate_cache_frame g gm0 : acwc2_cache_matches g gm0=>
 hoare[FORegenerateFinish(SHAKEGROM).run:ROG.m=gm0 ==>ROG.m=gm0].
proof.
 move=>hg; proc; seq 6:(ROG.m=gm0).
 + do 2!(call(_:true ==>true); first by trivial).
   ecall(fo_hash_g_prepared (poly_cbd1_spec(complete_hash_tail hashout)) g gm0 (pke_domain_cbd _) hg).
   ecall(poly_cbd1_functional witness (complete_hash_tail hashout)).
   wp; call(_:true ==>true); first by trivial. auto.
 sp; if; last by auto.
 call(_:true ==>true); first by trivial. auto.
qed.
lemma sim_regenerate_actual_cache_frame g gm0 : acwc2_cache_matches g gm0=>
 phoare[FORegenerateFinish(FOGHash(FOGActual)).run:ROG.m=gm0 ==>ROG.m=gm0]=1%r.
proof.
 move=>hg.
 have hf:hoare[FORegenerateFinish(FOGHash(FOGActual)).run:ROG.m=gm0 ==>ROG.m=gm0].
 + conseq sim_regenerate_g_actual (sim_regenerate_cache_frame g gm0 hg); smt().
 have hl:islossless FOGHash(FOGActual).shake by proc; call rog_get_ll; auto.
 conseq(fo_regenerate_finish_lossless (FOGHash(FOGActual)) hl) hf; smt().
qed.

lemma sim_reject_sample g gm0 :
 equiv[SimAnswerRejectGet(FOGActual,SimHPROMGet(SimHRO.RO)).answer ~ SimAnswerSample(SimHRO.RO).answer:
 ={q,SimHRO.RO.m} /\ ROG.m{1}=gm0 /\ ROG.m{2}=gm0 /\ acwc2_cache_matches g gm0 ==>
 ={res,SimHRO.RO.m} /\ res{1}=None /\ ROG.m{1}=gm0 /\ ROG.m{2}=gm0 /\ acwc2_cache_matches g gm0].
proof.
 case(acwc2_cache_matches g gm0)=>hg; last by exfalso=> />.
 proc.
 inline{1} SimAnswerReal(FOGActual,SimHPROMGet(SimHRO.RO)).answer.
 inline{2} SimHRO.RO.sample; wp.
 call{1}(sim_regenerate_actual_cache_frame g gm0 hg).
 inline{1} SimHPROMGet(SimHRO.RO).get; wp.
 call(_: ={x,SimHRO.RO.m} ==> ={res,SimHRO.RO.m}); first by sim.
 auto.
qed.

module type SimAnswerContext(G:FOGPort,H:SimHPort,D:SimAnswer) = {
 proc distinguish(s:fo_setup_observation) : bool {G.get,H.get,D.answer}
}.
module SimRejectWorld(C:SimAnswerContext,H:SimHRO.RO) = {
 proc distinguish(s:fo_setup_observation) : bool = {
  var b;
  b <@ C(FOGActual,SimHPROMGet(H),SimAnswerRejectGet(FOGActual,SimHPROMGet(H))).distinguish(s);
  return b;
 }
}.
module SimSampleWorld(C:SimAnswerContext,H:SimHRO.RO) = {
 proc distinguish(s:fo_setup_observation) : bool = {
  var b;
  b <@ C(FOGActual,SimHPROMGet(H),SimAnswerSample(H)).distinguish(s);
  return b;
 }
}.
module SimNeverWorld(C:SimAnswerContext,H:SimHRO.RO) = {
 proc distinguish(s:fo_setup_observation) : bool = {
  var b;
  b <@ C(FOGActual,SimHPROMGet(H),SimAnswerNever).distinguish(s);
  return b;
 }
}.

lemma sim_g_cache_preserves g : hoare[ROG.get:
 acwc2_cache_matches g ROG.m ==>acwc2_cache_matches g ROG.m].
proof. proc*; ecall(rog_get_value ROG.m input); auto=> />; smt(fo_cache_extension). qed.

lemma sim_reject_sample_context
 (C<:SimAnswerContext {-ROG,-ROH,-SimGRO.RO,-SimGRO.FRO,-SimHRO.RO,-SimHRO.FRO,-SimBad}) g :
 equiv[SimRejectWorld(C,SimHRO.RO).distinguish ~ SimSampleWorld(C,SimHRO.RO).distinguish:
 ={arg,glob C,ROG.m,SimHRO.RO.m} /\ acwc2_cache_matches g ROG.m{1} ==>
 ={res,glob C,ROG.m,SimHRO.RO.m} /\ acwc2_cache_matches g ROG.m{1}].
proof.
 proc; call(_: ={ROG.m,SimHRO.RO.m} /\ acwc2_cache_matches g ROG.m{1}).
 + conseq(_: ={arg,ROG.m} ==> ={res,ROG.m}) (sim_g_cache_preserves g) _=> //; by sim.
 + conseq(_: ={arg,SimHRO.RO.m} ==> ={res,SimHRO.RO.m})=> //; by sim.
 + proc*; ecall(sim_reject_sample g ROG.m{1}); auto=> />; smt().
 auto.
qed.

lemma sim_sample_world_erase
 (C<:SimAnswerContext {-ROG,-ROH,-SimGRO.RO,-SimGRO.FRO,-SimHRO.RO,-SimHRO.FRO,-SimBad}) :
 equiv[SimSampleWorld(C,SimHRO.RO).distinguish ~ SimSampleWorld(C,SimHRO.LRO).distinguish:
 ={arg,glob C,ROG.m,SimHRO.RO.m} ==> ={res,glob C,ROG.m}].
proof. conseq(sim_h_sampling_erase (SimSampleWorld(C))); smt(). qed.

lemma sim_sample_lazy_never
 (C<:SimAnswerContext {-ROG,-ROH,-SimGRO.RO,-SimGRO.FRO,-SimHRO.RO,-SimHRO.FRO,-SimBad}) :
 equiv[SimSampleWorld(C,SimHRO.LRO).distinguish ~ SimNeverWorld(C,SimHRO.RO).distinguish:
 ={arg,glob C,ROG.m,SimHRO.RO.m} ==> ={res,glob C,ROG.m,SimHRO.RO.m}].
proof.
 proc; call(_: ={ROG.m,SimHRO.RO.m}); first 2 by sim.
 + proc; inline SimHRO.LRO.sample; auto.
 auto.
qed.
lemma sim_reject_sample_probability
 (C<:SimAnswerContext {-ROG,-ROH,-SimGRO.RO,-SimGRO.FRO,-SimHRO.RO,-SimHRO.FRO,-SimBad})
 g &m s0 (event:bool->bool) : acwc2_cache_matches g ROG.m{m}=>
 Pr[SimRejectWorld(C,SimHRO.RO).distinguish(s0) @ &m:event res]=
 Pr[SimSampleWorld(C,SimHRO.RO).distinguish(s0) @ &m:event res].
proof. move=>hg; by byequiv(sim_reject_sample_context C g)=> //. qed.
lemma sim_sample_never_probability
 (C<:SimAnswerContext {-ROG,-ROH,-SimGRO.RO,-SimGRO.FRO,-SimHRO.RO,-SimHRO.FRO,-SimBad})
 &m s0 (event:bool->bool) :
 Pr[SimSampleWorld(C,SimHRO.RO).distinguish(s0) @ &m:event res]=
 Pr[SimNeverWorld(C,SimHRO.RO).distinguish(s0) @ &m:event res].
proof.
 have he:Pr[SimSampleWorld(C,SimHRO.RO).distinguish(s0) @ &m:event res]=
 Pr[SimSampleWorld(C,SimHRO.LRO).distinguish(s0) @ &m:event res]
  by byequiv(sim_sample_world_erase C)=> //.
 rewrite he; by byequiv(sim_sample_lazy_never C)=> //.
qed.
lemma sim_reject_never_probability
 (C<:SimAnswerContext {-ROG,-ROH,-SimGRO.RO,-SimGRO.FRO,-SimHRO.RO,-SimHRO.FRO,-SimBad})
 g &m s0 (event:bool->bool) : acwc2_cache_matches g ROG.m{m}=>
 Pr[SimRejectWorld(C,SimHRO.RO).distinguish(s0) @ &m:event res]=
 Pr[SimNeverWorld(C,SimHRO.RO).distinguish(s0) @ &m:event res].
proof.
 move=>hg; rewrite(sim_reject_sample_probability C g &m s0 event hg).
 exact(sim_sample_never_probability C &m s0 event).
qed.
