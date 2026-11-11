require import AllCore Distr FMap.
from Jasmin require import JWord.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768ACWC2Oracle.
require import NTRUPlus768FOModel NTRUPlus768FOSetupDistribution NTRUPlus768FOChallenge NTRUPlus768FOHMonitor.
require import NTRUPlus768ROMOracles NTRUPlus768RawXOFStreams NTRUPlus768CCADecapOracle NTRUPlus768FOKEMGame.
require import NTRUPlus768DecapCompleteSpec.
require import NTRUPlus768SimModel NTRUPlus768SimGames NTRUPlus768SimPorts NTRUPlus768SimSetupBridge.

(* A proof-only predicate on explicit values; it reads no global state.
   The history is initially empty, so initial H-goodness is vacuous.
   This guard is evaluated once before the adversary phase, never after
   a query or after a bad event, and is removed by the projection below. *)
op [opaque] sim_phase_ready (s:fo_setup_observation) pk suffix sk star
 (w:keygen_witness) (g:acwc2_g_function) ex hs cs gm hm log corr =
 fo_setup_valid s /\ w=s.`1.`1 /\ g=acwc2_gfun s.`3 /\
 pk=w.`kg_pk /\ suffix=complete_sk_suffix w.`kg_sk /\ sk=w.`kg_sk /\ star=Some cs /\
 acwc2_cache_matches g gm /\ sim_log_included log hm /\ sim_h_cover log hm ex /\
 fo_challenge_invariant w g ex hs cs hm /\ !corr /\ fo_hcache_good w g ex log.

module type SimBoolPhase = {proc distinguish(s:fo_setup_observation):bool}.

module SimReadyPhase(P:SimBoolPhase) = {
 proc distinguish(s:fo_setup_observation) : bool = {
  var result:bool;
  result<-false;
  if(sim_phase_ready s SimPublic.pk SimPublic.suffix CCADecapOracle.sk SimPublic.cstar
    FOContext.w FOContext.g FOContext.challenge_h FOContext.challenge_hash FOContext.challenge_ct
    ROG.m ROH.m SimHistory.h SimBad.corr){
   result<@P.distinguish(s);
  }
  return result;
 }
}.
module SimReadyKernel(P:SimBoolPhase) = {
 proc guess(s:fo_setup_observation) : bool = {
  var result:bool;
  SimObservedSetup.run(s);
  result<@SimReadyPhase(P).distinguish(s);
  return result;
 }
}.
module SimSetupPhase(P:SimBoolPhase) = {
 proc guess(s:fo_setup_observation) : bool = {
  var result:bool;
  SimObservedSetup.run(s);
  result<@P.distinguish(s);
  return result;
 }
}.

lemma sim_ready_phase_ll (P<:SimBoolPhase) :
 islossless P.distinguish=>islossless SimReadyPhase(P).distinguish.
proof. move=>hp;proc;sp;if;last by auto. call hp;auto. qed.
lemma sim_ready_kernel_ll (P<:SimBoolPhase) :
 islossless P.distinguish=>islossless SimReadyKernel(P).guess.
proof. move=>hp;proc;call(sim_ready_phase_ll P hp);call sim_observed_setup_ll;auto. qed.
lemma sim_setup_phase_ll (P<:SimBoolPhase) :
 islossless P.distinguish=>islossless SimSetupPhase(P).guess.
proof. move=>hp;proc;call hp;call sim_observed_setup_ll;auto. qed.

lemma sim_ready_setup_state s0 : fo_setup_valid s0=>
 hoare[SimObservedSetup.run:s=s0 ==>
 sim_phase_ready s0 SimPublic.pk SimPublic.suffix CCADecapOracle.sk SimPublic.cstar
  FOContext.w FOContext.g FOContext.challenge_h FOContext.challenge_hash FOContext.challenge_ct
  ROG.m ROH.m SimHistory.h SimBad.corr].
proof.
 move=>hv;conseq(sim_observed_setup_state s0 hv)=> //.
 rewrite /sim_phase_ready;auto=> />.
 move=>ct ex hs gm hm corr hidden _ _ _ _ _ _ _.
 exact(fo_hcache_empty s0.`1.`1 (acwc2_gfun s0.`3) ex).
qed.
lemma sim_ready_setup_correct s0 : fo_setup_valid s0=>
 phoare[SimObservedSetup.run:s=s0 ==>
 sim_phase_ready s0 SimPublic.pk SimPublic.suffix CCADecapOracle.sk SimPublic.cstar
  FOContext.w FOContext.g FOContext.challenge_h FOContext.challenge_hash FOContext.challenge_ct
  ROG.m ROH.m SimHistory.h SimBad.corr]=1%r.
proof. move=>hv;by conseq sim_observed_setup_ll (sim_ready_setup_state s0 hv). qed.

lemma sim_ready_phase_projection (P<:SimBoolPhase) s0 :
 equiv[P.distinguish ~ SimReadyPhase(P).distinguish:
 ={s,glob P} /\ s{1}=s0 /\
 sim_phase_ready s0 SimPublic.pk{2} SimPublic.suffix{2} CCADecapOracle.sk{2} SimPublic.cstar{2}
  FOContext.w{2} FOContext.g{2} FOContext.challenge_h{2} FOContext.challenge_hash{2} FOContext.challenge_ct{2}
  ROG.m{2} ROH.m{2} SimHistory.h{2} SimBad.corr{2} ==>
 ={res,glob P}].
proof.
 proc*;inline{2} SimReadyPhase(P).distinguish;sp.
 rcondt{2} 1;first by auto=> />.
 wp;call(_: ={arg,glob P} ==> ={res,glob P});first by proc true;auto.
 auto.
qed.

lemma sim_ready_kernel_projection (P<:SimBoolPhase) s0 : fo_setup_valid s0=>
 equiv[SimSetupPhase(P).guess ~ SimReadyKernel(P).guess:
 ={s,glob SimSetupPhase(P)} /\ s{1}=s0 ==> ={res}].
proof.
 move=>hv;proc;inline{2} SimReadyPhase(P).distinguish.
 rcondt{2} 4.
 + move=> &ml;wp;call(sim_ready_setup_state s0 hv);auto=> />.
 by sim.
qed.

lemma sim_ready_kernel_probability (P<:SimBoolPhase) s0 event &m : fo_setup_valid s0=>
 Pr[SimSetupPhase(P).guess(s0) @ &m:event res]=
 Pr[SimReadyKernel(P).guess(s0) @ &m:event res].
proof. move=>hv;byequiv(sim_ready_kernel_projection P s0 hv)=> //. qed.
