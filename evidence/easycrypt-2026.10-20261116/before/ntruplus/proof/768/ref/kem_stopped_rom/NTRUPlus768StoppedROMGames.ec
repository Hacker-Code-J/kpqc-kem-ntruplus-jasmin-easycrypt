require import AllCore Distr FMap StdOrder.
from Jasmin require import JWord.
require import Array32 Array192 Array14466.
require import NTRUPlus768StoppedKeygenModel NTRUPlus768StoppedKeygenPrefix.
require import NTRUPlus768ProposalModel NTRUPlus768ProposalSwitch.
require import NTRUPlus768FreshRetryLaw NTRUPlus768ProposalKeygenBridge.
require import NTRUPlus768ROMOracles.
import IntOrder RealOrder.

(* These direct games use the actual stopped implementation.  Only E's
   prior cache is configured; the current F-oracle state is retained. *)
module DirectROMStopped = {
  proc run(qf:int,qg:int,m0:(W8.t Array32.t,W8.t Array192.t) fmap) : stopped_output = {
    var result;
    ROE.m <- m0;
    result <@ StoppedKeygen(UniformSeedRNG,ExpandROM).run(qf,qg,witness);
    return result;
  }
}.
module DirectFreshStopped = {
  proc run(qf:int,qg:int) : stopped_output = {
    var result;
    result <@ StoppedKeygen(UniformSeedRNG,FreshExpand).run(qf,qg,witness);
    return result;
  }
}.

(* The event is an explicit argument, so none of the public probability
   statements requires a preconfigured ghost predicate. *)
module ROMStoppedEvent = {
  proc run(qf:int,qg:int,m0:(W8.t Array32.t,W8.t Array192.t) fmap,
    event:stopped_output -> bool) : bool = {
    var result;
    StoppedKeygenContext.event <- event;
    result <@ ROMProposalExperiment(StoppedKeygenContext).run(qf,qg,qf+qg,m0);
    return result;
  }
}.
module FreshStoppedEvent = {
  proc run(qf:int,qg:int,m0:(W8.t Array32.t,W8.t Array192.t) fmap,
    event:stopped_output -> bool) : bool = {
    var result;
    StoppedKeygenContext.event <- event;
    result <@ FreshProposalExperiment(StoppedKeygenContext).run(qf,qg,qf+qg,m0);
    return result;
  }
}.

lemma direct_rom_stopped_ll : islossless DirectROMStopped.run.
proof.
  proc; call (stopped_keygen_lossless UniformSeedRNG ExpandROM
    uniform_seed_rng_ll ro_e_shake_ll); auto.
qed.
lemma direct_fresh_stopped_ll : islossless DirectFreshStopped.run.
proof.
  proc; call (stopped_keygen_lossless UniformSeedRNG FreshExpand
    uniform_seed_rng_ll fresh_expand_ll); auto.
qed.

lemma configured_stopped_upto :
  equiv[ROMStoppedEvent.run ~ FreshStoppedEvent.run :
    ={qf,qg,m0,event,glob ROF,PairPorts.pending} ==>
    ROMProposal.bad{1}=FreshProposal.bad{2} /\
    (!FreshProposal.bad{2} => ={res})].
proof.
  proc; call (proposal_upto StoppedKeygenContext stopped_keygen_context_ll); auto.
qed.

lemma configured_fresh_birthday &mem qf0 qg0 ab cache event0 :
  0<=qf0 => 0<=qg0 => 0<=ab => fsize cache<=ab =>
  Pr[FreshStoppedEvent.run(qf0,qg0,cache,event0) @ &mem : FreshProposal.bad]
  <= proposal_delta ab (qf0+qg0).
proof.
  move=> qfge qgge age ms.
  have hb : phoare[FreshProposalExperiment(StoppedKeygenContext).run :
    qf=qf0 /\ qg=qg0 /\ q0=qf0+qg0 /\ m0=cache ==> FreshProposal.bad]
    <= (proposal_delta ab (qf0+qg0)).
  + bypr=> &m [hf [hg [hq hm]]].
    rewrite hf hg hq hm.
    apply (fresh_proposal_birthday StoppedKeygenContext &m qf0 qg0
      (qf0+qg0) ab cache); smt().
  byphoare (_: qf=qf0 /\ qg=qg0 /\ m0=cache ==> _) => //.
  proc; call hb; auto.
qed.

lemma configured_stopped_good &mem qf qg m0 event :
  Pr[ROMStoppedEvent.run(qf,qg,m0,event) @ &mem : res /\ !ROMProposal.bad] =
  Pr[FreshStoppedEvent.run(qf,qg,m0,event) @ &mem : res /\ !FreshProposal.bad].
proof. byequiv configured_stopped_upto=> //; smt(). qed.

lemma configured_stopped_bad &mem qf qg m0 event :
  Pr[ROMStoppedEvent.run(qf,qg,m0,event) @ &mem : ROMProposal.bad] =
  Pr[FreshStoppedEvent.run(qf,qg,m0,event) @ &mem : FreshProposal.bad].
proof. byequiv configured_stopped_upto=> //; smt(). qed.

lemma configured_stopped_distance &mem qf qg ab m0 event :
  0<=qf => 0<=qg => 0<=ab => fsize m0<=ab =>
  `|Pr[ROMStoppedEvent.run(qf,qg,m0,event) @ &mem : res] -
    Pr[FreshStoppedEvent.run(qf,qg,m0,event) @ &mem : res]|
  <= proposal_delta ab (qf+qg).
proof.
  move=> qfge qgge age ms.
  have good:=configured_stopped_good &mem qf qg m0 event.
  have bad:=configured_stopped_bad &mem qf qg m0 event.
  have fb:=configured_fresh_birthday &mem qf qg ab m0 event qfge qgge age ms.
  have rsub: Pr[ROMStoppedEvent.run(qf,qg,m0,event) @ &mem :
    res /\ ROMProposal.bad] <=
    Pr[ROMStoppedEvent.run(qf,qg,m0,event) @ &mem : ROMProposal.bad]
    by rewrite Pr[mu_sub].
  have fsub: Pr[FreshStoppedEvent.run(qf,qg,m0,event) @ &mem :
    res /\ FreshProposal.bad] <=
    Pr[FreshStoppedEvent.run(qf,qg,m0,event) @ &mem : FreshProposal.bad]
    by rewrite Pr[mu_sub].
  rewrite Pr[mu_split ROMProposal.bad].
  have -> : Pr[FreshStoppedEvent.run(qf,qg,m0,event) @ &mem : res] =
    Pr[FreshStoppedEvent.run(qf,qg,m0,event) @ &mem : res /\ FreshProposal.bad] +
    Pr[FreshStoppedEvent.run(qf,qg,m0,event) @ &mem : res /\ !FreshProposal.bad]
    by rewrite Pr[mu_split FreshProposal.bad].
  smt(mu_bounded).
qed.

lemma direct_rom_stopped_event_equiv (event0:stopped_output -> bool) :
  equiv[DirectROMStopped.run ~ ROMStoppedEvent.run :
    ={qf,qg,m0,glob ROF} /\ 0<=qf{1} /\ 0<=qg{1} /\ event{2}=event0 ==>
    event0 res{1}=res{2} /\ ={glob ROF}].
proof.
  proc; inline ROMProposalExperiment(StoppedKeygenContext).run
    StoppedKeygenContext(ROMProposal).run ROMProposal.init.
  wp; call stopped_rom_proposal_bridge; auto=> />; smt().
qed.
lemma direct_fresh_stopped_event_equiv (event0:stopped_output -> bool) :
  equiv[DirectFreshStopped.run ~ FreshStoppedEvent.run :
    ={qf,qg,glob ROF} /\ 0<=qf{1} /\ 0<=qg{1} /\ event{2}=event0 ==>
    event0 res{1}=res{2} /\ ={glob ROF}].
proof.
  proc; inline FreshProposalExperiment(StoppedKeygenContext).run
    StoppedKeygenContext(FreshProposal).run FreshProposal.init.
  wp; call stopped_fresh_proposal_bridge; auto=> />; smt().
qed.

lemma direct_rom_stopped_event &mem qf qg m0 (event:stopped_output -> bool) :
  0<=qf => 0<=qg =>
  Pr[DirectROMStopped.run(qf,qg,m0) @ &mem : event res] =
  Pr[ROMStoppedEvent.run(qf,qg,m0,event) @ &mem : res].
proof.
  move=> qfge qgge.
  byequiv (direct_rom_stopped_event_equiv event)=> //; smt().
qed.
lemma direct_fresh_stopped_event &mem qf qg m0 (event:stopped_output -> bool) :
  0<=qf => 0<=qg =>
  Pr[DirectFreshStopped.run(qf,qg) @ &mem : event res] =
  Pr[FreshStoppedEvent.run(qf,qg,m0,event) @ &mem : res].
proof.
  move=> qfge qgge.
  byequiv (direct_fresh_stopped_event_equiv event)=> //; smt().
qed.

lemma stopped_rom_fresh_distance &mem qf qg ab m0 (event:stopped_output -> bool) :
  0<=qf => 0<=qg => 0<=ab => fsize m0<=ab =>
  `|Pr[DirectROMStopped.run(qf,qg,m0) @ &mem : event res] -
    Pr[DirectFreshStopped.run(qf,qg) @ &mem : event res]|
  <= proposal_delta ab (qf+qg).
proof.
  move=> qfge qgge age ms.
  rewrite (direct_rom_stopped_event &mem qf qg m0 event qfge qgge)
    (direct_fresh_stopped_event &mem qf qg m0 event qfge qgge).
  exact (configured_stopped_distance &mem qf qg ab m0 event qfge qgge age ms).
qed.
