require import AllCore Distr FMap StdOrder.
from Jasmin require import JWord.
require import Array32 Array192 Array14466.
require import NTRUPlus768ProposalModel NTRUPlus768ProposalSwitch.
require import NTRUPlus768ROMDistributions NTRUPlus768ROMOracles.
require import NTRUPlus768StoppedKeygenModel NTRUPlus768StoppedKeygenPrefix.
require import NTRUPlus768FreshRetryLaw NTRUPlus768ProposalKeygenBridge.
require import NTRUPlus768KeygenCompleteSpec.
require import NTRUPlus768CCASetupState.
import IntOrder RealOrder.

(* The context cannot inspect E, the shadow table, or the proposal counters.
   Its own final state and the complete E tables agree until the first hit. *)
lemma cca_proposal_upto
 (A <: ProposalContext {-FreshProposal,-ROMProposal,-ROE}) :
 (forall (P <: ProposalPort {-A}),
   islossless P.draw => islossless A(P).run) =>
 equiv[ROMProposalExperiment(A).run ~ FreshProposalExperiment(A).run :
   ={qf,qg,q0,m0,glob A} ==>
   ROMProposal.bad{1}=FreshProposal.bad{2} /\
   (!FreshProposal.bad{2} => ={res,glob A} /\ ROE.m{1}=FreshProposal.m{2})].
proof.
 move=>all; proc.
 call (_: FreshProposal.bad,
   ROMProposal.n{1}=FreshProposal.n{2} /\
   ROMProposal.q{1}=FreshProposal.q{2} /\
   ROMProposal.bad{1}=FreshProposal.bad{2} /\
   ROE.m{1}=FreshProposal.m{2},
   ROMProposal.bad{1}=FreshProposal.bad{2}).
 + conseq rom_fresh_proposal_step; smt().
 + move=> &2 h; proc; sp 2; if; last by auto; smt().
   wp; call roe_get_ll; auto=> />; smt(uniform32_ll).
 + move=> &1; proc; sp 2; if; auto=> />; smt(uniform32_ll uniform192_ll).
 + inline ROMProposal.init FreshProposal.init; auto; smt().
qed.

type cca_stopped_state = stopped_output * cca_e_table * cca_f_table.

module CCAStoppedContext(P:ProposalPort) = {
 var out:stopped_output
 proc run(qf:int,qg:int) : bool = {
  out <@ StoppedKeygen(PairPorts(P),PairPorts(P)).run(qf,qg,witness);
  return true;
 }
}.
lemma cca_stopped_context_ll (P<:ProposalPort {-CCAStoppedContext}) :
 islossless P.draw => islossless CCAStoppedContext(P).run.
proof.
 move=>hp; proc.
 call(stopped_keygen_lossless (PairPorts(P)) (PairPorts(P))
   (pair_ports_sample_lossless P hp) (pair_ports_shake_lossless P)); auto.
qed.

(* Explicit initial tables make the joint observation independent of a
   preconfigured ghost event. Arbitrary prior F entries are retained. *)
module CCAStoppedJoint(E:KeygenExpand) = {
 proc run(qf:int,qg:int,m0:cca_e_table,f0:cca_f_table) : cca_stopped_state = {
  var out:stopped_output;
  ROE.m <- m0; ROF.m <- f0;
  out <@ StoppedKeygen(UniformSeedRNG,E).run(qf,qg,witness);
  return(out,ROE.m,ROF.m);
 }
}.
module CCAROMStoppedProposal = {
 proc run(qf:int,qg:int,m0:cca_e_table,f0:cca_f_table) : cca_stopped_state = {
  var b:bool;
  ROF.m <- f0; CCAStoppedContext.out <- witness; PairPorts.pending <- witness;
  b <@ ROMProposalExperiment(CCAStoppedContext).run(qf,qg,qf+qg,m0);
  return(CCAStoppedContext.out,ROE.m,ROF.m);
 }
}.
module CCAFreshStoppedProposal = {
 proc run(qf:int,qg:int,m0:cca_e_table,f0:cca_f_table) : cca_stopped_state = {
  var b:bool;
  ROF.m <- f0; CCAStoppedContext.out <- witness; PairPorts.pending <- witness;
  b <@ FreshProposalExperiment(CCAStoppedContext).run(qf,qg,qf+qg,m0);
  return(CCAStoppedContext.out,FreshProposal.m,ROF.m);
 }
}.

lemma cca_stopped_proposal_upto :
 equiv[CCAROMStoppedProposal.run ~ CCAFreshStoppedProposal.run:
   ={qf,qg,m0,f0} ==>
   ROMProposal.bad{1}=FreshProposal.bad{2} /\ (!FreshProposal.bad{2} => ={res})].
proof.
 proc; call(cca_proposal_upto CCAStoppedContext cca_stopped_context_ll); auto=> />; smt().
qed.

lemma cca_stopped_joint_ll (E<:KeygenExpand) :
 islossless E.shake => islossless CCAStoppedJoint(E).run.
proof.
 move=>he; proc.
 call(stopped_keygen_lossless UniformSeedRNG E uniform_seed_rng_ll he); auto.
qed.

lemma cca_stopped_proposal_good &mem qf qg m0 f0 (event:cca_stopped_state->bool) :
 Pr[CCAROMStoppedProposal.run(qf,qg,m0,f0) @ &mem:event res /\ !ROMProposal.bad]=
 Pr[CCAFreshStoppedProposal.run(qf,qg,m0,f0) @ &mem:event res /\ !FreshProposal.bad].
proof. byequiv cca_stopped_proposal_upto=>//; smt(). qed.
lemma cca_stopped_proposal_bad &mem qf qg m0 f0 :
 Pr[CCAROMStoppedProposal.run(qf,qg,m0,f0) @ &mem:ROMProposal.bad]=
 Pr[CCAFreshStoppedProposal.run(qf,qg,m0,f0) @ &mem:FreshProposal.bad].
proof. byequiv cca_stopped_proposal_upto=>//; smt(). qed.

lemma cca_stopped_fresh_birthday &mem qf0 qg0 a cache f0 :
 0<=qf0 =>0<=qg0 =>0<=a =>fsize cache<=a =>
 Pr[CCAFreshStoppedProposal.run(qf0,qg0,cache,f0) @ &mem:FreshProposal.bad]
 <=proposal_delta a(qf0+qg0).
proof.
 move=>hf hg ha hs.
 have hb:phoare[FreshProposalExperiment(CCAStoppedContext).run:
   qf=qf0 /\ qg=qg0 /\ q0=qf0+qg0 /\ m0=cache ==>FreshProposal.bad]
   <=(proposal_delta a(qf0+qg0)).
 + bypr=> &m [hqf [hqg [hq hm]]].
   rewrite hqf hqg hq hm.
   apply(fresh_proposal_birthday CCAStoppedContext &m qf0 qg0 (qf0+qg0) a cache); smt().
 byphoare(_:qf=qf0 /\ qg=qg0 /\ m0=cache ==>_)=>//.
 proc; call hb; auto.
qed.

lemma cca_stopped_proposal_distance &mem qf qg a m0 f0 (event:cca_stopped_state->bool) :
 0<=qf =>0<=qg =>0<=a =>fsize m0<=a =>
 `|Pr[CCAROMStoppedProposal.run(qf,qg,m0,f0) @ &mem:event res]-
   Pr[CCAFreshStoppedProposal.run(qf,qg,m0,f0) @ &mem:event res]|
 <=proposal_delta a(qf+qg).
proof.
 move=>hf hg ha hs.
 have good:=cca_stopped_proposal_good &mem qf qg m0 f0 event.
 have bad:=cca_stopped_proposal_bad &mem qf qg m0 f0.
 have fb:=cca_stopped_fresh_birthday &mem qf qg a m0 f0 hf hg ha hs.
 have rsub:Pr[CCAROMStoppedProposal.run(qf,qg,m0,f0) @ &mem:event res /\ ROMProposal.bad]<=
   Pr[CCAROMStoppedProposal.run(qf,qg,m0,f0) @ &mem:ROMProposal.bad]
   by rewrite Pr[mu_sub].
 have fsub:Pr[CCAFreshStoppedProposal.run(qf,qg,m0,f0) @ &mem:event res /\ FreshProposal.bad]<=
   Pr[CCAFreshStoppedProposal.run(qf,qg,m0,f0) @ &mem:FreshProposal.bad]
   by rewrite Pr[mu_sub].
 rewrite Pr[mu_split ROMProposal.bad].
 have ->:Pr[CCAFreshStoppedProposal.run(qf,qg,m0,f0) @ &mem:event res]=
   Pr[CCAFreshStoppedProposal.run(qf,qg,m0,f0) @ &mem:event res /\ FreshProposal.bad]+
   Pr[CCAFreshStoppedProposal.run(qf,qg,m0,f0) @ &mem:event res /\ !FreshProposal.bad]
   by rewrite Pr[mu_split FreshProposal.bad].
 smt(mu_bounded).
qed.

lemma cca_stopped_rom_proposal_equiv :
 equiv[CCAStoppedJoint(ExpandROM).run ~ CCAROMStoppedProposal.run:
   ={qf,qg,m0,f0} /\ 0<=qf{1} /\ 0<=qg{1} ==> ={res}].
proof.
 proc; inline ROMProposalExperiment(CCAStoppedContext).run
   CCAStoppedContext(ROMProposal).run ROMProposal.init.
 wp; call stopped_rom_proposal_bridge; auto=> />; smt().
qed.

require import NTRUPlus768CCASetupProgrammedBridge.

lemma cca_stopped_programmed_proposal_equiv :
 equiv[CCAStoppedJoint(ProgrammedFreshExpand).run ~ CCAFreshStoppedProposal.run:
   ={qf,qg,m0,f0} /\ 0<=qf{1} /\ 0<=qg{1} ==> ={res}].
proof.
 proc; inline FreshProposalExperiment(CCAStoppedContext).run
   CCAStoppedContext(FreshProposal).run FreshProposal.init.
 wp; call programmed_stopped_proposal_bridge; auto=> />; smt().
qed.

lemma cca_stopped_rom_proposal_event &mem qf qg m0 f0 (event:cca_stopped_state->bool) :
 0<=qf =>0<=qg =>
 Pr[CCAStoppedJoint(ExpandROM).run(qf,qg,m0,f0) @ &mem:event res]=
 Pr[CCAROMStoppedProposal.run(qf,qg,m0,f0) @ &mem:event res].
proof. move=>hf hg; byequiv cca_stopped_rom_proposal_equiv=>//; smt(). qed.

lemma cca_stopped_programmed_proposal_event &mem qf qg m0 f0 (event:cca_stopped_state->bool) :
 0<=qf =>0<=qg =>
 Pr[CCAStoppedJoint(ProgrammedFreshExpand).run(qf,qg,m0,f0) @ &mem:event res]=
 Pr[CCAFreshStoppedProposal.run(qf,qg,m0,f0) @ &mem:event res].
proof. move=>hf hg; byequiv cca_stopped_programmed_proposal_equiv=>//; smt(). qed.

(* Arbitrary joint events may inspect the complete stopped output and both
   final tables. F's initial cache is unrestricted; E is charged by fsize. *)
lemma cca_stopped_joint_distance &mem qf qg a m0 f0 (event:cca_stopped_state->bool) :
 0<=qf =>0<=qg =>0<=a =>fsize m0<=a =>
 `|Pr[CCAStoppedJoint(ExpandROM).run(qf,qg,m0,f0) @ &mem:event res]-
   Pr[CCAStoppedJoint(ProgrammedFreshExpand).run(qf,qg,m0,f0) @ &mem:event res]|
 <=proposal_delta a(qf+qg).
proof.
 move=>hf hg ha hs.
 rewrite (cca_stopped_rom_proposal_event &mem qf qg m0 f0 event hf hg)
   (cca_stopped_programmed_proposal_event &mem qf qg m0 f0 event hf hg).
 exact(cca_stopped_proposal_distance &mem qf qg a m0 f0 event hf hg ha hs).
qed.
