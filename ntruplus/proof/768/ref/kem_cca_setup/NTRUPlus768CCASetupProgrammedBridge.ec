require import AllCore Distr FMap.
from Jasmin require import JWord.
require import Array32 Array192 Array14466.
require import NTRUPlus768CCASetupState NTRUPlus768ROMOracles.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768StoppedKeygenModel.
require import NTRUPlus768FreshRetryLaw NTRUPlus768AttemptRealized.
require import NTRUPlus768ProposalModel NTRUPlus768ProposalSwitch NTRUPlus768ProposalKeygenBridge.

(* The programmed E table equals the proposal's shadow table even after a
   repeated seed: both fresh models retain the most recently sampled value.
   This exact bridge is separate from the ROM coupling, which is only good
   until the first collision. One counter covers both rejection stages. *)

lemma programmed_result_f_proposal c qb q0 :
 equiv[ResultRetry(UniformSeedRNG,ProgrammedFreshExpand).f ~
       ResultRetry(PairPorts(FreshProposal),PairPorts(FreshProposal)).f :
 0<=q0 /\ c+q0<=qb /\ limit{1}=q0 /\ ={limit} /\
 ROE.m{1}=FreshProposal.m{2} /\ FreshProposal.n{2}=c /\ FreshProposal.q{2}=qb ==>
 ={res} /\ ROE.m{1}=FreshProposal.m{2} /\
 FreshProposal.n{2}=c+res.`rs_count{2} /\ FreshProposal.q{2}=qb /\ 0<=res.`rs_count{2}<=q0].
proof.
 proc.
 while(0<=q0 /\ c+q0<=qb /\ ={limit,buf,ntt,inverse,status,count} /\ limit{1}=q0 /\
  ROE.m{1}=FreshProposal.m{2} /\ FreshProposal.n{2}=c+count{2} /\
  FreshProposal.q{2}=qb /\ 0<=count{2}<=q0).
 + inline AttemptResult(ProgrammedFreshExpand).f AttemptResult(PairPorts(FreshProposal)).f.
   inline UniformSeedRNG.sample ProgrammedFreshExpand.shake PairPorts(FreshProposal).sample
     PairPorts(FreshProposal).shake FreshProposal.draw.
   rcondt{2} 3; first by auto=> />; smt().
   by auto=> />; smt().
 by auto=> />; smt().
qed.

lemma programmed_result_g_proposal c qb q0 :
 equiv[ResultRetry(UniformSeedRNG,ProgrammedFreshExpand).g ~
       ResultRetry(PairPorts(FreshProposal),PairPorts(FreshProposal)).g :
 0<=q0 /\ c+q0<=qb /\ limit{1}=q0 /\ ={limit} /\
 ROE.m{1}=FreshProposal.m{2} /\ FreshProposal.n{2}=c /\ FreshProposal.q{2}=qb ==>
 ={res} /\ ROE.m{1}=FreshProposal.m{2} /\
 FreshProposal.n{2}=c+res.`rs_count{2} /\ FreshProposal.q{2}=qb /\ 0<=res.`rs_count{2}<=q0].
proof.
 proc.
 while(0<=q0 /\ c+q0<=qb /\ ={limit,buf,ntt,inverse,status,count} /\ limit{1}=q0 /\
  ROE.m{1}=FreshProposal.m{2} /\ FreshProposal.n{2}=c+count{2} /\
  FreshProposal.q{2}=qb /\ 0<=count{2}<=q0).
 + inline AttemptResult(ProgrammedFreshExpand).g AttemptResult(PairPorts(FreshProposal)).g.
   inline UniformSeedRNG.sample ProgrammedFreshExpand.shake PairPorts(FreshProposal).sample
     PairPorts(FreshProposal).shake FreshProposal.draw.
   rcondt{2} 3; first by auto=> />; smt().
   by auto=> />; smt().
 by auto=> />; smt().
qed.

lemma programmed_result_stopped_proposal :
 equiv[ResultStoppedKeygen(UniformSeedRNG,ProgrammedFreshExpand).run ~
       ResultStoppedKeygen(PairPorts(FreshProposal),PairPorts(FreshProposal)).run :
 ={qf,qg,workspace,glob ROF} /\ ROE.m{1}=FreshProposal.m{2} /\
 0<=qf{1} /\ 0<=qg{1} /\ FreshProposal.n{2}=0 /\ FreshProposal.q{2}=qf{1}+qg{1} ==>
 ={res,glob ROF} /\ ROE.m{1}=FreshProposal.m{2}].
proof.
 proc.
 seq 3 3:(={qf,qg,workspace,fv,gv,result,glob ROF} /\ ROE.m{1}=FreshProposal.m{2} /\
  0<=qf{1} /\ 0<=qg{1} /\ FreshProposal.n{2}=fv.`rs_count{2} /\
  FreshProposal.q{2}=qf{1}+qg{1} /\ 0<=fv.`rs_count{2}<=qf{1}).
 + ecall(programmed_result_f_proposal 0 (qf{1}+qg{1}) qf{1}); auto=> />; smt().
 if; 1,3:by auto.
 seq 1 1:(={workspace,fv,gv,result,glob ROF} /\ ROE.m{1}=FreshProposal.m{2}).
 + ecall(programmed_result_g_proposal fv.`rs_count{2} (qf{1}+qg{1}) qg{1}); auto=> />; smt().
 if; 1,3:by auto.
 wp; call (_: ={fv,gv,workspace,glob ROF} ==> ={res,glob ROF}); first by sim.
 auto.
qed.

lemma programmed_stopped_proposal_bridge :
 equiv[StoppedKeygen(UniformSeedRNG,ProgrammedFreshExpand).run ~
       StoppedKeygen(PairPorts(FreshProposal),PairPorts(FreshProposal)).run :
 ={qf,qg,workspace,glob ROF} /\ ROE.m{1}=FreshProposal.m{2} /\
 0<=qf{1} /\ 0<=qg{1} /\ FreshProposal.n{2}=0 /\ FreshProposal.q{2}=qf{1}+qg{1} ==>
 ={res,glob ROF} /\ ROE.m{1}=FreshProposal.m{2}].
proof.
 transitivity ResultStoppedKeygen(UniformSeedRNG,ProgrammedFreshExpand).run
  (={qf,qg,workspace,glob ROE,glob ROF} ==> ={res,glob ROE,glob ROF})
  (={qf,qg,workspace,glob ROF} /\ ROE.m{1}=FreshProposal.m{2} /\
   0<=qf{1} /\ 0<=qg{1} /\ FreshProposal.n{2}=0 /\ FreshProposal.q{2}=qf{1}+qg{1} ==>
   ={res,glob ROF} /\ ROE.m{1}=FreshProposal.m{2}) => //.
 + smt().
 + exact(stopped_result_equiv UniformSeedRNG ProgrammedFreshExpand).
 transitivity ResultStoppedKeygen(PairPorts(FreshProposal),PairPorts(FreshProposal)).run
  (={qf,qg,workspace,glob ROF} /\ ROE.m{1}=FreshProposal.m{2} /\
   0<=qf{1} /\ 0<=qg{1} /\ FreshProposal.n{2}=0 /\ FreshProposal.q{2}=qf{1}+qg{1} ==>
   ={res,glob ROF} /\ ROE.m{1}=FreshProposal.m{2})
  (={qf,qg,workspace,glob FreshProposal,PairPorts.pending,glob ROF} ==>
   ={res,glob FreshProposal,PairPorts.pending,glob ROF}) => //.
 + smt().
 + exact programmed_result_stopped_proposal.
 symmetry; conseq(stopped_paired_result_equiv FreshProposal); smt().
qed.

