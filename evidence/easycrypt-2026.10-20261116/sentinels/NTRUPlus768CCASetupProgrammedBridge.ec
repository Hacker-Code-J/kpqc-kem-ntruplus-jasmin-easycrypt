

lemma __cca_setup_eof_2 :
 equiv[StoppedKeygen(UniformSeedRNG,ProgrammedFreshExpand).run ~
       StoppedKeygen(PairPorts(FreshProposal),PairPorts(FreshProposal)).run :
 ={qf,qg,workspace,glob ROF} /\ ROE.m{1}=FreshProposal.m{2} /\
 0<=qf{1} /\ 0<=qg{1} /\ FreshProposal.n{2}=0 /\ FreshProposal.q{2}=qf{1}+qg{1} ==>
 ={res,glob ROF} /\ ROE.m{1}=FreshProposal.m{2}].
proof. exact (programmed_stopped_proposal_bridge). qed.
