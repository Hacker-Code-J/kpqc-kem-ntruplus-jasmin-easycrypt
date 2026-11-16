
lemma __stopped_actual_bridge_eof :
 equiv[StoppedKeygen(UniformSeedRNG,ExpandROM).run ~
       StoppedKeygen(PairPorts(ROMProposal),PairPorts(ROMProposal)).run :
 ={qf,qg,workspace,glob ROE,glob ROF} /\ 0<=qf{1} /\ 0<=qg{1} /\
 ROMProposal.n{2}=0 /\ ROMProposal.q{2}=qf{1}+qg{1} ==>
 ={res,glob ROE,glob ROF}].
proof. exact stopped_rom_proposal_bridge. qed.
