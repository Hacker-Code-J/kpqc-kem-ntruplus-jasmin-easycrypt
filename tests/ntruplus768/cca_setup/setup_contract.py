"""The setup comparison carries actual key output and both correlated tables."""
BASE='ntruplus/proof/768/ref/kem_cca_setup/'
STATE=BASE+'NTRUPlus768CCASetupState.ec'
PROGRAMMED=BASE+'NTRUPlus768CCASetupProgrammed.ec'
BRIDGE=BASE+'NTRUPlus768CCASetupProgrammedBridge.ec'
SWITCH=BASE+'NTRUPlus768CCASetupSwitch.ec'
RULES=(
 (STATE,'joint setup retains key output, E table and F table',r'type cca_setup_state = keygen_output * cca_e_table * cca_f_table.'),
 (STATE,'programmed expansion always draws independently and records even repeated seeds',r'module ProgrammedFreshExpand = { proc shake(seed:W8.t Array32.t) : W8.t Array192.t = { var y:W8.t Array192.t; y <$ uniform192; ROE.m.[seed] <- y; return y; } }.'),
 (STATE,'joint observation follows the actual instrumented KeyGen and its F port',r'module JointSetup(E:KeygenExpand) = { proc run(workspace:W8.t Array14466.t) : cca_setup_state = { var out:keygen_output; out <@ KeygenInstrumented(UniformSeedRNG,E,SHAKEFROM).run(workspace); return (out,ROE.m,ROF.m); } }.'),
 (STATE,'setup source initializes E/F before key generation and preserves the resulting snapshot',r'module JointSetupSource(E:KeygenExpand) = { proc guess(workspace:W8.t Array14466.t) : cca_setup_state = { var out:cca_setup_state; ROE.init(); ROF.init(); out <@ JointSetup(E).run(workspace); return out; } }.'),
 (PROGRAMMED,'the fresh-key projection preserves F state without identifying the E table',r'lemma programmed_keygen_projection : equiv[KeygenInstrumented(UniformSeedRNG,ProgrammedFreshExpand,SHAKEFROM).run ~ KeygenInstrumented(UniformSeedRNG,FreshExpand,SHAKEFROM).run : ={workspace,glob ROF} ==> ={res,glob ROF}].'),
 (PROGRAMMED,'unlimited losslessness is proved for the programmed fresh model only',r'lemma programmed_keygen_ll : islossless KeygenInstrumented(UniformSeedRNG,ProgrammedFreshExpand,SHAKEFROM).run.'),
 (SWITCH,'stopped joint experiment retains explicitly supplied E/F before the actual stopped keygen',r'module CCAStoppedJoint(E:KeygenExpand) = { proc run(qf:int,qg:int,m0:cca_e_table,f0:cca_f_table) : cca_stopped_state = { var out:stopped_output; ROE.m <- m0; ROF.m <- f0; out <@ StoppedKeygen(UniformSeedRNG,E).run(qf,qg,witness); return(out,ROE.m,ROF.m); } }.'),
 (SWITCH,'fresh proposal experiment uses one summed budget and returns its actual shadow E table',r'module CCAFreshStoppedProposal = { proc run(qf:int,qg:int,m0:cca_e_table,f0:cca_f_table) : cca_stopped_state = { var b:bool; ROF.m <- f0; CCAStoppedContext.out <- witness; PairPorts.pending <- witness; b <@ FreshProposalExperiment(CCAStoppedContext).run(qf,qg,qf+qg,m0); return(CCAStoppedContext.out,FreshProposal.m,ROF.m); } }.'),
 (BRIDGE,'programmed proposal bridge preserves both tables with one counter cap for both stages',r'lemma programmed_stopped_proposal_bridge : equiv[StoppedKeygen(UniformSeedRNG,ProgrammedFreshExpand).run ~ StoppedKeygen(PairPorts(FreshProposal),PairPorts(FreshProposal)).run : ={qf,qg,workspace,glob ROF} /\ ROE.m{1}=FreshProposal.m{2} /\ 0<=qf{1} /\ 0<=qg{1} /\ FreshProposal.n{2}=0 /\ FreshProposal.q{2}=qf{1}+qg{1} ==> ={res,glob ROF} /\ ROE.m{1}=FreshProposal.m{2}].'),
)
MUTATIONS=(
 ('setup-state-omits-E-table',STATE,'type cca_setup_state = keygen_output * cca_e_table * cca_f_table.','type cca_setup_state = keygen_output * cca_f_table.'),
 ('setup-state-omits-F-table',STATE,'type cca_setup_state = keygen_output * cca_e_table * cca_f_table.','type cca_setup_state = keygen_output * cca_e_table.'),
 ('programmed-expansion-forgets-to-record-the-draw',STATE,'ROE.m.[seed] <- y;',''),
 ('programmed-expansion-caches-hits-instead-of-drawing-independently',STATE,'y <$ uniform192; ROE.m.[seed] <- y;','if(seed \\in ROE.m){y <- oget ROE.m.[seed];}else{y <$ uniform192;ROE.m.[seed] <- y;}'),
 ('programmed-expansion-refuses-to-overwrite-an-existing-seed',STATE,'ROE.m.[seed] <- y;','if(seed \\notin ROE.m){ROE.m.[seed] <- y;}'),
 ('joint-keygen-ignores-its-actual-expansion-port',STATE,'KeygenInstrumented(UniformSeedRNG,E,SHAKEFROM).run(workspace)','KeygenInstrumented(UniformSeedRNG,FreshExpand,SHAKEFROM).run(workspace)'),
 ('joint-output-replaces-E-with-an-empty-table',STATE,'return (out,ROE.m,ROF.m);','return (out,empty,ROF.m);'),
 ('joint-output-replaces-F-with-an-empty-table',STATE,'return (out,ROE.m,ROF.m);','return (out,ROE.m,empty);'),
 ('setup-source-clears-tables-after-key-generation',STATE,'out <@ JointSetup(E).run(workspace); return out;','out <@ JointSetup(E).run(workspace); ROE.init(); ROF.init(); return out;'),
 ('unlimited-actual-ROM-losslessness-substituted-for-fresh-model',PROGRAMMED,'lemma programmed_keygen_ll : islossless KeygenInstrumented(UniformSeedRNG,ProgrammedFreshExpand,SHAKEFROM).run.','lemma programmed_keygen_ll : islossless KeygenInstrumented(UniformSeedRNG,ExpandROM,SHAKEFROM).run.'),
 ('joint-stopped-call-drops-the-g-budget',SWITCH,'StoppedKeygen(UniformSeedRNG,E).run(qf,qg,witness)','StoppedKeygen(UniformSeedRNG,E).run(qf,0,witness)'),
 ('proposal-cap-resets-at-the-start-of-g',SWITCH,'FreshProposalExperiment(CCAStoppedContext).run(qf,qg,qf+qg,m0)','FreshProposalExperiment(CCAStoppedContext).run(qf,qg,qg,m0)'),
 ('fresh-proposal-snapshot-substitutes-unrelated-ROE-state',SWITCH,'return(CCAStoppedContext.out,FreshProposal.m,ROF.m);','return(CCAStoppedContext.out,ROE.m,ROF.m);'),
 ('programmed-bridge-forgets-correlation-with-the-final-E-table',BRIDGE,r'lemma programmed_stopped_proposal_bridge : equiv[StoppedKeygen(UniformSeedRNG,ProgrammedFreshExpand).run ~ StoppedKeygen(PairPorts(FreshProposal),PairPorts(FreshProposal)).run : ={qf,qg,workspace,glob ROF} /\ ROE.m{1}=FreshProposal.m{2} /\ 0<=qf{1} /\ 0<=qg{1} /\ FreshProposal.n{2}=0 /\ FreshProposal.q{2}=qf{1}+qg{1} ==> ={res,glob ROF} /\ ROE.m{1}=FreshProposal.m{2}].',r'lemma programmed_stopped_proposal_bridge : equiv[StoppedKeygen(UniformSeedRNG,ProgrammedFreshExpand).run ~ StoppedKeygen(PairPorts(FreshProposal),PairPorts(FreshProposal)).run : ={qf,qg,workspace,glob ROF} /\ ROE.m{1}=FreshProposal.m{2} /\ 0<=qf{1} /\ 0<=qg{1} /\ FreshProposal.n{2}=0 /\ FreshProposal.q{2}=qf{1}+qg{1} ==> ={res,glob ROF}].'),
)
