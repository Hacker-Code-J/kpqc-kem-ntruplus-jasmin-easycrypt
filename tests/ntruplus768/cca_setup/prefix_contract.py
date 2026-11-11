"""The stopped prefix retains joint state and actual-ROM nontermination mass."""
BASE='ntruplus/proof/768/ref/kem_cca_setup/'
PREFIX=BASE+'NTRUPlus768CCASetupPrefix.ec'
BOUND=BASE+'NTRUPlus768CCASetupBound.ec'
SWITCH=BASE+'NTRUPlus768CCASetupSwitch.ec'
RULES=(
 (PREFIX,'stopped events require a completed key and include both final tables',r'op stopped_success_event (event:cca_setup_state->bool) (s:cca_stopped_state) = stopped_success s.`1 /\ event (oget s.`1.`1,s.`2,s.`3).'),
 (PREFIX,'counted joint events erase only counters while retaining key and E/F',r'op counted_joint_event (event:cca_setup_state->bool) (s:cca_counted_state) = event (s.`1.`1,s.`2,s.`3).'),
 (PREFIX,'both retry counts remain in the prefix predicate',r'op counted_joint_within qf qg (s:cca_counted_state) = counted_within qf qg s.`1.'),
 (PREFIX,'resumption preserves prior retry states and tables through both stages and actual finish',r'module CCAFlatResumedSetup(E:KeygenExpand) = { proc run(qf:int,qg:int,m0:cca_e_table,f0:cca_f_table) : cca_counted_state = { var qf0,qg0:int; var workspace:W8.t Array14466.t; var fv,gv:retry_state; var out0:keygen_output; var out:counted_output; ROE.m <- m0; ROF.m <- f0; qf0 <- qf; qg0 <- qg; workspace <- witness; PrefixBad.bad <- false; fv <@ BoundedRetry(UniformSeedRNG,E).f(qf0); if (!fv.`rs_ok) { PrefixBad.bad <- true; fv <@ CountedRetry(UniformSeedRNG,E).f_from(fv); } gv <@ BoundedRetry(UniformSeedRNG,E).g(qg0); if (!gv.`rs_ok) { PrefixBad.bad <- true; gv <@ CountedRetry(UniformSeedRNG,E).g_from(gv); } out0 <@ ObservedFinish.run(fv,gv,workspace); out <- (out0,fv.`rs_count,gv.`rs_count); return(out,ROE.m,ROF.m); } }.'),
 (PREFIX,'actual-ROM prefix identity has no unlimited losslessness premise',r'lemma cca_configured_counted_stopped_prefix_rom &m qf0 qg0 m0 f0 (event:cca_setup_state->bool) : Pr[CCAConfiguredCountedSetup(ExpandROM).run(m0,f0) @ &m: counted_joint_within qf0 qg0 res /\ counted_joint_event event res] = Pr[CCAStoppedJoint(ExpandROM).run(qf0,qg0,m0,f0) @ &m: stopped_success_event event res].'),
 (SWITCH,'the stopped coupling equates outputs only before the collision bad event',r'lemma cca_stopped_proposal_upto : equiv[CCAROMStoppedProposal.run ~ CCAFreshStoppedProposal.run: ={qf,qg,m0,f0} ==> ROMProposal.bad{1}=FreshProposal.bad{2} /\ (!FreshProposal.bad{2} => ={res})].'),
 (BOUND,'arbitrary joint events are compared without setup termination conditioning',r'lemma cca_setup_source_distance &m qf qg (event:cca_setup_state->bool) : 0<=qf => 0<=qg => `|Pr[JointSetupSource(ExpandROM).guess(witness) @ &m:event res]- Pr[JointSetupSource(ProgrammedFreshExpand).guess(witness) @ &m:event res]| <= proposal_delta 0 (qf+qg)+fresh_retry_tail qf qg.'),
 (BOUND,'actual-ROM missing mass remains explicit and bounded without losslessness',r'lemma cca_setup_source_missing_mass_256 &m : 0%r<=1%r-Pr[JointSetupSource(ExpandROM).guess(witness) @ &m:true]<= 130818%r/(2%r^256).'),
)
MUTATIONS=(
 ('stopped-event-counts-absent-output-as-a-real-key',PREFIX,r'stopped_success s.`1 /\ event (oget s.`1.`1,s.`2,s.`3).','event (oget s.`1.`1,s.`2,s.`3).'),
 ('counted-joint-event-forgets-EF-correlation',PREFIX,'event (s.`1.`1,s.`2,s.`3).','event (s.`1.`1,empty,empty).'),
 ('prefix-predicate-uses-f-budget-for-both-counts',PREFIX,'counted_within qf qg s.`1.','counted_within qf qf s.`1.'),
 ('resumed-f-stage-restarts-its-count-and-buffer',PREFIX,'CountedRetry(UniformSeedRNG,E).f_from(fv)','CountedRetry(UniformSeedRNG,E).f()'),
 ('resumed-g-stage-restarts-its-count-and-buffer',PREFIX,'CountedRetry(UniformSeedRNG,E).g_from(gv)','CountedRetry(UniformSeedRNG,E).g()'),
 ('E-table-is-cleared-between-f-and-g-retry-stages',PREFIX,'gv <@ BoundedRetry(UniformSeedRNG,E).g(qg0);','ROE.init(); gv <@ BoundedRetry(UniformSeedRNG,E).g(qg0);'),
 ('resumed-finish-resamples-the-accepted-f-before-g-finalization',PREFIX,'out0 <@ ObservedFinish.run(fv,gv,workspace);','fv <@ CountedRetry(UniformSeedRNG,E).f(); out0 <@ ObservedFinish.run(fv,gv,workspace);'),
 ('actual-ROM-prefix-assumes-unlimited-keygen-termination',PREFIX,'lemma cca_configured_counted_stopped_prefix_rom &m qf0 qg0 m0 f0 (event:cca_setup_state->bool) :','lemma cca_configured_counted_stopped_prefix_rom &m qf0 qg0 m0 f0 (event:cca_setup_state->bool) : islossless CountedKeygen(UniformSeedRNG,ExpandROM).run =>'),
 ('ROM-fresh-equality-is-reused-after-a-collision',SWITCH,'(!FreshProposal.bad{2} => ={res})','(={res})'),
 ('source-event-distance-adds-actual-ROM-losslessness',BOUND,'lemma cca_setup_source_distance &m qf qg (event:cca_setup_state->bool) :','lemma cca_setup_source_distance &m qf qg (event:cca_setup_state->bool) : islossless JointSetupSource(ExpandROM).guess =>'),
 ('missing-mass-bound-is-replaced-by-an-assumed-zero-mass-loss',BOUND,'lemma cca_setup_source_missing_mass_256 &m :','lemma cca_setup_source_missing_mass_256 &m : Pr[JointSetupSource(ExpandROM).guess(witness) @ &m:true]=1%r =>'),
)
