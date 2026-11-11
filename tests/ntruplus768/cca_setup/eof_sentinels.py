"""Frozen complete semantic EOF declarations and isolated unfinished-proof inventory."""
SENTINELS = {
    'kem_cca_setup/NTRUPlus768CCASetupState.ec': r"""

lemma __cca_setup_eof_0 :
 equiv[ProgrammedFreshExpand.shake ~ FreshExpand.shake : ={seed} ==> ={res}].
proof. exact (programmed_fresh_expand_projection). qed.
""",
    'kem_cca_setup/NTRUPlus768CCASetupProgrammed.ec': r"""

lemma __cca_setup_eof_1 &m qf0 qg0 workspace0 :
 0<=qf0 => 0<=qg0 =>
 Pr[CountedKeygen(UniformSeedRNG,ProgrammedFreshExpand).run(workspace0) @ &m:
 !counted_within qf0 qg0 res] <= fresh_retry_tail qf0 qg0.
proof. exact (programmed_counted_tail &m qf0 qg0 workspace0). qed.
""",
    'kem_cca_setup/NTRUPlus768CCASetupProgrammedBridge.ec': r"""

lemma __cca_setup_eof_2 :
 equiv[StoppedKeygen(UniformSeedRNG,ProgrammedFreshExpand).run ~
       StoppedKeygen(PairPorts(FreshProposal),PairPorts(FreshProposal)).run :
 ={qf,qg,workspace,glob ROF} /\ ROE.m{1}=FreshProposal.m{2} /\
 0<=qf{1} /\ 0<=qg{1} /\ FreshProposal.n{2}=0 /\ FreshProposal.q{2}=qf{1}+qg{1} ==>
 ={res,glob ROF} /\ ROE.m{1}=FreshProposal.m{2}].
proof. exact (programmed_stopped_proposal_bridge). qed.
""",
    'kem_cca_setup/NTRUPlus768CCASetupSwitch.ec': r"""

lemma __cca_setup_eof_3 &mem qf qg a m0 f0 (event:cca_stopped_state->bool) :
 0<=qf =>0<=qg =>0<=a =>fsize m0<=a =>
 `|Pr[CCAStoppedJoint(ExpandROM).run(qf,qg,m0,f0) @ &mem:event res]-
   Pr[CCAStoppedJoint(ProgrammedFreshExpand).run(qf,qg,m0,f0) @ &mem:event res]|
 <=proposal_delta a(qf+qg).
proof. exact (cca_stopped_joint_distance &mem qf qg a m0 f0 event). qed.
""",
    'kem_cca_setup/NTRUPlus768CCASetupPrefix.ec': r"""

lemma __cca_setup_eof_4 &m qf0 qg0 m0 f0 (event:cca_setup_state->bool) :
 Pr[CCAConfiguredCountedSetup(ProgrammedFreshExpand).run(m0,f0) @ &m:
   counted_joint_within qf0 qg0 res /\ counted_joint_event event res] =
 Pr[CCAStoppedJoint(ProgrammedFreshExpand).run(qf0,qg0,m0,f0) @ &m:
   stopped_success_event event res].
proof. exact (cca_configured_counted_stopped_prefix_programmed &m qf0 qg0 m0 f0 event). qed.
""",
    'kem_cca_setup/NTRUPlus768CCASetupBound.ec': r"""

lemma __cca_setup_eof_5 &m (event:cca_setup_state->bool) :
 `|Pr[JointSetupSource(ExpandROM).guess(witness) @ &m:event res]-
   Pr[JointSetupSource(ProgrammedFreshExpand).guess(witness) @ &m:event res]|
 <1%r/(2%r^239).
proof. exact (cca_setup_source_distance_239 &m event). qed.
""",
    'kem_cca_setup/NTRUPlus768CCASetupDistribution.ec': r"""

lemma __cca_setup_eof_6 (E1<:KeygenExpand) (E2<:KeygenExpand) &m eps :
 (forall (event:cca_setup_state->bool),
  `|Pr[JointSetupSource(E1).guess(witness) @ &m:event res]-
    Pr[JointSetupSource(E2).guess(witness) @ &m:event res]|<=eps) =>
 sdist (mk(fun z=>Pr[JointSetupSource(E1).guess(witness) @ &m:res=z]))
       (mk(fun z=>Pr[JointSetupSource(E2).guess(witness) @ &m:res=z])) <= eps.
proof. exact (cca_setup_event_sdist E1 E2 &m eps). qed.
""",
    'kem_cca_setup/NTRUPlus768CCASetupGame.ec': r"""

lemma __cca_setup_eof_7
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams}) &m :
 Pr[CCASharedSetupGame(ProgrammedFreshExpand,A).run() @ &m:res]=
 Pr[CCASetupObserverDist.Sample(CCASetupObserver(A)).main(
  mk(fun z=>Pr[JointSetupSource(ProgrammedFreshExpand).guess(witness) @ &m:res=z])) @ &m:res].
proof. exact (cca_setup_game_reified_programmed A &m). qed.
""",
    'kem_cca_setup/NTRUPlus768CCASetupSecurity.ec': r"""

lemma __cca_setup_eof_8
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams}) &m :
 `|Pr[CCAOriginalGame(A).run() @ &m:res]-
   Pr[CCAProgrammedFreshGame(A).run() @ &m:res]| < 1%r/(2%r^239).
proof. exact (cca_original_programmed_setup_distance_239 A &m). qed.
""",
}

SEMANTIC_TARGETS = {'kem_cca_setup/NTRUPlus768CCASetupBound.ec': 'cca_setup_source_distance_239',
 'kem_cca_setup/NTRUPlus768CCASetupDistribution.ec': 'cca_setup_event_sdist',
 'kem_cca_setup/NTRUPlus768CCASetupGame.ec': 'cca_setup_game_reified_programmed',
 'kem_cca_setup/NTRUPlus768CCASetupPrefix.ec': 'cca_configured_counted_stopped_prefix_programmed',
 'kem_cca_setup/NTRUPlus768CCASetupProgrammed.ec': 'programmed_counted_tail',
 'kem_cca_setup/NTRUPlus768CCASetupProgrammedBridge.ec': 'programmed_stopped_proposal_bridge',
 'kem_cca_setup/NTRUPlus768CCASetupSecurity.ec': 'cca_original_programmed_setup_distance_239',
 'kem_cca_setup/NTRUPlus768CCASetupState.ec': 'programmed_fresh_expand_projection',
 'kem_cca_setup/NTRUPlus768CCASetupSwitch.ec': 'cca_stopped_joint_distance'}

MODULE_BINDERS = {'kem_cca_setup/NTRUPlus768CCASetupBound.ec': (),
 'kem_cca_setup/NTRUPlus768CCASetupDistribution.ec': ('E1', 'E2'),
 'kem_cca_setup/NTRUPlus768CCASetupGame.ec': ('A',),
 'kem_cca_setup/NTRUPlus768CCASetupPrefix.ec': (),
 'kem_cca_setup/NTRUPlus768CCASetupProgrammed.ec': (),
 'kem_cca_setup/NTRUPlus768CCASetupProgrammedBridge.ec': (),
 'kem_cca_setup/NTRUPlus768CCASetupSecurity.ec': ('A',),
 'kem_cca_setup/NTRUPlus768CCASetupState.ec': (),
 'kem_cca_setup/NTRUPlus768CCASetupSwitch.ec': ()}

NEGATIVE_PROOFS = ('kem_cca_setup/NTRUPlus768CCASetupState.ec',
 'kem_cca_setup/NTRUPlus768CCASetupProgrammed.ec',
 'kem_cca_setup/NTRUPlus768CCASetupProgrammedBridge.ec',
 'kem_cca_setup/NTRUPlus768CCASetupSwitch.ec',
 'kem_cca_setup/NTRUPlus768CCASetupPrefix.ec',
 'kem_cca_setup/NTRUPlus768CCASetupBound.ec',
 'kem_cca_setup/NTRUPlus768CCASetupDistribution.ec',
 'kem_cca_setup/NTRUPlus768CCASetupGame.ec',
 'kem_cca_setup/NTRUPlus768CCASetupSecurity.ec')
