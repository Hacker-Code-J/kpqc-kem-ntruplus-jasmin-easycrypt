"""Semantic EOF references matching the frozen theorem declarations."""
SENTINELS = {
    'kem_stopped_rom/NTRUPlus768ProposalModel.ec': r'''
lemma __stopped_pair_ports_eof (P <: ProposalPort) :
 hoare[PairPorts(P).shake : true ==> res=PairPorts.pending].
proof. exact (pair_ports_shake_value P). qed.
''',
    'kem_stopped_rom/NTRUPlus768StoppedKeygenModel.ec': r'''
lemma __stopped_model_eof (event:keygen_output -> bool) nf ng :
 stopped_event event (None,nf,ng)=false.
proof. exact (stopped_event_none event nf ng). qed.
''',
    'kem_stopped_rom/NTRUPlus768AttemptRealized.ec': r'''
lemma __stopped_attempt_eof (E <: KeygenExpand) :
 islossless E.shake =>
 phoare[KeygenAttempt(E).g : true ==> res=keygen_g_attempt_result res.`1]=1%r.
proof. exact (keygen_attempt_g_realized_total E). qed.
''',
    'kem_stopped_rom/NTRUPlus768BufferRejection.ec': r'''
lemma __stopped_buffer_eof &m d accept (event:W8.t Array192.t -> bool) :
 is_lossless d =>
 Pr[BufferRejection.sample(d,accept) @ &m:event res] =
 mu d (fun buffer => accept buffer /\ event buffer) / mu d accept.
proof. exact (buffer_rejection_exact_conditional &m d accept event). qed.
''',
    'kem_stopped_rom/NTRUPlus768BoundedBufferRejection.ec': r'''
lemma __stopped_bounded_buffer_eof &m d0 accept0 q0 :
 is_lossless d0 => 0<=q0 =>
 Pr[BoundedBufferRejection.run(d0,accept0,q0) @ &m:res=None] =
 (1%r-mu d0 accept0)^q0.
proof. exact (bounded_buffer_rejection_tail &m d0 accept0 q0). qed.
''',
}
SENTINELS['kem_stopped_rom/NTRUPlus768ProposalSwitch.ec'] = r"""
lemma __stopped_proposal_switch_eof
 (A <: ProposalContext {-FreshProposal,-ROMProposal,-ROE})
 &mem qf qg qb ab m0 :
 (forall (P <: ProposalPort {-A}),
  islossless P.draw => islossless A(P).run) =>
 0<=qb => 0<=ab => fsize m0<=ab =>
 `|Pr[ROMProposalExperiment(A).run(qf,qg,qb,m0) @ &mem : res] -
   Pr[FreshProposalExperiment(A).run(qf,qg,qb,m0) @ &mem : res]| <= proposal_delta ab qb.
proof. exact (proposal_switch_distance A &mem qf qg qb ab m0). qed.
"""
SENTINELS['kem_stopped_rom/NTRUPlus768StoppedKeygenPrefix.ec'] = r"""
lemma __stopped_prefix_eof (R <: KeygenSeedRNG {-ROF,-PrefixBad})
 (E <: KeygenExpand {-ROF,-PrefixBad,-R}) (qf0 qg0:int)
 (w:W8.t Array14466.t) (event:keygen_output -> bool) &m :
 0<=qf0 => 0<=qg0 => islossless R.sample => islossless E.shake =>
 Pr[CountedKeygen(R,E).run(w) @ &m : (res.`2<=qf0 /\ res.`3<=qg0) /\ event res.`1] =
 Pr[StoppedKeygen(R,E).run(qf0,qg0,w) @ &m : res.`1<>None /\ event (oget res.`1)].
proof. exact (counted_stopped_prefix_nonnegative R E qf0 qg0 w event &m). qed.
"""
SENTINELS['kem_stopped_rom/NTRUPlus768FreshBoundedLaw.ec'] = r"""
lemma __stopped_fresh_tail_eof &m qf0 qg0 workspace0 :
 0<=qf0 => 0<=qg0 =>
 Pr[StoppedKeygen(UniformSeedRNG,FreshExpand).run(qf0,qg0,workspace0) @ &m :
   !stopped_success res] <= fresh_retry_tail qf0 qg0.
proof. exact (fresh_stopped_keygen_abort_probability &m qf0 qg0 workspace0). qed.
"""
SENTINELS['kem_stopped_rom/NTRUPlus768ProposalKeygenBridge.ec'] = r"""
lemma __stopped_actual_bridge_eof :
 equiv[StoppedKeygen(UniformSeedRNG,ExpandROM).run ~
       StoppedKeygen(PairPorts(ROMProposal),PairPorts(ROMProposal)).run :
 ={qf,qg,workspace,glob ROE,glob ROF} /\ 0<=qf{1} /\ 0<=qg{1} /\
 ROMProposal.n{2}=0 /\ ROMProposal.q{2}=qf{1}+qg{1} ==>
 ={res,glob ROE,glob ROF}].
proof. exact stopped_rom_proposal_bridge. qed.
"""
SENTINELS['kem_stopped_rom/NTRUPlus768StoppedROMGames.ec'] = r"""
lemma __stopped_actual_games_eof &mem qf qg ab m0 (event:stopped_output -> bool) :
 0<=qf => 0<=qg => 0<=ab => fsize m0<=ab =>
 `|Pr[DirectROMStopped.run(qf,qg,m0) @ &mem : event res] -
   Pr[DirectFreshStopped.run(qf,qg) @ &mem : event res]| <= proposal_delta ab (qf+qg).
proof. exact (stopped_rom_fresh_distance &mem qf qg ab m0 event). qed.
"""
SENTINELS['kem_stopped_rom/NTRUPlus768SubdistributionTransfer.ec'] = r"""
lemma __stopped_subdistribution_eof (mass good epsilon:real) :
 mass<=1%r => good<=mass => 1%r-epsilon<=good => 0%r<=1%r-mass<=epsilon.
proof. exact (subdistribution_missing_mass mass good epsilon). qed.
"""
SENTINELS['kem_stopped_rom/NTRUPlus768FreshRetryLaw.ec'] = r"""
lemma __stopped_fresh_buffer_eof (event:W8.t Array192.t -> bool) :
 phoare[KeygenRetry(UniformSeedRNG,FreshExpand).g : true ==> event res.`1] =
 (mu (dcond uniform192 keygen_g_accept) event).
proof. exact (fresh_retry_g_buffer_law event). qed.
"""
SENTINELS['kem_stopped_rom/NTRUPlus768StoppedROMBound.ec'] = r"""
lemma __stopped_actual_keygen_bound_eof &m qf0 qg0 ab m0
 (event:W8.t Array1152.t * W8.t Array2336.t -> bool) :
 0<=qf0 => 0<=qg0 => 0<=ab => fsize m0<=ab => ROE.m{m}=m0 =>
 0%r<fresh_f_accept_mass => 0%r<fresh_g_accept_mass =>
 `|Pr[Keygen(UniformSeedRNG,ExpandROM,SHAKEFROM).run() @ &m : event res] -
   Pr[Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run() @ &m : event res]|
 <= proposal_delta ab (qf0+qg0)+fresh_retry_tail qf0 qg0.
proof. exact (keygen_public_rom_fresh_distance &m qf0 qg0 ab m0 event). qed.
"""
SENTINELS['kem_stopped_rom/NTRUPlus768FreshKeyPairLaw.ec'] = r"""
lemma __stopped_actual_fresh_pair_eof &m workspace
 (event:(W8.t Array192.t * W8.t Array192.t) -> bool) :
 Pr[KeygenInstrumented(UniformSeedRNG,FreshExpand,SHAKEFROM).run(workspace) @ &m :
 event(res.`1.`kg_fbuf,res.`1.`kg_gbuf)] =
 mu (((dcond uniform192 keygen_f_accept) `*` (dcond uniform192 keygen_g_accept))) event.
proof. exact (fresh_keygen_buffer_pair_probability &m workspace event). qed.
"""
SEMANTIC_TARGETS = {
    'kem_stopped_rom/NTRUPlus768FreshKeyPairLaw.ec': 'fresh_keygen_buffer_pair_probability',
    'kem_stopped_rom/NTRUPlus768StoppedROMBound.ec': 'keygen_public_rom_fresh_distance',
    'kem_stopped_rom/NTRUPlus768FreshRetryLaw.ec': 'fresh_retry_g_buffer_law',
    'kem_stopped_rom/NTRUPlus768ProposalKeygenBridge.ec': 'stopped_rom_proposal_bridge',
    'kem_stopped_rom/NTRUPlus768StoppedROMGames.ec': 'stopped_rom_fresh_distance',
    'kem_stopped_rom/NTRUPlus768SubdistributionTransfer.ec': 'subdistribution_missing_mass',
    'kem_stopped_rom/NTRUPlus768FreshBoundedLaw.ec': 'fresh_stopped_keygen_abort_probability',
    'kem_stopped_rom/NTRUPlus768StoppedKeygenPrefix.ec': 'counted_stopped_prefix_nonnegative',
    'kem_stopped_rom/NTRUPlus768ProposalSwitch.ec': 'proposal_switch_distance',
    'kem_stopped_rom/NTRUPlus768ProposalModel.ec': 'pair_ports_shake_value',
    'kem_stopped_rom/NTRUPlus768StoppedKeygenModel.ec': 'stopped_event_none',
    'kem_stopped_rom/NTRUPlus768AttemptRealized.ec': 'keygen_attempt_g_realized_total',
    'kem_stopped_rom/NTRUPlus768BufferRejection.ec': 'buffer_rejection_exact_conditional',
    'kem_stopped_rom/NTRUPlus768BoundedBufferRejection.ec': 'bounded_buffer_rejection_tail',
}
MODULE_BINDERS = {name: () for name in SENTINELS}
MODULE_BINDERS.update({
    'kem_stopped_rom/NTRUPlus768StoppedKeygenPrefix.ec': ('R', 'E'),
    'kem_stopped_rom/NTRUPlus768ProposalSwitch.ec': ('A', 'P'),
    'kem_stopped_rom/NTRUPlus768ProposalModel.ec': ('P',),
    'kem_stopped_rom/NTRUPlus768AttemptRealized.ec': ('E',),
})
NEGATIVE_PROOFS = tuple(SENTINELS)
