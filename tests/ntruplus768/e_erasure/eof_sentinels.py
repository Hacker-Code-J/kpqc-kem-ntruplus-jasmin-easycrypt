"""Frozen complete semantic EOF declarations and isolated unfinished-proof inventory."""
SENTINELS = {
    'kem_e_erasure/NTRUPlus768ErasureModel.ec': r"""

lemma __e_erasure_eof_0 : islossless LoggedErasedExpand.shake.
proof. exact (logged_erased_expand_ll). qed.
""",
    'kem_e_erasure/NTRUPlus768ErasureBudget.ec': r"""

lemma __e_erasure_eof_1
 (A<:CCAExtendedAdversary {-EBudgetState,-ErasureHit,-ErasureSeedLog,-ErasureSeedPool})
 (H<:CCAExtendedOraclePort {-A,-EBudgetState,-ErasureHit,-ErasureSeedLog})
 (D<:CCADecapPort {-A,-EBudgetState,-ErasureHit,-ErasureSeedLog}) q0 :
 hoare[CappedA(A,H,D).guess:
 erasure_cap_invariant EBudgetState.requests EBudgetState.forwarded EBudgetState.limit EBudgetState.queries /\
 EBudgetState.limit=q0 ==> size EBudgetState.queries<=q0].
proof. exact (cap_adversary_queries_bound A H D q0). qed.
""",
    'kem_e_erasure/NTRUPlus768ErasureCapRemoval.ec': r"""

lemma __e_erasure_eof_2
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
   -EBudgetState,-ErasureHit,-ErasureSeedLog,-ErasureSeedPool}) &m q0 (event:bool->bool) :
 0<=q0 =>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
   islossless H.e =>islossless H.f =>islossless H.g =>islossless H.h =>islossless H.raw =>
   islossless D.decap =>islossless A(H,D).guess) =>
 hoare[CountedA(A,SharedCCAExtendedOracles,CCADecapOracle).guess:
 EBudgetState.requests=0 /\ EBudgetState.forwarded=0 /\ EBudgetState.limit=q0 /\
 !EBudgetState.overflow /\ EBudgetState.queries=[] ==> EBudgetState.requests<=q0] =>
 EBudgetState.requests{m}=0 =>EBudgetState.forwarded{m}=0 =>EBudgetState.limit{m}=q0 =>
 !EBudgetState.overflow{m} =>EBudgetState.queries{m}=[] =>
 Pr[CCAOriginalGame(CappedA(A)).run() @ &m:event res]=
 Pr[CCAOriginalGame(A).run() @ &m:event res].
proof. exact (capped_original_event A &m q0 event). qed.
""",
    'kem_e_erasure/NTRUPlus768ErasureSetup.ec': r"""

lemma __e_erasure_eof_3 :
 equiv[Keygen(UniformSeedRNG,LoggedProgrammedExpand,SHAKEFROM).run ~
       Keygen(UniformSeedRNG,LoggedErasedExpand,SHAKEFROM).run :
   ={glob ROF,ErasureSeedLog.used} /\
   erasure_tables_agree ErasureSeedLog.used{1} ROE.m{1} ROE.m{2} ==>
   ={res,glob ROF,ErasureSeedLog.used} /\
   erasure_tables_agree ErasureSeedLog.used{1} ROE.m{1} ROE.m{2}].
proof. exact (erasure_keygen_coupling). qed.
""",
    'kem_e_erasure/NTRUPlus768ErasurePrefix.ec': r"""

lemma __e_erasure_eof_4 qf0 qg0 :
 0<=qf0 =>0<=qg0 =>
 phoare[StoppedKeygen(UniformSeedRNG,LoggedErasedExpand).run:
   qf=qf0 /\ qg=qg0 ==> !stopped_success res] <= (fresh_retry_tail qf0 qg0).
proof. exact (erasure_erased_stopped_abort qf0 qg0). qed.
""",
    'kem_e_erasure/NTRUPlus768ErasureSeedTape.ec': r"""

lemma __e_erasure_eof_5 (A<:ErasureTapeContext {-ErasureSeedPool,-ErasureTape}) :
 eager[ErasureTape.refresh();, A(ErasureSeedPool).run ~ A(ErasureOnlinePool).run,
       ErasureTape.refresh(); :
 ={arg,glob A,ErasureSeedPool.seeds,ErasureSeedPool.cursor,ErasureTape.q} ==>
 ={res,glob A,ErasureSeedPool.seeds,ErasureSeedPool.cursor,ErasureTape.q}].
proof. exact (erasure_tape_context A). qed.
""",
    'kem_e_erasure/NTRUPlus768ErasureSeedPool.ec': r"""

lemma __e_erasure_eof_6 qf0 qg0 :
 equiv[ErasureOnlineExperiment.padded ~ ErasurePoolExperiment.after :
 ={qf,qg,workspace,glob ROF} /\ qf{1}=qf0 /\ qg{1}=qg0 /\ 0<=qf0 /\ 0<=qg0 ==> ={res,glob ROF,glob ErasureSeedPool,glob ErasureSeedLog}].
proof. exact (erasure_padded_postsample qf0 qg0). qed.
""",
    'kem_e_erasure/NTRUPlus768ErasureHitBound.ec': r"""

lemma __e_erasure_eof_7 ['a] (K:'a distr) (queries:'a->erasure_seed list)
 (used_count:'a->int) Q qE :
 0<=Q=>0<=qE=>(forall z,z \in K=>size(queries z)<=qE) =>
 mu(erasure_joint_after K Q)
   (fun (zpool:'a*erasure_seed list)=>erasure_pool_hits (rev(take(used_count zpool.`1)zpool.`2))(queries zpool.`1))<=
 erasure_hit_bound Q qE.
proof. exact (erasure_used_prefix_hit_bound K queries used_count Q qE). qed.
""",
    'kem_e_erasure/NTRUPlus768ErasureOracleCoupling.ec': r"""

lemma __e_erasure_eof_8 :
 phoare[CapEPort(SharedCCAExtendedOracles).raw:ErasureHit.bad ==>ErasureHit.bad]=1%r.
proof. exact (erasure_cap_raw_bad). qed.
""",
    'kem_e_erasure/NTRUPlus768ErasureAdversaryCoupling.ec': r"""

lemma __e_erasure_eof_9
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
   -EBudgetState,-ErasureSeedLog,-ErasureHit,-ErasureSeedPool}) :
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e =>islossless H.f =>islossless H.g =>islossless H.h =>
  islossless H.raw =>islossless D.decap =>islossless A(H,D).guess) =>
 islossless CCAChallengeOriginal(CappedA(A)).run.
proof. exact (erasure_challenge_ll A). qed.
""",
    'kem_e_erasure/NTRUPlus768ErasureGames.ec': r"""

lemma __e_erasure_eof_10
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState}) q0 :
 hoare[CCAChallengeOriginal(CappedA(A)).run:
 erasure_cap_invariant EBudgetState.requests EBudgetState.forwarded EBudgetState.limit EBudgetState.queries /\
 EBudgetState.limit=q0 ==> size EBudgetState.queries<=q0].
proof. exact (erasure_capped_challenge_query_bound A q0). qed.
""",
    'kem_e_erasure/NTRUPlus768ErasureQueryKernel.ec': r"""

lemma __e_erasure_eof_11
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState}) &m qf0 qg0 q0 :
 0<=qf0=>0<=qg0=>
 erasure_budget_initial q0 EBudgetState.requests{m} EBudgetState.forwarded{m}
  EBudgetState.limit{m} EBudgetState.overflow{m} EBudgetState.queries{m} =>
 Pr[ErasurePostQueryPool(A).run(qf0,qg0) @ &m:res]<=erasure_hit_bound (qf0+qg0)q0.
proof. exact (erasure_postquery_hit_bound A &m qf0 qg0 q0). qed.
""",
    'kem_e_erasure/NTRUPlus768ErasureActualHit.ec': r"""

lemma __e_erasure_eof_12
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState,-ErasureTape}) &m qf0 qg0 q0 :
 0<=qf0 =>0<=qg0 =>
 erasure_budget_initial q0 EBudgetState.requests{m} EBudgetState.forwarded{m}
   EBudgetState.limit{m} EBudgetState.overflow{m} EBudgetState.queries{m} =>
 Pr[ErasureStoppedIndependentGame(A).run(qf0,qg0) @ &m:ErasureHit.bad]
 <=erasure_hit_bound(qf0+qg0)q0.
proof. exact (erasure_actual_stopped_hit_bound A &m qf0 qg0 q0). qed.
""",
    'kem_e_erasure/NTRUPlus768ErasureGameTail.ec': r"""

lemma __e_erasure_eof_13
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState}) &m qf qg :
 islossless CCAChallengeOriginal(CappedA(A)).run =>
 0<=qf=>0<=qg=>
 `|Pr[ErasureProgrammedGame(A).run() @ &m:res]-
    Pr[ErasureIndependentGame(A).run() @ &m:res]| <=
 `|Pr[ErasureStoppedProgrammedGame(A).run(qf,qg) @ &m:res=Some true]-
    Pr[ErasureStoppedIndependentGame(A).run(qf,qg) @ &m:res=Some true]|+
 fresh_retry_tail qf qg.
proof. exact (erasure_games_common_tail A &m qf qg). qed.
""",
    'kem_e_erasure/NTRUPlus768ErasureSecurity.ec': r"""

lemma __e_erasure_eof_14
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState,-ErasureTape}) &m qE :
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>
  islossless H.raw=>islossless D.decap=>islossless A(H,D).guess) =>
 hoare[CountedA(A,SharedCCAExtendedOracles,CCADecapOracle).guess:
 EBudgetState.requests=0 /\ EBudgetState.forwarded=0 /\ EBudgetState.limit=qE /\
 !EBudgetState.overflow /\ EBudgetState.queries=[] ==> EBudgetState.requests<=qE] =>
 erasure_budget_initial qE EBudgetState.requests{m} EBudgetState.forwarded{m}
  EBudgetState.limit{m} EBudgetState.overflow{m} EBudgetState.queries{m} =>
 `|Pr[CCAOriginalGame(A).run() @ &m:res]-
   Pr[CCASharedSetupGame(FreshExpand,A).run() @ &m:res]|<=
 (130820%r+512%r*qE%r)/(2%r^256).
proof. exact (erasure_original_independent_256 A &m qE). qed.
""",
}

SEMANTIC_TARGETS = {'kem_e_erasure/NTRUPlus768ErasureActualHit.ec': 'erasure_actual_stopped_hit_bound',
 'kem_e_erasure/NTRUPlus768ErasureAdversaryCoupling.ec': 'erasure_challenge_ll',
 'kem_e_erasure/NTRUPlus768ErasureBudget.ec': 'cap_adversary_queries_bound',
 'kem_e_erasure/NTRUPlus768ErasureCapRemoval.ec': 'capped_original_event',
 'kem_e_erasure/NTRUPlus768ErasureGameTail.ec': 'erasure_games_common_tail',
 'kem_e_erasure/NTRUPlus768ErasureGames.ec': 'erasure_capped_challenge_query_bound',
 'kem_e_erasure/NTRUPlus768ErasureHitBound.ec': 'erasure_used_prefix_hit_bound',
 'kem_e_erasure/NTRUPlus768ErasureModel.ec': 'logged_erased_expand_ll',
 'kem_e_erasure/NTRUPlus768ErasureOracleCoupling.ec': 'erasure_cap_raw_bad',
 'kem_e_erasure/NTRUPlus768ErasurePrefix.ec': 'erasure_erased_stopped_abort',
 'kem_e_erasure/NTRUPlus768ErasureQueryKernel.ec': 'erasure_postquery_hit_bound',
 'kem_e_erasure/NTRUPlus768ErasureSecurity.ec': 'erasure_original_independent_256',
 'kem_e_erasure/NTRUPlus768ErasureSeedPool.ec': 'erasure_padded_postsample',
 'kem_e_erasure/NTRUPlus768ErasureSeedTape.ec': 'erasure_tape_context',
 'kem_e_erasure/NTRUPlus768ErasureSetup.ec': 'erasure_keygen_coupling'}

MODULE_BINDERS = {'kem_e_erasure/NTRUPlus768ErasureActualHit.ec': ('A',),
 'kem_e_erasure/NTRUPlus768ErasureAdversaryCoupling.ec': ('A', 'H', 'D'),
 'kem_e_erasure/NTRUPlus768ErasureBudget.ec': ('A', 'H', 'D'),
 'kem_e_erasure/NTRUPlus768ErasureCapRemoval.ec': ('A', 'H', 'D'),
 'kem_e_erasure/NTRUPlus768ErasureGameTail.ec': ('A',),
 'kem_e_erasure/NTRUPlus768ErasureGames.ec': ('A',),
 'kem_e_erasure/NTRUPlus768ErasureHitBound.ec': (),
 'kem_e_erasure/NTRUPlus768ErasureModel.ec': (),
 'kem_e_erasure/NTRUPlus768ErasureOracleCoupling.ec': (),
 'kem_e_erasure/NTRUPlus768ErasurePrefix.ec': (),
 'kem_e_erasure/NTRUPlus768ErasureQueryKernel.ec': ('A',),
 'kem_e_erasure/NTRUPlus768ErasureSecurity.ec': ('A', 'H', 'D'),
 'kem_e_erasure/NTRUPlus768ErasureSeedPool.ec': (),
 'kem_e_erasure/NTRUPlus768ErasureSeedTape.ec': ('A',),
 'kem_e_erasure/NTRUPlus768ErasureSetup.ec': ()}

NEGATIVE_PROOFS = ('kem_e_erasure/NTRUPlus768ErasureModel.ec',
 'kem_e_erasure/NTRUPlus768ErasureBudget.ec',
 'kem_e_erasure/NTRUPlus768ErasureCapRemoval.ec',
 'kem_e_erasure/NTRUPlus768ErasureSetup.ec',
 'kem_e_erasure/NTRUPlus768ErasurePrefix.ec',
 'kem_e_erasure/NTRUPlus768ErasureSeedTape.ec',
 'kem_e_erasure/NTRUPlus768ErasureSeedPool.ec',
 'kem_e_erasure/NTRUPlus768ErasureHitBound.ec',
 'kem_e_erasure/NTRUPlus768ErasureOracleCoupling.ec',
 'kem_e_erasure/NTRUPlus768ErasureAdversaryCoupling.ec',
 'kem_e_erasure/NTRUPlus768ErasureGames.ec',
 'kem_e_erasure/NTRUPlus768ErasureQueryKernel.ec',
 'kem_e_erasure/NTRUPlus768ErasureActualHit.ec',
 'kem_e_erasure/NTRUPlus768ErasureGameTail.ec',
 'kem_e_erasure/NTRUPlus768ErasureSecurity.ec')
