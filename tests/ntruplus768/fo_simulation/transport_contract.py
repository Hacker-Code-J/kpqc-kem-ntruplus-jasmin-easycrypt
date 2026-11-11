"""Frozen final transport contracts for the actual adaptive-game endpoints."""
RULES = [('ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimPhaseState.ec',
  'ready-is-local-state-not-security-conclusion',
  'op [opaque] sim_phase_ready (s:fo_setup_observation) pk suffix sk star\n'
  ' (w:keygen_witness) (g:acwc2_g_function) ex hs cs gm hm log corr =\n'
  ' fo_setup_valid s /\\ w=s.`1.`1 /\\ g=acwc2_gfun s.`3 /\\\n'
  ' pk=w.`kg_pk /\\ suffix=complete_sk_suffix w.`kg_sk /\\ sk=w.`kg_sk /\\ star=Some cs /\\\n'
  ' acwc2_cache_matches g gm /\\ sim_log_included log hm /\\ sim_h_cover log hm ex /\\\n'
  ' fo_challenge_invariant w g ex hs cs hm /\\ !corr /\\ fo_hcache_good w g ex log.\n'),
 ('ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimPhaseState.ec',
  'ready-guard-removed-for-valid-setup',
  'lemma sim_ready_kernel_probability (P<:SimBoolPhase) s0 event &m : fo_setup_valid s0=>\n'
  ' Pr[SimSetupPhase(P).guess(s0) @ &m:event res]=\n'
  ' Pr[SimReadyKernel(P).guess(s0) @ &m:event res].'),
 ('ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimSequentialDistance.ec',
  'sequential-lift-assumes-phase-not-kernel-distance',
  'lemma sim_sequential_unconditional (S<:SimSequentialSystem) i0 gamma &m :\n'
  ' islossless S.setup=>islossless S.phase=>\n'
  ' (forall &n,`|Pr[S.phase(i0,true)@&n:res]-Pr[S.phase(i0,false)@&n:res]|<=gamma)=>\n'
  ' '
  '`|Pr[SimSequentialKernel(S).phase(i0,true)@&m:res]-Pr[SimSequentialKernel(S).phase(i0,false)@&m:res]|<=gamma.'),
 ('ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimFinal.ec',
  'final-actual-uncapped-endpoints',
  'lemma sim_fo_public_distance\n'
  ' (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,\n'
  '  -FOContext,-FOBadState,-FOBudgetState,-FOGRO.RO,-FOGRO.FRO,-SimPublic,-SimHistory,-SimBad,\n'
  '  -SimPhaseInput,-SimSelectedFixed,-SimPublicBudget,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,\n'
  '  -SH.HB.Count,-SH.HB.HybOrcl}) qH &m :\n'
  ' 0<=qH=>\n'
  ' (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),\n'
  '  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>\n'
  '  islossless D.decap=>islossless A(H,D).guess)=>\n'
  ' (forall(H<:CCAExtendedOraclePort {-A,-FOBudgetState})(D<:CCADecapPort {-A,-FOBudgetState}),\n'
  '  hoare[FOCountedA(A,H,D).guess:FOBudgetState.nD=0 ==>FOBudgetState.nD<=max 0 budget])=>\n'
  ' hoare[SimPublicCountedA(A,FOHashView(SimKnownPublicBackend),FODecapView(SimKnownPublicBackend)).guess:\n'
  '  sim_public_budget_initial qH SimPublicBudget.nh SimPublicBudget.limit SimPublicBudget.overflow ==>\n'
  '  SimPublicBudget.nh<=qH]=>\n'
  ' `|Pr[FOFreshReencryptGame(A).run() @ &m:res]-Pr[SimPublicFreshGame(A).run() @ &m:res]|\n'
  ' <=(max 0 budget)%r/(2%r^768)+(qH+max 0 budget)%r/(2%r^353).'),
 ('ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimFinal.ec',
  'final-has-no-assumed-security-distance',
  'lemma sim_fo_public_distance\n'
  ' (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,\n'
  '  -FOContext,-FOBadState,-FOBudgetState,-FOGRO.RO,-FOGRO.FRO,-SimPublic,-SimHistory,-SimBad,\n'
  '  -SimPhaseInput,-SimSelectedFixed,-SimPublicBudget,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,\n'
  '  -SH.HB.Count,-SH.HB.HybOrcl}) qH &m :\n'
  ' 0<=qH=>\n'
  ' (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),\n'
  '  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>\n'
  '  islossless D.decap=>islossless A(H,D).guess)=>\n'
  ' (forall(H<:CCAExtendedOraclePort {-A,-FOBudgetState})(D<:CCADecapPort {-A,-FOBudgetState}),\n'
  '  hoare[FOCountedA(A,H,D).guess:FOBudgetState.nD=0 ==>FOBudgetState.nD<=max 0 budget])=>\n'
  ' hoare[SimPublicCountedA(A,FOHashView(SimKnownPublicBackend),FODecapView(SimKnownPublicBackend)).guess:\n'
  '  sim_public_budget_initial qH SimPublicBudget.nh SimPublicBudget.limit SimPublicBudget.overflow ==>\n'
  '  SimPublicBudget.nh<=qH]=>\n'
  ' `|Pr[FOFreshReencryptGame(A).run() @ &m:res]-Pr[SimPublicFreshGame(A).run() @ &m:res]|\n'
  ' <=(max 0 budget)%r/(2%r^768)+(qH+max 0 budget)%r/(2%r^353).')]
MUTATIONS = [('ready-is-local-state-not-security-conclusion',
  'ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimPhaseState.ec',
  'op [opaque] sim_phase_ready (s:fo_setup_observation) pk suffix sk star\n'
  ' (w:keygen_witness) (g:acwc2_g_function) ex hs cs gm hm log corr =\n'
  ' fo_setup_valid s /\\ w=s.`1.`1 /\\ g=acwc2_gfun s.`3 /\\\n'
  ' pk=w.`kg_pk /\\ suffix=complete_sk_suffix w.`kg_sk /\\ sk=w.`kg_sk /\\ star=Some cs /\\\n'
  ' acwc2_cache_matches g gm /\\ sim_log_included log hm /\\ sim_h_cover log hm ex /\\\n'
  ' fo_challenge_invariant w g ex hs cs hm /\\ !corr /\\ fo_hcache_good w g ex log.\n',
  'op [opaque] sim_phase_ready (s:fo_setup_observation) pk suffix sk star\n'
  ' (w:keygen_witness) (g:acwc2_g_function) ex hs cs gm hm log corr =\n'
  ' fo_setup_valid s /\\ fo_error w g=0%r /\\ w=s.`1.`1 /\\ g=acwc2_gfun s.`3 /\\\n'
  ' pk=w.`kg_pk /\\ suffix=complete_sk_suffix w.`kg_sk /\\ sk=w.`kg_sk /\\ star=Some cs /\\\n'
  ' acwc2_cache_matches g gm /\\ sim_log_included log hm /\\ sim_h_cover log hm ex /\\\n'
  ' fo_challenge_invariant w g ex hs cs hm /\\ !corr /\\ fo_hcache_good w g ex log.\n'),
 ('ready-guard-removed-for-valid-setup',
  'ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimPhaseState.ec',
  'lemma sim_ready_kernel_probability (P<:SimBoolPhase) s0 event &m : fo_setup_valid s0=>\n'
  ' Pr[SimSetupPhase(P).guess(s0) @ &m:event res]=\n'
  ' Pr[SimReadyKernel(P).guess(s0) @ &m:event res].',
  'lemma sim_ready_kernel_probability (P<:SimBoolPhase) s0 event &m : fo_setup_valid s0=>already_secure '
  's0=>\n'
  ' Pr[SimSetupPhase(P).guess(s0) @ &m:event res]=\n'
  ' Pr[SimReadyKernel(P).guess(s0) @ &m:event res].'),
 ('sequential-lift-assumes-phase-not-kernel-distance',
  'ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimSequentialDistance.ec',
  'lemma sim_sequential_unconditional (S<:SimSequentialSystem) i0 gamma &m :\n'
  ' islossless S.setup=>islossless S.phase=>\n'
  ' (forall &n,`|Pr[S.phase(i0,true)@&n:res]-Pr[S.phase(i0,false)@&n:res]|<=gamma)=>\n'
  ' '
  '`|Pr[SimSequentialKernel(S).phase(i0,true)@&m:res]-Pr[SimSequentialKernel(S).phase(i0,false)@&m:res]|<=gamma.',
  'lemma sim_sequential_unconditional (S<:SimSequentialSystem) i0 gamma &m :\n'
  ' islossless S.setup=>islossless S.phase=>\n'
  ' (forall '
  '&n,`|Pr[SimSequentialKernel(S).phase(i0,true)@&n:res]-Pr[SimSequentialKernel(S).phase(i0,false)@&n:res]|<=gamma)=>\n'
  ' '
  '`|Pr[SimSequentialKernel(S).phase(i0,true)@&m:res]-Pr[SimSequentialKernel(S).phase(i0,false)@&m:res]|<=gamma.'),
 ('final-actual-uncapped-endpoints',
  'ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimFinal.ec',
  'lemma sim_fo_public_distance\n'
  ' (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,\n'
  '  -FOContext,-FOBadState,-FOBudgetState,-FOGRO.RO,-FOGRO.FRO,-SimPublic,-SimHistory,-SimBad,\n'
  '  -SimPhaseInput,-SimSelectedFixed,-SimPublicBudget,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,\n'
  '  -SH.HB.Count,-SH.HB.HybOrcl}) qH &m :\n'
  ' 0<=qH=>\n'
  ' (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),\n'
  '  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>\n'
  '  islossless D.decap=>islossless A(H,D).guess)=>\n'
  ' (forall(H<:CCAExtendedOraclePort {-A,-FOBudgetState})(D<:CCADecapPort {-A,-FOBudgetState}),\n'
  '  hoare[FOCountedA(A,H,D).guess:FOBudgetState.nD=0 ==>FOBudgetState.nD<=max 0 budget])=>\n'
  ' hoare[SimPublicCountedA(A,FOHashView(SimKnownPublicBackend),FODecapView(SimKnownPublicBackend)).guess:\n'
  '  sim_public_budget_initial qH SimPublicBudget.nh SimPublicBudget.limit SimPublicBudget.overflow ==>\n'
  '  SimPublicBudget.nh<=qH]=>\n'
  ' `|Pr[FOFreshReencryptGame(A).run() @ &m:res]-Pr[SimPublicFreshGame(A).run() @ &m:res]|\n'
  ' <=(max 0 budget)%r/(2%r^768)+(qH+max 0 budget)%r/(2%r^353).',
  'lemma sim_fo_public_distance\n'
  ' (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,\n'
  '  -FOContext,-FOBadState,-FOBudgetState,-FOGRO.RO,-FOGRO.FRO,-SimPublic,-SimHistory,-SimBad,\n'
  '  -SimPhaseInput,-SimSelectedFixed,-SimPublicBudget,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,\n'
  '  -SH.HB.Count,-SH.HB.HybOrcl}) qH &m :\n'
  ' 0<=qH=>\n'
  ' (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),\n'
  '  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>\n'
  '  islossless D.decap=>islossless A(H,D).guess)=>\n'
  ' (forall(H<:CCAExtendedOraclePort {-A,-FOBudgetState})(D<:CCADecapPort {-A,-FOBudgetState}),\n'
  '  hoare[FOCountedA(A,H,D).guess:FOBudgetState.nD=0 ==>FOBudgetState.nD<=max 0 budget])=>\n'
  ' hoare[SimPublicCountedA(A,FOHashView(SimKnownPublicBackend),FODecapView(SimKnownPublicBackend)).guess:\n'
  '  sim_public_budget_initial qH SimPublicBudget.nh SimPublicBudget.limit SimPublicBudget.overflow ==>\n'
  '  SimPublicBudget.nh<=qH]=>\n'
  ' `|Pr[FOFreshReencryptGame(A).run() @ &m:res]-Pr[SimGuardedPublicGame(A).run() @ &m:res]|\n'
  ' <=(max 0 budget)%r/(2%r^768)+(qH+max 0 budget)%r/(2%r^353).'),
 ('final-has-no-assumed-security-distance',
  'ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimFinal.ec',
  'lemma sim_fo_public_distance\n'
  ' (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,\n'
  '  -FOContext,-FOBadState,-FOBudgetState,-FOGRO.RO,-FOGRO.FRO,-SimPublic,-SimHistory,-SimBad,\n'
  '  -SimPhaseInput,-SimSelectedFixed,-SimPublicBudget,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,\n'
  '  -SH.HB.Count,-SH.HB.HybOrcl}) qH &m :\n'
  ' 0<=qH=>\n'
  ' (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),\n'
  '  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>\n'
  '  islossless D.decap=>islossless A(H,D).guess)=>\n'
  ' (forall(H<:CCAExtendedOraclePort {-A,-FOBudgetState})(D<:CCADecapPort {-A,-FOBudgetState}),\n'
  '  hoare[FOCountedA(A,H,D).guess:FOBudgetState.nD=0 ==>FOBudgetState.nD<=max 0 budget])=>\n'
  ' hoare[SimPublicCountedA(A,FOHashView(SimKnownPublicBackend),FODecapView(SimKnownPublicBackend)).guess:\n'
  '  sim_public_budget_initial qH SimPublicBudget.nh SimPublicBudget.limit SimPublicBudget.overflow ==>\n'
  '  SimPublicBudget.nh<=qH]=>\n'
  ' `|Pr[FOFreshReencryptGame(A).run() @ &m:res]-Pr[SimPublicFreshGame(A).run() @ &m:res]|\n'
  ' <=(max 0 budget)%r/(2%r^768)+(qH+max 0 budget)%r/(2%r^353).',
  'lemma sim_fo_public_distance\n'
  ' (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,\n'
  '  -FOContext,-FOBadState,-FOBudgetState,-FOGRO.RO,-FOGRO.FRO,-SimPublic,-SimHistory,-SimBad,\n'
  '  -SimPhaseInput,-SimSelectedFixed,-SimPublicBudget,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,\n'
  '  -SH.HB.Count,-SH.HB.HybOrcl}) qH &m :\n'
  ' 0<=qH=>(`|Pr[FOFreshReencryptGame(A).run() @ &m:res]-Pr[SimPublicFreshGame(A).run() @ &m:res]|<=(max 0 '
  'budget)%r/(2%r^768)+(qH+max 0 budget)%r/(2%r^353))=>\n'
  ' (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),\n'
  '  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>\n'
  '  islossless D.decap=>islossless A(H,D).guess)=>\n'
  ' (forall(H<:CCAExtendedOraclePort {-A,-FOBudgetState})(D<:CCADecapPort {-A,-FOBudgetState}),\n'
  '  hoare[FOCountedA(A,H,D).guess:FOBudgetState.nD=0 ==>FOBudgetState.nD<=max 0 budget])=>\n'
  ' hoare[SimPublicCountedA(A,FOHashView(SimKnownPublicBackend),FODecapView(SimKnownPublicBackend)).guess:\n'
  '  sim_public_budget_initial qH SimPublicBudget.nh SimPublicBudget.limit SimPublicBudget.overflow ==>\n'
  '  SimPublicBudget.nh<=qH]=>\n'
  ' `|Pr[FOFreshReencryptGame(A).run() @ &m:res]-Pr[SimPublicFreshGame(A).run() @ &m:res]|\n'
  ' <=(max 0 budget)%r/(2%r^768)+(qH+max 0 budget)%r/(2%r^353).')]
