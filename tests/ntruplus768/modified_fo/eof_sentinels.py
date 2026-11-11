"""Reviewed semantic declarations; source pins remain pending final family freeze."""

SENTINELS = {'kem_modified_fo/NTRUPlus768FOEagerG.ec': '\n'
                                           '\n'
                                           'lemma __modified_fo_eof\n'
                                           ' (C<:FOGContext {-FOGRO.RO,-FOGRO.FRO}) :\n'
                                           ' equiv[FOGCompletedContext(C,FOGRO.RO).distinguish ~ '
                                           'C(FOGPROMGet(FOGRO.RO)).run :\n'
                                           '   ={arg,glob C,FOGRO.RO.m} ==> ={res,glob C}].\n'
                                           'proof. exact (fo_g_partial_eager C). qed.\n',
 'kem_modified_fo/NTRUPlus768FOModel.ec': '\n'
                                          '\n'
                                          'lemma __modified_fo_eof : islossless FOBudgetState.configure.\n'
                                          'proof. exact fo_budget_configure_ll. qed.\n',
 'kem_modified_fo/NTRUPlus768FOProcedures.ec': '\n'
                                               '\n'
                                               'lemma __modified_fo_eof (G<:MessageSHAKE) '
                                               '(H<:CompleteSHAKEH) :\n'
                                               ' islossless G.shake =>islossless H.shake =>islossless '
                                               'FODecaps(G,H).run.\n'
                                               'proof. exact (fo_decaps_lossless G H). qed.\n',
 'kem_modified_fo/NTRUPlus768FOSetupDistribution.ec': '\n'
                                                      '\n'
                                                      'lemma __modified_fo_eof &m workspace0 :\n'
                                                      ' mk(fun z=>Pr[FOSetupSource.guess(workspace0) @ '
                                                      '&m:res=z])=\n'
                                                      ' fo_setup_joint_law(mk(fun '
                                                      '(key:fo_setup_key_observation)=>Pr[FOSetupKeySource.guess(workspace0) '
                                                      '@ &m:res=key])).\n'
                                                      'proof. exact (fo_setup_joint_distribution &m '
                                                      'workspace0). qed.\n',
 'kem_modified_fo/NTRUPlus768FOAlgebra.ec': '\n'
                                            '\n'
                                            'lemma __modified_fo_eof w g ct pad hout :pke_key_relation w=>\n'
                                            ' fo_pad_consistent g (rrec_native_bytes w ct) pad=>\n'
                                            ' (!fo_base_bad w g (fo_candidate_message w ct pad) hout \\/\n'
                                            '  fo_reencryption w g (fo_candidate_message w ct pad) '
                                            'hout<>Some ct)=>\n'
                                            ' fo_native_accept w ct pad hout=fo_full_accept w g ct pad '
                                            'hout.\n'
                                            'proof. exact (fo_acceptance_good_or_reject w g ct pad hout). '
                                            'qed.\n',
 'kem_modified_fo/NTRUPlus768FOError.ec': '\n'
                                          '\n'
                                          'lemma __modified_fo_eof w :\n'
                                          ' E acwc2_eager_g_law (fo_error w)<=acwc2_base_mean '
                                          'w+acwc2_epsilon+acwc2_union_tail.\n'
                                          'proof. exact (fo_eager_error_bound w). qed.\n',
 'kem_modified_fo/NTRUPlus768FOGCompletion.ec': '\n'
                                                '\n'
                                                'lemma __modified_fo_eof :\n'
                                                ' equiv[FOGComplete(FOGRO.RO).run ~ FOGIIDSetup.run:\n'
                                                ' FOGRO.RO.m{1}=empty /\\ ROG.m{2}=empty ==>\n'
                                                ' FOGRO.RO.m{1}=ROG.m{2} /\\ ROG.m{2}=acwc2_g_cache res{2} '
                                                '/\\\n'
                                                ' size res{2}=size acwc2_r_enum].\n'
                                                'proof. exact fo_g_completion_iid. qed.\n',
 'kem_modified_fo/NTRUPlus768FOKEMGame.ec': '\n'
                                            '\n'
                                            'lemma __modified_fo_eof\n'
                                            ' (A<:CCAExtendedAdversary '
                                            '{-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey})\n'
                                            ' &m (event:bool->bool) :\n'
                                            ' Pr[FOFreshNativeGame(A).run() @ &m:event res]=\n'
                                            ' Pr[CCASharedSetupGame(FreshExpand,A).run() @ &m:event res].\n'
                                            'proof. exact (fo_fresh_native_game_event A &m event). qed.\n',
 'kem_modified_fo/NTRUPlus768FOQueryBudget.ec': '\n'
                                                '\n'
                                                'lemma __modified_fo_eof\n'
                                                ' (A<:CCAExtendedAdversary {-FOBudgetState})\n'
                                                ' (H<:CCAExtendedOraclePort {-A,-FOBudgetState}) '
                                                '(D<:CCADecapPort {-A,-FOBudgetState}) q0 :\n'
                                                ' hoare[FOCappedA(A,H,D).guess:\n'
                                                ' fo_budget_range FOBudgetState.nH FOBudgetState.nD '
                                                'FOBudgetState.limit /\\ FOBudgetState.limit=q0 ==>\n'
                                                ' fo_budget_range FOBudgetState.nH FOBudgetState.nD '
                                                'FOBudgetState.limit /\\ FOBudgetState.limit=q0].\n'
                                                'proof. exact (fo_cap_adversary_range A H D q0). qed.\n',
 'kem_modified_fo/NTRUPlus768FOBadBound.ec': '\n'
                                             '\n'
                                             'lemma __modified_fo_eof\n'
                                             ' (A<:CCAExtendedAdversary '
                                             '{-FOContext,-FOBadState,-FOBudgetState})\n'
                                             ' (B<:FOBackend {-A,-FOBudgetState})\n'
                                             ' w0 g0 q0 pk0 ct0 key0 &m :\n'
                                             ' 0<=q0 =>FOContext.w{m}=w0 =>FOContext.g{m}=g0 =>\n'
                                             ' (forall b,hoare[B.e:FOContext.w=w0 /\\ FOContext.g=g0 /\\ '
                                             'FOBadState.bad=b ==>\n'
                                             '   FOContext.w=w0 /\\ FOContext.g=g0 /\\ FOBadState.bad=b]) '
                                             '=>\n'
                                             ' (forall b,hoare[B.f:FOContext.w=w0 /\\ FOContext.g=g0 /\\ '
                                             'FOBadState.bad=b ==>\n'
                                             '   FOContext.w=w0 /\\ FOContext.g=g0 /\\ FOBadState.bad=b]) '
                                             '=>\n'
                                             ' (forall b,hoare[B.g:FOContext.w=w0 /\\ FOContext.g=g0 /\\ '
                                             'FOBadState.bad=b ==>\n'
                                             '   FOContext.w=w0 /\\ FOContext.g=g0 /\\ FOBadState.bad=b]) '
                                             '=>\n'
                                             ' (forall b,hoare[B.h:FOContext.w=w0 /\\ FOContext.g=g0 /\\ '
                                             'FOBadState.bad=b ==>\n'
                                             '   FOContext.w=w0 /\\ FOContext.g=g0 /\\ (b=>FOBadState.bad)]) '
                                             '=>\n'
                                             ' (forall b,hoare[B.raw:FOContext.w=w0 /\\ FOContext.g=g0 /\\ '
                                             'FOBadState.bad=b ==>\n'
                                             '   FOContext.w=w0 /\\ FOContext.g=g0 /\\ (b=>FOBadState.bad)]) '
                                             '=>\n'
                                             ' (forall b,hoare[B.raw:FOContext.w=w0 /\\ FOContext.g=g0 /\\ '
                                             'FOBadState.bad=b /\\ !fo_raw_h input outlen ==>\n'
                                             '   FOContext.w=w0 /\\ FOContext.g=g0 /\\ FOBadState.bad=b]) '
                                             '=>\n'
                                             ' (forall b,hoare[B.decap:FOContext.w=w0 /\\ FOContext.g=g0 /\\ '
                                             'FOBadState.bad=b ==>\n'
                                             '   FOContext.w=w0 /\\ FOContext.g=g0 /\\ (b=>FOBadState.bad)]) '
                                             '=>\n'
                                             ' (phoare[B.h:FOContext.w=w0 /\\ FOContext.g=g0 /\\ '
                                             '!FOBadState.bad ==>FOBadState.bad]\n'
                                             '   <=(fo_error w0 g0)) =>\n'
                                             ' (phoare[B.raw:FOContext.w=w0 /\\ FOContext.g=g0 /\\ '
                                             '!FOBadState.bad /\\ fo_raw_h input outlen ==>FOBadState.bad]\n'
                                             '   <=(fo_error w0 g0)) =>\n'
                                             ' (phoare[B.decap:FOContext.w=w0 /\\ FOContext.g=g0 /\\ '
                                             '!FOBadState.bad ==>FOBadState.bad]\n'
                                             '   <=(fo_error w0 g0)) =>\n'
                                             ' Pr[FOBadPhase(A,B).run(q0,pk0,ct0,key0) @ &m:FOBadState.bad] '
                                             '<=q0%r*fo_error w0 g0.\n'
                                             'proof. exact (fo_bounded_phase_bad A B w0 g0 q0 pk0 ct0 key0 '
                                             '&m). qed.\n',
 'kem_modified_fo/NTRUPlus768FOCapRemoval.ec': '\n'
                                               '\n'
                                               'lemma __modified_fo_eof\n'
                                               ' (A<:CCAExtendedAdversary {-FOBudgetState}) (B<:FOBackend '
                                               '{-A,-FOBudgetState}) q0 :\n'
                                               ' 0<=q0 =>\n'
                                               ' islossless B.e=>islossless B.f=>islossless B.g=>islossless '
                                               'B.h=>islossless B.raw=>islossless B.decap=>\n'
                                               ' (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort '
                                               '{-A}),\n'
                                               '  islossless H.e=>islossless H.f=>islossless H.g=>islossless '
                                               'H.h=>islossless H.raw=>\n'
                                               '  islossless D.decap=>islossless A(H,D).guess) =>\n'
                                               ' hoare[FOCountedA(A,FOHashView(B),FODecapView(B)).guess:\n'
                                               ' fo_budget_initial q0 FOBudgetState.nH FOBudgetState.nD '
                                               'FOBudgetState.limit FOBudgetState.overflow ==>\n'
                                               ' fo_query_count FOBudgetState.nH FOBudgetState.nD<=q0] =>\n'
                                               ' equiv[FOConfiguredA(A,FOHashView(B),FODecapView(B)).guess ~ '
                                               'A(FOHashView(B),FODecapView(B)).guess:\n'
                                               ' ={arg,glob A,glob B} /\\ FOBudgetState.limit{1}=q0 ==> '
                                               '={res,glob A,glob B}].\n'
                                               'proof. exact (fo_configured_phase_plain A B q0). qed.\n',
 'kem_modified_fo/NTRUPlus768FOChallenge.ec': '\n'
                                              '\n'
                                              'lemma __modified_fo_eof w g excluded hstar cstar hm ct pad '
                                              'hout :\n'
                                              ' pke_key_relation w =>fo_pad_consistent g (rrec_native_bytes '
                                              'w ct) pad =>\n'
                                              ' fo_challenge_invariant w g excluded hstar cstar hm =>\n'
                                              ' Some(fo_candidate_message w ct pad,complete_sk_suffix '
                                              'w.`kg_sk)=excluded =>\n'
                                              ' hm.[(fo_candidate_message w ct pad,complete_sk_suffix '
                                              'w.`kg_sk)]=Some hout =>\n'
                                              ' ct<>cstar =>!fo_native_accept w ct pad hout /\\ '
                                              '!fo_full_accept w g ct pad hout.\n'
                                              'proof. exact (fo_challenge_both_reject w g excluded hstar '
                                              'cstar hm ct pad hout). qed.\n',
 'kem_modified_fo/NTRUPlus768FOErrorExpectation.ec': '\n'
                                                     '\n'
                                                     "lemma __modified_fo_eof ['a 'b] (d:'a distr) (K:'a->'b "
                                                     "distr) bad (bound:'a->real) :\n"
                                                     ' hasE d bound =>(forall x,x \\in d=>mu(K x)bad<=bound '
                                                     'x) =>\n'
                                                     ' mu(dlet d K)bad<=E d bound.\n'
                                                     'proof. exact (fo_kernel_average d K bad bound). qed.\n',
 'kem_modified_fo/NTRUPlus768FOGAdapters.ec': '\n'
                                              '\n'
                                              'lemma __modified_fo_eof\n'
                                              ' (A<:CCAExtendedAdversary '
                                              '{-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOGRO.RO,-FOGRO.FRO}) '
                                              '&m (event:bool->bool) :\n'
                                              ' Pr[FOFreshReencryptGame(A).run() @ &m:event res]=\n'
                                              ' Pr[FOGEagerFullGame(A).run() @ &m:event res].\n'
                                              'proof. exact (fo_g_full_eager_probability A &m event). qed.\n',
 'kem_modified_fo/NTRUPlus768FOHMonitor.ec': '\n'
                                             '\n'
                                             'lemma __modified_fo_eof w0 g0 ex0 : hoare[FOHRawXOF.get:\n'
                                             ' FOContext.w=w0 /\\ FOContext.g=g0 /\\ '
                                             'FOContext.challenge_h=ex0 /\\\n'
                                             ' (!FOBadState.bad=>fo_hcache_good w0 g0 ex0 ROH.m) ==>\n'
                                             ' FOContext.w=w0 /\\ FOContext.g=g0 /\\ '
                                             'FOContext.challenge_h=ex0 /\\\n'
                                             ' (!FOBadState.bad=>fo_hcache_good w0 g0 ex0 ROH.m)].\n'
                                             'proof. exact (fo_raw_get_invariant w0 g0 ex0). qed.\n',
 'kem_modified_fo/NTRUPlus768FOBackendContracts.ec': '\n'
                                                     '\n'
                                                     'lemma __modified_fo_eof w0 g0 : '
                                                     'phoare[FOFullBackend.decap:\n'
                                                     ' FOContext.w=w0 /\\ FOContext.g=g0 /\\ !FOBadState.bad '
                                                     '==>FOBadState.bad] <=(fo_error w0 g0).\n'
                                                     'proof. exact (fo_full_decap_bad_bound w0 g0). qed.\n',
 'kem_modified_fo/NTRUPlus768FOChallengeBridge.ec': '\n'
                                                    '\n'
                                                    'lemma __modified_fo_eof\n'
                                                    ' (A<:CCAExtendedAdversary '
                                                    '{-FOContext,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle}) '
                                                    ':\n'
                                                    ' islossless '
                                                    'A(SharedCCAExtendedOracles,CCADecapOracle).guess =>\n'
                                                    ' islossless FOChallengeOriginal(A).run.\n'
                                                    'proof. exact (fo_challenge_original_ll A). qed.\n',
 'kem_modified_fo/NTRUPlus768FOGameCapRemoval.ec': '\n'
                                                   '\n'
                                                   'lemma __modified_fo_eof\n'
                                                   ' (A<:CCAExtendedAdversary '
                                                   '{-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOBudgetState}) '
                                                   '&m q0 (event:bool->bool) :\n'
                                                   ' 0<=q0=>FOBudgetState.limit{m}=q0=>\n'
                                                   ' (forall (H<:CCAExtendedOraclePort {-A}) '
                                                   '(D<:CCADecapPort {-A}),\n'
                                                   '  islossless H.e=>islossless H.f=>islossless '
                                                   'H.g=>islossless H.h=>islossless H.raw=>\n'
                                                   '  islossless D.decap=>islossless A(H,D).guess)=>\n'
                                                   ' '
                                                   'hoare[FOCountedA(A,FOHashView(FOFullPlainBackend),FODecapView(FOFullPlainBackend)).guess:\n'
                                                   ' fo_budget_initial q0 FOBudgetState.nH FOBudgetState.nD '
                                                   'FOBudgetState.limit FOBudgetState.overflow ==>\n'
                                                   ' fo_query_count FOBudgetState.nH '
                                                   'FOBudgetState.nD<=q0]=>\n'
                                                   ' Pr[FOFreshReencryptGame(FOConfiguredA(A)).run() @ '
                                                   '&m:event res]=\n'
                                                   ' Pr[FOFreshReencryptGame(A).run() @ &m:event res].\n'
                                                   'proof. exact (fo_full_configured_event A &m q0 event). '
                                                   'qed.\n',
 'kem_modified_fo/NTRUPlus768FOJointGames.ec': '\n'
                                               '\n'
                                               'lemma __modified_fo_eof\n'
                                               ' (A<:CCAExtendedAdversary '
                                               '{-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOGRO.RO,-FOGRO.FRO}) '
                                               '&m :\n'
                                               ' Pr[FOGEagerFullGame(A).run() @ &m:res]=\n'
                                               ' mu1(dlet(mk(fun s=>Pr[FOSetupSource.guess(witness) @ '
                                               '&m:res=s]))\n'
                                               '   (fun s=>mk(fun '
                                               'b=>Pr[FOPlainKernel(A,FOReencryptDecap(SHAKEGROM,SHAKEHROM)).guess(s) '
                                               '@ &m:res=b])))true.\n'
                                               'proof. exact (fo_full_eager_mu A &m). qed.\n',
 'kem_modified_fo/NTRUPlus768FOMonitorBridge.ec': '\n'
                                                  '\n'
                                                  'lemma __modified_fo_eof w g ex hs cs ct msg : ct<>cs=>\n'
                                                  ' hoare[FOSHAKEH.shake:\n'
                                                  ' input=hash_h_prepare_spec msg (complete_sk_suffix '
                                                  'w.`kg_sk) /\\\n'
                                                  ' fo_monitor_invariant w g ex hs cs (glob FOSHAKEH) ==>\n'
                                                  ' fo_monitor_invariant w g ex hs cs (glob FOSHAKEH) /\\\n'
                                                  ' (fo_monitor_good(glob FOSHAKEH)=>(!fo_base_bad w g msg '
                                                  'res \\/ fo_reencryption w g msg res<>Some ct))].\n'
                                                  'proof. exact (fo_monitored_hash_contract w g ex hs cs ct '
                                                  'msg). qed.\n',
 'kem_modified_fo/NTRUPlus768FOSetupExpectation.ec': '\n'
                                                     '\n'
                                                     "lemma __modified_fo_eof ['a] &m "
                                                     "(K:fo_setup_observation->'a distr) bad (Q:real) :\n"
                                                     ' 0%r<=Q =>\n'
                                                     ' (forall x,x \\in mk(fun '
                                                     'z=>Pr[FOSetupSource.guess(witness) @ &m:res=z]) =>\n'
                                                     '   mu(K x)bad<=Q*fo_setup_error x) =>\n'
                                                     ' mu(dlet(mk(fun z=>Pr[FOSetupSource.guess(witness) @ '
                                                     '&m:res=z]))K)bad<=Q/(2%r^353).\n'
                                                     'proof. exact (fo_setup_kernel_bound &m K bad Q). '
                                                     'qed.\n',
 'kem_modified_fo/NTRUPlus768FOBackendBounds.ec': '\n'
                                                  '\n'
                                                  'lemma __modified_fo_eof\n'
                                                  ' (A<:CCAExtendedAdversary '
                                                  '{-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,\n'
                                                  '   -FOPublicKey,-FOContext,-FOBadState,-FOBudgetState})\n'
                                                  ' w0 g0 q0 pk0 ct0 key0 &m :\n'
                                                  ' 0<=q0 =>FOContext.w{m}=w0 =>FOContext.g{m}=g0 =>\n'
                                                  ' Pr[FOBadPhase(A,FOFullBackend).run(q0,pk0,ct0,key0) @ '
                                                  '&m:FOBadState.bad]\n'
                                                  ' <=q0%r*fo_error w0 g0.\n'
                                                  'proof. exact (fo_full_bounded_bad A w0 g0 q0 pk0 ct0 key0 '
                                                  '&m). qed.\n',
 'kem_modified_fo/NTRUPlus768FOFixedGames.ec': '\n'
                                               '\n'
                                               'lemma __modified_fo_eof\n'
                                               ' (A<:CCAExtendedAdversary {-FOBudgetState}) (B<:FOBackend '
                                               '{-A,-FOBudgetState}) :\n'
                                               ' islossless B.e=>islossless B.f=>islossless B.g=>islossless '
                                               'B.h=>islossless B.raw=>islossless B.decap=>\n'
                                               ' (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort '
                                               '{-A}),\n'
                                               '  islossless H.e=>islossless H.f=>islossless H.g=>islossless '
                                               'H.h=>islossless H.raw=>\n'
                                               '  islossless D.decap=>islossless A(H,D).guess) =>\n'
                                               ' islossless FOObservedKernel(A,B).guess.\n'
                                               'proof. exact (fo_observed_kernel_ll A B). qed.\n',
 'kem_modified_fo/NTRUPlus768FOGameAverage.ec': '\n'
                                                '\n'
                                                'lemma __modified_fo_eof &m\n'
                                                ' (K0 K1:fo_setup_observation->bool distr) (q:int) :\n'
                                                ' 0<=q =>\n'
                                                ' (forall s,s \\in mk(fun z=>Pr[FOSetupSource.guess(witness) '
                                                '@ &m:res=z]) =>\n'
                                                '   `|mu1(K0 s)true-mu1(K1 s)true|<=q%r*fo_setup_error s) '
                                                '=>\n'
                                                ' `|mu1(dlet(mk(fun z=>Pr[FOSetupSource.guess(witness) @ '
                                                '&m:res=z]))K0)true-\n'
                                                '   mu1(dlet(mk(fun z=>Pr[FOSetupSource.guess(witness) @ '
                                                '&m:res=z]))K1)true|\n'
                                                ' <=q%r/(2%r^353).\n'
                                                'proof. exact (fo_setup_kernel_win_distance &m K0 K1 q). '
                                                'qed.\n',
 'kem_modified_fo/NTRUPlus768FONativeBridge.ec': '\n'
                                                 '\n'
                                                 'lemma __modified_fo_eof w g ex hs cs ct0 :\n'
                                                 ' pke_key_relation w=>ct0<>cs=>\n'
                                                 ' equiv[CompleteDecaps(SHAKEGROM,FOSHAKEH).run ~ '
                                                 'FODecaps(SHAKEGROM,FOSHAKEH).run:\n'
                                                 ' ct{1}=ct0 /\\ ct{2}=ct0 /\\ sk{1}=w.`kg_sk /\\ '
                                                 'sk{2}=w.`kg_sk /\\ pk{2}=w.`kg_pk /\\\n'
                                                 ' ={workspace,ROG.m,ROH.m,glob FOContext,glob FOBadState} '
                                                 '/\\\n'
                                                 ' FOContext.w{1}=w /\\ FOContext.g{1}=g /\\ '
                                                 'FOContext.challenge_h{1}=ex /\\\n'
                                                 ' (!FOBadState.bad{1}=>fo_hcache_good w g ex ROH.m{1}) /\\\n'
                                                 ' fo_challenge_invariant w g ex hs cs ROH.m{1} /\\ '
                                                 'acwc2_cache_matches g ROG.m{1} ==>\n'
                                                 ' ={ROG.m,ROH.m,glob FOContext,glob FOBadState} /\\\n'
                                                 ' FOContext.w{1}=w /\\ FOContext.g{1}=g /\\ '
                                                 'FOContext.challenge_h{1}=ex /\\\n'
                                                 ' (!FOBadState.bad{1}=>fo_hcache_good w g ex ROH.m{1}) /\\\n'
                                                 ' fo_challenge_invariant w g ex hs cs ROH.m{1} /\\ '
                                                 'acwc2_cache_matches g ROG.m{1} /\\\n'
                                                 ' res.`3{1}=clear_zero_spec /\\ res.`3{2}=clear_zero_spec '
                                                 '/\\ (!FOBadState.bad{1}=>res{1}=res{2})].\n'
                                                 'proof. exact (fo_monitored_decaps_equiv w g ex hs cs ct0). '
                                                 'qed.\n',
 'kem_modified_fo/NTRUPlus768FOAdversaryCoupling.ec': '\n'
                                                      '\n'
                                                      'lemma __modified_fo_eof\n'
                                                      ' (A<:CCAExtendedAdversary '
                                                      '{-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOContext,-FOBadState,-FOBudgetState}) '
                                                      'w g ex hs cs :\n'
                                                      ' pke_key_relation w=>\n'
                                                      ' (forall (H<:CCAExtendedOraclePort {-A}) '
                                                      '(D<:CCADecapPort {-A}),\n'
                                                      ' islossless H.e=>islossless H.f=>islossless '
                                                      'H.g=>islossless H.h=>islossless H.raw=>\n'
                                                      ' islossless D.decap=>islossless A(H,D).guess) =>\n'
                                                      ' equiv[FOBadPhase(A,FONativeBackend).run ~ '
                                                      'FOBadPhase(A,FOFullBackend).run:\n'
                                                      ' ={arg,glob '
                                                      'A,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk,glob '
                                                      'FOContext,glob FOBadState,glob FOBudgetState} /\\ '
                                                      'FOPublicKey.pk{1}=w.`kg_pk /\\ '
                                                      'CCADecapOracle.sk{1}=w.`kg_sk /\\ '
                                                      'CCADecapOracle.cstar{1}=Some cs /\\\n'
                                                      ' acwc2_cache_matches g ROG.m{1} /\\\n'
                                                      ' FOContext.w{1}=w /\\ FOContext.g{1}=g /\\ '
                                                      'FOContext.challenge_h{1}=ex /\\\n'
                                                      ' fo_hcache_good w g ex ROH.m{1} /\\ '
                                                      'fo_challenge_invariant w g ex hs cs ROH.m{1} ==>\n'
                                                      ' ={FOBadState.bad} /\\ (!FOBadState.bad{2}=>\n'
                                                      ' ={res,glob '
                                                      'A,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk,glob '
                                                      'FOContext,glob FOBadState,glob FOBudgetState} /\\ '
                                                      'fo_adversary_invariant w g ex hs cs ROG.m{1} (glob '
                                                      'FOSHAKEH){1})].\n'
                                                      'proof. exact (fo_observed_phase_upto A w g ex hs cs). '
                                                      'qed.\n',
 'kem_modified_fo/NTRUPlus768FOKernelBound.ec': '\n'
                                                '\n'
                                                'lemma __modified_fo_eof\n'
                                                ' (A<:CCAExtendedAdversary '
                                                '{-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,\n'
                                                '   -FOPublicKey,-FOContext,-FOBadState,-FOBudgetState}) s Q '
                                                '&m :\n'
                                                ' 0<=Q =>FOBudgetState.limit{m}=Q =>\n'
                                                ' Pr[FOObservedFullKernel(A).guess(s) @ '
                                                '&m:FOBadState.bad]<=Q%r*fo_setup_error s.\n'
                                                'proof. exact (fo_observed_full_kernel_bad A s Q &m). qed.\n',
 'kem_modified_fo/NTRUPlus768FOMonitorProjection.ec': '\n'
                                                      '\n'
                                                      'lemma __modified_fo_eof\n'
                                                      ' (A<:CCAExtendedAdversary '
                                                      '{-FOContext,-FOBadState,-FOBudgetState,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey}) '
                                                      '&m s (event:bool->bool) :\n'
                                                      ' '
                                                      'Pr[FOPlainKernel(FOConfiguredA(A),FOReencryptDecap(SHAKEGROM,SHAKEHROM)).guess(s) '
                                                      '@ &m:event res]=\n'
                                                      ' Pr[FOObservedFullKernel(A).guess(s) @ &m:event '
                                                      'res].\n'
                                                      'proof. exact (fo_full_kernel_monitor_event A &m s '
                                                      'event). qed.\n',
 'kem_modified_fo/NTRUPlus768FOGameHop.ec': '\n'
                                            '\n'
                                            'lemma __modified_fo_eof\n'
                                            ' (A<:CCAExtendedAdversary '
                                            '{-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOContext,-FOBadState,-FOBudgetState}) '
                                            's Q &m :\n'
                                            ' fo_setup_valid s=>0<=Q=>FOBudgetState.limit{m}=Q=>\n'
                                            ' (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort '
                                            '{-A}),\n'
                                            ' islossless H.e=>islossless H.f=>islossless H.g=>islossless '
                                            'H.h=>islossless H.raw=>\n'
                                            ' islossless D.decap=>islossless A(H,D).guess) =>\n'
                                            ' `|Pr[FOObservedNativeKernel(A).guess(s) @ &m:res=true]-\n'
                                            '   Pr[FOObservedFullKernel(A).guess(s) @ '
                                            '&m:res=true]|<=Q%r*fo_setup_error s.\n'
                                            'proof. exact (fo_observed_kernel_distance A s Q &m). qed.\n',
 'kem_modified_fo/NTRUPlus768FOSecurity.ec': '\n'
                                             '\n'
                                             'lemma __modified_fo_eof\n'
                                             ' (A<:CCAExtendedAdversary '
                                             '{-FOContext,-FOBadState,-FOBudgetState,-ROE,-ROF,-ROG,-ROH,\n'
                                             '  '
                                             '-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOGRO.RO,-FOGRO.FRO,\n'
                                             '  '
                                             '-ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState,-ErasureTape}) '
                                             '&m qE q0 :\n'
                                             ' 0<=q0=>FOBudgetState.limit{m}=q0=>\n'
                                             ' (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort '
                                             '{-A}),\n'
                                             '  islossless H.e=>islossless H.f=>islossless H.g=>islossless '
                                             'H.h=>islossless H.raw=>\n'
                                             '  islossless D.decap=>islossless A(H,D).guess)=>\n'
                                             ' '
                                             'hoare[CountedA(A,SharedCCAExtendedOracles,CCADecapOracle).guess:\n'
                                             ' EBudgetState.requests=0 /\\ EBudgetState.forwarded=0 /\\ '
                                             'EBudgetState.limit=qE /\\\n'
                                             ' !EBudgetState.overflow /\\ EBudgetState.queries=[] ==> '
                                             'EBudgetState.requests<=qE]=>\n'
                                             ' erasure_budget_initial qE EBudgetState.requests{m} '
                                             'EBudgetState.forwarded{m}\n'
                                             '  EBudgetState.limit{m} EBudgetState.overflow{m} '
                                             'EBudgetState.queries{m}=>\n'
                                             ' '
                                             'hoare[FOCountedA(A,FOHashView(FONativePlainBackend),FODecapView(FONativePlainBackend)).guess:\n'
                                             ' fo_budget_initial q0 FOBudgetState.nH FOBudgetState.nD '
                                             'FOBudgetState.limit FOBudgetState.overflow ==>\n'
                                             ' fo_query_count FOBudgetState.nH FOBudgetState.nD<=q0]=>\n'
                                             ' '
                                             'hoare[FOCountedA(A,FOHashView(FOFullPlainBackend),FODecapView(FOFullPlainBackend)).guess:\n'
                                             ' fo_budget_initial q0 FOBudgetState.nH FOBudgetState.nD '
                                             'FOBudgetState.limit FOBudgetState.overflow ==>\n'
                                             ' fo_query_count FOBudgetState.nH FOBudgetState.nD<=q0]=>\n'
                                             ' `|Pr[CCAOriginalGame(A).run() @ &m:res]-\n'
                                             '   Pr[FOFreshReencryptGame(A).run() @ &m:res]|<=\n'
                                             ' (130820%r+512%r*qE%r)/(2%r^256)+q0%r/(2%r^353).\n'
                                             'proof. exact (fo_original_full_distance_256 A &m qE q0). '
                                             'qed.\n'}

SEMANTIC_TARGETS = {'kem_modified_fo/NTRUPlus768FOEagerG.ec': 'fo_g_partial_eager',
 'kem_modified_fo/NTRUPlus768FOModel.ec': 'fo_budget_configure_ll',
 'kem_modified_fo/NTRUPlus768FOProcedures.ec': 'fo_decaps_lossless',
 'kem_modified_fo/NTRUPlus768FOSetupDistribution.ec': 'fo_setup_joint_distribution',
 'kem_modified_fo/NTRUPlus768FOAlgebra.ec': 'fo_acceptance_good_or_reject',
 'kem_modified_fo/NTRUPlus768FOError.ec': 'fo_eager_error_bound',
 'kem_modified_fo/NTRUPlus768FOGCompletion.ec': 'fo_g_completion_iid',
 'kem_modified_fo/NTRUPlus768FOKEMGame.ec': 'fo_fresh_native_game_event',
 'kem_modified_fo/NTRUPlus768FOQueryBudget.ec': 'fo_cap_adversary_range',
 'kem_modified_fo/NTRUPlus768FOBadBound.ec': 'fo_bounded_phase_bad',
 'kem_modified_fo/NTRUPlus768FOCapRemoval.ec': 'fo_configured_phase_plain',
 'kem_modified_fo/NTRUPlus768FOChallenge.ec': 'fo_challenge_both_reject',
 'kem_modified_fo/NTRUPlus768FOErrorExpectation.ec': 'fo_kernel_average',
 'kem_modified_fo/NTRUPlus768FOGAdapters.ec': 'fo_g_full_eager_probability',
 'kem_modified_fo/NTRUPlus768FOHMonitor.ec': 'fo_raw_get_invariant',
 'kem_modified_fo/NTRUPlus768FOBackendContracts.ec': 'fo_full_decap_bad_bound',
 'kem_modified_fo/NTRUPlus768FOChallengeBridge.ec': 'fo_challenge_original_ll',
 'kem_modified_fo/NTRUPlus768FOGameCapRemoval.ec': 'fo_full_configured_event',
 'kem_modified_fo/NTRUPlus768FOJointGames.ec': 'fo_full_eager_mu',
 'kem_modified_fo/NTRUPlus768FOMonitorBridge.ec': 'fo_monitored_hash_contract',
 'kem_modified_fo/NTRUPlus768FOSetupExpectation.ec': 'fo_setup_kernel_bound',
 'kem_modified_fo/NTRUPlus768FOBackendBounds.ec': 'fo_full_bounded_bad',
 'kem_modified_fo/NTRUPlus768FOFixedGames.ec': 'fo_observed_kernel_ll',
 'kem_modified_fo/NTRUPlus768FOGameAverage.ec': 'fo_setup_kernel_win_distance',
 'kem_modified_fo/NTRUPlus768FONativeBridge.ec': 'fo_monitored_decaps_equiv',
 'kem_modified_fo/NTRUPlus768FOAdversaryCoupling.ec': 'fo_observed_phase_upto',
 'kem_modified_fo/NTRUPlus768FOKernelBound.ec': 'fo_observed_full_kernel_bad',
 'kem_modified_fo/NTRUPlus768FOMonitorProjection.ec': 'fo_full_kernel_monitor_event',
 'kem_modified_fo/NTRUPlus768FOGameHop.ec': 'fo_observed_kernel_distance',
 'kem_modified_fo/NTRUPlus768FOSecurity.ec': 'fo_original_full_distance_256'}

MODULE_BINDERS = {'kem_modified_fo/NTRUPlus768FOEagerG.ec': ('C',),
 'kem_modified_fo/NTRUPlus768FOModel.ec': (),
 'kem_modified_fo/NTRUPlus768FOProcedures.ec': ('G', 'H'),
 'kem_modified_fo/NTRUPlus768FOSetupDistribution.ec': (),
 'kem_modified_fo/NTRUPlus768FOAlgebra.ec': (),
 'kem_modified_fo/NTRUPlus768FOError.ec': (),
 'kem_modified_fo/NTRUPlus768FOGCompletion.ec': (),
 'kem_modified_fo/NTRUPlus768FOKEMGame.ec': ('A',),
 'kem_modified_fo/NTRUPlus768FOQueryBudget.ec': ('A', 'H', 'D'),
 'kem_modified_fo/NTRUPlus768FOBadBound.ec': ('A', 'B'),
 'kem_modified_fo/NTRUPlus768FOCapRemoval.ec': ('A', 'B', 'H', 'D'),
 'kem_modified_fo/NTRUPlus768FOChallenge.ec': (),
 'kem_modified_fo/NTRUPlus768FOErrorExpectation.ec': (),
 'kem_modified_fo/NTRUPlus768FOGAdapters.ec': ('A',),
 'kem_modified_fo/NTRUPlus768FOHMonitor.ec': (),
 'kem_modified_fo/NTRUPlus768FOBackendContracts.ec': (),
 'kem_modified_fo/NTRUPlus768FOChallengeBridge.ec': ('A',),
 'kem_modified_fo/NTRUPlus768FOGameCapRemoval.ec': ('A', 'H', 'D'),
 'kem_modified_fo/NTRUPlus768FOJointGames.ec': ('A',),
 'kem_modified_fo/NTRUPlus768FOMonitorBridge.ec': (),
 'kem_modified_fo/NTRUPlus768FOSetupExpectation.ec': (),
 'kem_modified_fo/NTRUPlus768FOBackendBounds.ec': ('A',),
 'kem_modified_fo/NTRUPlus768FOFixedGames.ec': ('A', 'B', 'H', 'D'),
 'kem_modified_fo/NTRUPlus768FOGameAverage.ec': (),
 'kem_modified_fo/NTRUPlus768FONativeBridge.ec': (),
 'kem_modified_fo/NTRUPlus768FOAdversaryCoupling.ec': ('A', 'H', 'D'),
 'kem_modified_fo/NTRUPlus768FOKernelBound.ec': ('A',),
 'kem_modified_fo/NTRUPlus768FOMonitorProjection.ec': ('A',),
 'kem_modified_fo/NTRUPlus768FOGameHop.ec': ('A', 'H', 'D'),
 'kem_modified_fo/NTRUPlus768FOSecurity.ec': ('A', 'H', 'D')}

NEGATIVE_PROOFS = ('kem_modified_fo/NTRUPlus768FOEagerG.ec',
 'kem_modified_fo/NTRUPlus768FOModel.ec',
 'kem_modified_fo/NTRUPlus768FOProcedures.ec',
 'kem_modified_fo/NTRUPlus768FOSetupDistribution.ec',
 'kem_modified_fo/NTRUPlus768FOAlgebra.ec',
 'kem_modified_fo/NTRUPlus768FOError.ec',
 'kem_modified_fo/NTRUPlus768FOGCompletion.ec',
 'kem_modified_fo/NTRUPlus768FOKEMGame.ec',
 'kem_modified_fo/NTRUPlus768FOQueryBudget.ec',
 'kem_modified_fo/NTRUPlus768FOBadBound.ec',
 'kem_modified_fo/NTRUPlus768FOCapRemoval.ec',
 'kem_modified_fo/NTRUPlus768FOChallenge.ec',
 'kem_modified_fo/NTRUPlus768FOErrorExpectation.ec',
 'kem_modified_fo/NTRUPlus768FOGAdapters.ec',
 'kem_modified_fo/NTRUPlus768FOHMonitor.ec',
 'kem_modified_fo/NTRUPlus768FOBackendContracts.ec',
 'kem_modified_fo/NTRUPlus768FOChallengeBridge.ec',
 'kem_modified_fo/NTRUPlus768FOGameCapRemoval.ec',
 'kem_modified_fo/NTRUPlus768FOJointGames.ec',
 'kem_modified_fo/NTRUPlus768FOMonitorBridge.ec',
 'kem_modified_fo/NTRUPlus768FOSetupExpectation.ec',
 'kem_modified_fo/NTRUPlus768FOBackendBounds.ec',
 'kem_modified_fo/NTRUPlus768FOFixedGames.ec',
 'kem_modified_fo/NTRUPlus768FOGameAverage.ec',
 'kem_modified_fo/NTRUPlus768FONativeBridge.ec',
 'kem_modified_fo/NTRUPlus768FOAdversaryCoupling.ec',
 'kem_modified_fo/NTRUPlus768FOKernelBound.ec',
 'kem_modified_fo/NTRUPlus768FOMonitorProjection.ec',
 'kem_modified_fo/NTRUPlus768FOGameHop.ec',
 'kem_modified_fo/NTRUPlus768FOSecurity.ec')

