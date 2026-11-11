"""Frozen whole-declaration semantic probes, inserted before trailing theory ends/declarations."""

SENTINELS = {'kem_fo_simulation/NTRUPlus768SimAverage.ec': '\n'
                                               '\n'
                                               'lemma __fo_simulation_eof &m (K0 '
                                               'K1:fo_setup_observation->bool distr) qD qH :\n'
                                               ' 0<=qD=>0<=qH=>\n'
                                               ' (forall s,s \\in mk(fun z=>Pr[FOSetupSource.guess(witness) '
                                               '@ &m:res=z])=>\n'
                                               '  `|mu1(K0 s)true-mu1(K1 '
                                               's)true|<=qD%r/(2%r^768)+(qH+qD)%r*fo_setup_error s)=>\n'
                                               ' `|mu1(dlet(mk(fun z=>Pr[FOSetupSource.guess(witness) @ '
                                               '&m:res=z]))K0)true-\n'
                                               '   mu1(dlet(mk(fun z=>Pr[FOSetupSource.guess(witness) @ '
                                               '&m:res=z]))K1)true|\n'
                                               ' <=qD%r/(2%r^768)+(qH+qD)%r/(2%r^353).\n'
                                               'proof. exact (sim_setup_win_distance &m K0 K1 qD qH). qed.\n',
 'kem_fo_simulation/NTRUPlus768SimCandidate.ec': '\n'
                                                 '\n'
                                                 'lemma __fo_simulation_eof w g excluded hstar cstar\n'
                                                 ' (tab:(fo_h_input,W8.t Array224.t)fmap) (x1 x2:fo_h_input) '
                                                 'hout1 hout2 ct :\n'
                                                 ' pke_key_relation w=>fo_hcache_good w g excluded tab=>\n'
                                                 ' fo_challenge_invariant w g excluded hstar cstar '
                                                 'tab=>ct<>cstar=>\n'
                                                 ' x1.`2=complete_sk_suffix '
                                                 'w.`kg_sk=>x2.`2=complete_sk_suffix w.`kg_sk=>\n'
                                                 ' tab.[x1]=Some hout1=>tab.[x2]=Some hout2=>\n'
                                                 ' fo_reencryption w g x1.`1 hout1=Some ct=>fo_reencryption '
                                                 'w g x2.`1 hout2=Some ct=>\n'
                                                 ' x1=x2 /\\ hout1=hout2 /\\ payload_shared_key '
                                                 'hout1=payload_shared_key hout2.\n'
                                                 'proof. exact (sim_table_matches_unique w g excluded hstar '
                                                 'cstar tab x1 x2 hout1 hout2 ct). qed.\n',
 'kem_fo_simulation/NTRUPlus768SimFreshHash.ec': '\n'
                                                 '\n'
                                                 'lemma __fo_simulation_eof w ct pad :\n'
                                                 ' mu uniform224(fo_native_accept w ct pad)<=1%r/(2%r^768).\n'
                                                 'proof. exact (sim_native_fresh_hash_bound w ct pad). '
                                                 'qed.\n',
 'kem_fo_simulation/NTRUPlus768SimModel.ec': '\n'
                                             '\n'
                                             'lemma __fo_simulation_eof : islossless SimPublic.init.\n'
                                             'proof. exact sim_public_init_ll. qed.\n',
 'kem_fo_simulation/NTRUPlus768SimSequentialDistance.ec': '\n'
                                                          '\n'
                                                          'lemma __fo_simulation_eof '
                                                          '(S<:SimSequentialSystem) i0 gamma &m :\n'
                                                          ' islossless S.setup=>islossless S.phase=>\n'
                                                          ' (forall '
                                                          '&n,`|Pr[S.phase(i0,true)@&n:res]-Pr[S.phase(i0,false)@&n:res]|<=gamma)=>\n'
                                                          ' '
                                                          '`|Pr[SimSequentialKernel(S).phase(i0,true)@&m:res]-Pr[SimSequentialKernel(S).phase(i0,false)@&m:res]|<=gamma.\n'
                                                          'proof. exact (sim_sequential_unconditional S i0 '
                                                          'gamma &m). qed.\n',
 'kem_fo_simulation/NTRUPlus768SimHybrid.ec': '\n'
                                              '\n'
                                              'lemma __fo_simulation_eof\n'
                                              ' (B<:HB.Orclb {-HB.Count,-HB.HybOrcl})\n'
                                              ' (A<:HB.AdvOrclb {-HB.Count,-HB.HybOrcl,-B}) &m gamma :\n'
                                              ' (forall (O<:HB.Orcl {-HB.Count,-A}),\n'
                                              '  hoare[HB.Orcln(A(B),O).main:true ==>HB.Count.c<=max 0 '
                                              'budget])=>\n'
                                              ' islossless B.leaks=>islossless B.orclL=>islossless '
                                              'B.orclR=>\n'
                                              ' (forall (B0<:HB.Orclb {-A})(O<:HB.Orcl {-A}),\n'
                                              '  islossless O.orcl=>islossless B0.leaks=>islossless '
                                              'B0.orclL=>islossless B0.orclR=>\n'
                                              '  islossless A(B0,O).main)=>\n'
                                              ' `|Pr[HB.HybGame(A,B,HB.L(B)).main() @ &m:res]-\n'
                                              '   Pr[HB.HybGame(A,B,HB.R(B)).main() @ &m:res]|<=gamma=>\n'
                                              ' `|Pr[HB.Ln(B,A).main() @ &m:res]-Pr[HB.Rn(B,A).main() @ '
                                              '&m:res]|\n'
                                              ' <=(max 0 budget)%r*gamma.\n'
                                              'proof. exact (sim_hybrid_distance B A &m gamma). qed.\n',
 'kem_fo_simulation/NTRUPlus768SimLookup.ec': '\n'
                                              '\n'
                                              'lemma __fo_simulation_eof pk0 suffix0 star0 log0 n0 ct0 g gm0 '
                                              ': acwc2_cache_matches g gm0=>\n'
                                              ' phoare[SimLookup(FOGActual).decap:\n'
                                              ' ct=ct0 /\\ SimPublic.pk=pk0 /\\ SimPublic.suffix=suffix0 /\\ '
                                              'SimPublic.cstar=star0 /\\\n'
                                              ' SimPublic.count=n0 /\\ SimHistory.h=log0 /\\ ROG.m=gm0 ==>\n'
                                              ' res=sim_lookup_spec pk0 suffix0 star0 g log0 ct0 /\\ '
                                              'ROG.m=gm0 /\\\n'
                                              ' SimPublic.pk=pk0 /\\ SimPublic.suffix=suffix0 /\\ '
                                              'SimPublic.cstar=star0 /\\\n'
                                              ' SimPublic.count=n0+1 /\\ SimHistory.h=log0]=1%r.\n'
                                              'proof. exact (sim_lookup_correct pk0 suffix0 star0 log0 n0 '
                                              'ct0 g gm0). qed.\n',
 'kem_fo_simulation/NTRUPlus768SimSampling.ec': '\n'
                                                '\n'
                                                'lemma __fo_simulation_eof\n'
                                                ' (C<:SimGSamplingContext {-ROG,-SimGRO.RO,-SimGRO.FRO}) &m '
                                                's0 (event:bool->bool) :\n'
                                                ' Pr[C(SimGRO.RO).distinguish(s0) @ &m:event res]=\n'
                                                ' Pr[C(SimGRO.LRO).distinguish(s0) @ &m:event res].\n'
                                                'proof. exact (sim_g_sampling_probability C &m s0 event). '
                                                'qed.\n',
 'kem_fo_simulation/NTRUPlus768SimAnswer.ec': '\n'
                                              '\n'
                                              'lemma __fo_simulation_eof (G<:FOGPort)(H<:SimHPort) :\n'
                                              ' islossless G.get=>islossless H.get=>islossless '
                                              'SimAnswerReal(G,H).answer.\n'
                                              'proof. exact (sim_answer_real_ll G H). qed.\n',
 'kem_fo_simulation/NTRUPlus768SimKnownAlgebra.ec': '\n'
                                                    '\n'
                                                    'lemma __fo_simulation_eof w g log table ct pad ex hs cs '
                                                    ':\n'
                                                    ' pke_key_relation w=>sim_log_included log '
                                                    'table=>fo_hcache_good w g ex log=>\n'
                                                    ' fo_challenge_invariant w g ex hs cs table=>ct<>cs=>\n'
                                                    ' fo_pad_consistent g (rrec_native_bytes w ct) pad=>\n'
                                                    ' sim_known_result w g log ct pad=\n'
                                                    ' sim_lookup_spec w.`kg_pk (complete_sk_suffix w.`kg_sk) '
                                                    '(Some cs) g log ct.\n'
                                                    'proof. exact (sim_known_lookup_challenge w g log table '
                                                    'ct pad ex hs cs). qed.\n',
 'kem_fo_simulation/NTRUPlus768SimOracles.ec': '\n'
                                               '\n'
                                               'lemma __fo_simulation_eof :\n'
                                               ' hoare[SimRaw(SimGActual,SimHActual).get:sim_log_included '
                                               'SimHistory.h ROH.m ==>\n'
                                               ' sim_log_included SimHistory.h ROH.m].\n'
                                               'proof. exact sim_raw_actual_invariant. qed.\n',
 'kem_fo_simulation/NTRUPlus768SimPrefix.ec': '\n'
                                              '\n'
                                              'lemma __fo_simulation_eof (G<:FOGPort)(H<:SimHPort {-G}) :\n'
                                              ' equiv[FODecaps(FOGHash(G),SimHShake(H)).run ~ '
                                              'SimCore(G,SimAnswerReal(G,H)).run:\n'
                                              ' ={pk,ct,sk,glob G,glob H} ==>\n'
                                              ' cca_status_result res{1}.`1 res{1}.`2=res{2} /\\\n'
                                              ' res{1}.`3=clear_zero_spec /\\ ={glob G,glob H}].\n'
                                              'proof. exact (sim_decaps_actual G H). qed.\n',
 'kem_fo_simulation/NTRUPlus768SimPublicError.ec': '\n'
                                                   '\n'
                                                   'lemma __fo_simulation_eof w0 g0 ex0 :\n'
                                                   ' '
                                                   'hoare[SimRaw(SimGActual,SimPublicErrorH(SimHActual)).get:\n'
                                                   ' FOContext.w=w0 /\\ FOContext.g=g0 /\\ '
                                                   'FOContext.challenge_h=ex0 /\\\n'
                                                   ' sim_log_included SimHistory.h ROH.m /\\ sim_h_cover '
                                                   'SimHistory.h ROH.m ex0 /\\\n'
                                                   ' (!SimBad.corr=>fo_hcache_good w0 g0 ex0 SimHistory.h) '
                                                   '==>\n'
                                                   ' FOContext.w=w0 /\\ FOContext.g=g0 /\\ '
                                                   'FOContext.challenge_h=ex0 /\\\n'
                                                   ' sim_log_included SimHistory.h ROH.m /\\ sim_h_cover '
                                                   'SimHistory.h ROH.m ex0 /\\\n'
                                                   ' (!SimBad.corr=>fo_hcache_good w0 g0 ex0 '
                                                   'SimHistory.h)].\n'
                                                   'proof. exact (sim_public_raw_invariants w0 g0 ex0). '
                                                   'qed.\n',
 'kem_fo_simulation/NTRUPlus768SimSpreadHash.ec': '\n'
                                                  '\n'
                                                  'lemma __fo_simulation_eof w g q0 gm0 hm0 :\n'
                                                  ' pke_key_relation '
                                                  'w=>q0.`sr_pk=w.`kg_pk=>acwc2_cache_matches g gm0=>\n'
                                                  ' sim_h_input q0 \\notin hm0=>\n'
                                                  ' phoare[SimAnswerReal(FOGActual,SimHActual).answer:\n'
                                                  ' q=q0 /\\ ROG.m=gm0 /\\ ROH.m=hm0 ==>res<>None]\n'
                                                  ' <=(1%r/(2%r^768)+fo_error w g).\n'
                                                  'proof. exact (sim_answer_actual_fresh_bound w g q0 gm0 '
                                                  'hm0). qed.\n',
 'kem_fo_simulation/NTRUPlus768SimAnswerErasure.ec': '\n'
                                                     '\n'
                                                     'lemma __fo_simulation_eof\n'
                                                     ' (C<:SimAnswerContext '
                                                     '{-ROG,-ROH,-SimGRO.RO,-SimGRO.FRO,-SimHRO.RO,-SimHRO.FRO,-SimBad})\n'
                                                     ' g &m s0 (event:bool->bool) : acwc2_cache_matches g '
                                                     'ROG.m{m}=>\n'
                                                     ' Pr[SimRejectWorld(C,SimHRO.RO).distinguish(s0) @ '
                                                     '&m:event res]=\n'
                                                     ' Pr[SimNeverWorld(C,SimHRO.RO).distinguish(s0) @ '
                                                     '&m:event res].\n'
                                                     'proof. exact (sim_reject_never_probability C g &m s0 '
                                                     'event). qed.\n',
 'kem_fo_simulation/NTRUPlus768SimGErasure.ec': '\n'
                                                '\n'
                                                'lemma __fo_simulation_eof\n'
                                                ' (C<:SimGDecapContext '
                                                '{-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-CCADecapOracle,-SimGRO.RO,-SimGRO.FRO}) '
                                                '&m s0 (event:bool->bool) :\n'
                                                ' Pr[SimGGetWorld(C,FOGActual).distinguish(s0) @ &m:event '
                                                'res]=\n'
                                                ' Pr[SimGLookupWorld(C,FOGActual).distinguish(s0) @ &m:event '
                                                'res].\n'
                                                'proof. exact (sim_g_ghost_lookup_probability C &m s0 '
                                                'event). qed.\n',
 'kem_fo_simulation/NTRUPlus768SimKnown.ec': '\n'
                                             '\n'
                                             'lemma __fo_simulation_eof w ct0 g log0 hm0 ex hs cs n0 :\n'
                                             ' pke_key_relation w=>sim_log_included log0 hm0=>fo_hcache_good '
                                             'w g ex log0=>\n'
                                             ' NTRUPlus768FOChallenge.fo_challenge_invariant w g ex hs cs '
                                             'hm0=>\n'
                                             ' phoare[SimKnownDecap(FOGActual,SimHActual).decap:\n'
                                             ' ct=ct0 /\\ SimPublic.pk=w.`kg_pk /\\ '
                                             'SimPublic.suffix=complete_sk_suffix w.`kg_sk /\\\n'
                                             ' CCADecapOracle.sk=w.`kg_sk /\\ SimPublic.cstar=Some cs /\\ '
                                             'SimPublic.count=n0 /\\\n'
                                             ' SimHistory.h=log0 /\\ ROH.m=hm0 /\\ acwc2_cache_matches g '
                                             'ROG.m ==>\n'
                                             ' res=sim_lookup_spec w.`kg_pk (complete_sk_suffix w.`kg_sk) '
                                             '(Some cs) g log0 ct0 /\\\n'
                                             ' acwc2_cache_matches g ROG.m /\\ ROH.m=hm0 /\\ '
                                             'SimHistory.h=log0 /\\\n'
                                             ' SimPublic.pk=w.`kg_pk /\\ SimPublic.suffix=complete_sk_suffix '
                                             'w.`kg_sk /\\\n'
                                             ' SimPublic.cstar=Some cs /\\ SimPublic.count=n0+1 /\\ '
                                             'CCADecapOracle.sk=w.`kg_sk]=1%r.\n'
                                             'proof. exact (sim_known_decap_challenge_correct w ct0 g log0 '
                                             'hm0 ex hs cs n0). qed.\n',
 'kem_fo_simulation/NTRUPlus768SimPorts.ec': '\n'
                                             '\n'
                                             'lemma __fo_simulation_eof (A<:CCAExtendedAdversary) '
                                             '(B<:SimLeaks {-A})(U<:SimAnswer {-A}) :\n'
                                             ' islossless B.leaks=>islossless U.answer=>\n'
                                             ' (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort '
                                             '{-A}),\n'
                                             ' islossless H.e=>islossless H.f=>islossless H.g=>islossless '
                                             'H.h=>islossless H.raw=>\n'
                                             ' islossless D.decap=>islossless A(H,D).guess)=>\n'
                                             ' islossless SimAdaptive(A,B,U).distinguish.\n'
                                             'proof. exact (sim_adaptive_ll A B U). qed.\n',
 'kem_fo_simulation/NTRUPlus768SimPublicBound.ec': '\n'
                                                   '\n'
                                                   'lemma __fo_simulation_eof\n'
                                                   ' (A<:CCAExtendedAdversary '
                                                   '{-FOContext,-SimHistory,-ROH,-SimBad,-SimPublicBudget})\n'
                                                   ' (B<:FOBackend {-A,-SimPublicBudget}) w0 g0 ex0 q0 pk0 '
                                                   'ct0 key0 &m :\n'
                                                   ' 0<=q0 =>sim_public_inv w0 g0 ex0 '
                                                   '(FOContext.w{m},FOContext.g{m},FOContext.challenge_h{m},SimHistory.h{m},ROH.m{m}) '
                                                   '=>\n'
                                                   ' (forall b,hoare[B.e:sim_public_inv w0 g0 ex0 '
                                                   '(FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) '
                                                   '/\\ SimBad.corr=b ==> sim_public_inv w0 g0 ex0 '
                                                   '(FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) '
                                                   '/\\ SimBad.corr=b]) =>\n'
                                                   ' (forall b,hoare[B.f:sim_public_inv w0 g0 ex0 '
                                                   '(FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) '
                                                   '/\\ SimBad.corr=b ==> sim_public_inv w0 g0 ex0 '
                                                   '(FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) '
                                                   '/\\ SimBad.corr=b]) =>\n'
                                                   ' (forall b,hoare[B.g:sim_public_inv w0 g0 ex0 '
                                                   '(FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) '
                                                   '/\\ SimBad.corr=b ==> sim_public_inv w0 g0 ex0 '
                                                   '(FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) '
                                                   '/\\ SimBad.corr=b]) =>\n'
                                                   ' (forall b,hoare[B.h:sim_public_inv w0 g0 ex0 '
                                                   '(FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) '
                                                   '/\\ SimBad.corr=b ==> sim_public_inv w0 g0 ex0 '
                                                   '(FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) '
                                                   '/\\ (b=>SimBad.corr)]) =>\n'
                                                   ' (forall b,hoare[B.raw:sim_public_inv w0 g0 ex0 '
                                                   '(FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) '
                                                   '/\\ SimBad.corr=b ==> sim_public_inv w0 g0 ex0 '
                                                   '(FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) '
                                                   '/\\ (b=>SimBad.corr)]) =>\n'
                                                   ' (forall b,hoare[B.raw:sim_public_inv w0 g0 ex0 '
                                                   '(FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) '
                                                   '/\\ SimBad.corr=b /\\ !fo_raw_h input outlen ==> '
                                                   'sim_public_inv w0 g0 ex0 '
                                                   '(FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) '
                                                   '/\\ SimBad.corr=b]) =>\n'
                                                   ' (forall b,hoare[B.decap:sim_public_inv w0 g0 ex0 '
                                                   '(FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) '
                                                   '/\\ SimBad.corr=b ==> sim_public_inv w0 g0 ex0 '
                                                   '(FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) '
                                                   '/\\ SimBad.corr=b]) =>\n'
                                                   ' (phoare[B.h:sim_public_inv w0 g0 ex0 '
                                                   '(FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) '
                                                   '/\\ !SimBad.corr ==>SimBad.corr]<=(fo_error w0 g0)) =>\n'
                                                   ' (phoare[B.raw:sim_public_inv w0 g0 ex0 '
                                                   '(FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) '
                                                   '/\\ !SimBad.corr /\\ fo_raw_h input outlen '
                                                   '==>SimBad.corr]<=(fo_error w0 g0)) =>\n'
                                                   ' Pr[SimPublicBoundedPhase(A,B).run(q0,pk0,ct0,key0) @ '
                                                   '&m:SimBad.corr]<=q0%r*fo_error w0 g0.\n'
                                                   'proof. exact (sim_public_bounded_corr A B w0 g0 ex0 q0 '
                                                   'pk0 ct0 key0 &m). qed.\n',
 'kem_fo_simulation/NTRUPlus768SimChallengeAnswer.ec': '\n'
                                                       '\n'
                                                       'lemma __fo_simulation_eof w g q0 gm0 hm0 ex hs cs :\n'
                                                       ' pke_key_relation w=>acwc2_cache_matches g '
                                                       'gm0=>fo_challenge_invariant w g ex hs cs hm0=>\n'
                                                       ' q0.`sr_pk=w.`kg_pk=>q0.`sr_ct<>cs=>Some(sim_h_input '
                                                       'q0)=ex=>\n'
                                                       ' phoare[SimAnswerReal(FOGActual,SimHActual).answer:\n'
                                                       ' q=q0 /\\ ROG.m=gm0 /\\ ROH.m=hm0 ==>res=None /\\ '
                                                       'ROG.m=gm0 /\\ ROH.m=hm0]=1%r.\n'
                                                       'proof. exact (sim_answer_challenge_correct w g q0 '
                                                       'gm0 hm0 ex hs cs). qed.\n',
 'kem_fo_simulation/NTRUPlus768SimGames.ec': '\n'
                                             '\n'
                                             'lemma __fo_simulation_eof : islossless SimObservedSetup.run.\n'
                                             'proof. exact sim_observed_setup_ll. qed.\n',
 'kem_fo_simulation/NTRUPlus768SimPortContracts.ec': '\n'
                                                     '\n'
                                                     'lemma __fo_simulation_eof pk0 log0 ex0 : '
                                                     'hoare[SimLeaksBackend(FOGActual,SimHActual).leaks:\n'
                                                     ' SimPublic.pk=pk0 /\\ SimHistory.h=log0 /\\ '
                                                     'FOContext.challenge_h=ex0 /\\ sim_h_cover log0 ROH.m '
                                                     'ex0 ==>\n'
                                                     ' (sim_out_decap res).`1<>None=>let '
                                                     'q=oget(sim_out_decap res).`1 in\n'
                                                     ' q.`sr_pk=pk0 /\\ sim_h_input q \\notin ROH.m].\n'
                                                     'proof. exact (sim_leaks_fresh pk0 log0 ex0). qed.\n',
 'kem_fo_simulation/NTRUPlus768SimPublicCapRemoval.ec': '\n'
                                                        '\n'
                                                        'lemma __fo_simulation_eof\n'
                                                        ' (A<:CCAExtendedAdversary {-SimPublicBudget}) '
                                                        '(B<:FOBackend {-A,-SimPublicBudget}) q0 :\n'
                                                        ' 0<=q0 =>\n'
                                                        ' islossless B.e=>islossless B.f=>islossless '
                                                        'B.g=>islossless B.h=>islossless B.raw=>islossless '
                                                        'B.decap=>\n'
                                                        ' (forall (H<:CCAExtendedOraclePort {-A}) '
                                                        '(D<:CCADecapPort {-A}),\n'
                                                        '  islossless H.e=>islossless H.f=>islossless '
                                                        'H.g=>islossless H.h=>islossless H.raw=>\n'
                                                        '  islossless D.decap=>islossless A(H,D).guess) =>\n'
                                                        ' '
                                                        'hoare[SimPublicCountedA(A,FOHashView(B),FODecapView(B)).guess:\n'
                                                        ' sim_public_budget_initial q0 SimPublicBudget.nh '
                                                        'SimPublicBudget.limit SimPublicBudget.overflow ==>\n'
                                                        ' SimPublicBudget.nh<=q0] =>\n'
                                                        ' '
                                                        'equiv[SimPublicConfiguredA(A,FOHashView(B),FODecapView(B)).guess '
                                                        '~ A(FOHashView(B),FODecapView(B)).guess:\n'
                                                        ' ={arg,glob A,glob B} /\\ '
                                                        'SimPublicBudget.limit{1}=q0 ==> ={res,glob A,glob '
                                                        'B}].\n'
                                                        'proof. exact (sim_public_configured_phase_plain A B '
                                                        'q0). qed.\n',
 'kem_fo_simulation/NTRUPlus768SimPublicGames.ec': '\n'
                                                   '\n'
                                                   'lemma __fo_simulation_eof\n'
                                                   ' (A<:CCAExtendedAdversary '
                                                   '{-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-SimPublic,-SimHistory,-FOGRO.RO,-FOGRO.FRO}) '
                                                   '&m :\n'
                                                   ' Pr[SimPublicFreshGame(A).run() @ &m:res]=\n'
                                                   ' mu1(dlet(mk(fun s=>Pr[FOSetupSource.guess(witness) @ '
                                                   '&m:res=s]))\n'
                                                   '   (fun s=>mk(fun b=>Pr[SimPublicKernel(A).guess(s) @ '
                                                   '&m:res=b])))true.\n'
                                                   'proof. exact (sim_public_fresh_mu A &m). qed.\n',
 'kem_fo_simulation/NTRUPlus768SimPublicInstances.ec': '\n'
                                                       '\n'
                                                       'lemma __fo_simulation_eof\n'
                                                       ' (A<:CCAExtendedAdversary '
                                                       '{-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,\n'
                                                       '  '
                                                       '-FOContext,-SimPublic,-SimHistory,-SimBad,-SimPublicBudget}) '
                                                       'w0 g0 ex0 q0 pk0 ct0 key0 &m :\n'
                                                       ' 0<=q0 =>sim_public_inv w0 g0 ex0\n'
                                                       ' '
                                                       '(FOContext.w{m},FOContext.g{m},FOContext.challenge_h{m},SimHistory.h{m},ROH.m{m})=>\n'
                                                       ' !SimBad.corr{m} =>\n'
                                                       ' (forall (H<:CCAExtendedOraclePort '
                                                       '{-A})(D<:CCADecapPort {-A}),\n'
                                                       '  islossless H.e=>islossless H.f=>islossless '
                                                       'H.g=>islossless H.h=>islossless H.raw=>\n'
                                                       '  islossless D.decap=>islossless A(H,D).guess) =>\n'
                                                       ' '
                                                       'hoare[SimPublicCountedA(A,FOHashView(SimKnownPublicBackend),FODecapView(SimKnownPublicBackend)).guess:\n'
                                                       ' sim_public_budget_initial q0 SimPublicBudget.nh '
                                                       'SimPublicBudget.limit SimPublicBudget.overflow ==>\n'
                                                       ' SimPublicBudget.nh<=q0] =>\n'
                                                       ' '
                                                       'Pr[A(FOHashView(SimKnownPublicBackend),FODecapView(SimKnownPublicBackend)).guess(pk0,ct0,key0) '
                                                       '@ &m:SimBad.corr]\n'
                                                       ' <=q0%r*fo_error w0 g0.\n'
                                                       'proof. exact (sim_public_known_uncapped_corr A w0 g0 '
                                                       'ex0 q0 pk0 ct0 key0 &m). qed.\n',
 'kem_fo_simulation/NTRUPlus768SimRealBridge.ec': '\n'
                                                  '\n'
                                                  'lemma __fo_simulation_eof :\n'
                                                  ' equiv[SimRealDecap(FOGActual,SimHActual).decap ~ '
                                                  'FOReencryptDecap(SHAKEGROM,SHAKEHROM).decap:\n'
                                                  ' ={ct,ROG.m,ROH.m,CCADecapOracle.sk} /\\ '
                                                  'SimPublic.pk{1}=FOPublicKey.pk{2} /\\\n'
                                                  ' SimPublic.cstar{1}=CCADecapOracle.cstar{2} ==>\n'
                                                  ' ={res,ROG.m,ROH.m,CCADecapOracle.sk}].\n'
                                                  'proof. exact sim_real_decap_original. qed.\n',
 'kem_fo_simulation/NTRUPlus768SimSelected.ec': '\n'
                                                '\n'
                                                'lemma __fo_simulation_eof\n'
                                                ' (C<:SimAnswerContext '
                                                '{-ROG,-ROH,-SimSelectedFixed,-SimBad}) w0 g0 s0 &m :\n'
                                                ' pke_key_relation w0=>acwc2_cache_matches g0 ROG.m{m}=>\n'
                                                ' Pr[SimGuardedExperiment(C).run(w0,g0,s0) @ '
                                                '&m:SimBad.hidden /\\ SimBad.selected_calls<=1]\n'
                                                ' <=(1%r/(2%r^768)+fo_error w0 g0).\n'
                                                'proof. exact (sim_guarded_context_bad C w0 g0 s0 &m). '
                                                'qed.\n',
 'kem_fo_simulation/NTRUPlus768SimSetupBridge.ec': '\n'
                                                   '\n'
                                                   'lemma __fo_simulation_eof s0 : fo_setup_valid s0=>\n'
                                                   ' phoare[SimObservedSetup.run:s=s0 ==>\n'
                                                   ' FOContext.w=s0.`1.`1 /\\ FOContext.g=acwc2_gfun s0.`3 '
                                                   '/\\\n'
                                                   ' pke_key_relation FOContext.w /\\ '
                                                   'SimPublic.pk=FOContext.w.`kg_pk /\\\n'
                                                   ' SimPublic.suffix=complete_sk_suffix FOContext.w.`kg_sk '
                                                   '/\\\n'
                                                   ' SimPublic.cstar=Some FOContext.challenge_ct /\\ '
                                                   'SimPublic.count=0 /\\\n'
                                                   ' CCADecapOracle.sk=FOContext.w.`kg_sk /\\\n'
                                                   ' SimPhaseInput.pk=SimPublic.pk /\\ '
                                                   'SimPhaseInput.ct=FOContext.challenge_ct /\\\n'
                                                   ' SimHistory.h=empty /\\ !SimBad.hidden /\\ !SimBad.corr '
                                                   '/\\ SimBad.selected_calls=0 /\\\n'
                                                   ' acwc2_cache_matches FOContext.g ROG.m /\\ '
                                                   'sim_log_included SimHistory.h ROH.m /\\\n'
                                                   ' sim_h_cover SimHistory.h ROH.m FOContext.challenge_h '
                                                   '/\\\n'
                                                   ' fo_challenge_invariant FOContext.w FOContext.g '
                                                   'FOContext.challenge_h FOContext.challenge_hash '
                                                   'FOContext.challenge_ct ROH.m]=1%r.\n'
                                                   'proof. exact (sim_observed_setup_correct s0). qed.\n',
 'kem_fo_simulation/NTRUPlus768SimKnownCoupling.ec': '\n'
                                                     '\n'
                                                     'lemma __fo_simulation_eof\n'
                                                     ' (A<:CCAExtendedAdversary '
                                                     '{-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOContext,-SimPublic,-SimHistory,-SimBad,-SimPublicBudget,-SimGRO.RO,-SimGRO.FRO,-SimPhaseInput}) '
                                                     'w g ex hs cs qH &m s0 :\n'
                                                     ' pke_key_relation w=>(SimPublic.pk{m}=w.`kg_pk /\\ '
                                                     'SimPublic.suffix{m}=complete_sk_suffix w.`kg_sk /\\\n'
                                                     ' CCADecapOracle.sk{m}=w.`kg_sk /\\ '
                                                     'SimPublic.cstar{m}=Some cs /\\\n'
                                                     ' FOContext.w{m}=w /\\ FOContext.g{m}=g /\\ '
                                                     'FOContext.challenge_h{m}=ex /\\\n'
                                                     ' sim_known_invariant w g ex hs cs ROG.m{m} ROH.m{m} '
                                                     'SimHistory.h{m} SimBad.corr{m} /\\ '
                                                     '!SimBad.corr{m})=>0<=qH=>(forall '
                                                     '(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort '
                                                     '{-A}),\n'
                                                     ' islossless H.e=>islossless H.f=>islossless '
                                                     'H.g=>islossless H.h=>islossless H.raw=>\n'
                                                     ' islossless D.decap=>islossless A(H,D).guess)=>\n'
                                                     ' '
                                                     'hoare[SimPublicCountedA(A,FOHashView(SimKnownPublicBackend),FODecapView(SimKnownPublicBackend)).guess:\n'
                                                     ' sim_public_budget_initial qH SimPublicBudget.nh '
                                                     'SimPublicBudget.limit SimPublicBudget.overflow ==>\n'
                                                     ' SimPublicBudget.nh<=qH]=>\n'
                                                     ' '
                                                     '`|Pr[SimDirectPhase(A,SimOracles(FOGActual,SimHActual),SimKnownDecap(FOGActual,SimHActual)).distinguish(s0) '
                                                     '@ &m:res]-\n'
                                                     '   '
                                                     'Pr[SimDirectPhase(A,SimOracles(FOGActual,SimHActual),SimLookup(FOGActual)).distinguish(s0) '
                                                     '@ &m:res]|<=qH%r*fo_error w g.\n'
                                                     'proof. exact (sim_known_lookup_phase_bound A w g ex hs '
                                                     'cs qH &m s0). qed.\n',
 'kem_fo_simulation/NTRUPlus768SimLookupGameBridge.ec': '\n'
                                                        '\n'
                                                        'lemma __fo_simulation_eof\n'
                                                        ' (A<:CCAExtendedAdversary '
                                                        '{-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOContext,-SimPublic,-SimHistory,-SimBad,-SimPhaseInput})\n'
                                                        ' s0 &m (event:bool->bool) : fo_setup_valid s0=>\n'
                                                        ' Pr[SimObservedLookupKernel(A).guess(s0) @ &m:event '
                                                        'res]=\n'
                                                        ' Pr[SimPublicKernel(A).guess(s0) @ &m:event res].\n'
                                                        'proof. exact '
                                                        '(sim_lookup_observed_public_probability A s0 &m '
                                                        'event). qed.\n',
 'kem_fo_simulation/NTRUPlus768SimPhaseState.ec': '\n'
                                                  '\n'
                                                  'lemma __fo_simulation_eof (P<:SimBoolPhase) s0 event &m : '
                                                  'fo_setup_valid s0=>\n'
                                                  ' Pr[SimSetupPhase(P).guess(s0) @ &m:event res]=\n'
                                                  ' Pr[SimReadyKernel(P).guess(s0) @ &m:event res].\n'
                                                  'proof. exact (sim_ready_kernel_probability P s0 event '
                                                  '&m). qed.\n',
 'kem_fo_simulation/NTRUPlus768SimRealGameBridge.ec': '\n'
                                                      '\n'
                                                      'lemma __fo_simulation_eof\n'
                                                      ' (A<:CCAExtendedAdversary '
                                                      '{-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOContext,-SimPublic,-SimHistory,-SimBad,-SimPhaseInput}) '
                                                      '&m s0 (event:bool->bool) :\n'
                                                      ' Pr[SimObservedRealKernel(A).guess(s0) @ &m:event '
                                                      'res]=\n'
                                                      ' '
                                                      'Pr[FOPlainKernel(A,FOReencryptDecap(SHAKEGROM,SHAKEHROM)).guess(s0) '
                                                      '@ &m:event res].\n'
                                                      'proof. exact (sim_observed_real_plain_probability A '
                                                      '&m s0 event). qed.\n',
 'kem_fo_simulation/NTRUPlus768SimSelectedCoupling.ec': '\n'
                                                        '\n'
                                                        'lemma __fo_simulation_eof\n'
                                                        ' (C<:SimAnswerContext '
                                                        '{-ROG,-ROH,-SimGRO.RO,-SimGRO.FRO,-SimHRO.RO,-SimHRO.FRO,-SimBad})\n'
                                                        ' g &m s0 : acwc2_cache_matches g ROG.m{m}=>\n'
                                                        ' (forall(G<:FOGPort {-C})(H<:SimHPort '
                                                        '{-C})(D<:SimAnswer {-C}),\n'
                                                        ' islossless G.get=>islossless H.get=>islossless '
                                                        'D.answer=>islossless C(G,H,D).distinguish)=>\n'
                                                        ' `|Pr[SimRealContext(C).run(s0) @ '
                                                        '&m:res]-Pr[SimNeverContext(C).run(s0) @ &m:res]|\n'
                                                        ' <=Pr[SimRejectContext(C).run(s0) @ '
                                                        '&m:SimBad.hidden].\n'
                                                        'proof. exact (sim_context_real_never_distance C g '
                                                        '&m s0). qed.\n',
 'kem_fo_simulation/NTRUPlus768SimSelectedInvariant.ec': '\n'
                                                         '\n'
                                                         'lemma __fo_simulation_eof\n'
                                                         ' (A<:CCAExtendedAdversary '
                                                         '{-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,\n'
                                                         '  '
                                                         '-SimPublic,-SimHistory,-FOContext,-SimBad,-SimSelectedFixed,-SimPhaseInput,-FOBudgetState,\n'
                                                         '  -SH.HB.Count,-SH.HB.HybOrcl}) w0 g0 :\n'
                                                         ' equiv[SimSelectedReject(A).distinguish ~ '
                                                         'SimSelectedGuarded(A).run:\n'
                                                         ' w{2}=w0 /\\ g{2}=g0 /\\ ={s,glob A,glob ROE,glob '
                                                         'ROF,glob ROG,glob ROH,glob RawXOFStreams,glob '
                                                         'SimPublic,glob SimHistory,glob FOContext,glob '
                                                         'CCADecapOracle,glob SimBad,glob SH.HB.HybOrcl,glob '
                                                         'FOBudgetState,glob SimPhaseInput} /\\\n'
                                                         ' SimPublic.pk{1}=w0.`kg_pk /\\ acwc2_cache_matches '
                                                         'g0 ROG.m{1} /\\\n'
                                                         ' sim_log_included SimHistory.h{1} ROH.m{1} /\\ '
                                                         'sim_h_cover SimHistory.h{1} ROH.m{1} '
                                                         'FOContext.challenge_h{1} ==>\n'
                                                         ' ={res,glob A,glob ROE,glob ROF,glob ROG,glob '
                                                         'ROH,glob RawXOFStreams,glob SimPublic,glob '
                                                         'SimHistory,glob FOContext,glob CCADecapOracle,glob '
                                                         'SimBad,glob SH.HB.HybOrcl,glob FOBudgetState,glob '
                                                         'SimPhaseInput}].\n'
                                                         'proof. exact (sim_selected_reject_guarded A w0 '
                                                         'g0). qed.\n',
 'kem_fo_simulation/NTRUPlus768SimKnownBridge.ec': '\n'
                                                   '\n'
                                                   'lemma __fo_simulation_eof\n'
                                                   ' (A<:CCAExtendedAdversary '
                                                   '{-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOContext,-SimPublic,-SimHistory,-SimBad,-SimPhaseInput})\n'
                                                   ' s0 event &m : fo_setup_valid s0=>\n'
                                                   ' Pr[SimObservedKnownKernel(A).guess(s0) @ &m:event '
                                                   'res]=\n'
                                                   ' Pr[SimObservedDirectKnownKernel(A).guess(s0) @ &m:event '
                                                   'res].\n'
                                                   'proof. exact (sim_observed_known_direct_probability A s0 '
                                                   'event &m). qed.\n',
 'kem_fo_simulation/NTRUPlus768SimSelectedBound.ec': '\n'
                                                     '\n'
                                                     'lemma __fo_simulation_eof (A<:CCAExtendedAdversary '
                                                     '{-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,\n'
                                                     '  '
                                                     '-FOPublicKey,-FOContext,-FOBadState,-FOBudgetState,-SimPublic,-SimHistory,-SimBad,\n'
                                                     '  '
                                                     '-SimSelectedFixed,-SimPhaseInput,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,\n'
                                                     '  -SH.HB.Count,-SH.HB.HybOrcl}) w g s0 &m :\n'
                                                     ' pke_key_relation w=>SimPublic.pk{m}=w.`kg_pk=>\n'
                                                     ' acwc2_cache_matches g ROG.m{m}=>\n'
                                                     ' sim_log_included SimHistory.h{m} ROH.m{m}=>\n'
                                                     ' sim_h_cover SimHistory.h{m} ROH.m{m} '
                                                     'FOContext.challenge_h{m}=>\n'
                                                     ' (forall(H<:CCAExtendedOraclePort '
                                                     '{-A})(D<:CCADecapPort {-A}),\n'
                                                     '  islossless H.e=>islossless H.f=>islossless '
                                                     'H.g=>islossless H.h=>islossless H.raw=>\n'
                                                     '  islossless D.decap=>islossless A(H,D).guess)=>\n'
                                                     ' (forall(H<:CCAExtendedOraclePort '
                                                     '{-A,-FOBudgetState})(D<:CCADecapPort '
                                                     '{-A,-FOBudgetState}),\n'
                                                     '  hoare[FOCountedA(A,H,D).guess:FOBudgetState.nD=0 '
                                                     '==>\n'
                                                     '   FOBudgetState.nD<=max 0 budget])=>\n'
                                                     ' '
                                                     '`|Pr[SimAdaptive(A,SimLeaksBackend(FOGActual,SimHActual),SimAnswerReal(FOGActual,SimHActual)).distinguish(s0) '
                                                     '@ &m:res]-\n'
                                                     '   '
                                                     'Pr[SimAdaptive(A,SimLeaksBackend(FOGActual,SimHActual),SimAnswerNever).distinguish(s0) '
                                                     '@ &m:res]|\n'
                                                     ' <=(max 0 budget)%r*(1%r/(2%r^768)+fo_error w g).\n'
                                                     'proof. exact (sim_real_known_phase_distance A w g s0 '
                                                     '&m). qed.\n',
 'kem_fo_simulation/NTRUPlus768SimPhaseBound.ec': '\n'
                                                  '\n'
                                                  'lemma __fo_simulation_eof\n'
                                                  ' (A<:CCAExtendedAdversary '
                                                  '{-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,\n'
                                                  '  '
                                                  '-FOContext,-FOBadState,-FOBudgetState,-FOGRO.RO,-FOGRO.FRO,-SimPublic,-SimHistory,-SimBad,\n'
                                                  '  '
                                                  '-SimPhaseInput,-SimSelectedFixed,-SimPublicBudget,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,\n'
                                                  '  -SH.HB.Count,-SH.HB.HybOrcl}) w g ex hs cs qH s0 &m :\n'
                                                  ' pke_key_relation w=>\n'
                                                  ' (SimPublic.pk{m}=w.`kg_pk /\\ '
                                                  'SimPublic.suffix{m}=complete_sk_suffix w.`kg_sk /\\\n'
                                                  ' CCADecapOracle.sk{m}=w.`kg_sk /\\ '
                                                  'SimPublic.cstar{m}=Some cs /\\\n'
                                                  ' FOContext.w{m}=w /\\ FOContext.g{m}=g /\\ '
                                                  'FOContext.challenge_h{m}=ex /\\\n'
                                                  ' sim_known_invariant w g ex hs cs ROG.m{m} ROH.m{m} '
                                                  'SimHistory.h{m} SimBad.corr{m} /\\ !SimBad.corr{m})=>\n'
                                                  ' 0<=qH=>\n'
                                                  ' (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort '
                                                  '{-A}),\n'
                                                  '  islossless H.e=>islossless H.f=>islossless '
                                                  'H.g=>islossless H.h=>islossless H.raw=>\n'
                                                  '  islossless D.decap=>islossless A(H,D).guess)=>\n'
                                                  ' (forall(H<:CCAExtendedOraclePort '
                                                  '{-A,-FOBudgetState})(D<:CCADecapPort '
                                                  '{-A,-FOBudgetState}),\n'
                                                  '  hoare[FOCountedA(A,H,D).guess:FOBudgetState.nD=0 '
                                                  '==>FOBudgetState.nD<=max 0 budget])=>\n'
                                                  ' '
                                                  'hoare[SimPublicCountedA(A,FOHashView(SimKnownPublicBackend),FODecapView(SimKnownPublicBackend)).guess:\n'
                                                  '  sim_public_budget_initial qH SimPublicBudget.nh '
                                                  'SimPublicBudget.limit SimPublicBudget.overflow ==>\n'
                                                  '  SimPublicBudget.nh<=qH]=>\n'
                                                  ' '
                                                  '`|Pr[SimAdaptive(A,SimLeaksBackend(FOGActual,SimHActual),SimAnswerReal(FOGActual,SimHActual)).distinguish(s0) '
                                                  '@ &m:res]-\n'
                                                  '   '
                                                  'Pr[SimDirectPhase(A,SimOracles(FOGActual,SimHActual),SimLookup(FOGActual)).distinguish(s0) '
                                                  '@ &m:res]|\n'
                                                  ' <=(max 0 budget)%r/(2%r^768)+(qH+max 0 '
                                                  'budget)%r*fo_error w g.\n'
                                                  'proof. exact (sim_real_lookup_phase_distance A w g ex hs '
                                                  'cs qH s0 &m). qed.\n',
 'kem_fo_simulation/NTRUPlus768SimKernelBound.ec': '\n'
                                                   '\n'
                                                   'lemma __fo_simulation_eof (A<:CCAExtendedAdversary '
                                                   '{-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,\n'
                                                   '  '
                                                   '-FOContext,-FOBadState,-FOBudgetState,-FOGRO.RO,-FOGRO.FRO,-SimPublic,-SimHistory,-SimBad,\n'
                                                   '  '
                                                   '-SimPhaseInput,-SimSelectedFixed,-SimPublicBudget,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,\n'
                                                   '  -SH.HB.Count,-SH.HB.HybOrcl}) s0 qH &m :\n'
                                                   ' fo_setup_valid '
                                                   's0=>0<=qH=>(forall(H<:CCAExtendedOraclePort '
                                                   '{-A})(D<:CCADecapPort {-A}),\n'
                                                   ' islossless H.e=>islossless H.f=>islossless '
                                                   'H.g=>islossless H.h=>islossless H.raw=>\n'
                                                   ' islossless D.decap=>islossless '
                                                   'A(H,D).guess)=>(forall(H<:CCAExtendedOraclePort '
                                                   '{-A,-FOBudgetState})(D<:CCADecapPort '
                                                   '{-A,-FOBudgetState}),\n'
                                                   ' hoare[FOCountedA(A,H,D).guess:FOBudgetState.nD=0 '
                                                   '==>FOBudgetState.nD<=max 0 budget])=>\n'
                                                   ' '
                                                   'hoare[SimPublicCountedA(A,FOHashView(SimKnownPublicBackend),FODecapView(SimKnownPublicBackend)).guess:\n'
                                                   ' sim_public_budget_initial qH SimPublicBudget.nh '
                                                   'SimPublicBudget.limit SimPublicBudget.overflow ==>\n'
                                                   ' SimPublicBudget.nh<=qH]=>\n'
                                                   ' '
                                                   '`|Pr[FOPlainKernel(A,FOReencryptDecap(SHAKEGROM,SHAKEHROM)).guess(s0) '
                                                   '@ &m:res]-\n'
                                                   '   Pr[SimPublicKernel(A).guess(s0) @ &m:res]|\n'
                                                   ' <=(max 0 budget)%r/(2%r^768)+(qH+max 0 '
                                                   'budget)%r*fo_setup_error s0.\n'
                                                   'proof. exact (sim_plain_public_kernel_distance A s0 qH '
                                                   '&m). qed.\n',
 'kem_fo_simulation/NTRUPlus768SimFinal.ec': '\n'
                                             '\n'
                                             'lemma __fo_simulation_eof\n'
                                             ' (A<:CCAExtendedAdversary '
                                             '{-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,\n'
                                             '  '
                                             '-FOContext,-FOBadState,-FOBudgetState,-FOGRO.RO,-FOGRO.FRO,-SimPublic,-SimHistory,-SimBad,\n'
                                             '  '
                                             '-SimPhaseInput,-SimSelectedFixed,-SimPublicBudget,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,\n'
                                             '  -SH.HB.Count,-SH.HB.HybOrcl}) qH &m :\n'
                                             ' 0<=qH=>\n'
                                             ' (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort '
                                             '{-A}),\n'
                                             '  islossless H.e=>islossless H.f=>islossless H.g=>islossless '
                                             'H.h=>islossless H.raw=>\n'
                                             '  islossless D.decap=>islossless A(H,D).guess)=>\n'
                                             ' (forall(H<:CCAExtendedOraclePort '
                                             '{-A,-FOBudgetState})(D<:CCADecapPort {-A,-FOBudgetState}),\n'
                                             '  hoare[FOCountedA(A,H,D).guess:FOBudgetState.nD=0 '
                                             '==>FOBudgetState.nD<=max 0 budget])=>\n'
                                             ' '
                                             'hoare[SimPublicCountedA(A,FOHashView(SimKnownPublicBackend),FODecapView(SimKnownPublicBackend)).guess:\n'
                                             '  sim_public_budget_initial qH SimPublicBudget.nh '
                                             'SimPublicBudget.limit SimPublicBudget.overflow ==>\n'
                                             '  SimPublicBudget.nh<=qH]=>\n'
                                             ' `|Pr[FOFreshReencryptGame(A).run() @ '
                                             '&m:res]-Pr[SimPublicFreshGame(A).run() @ &m:res]|\n'
                                             ' <=(max 0 budget)%r/(2%r^768)+(qH+max 0 budget)%r/(2%r^353).\n'
                                             'proof. exact (sim_fo_public_distance A qH &m). qed.\n'}

SEMANTIC_TARGETS = {'kem_fo_simulation/NTRUPlus768SimAverage.ec': 'sim_setup_win_distance',
 'kem_fo_simulation/NTRUPlus768SimCandidate.ec': 'sim_table_matches_unique',
 'kem_fo_simulation/NTRUPlus768SimFreshHash.ec': 'sim_native_fresh_hash_bound',
 'kem_fo_simulation/NTRUPlus768SimModel.ec': 'sim_public_init_ll',
 'kem_fo_simulation/NTRUPlus768SimSequentialDistance.ec': 'sim_sequential_unconditional',
 'kem_fo_simulation/NTRUPlus768SimHybrid.ec': 'sim_hybrid_distance',
 'kem_fo_simulation/NTRUPlus768SimLookup.ec': 'sim_lookup_correct',
 'kem_fo_simulation/NTRUPlus768SimSampling.ec': 'sim_g_sampling_probability',
 'kem_fo_simulation/NTRUPlus768SimAnswer.ec': 'sim_answer_real_ll',
 'kem_fo_simulation/NTRUPlus768SimKnownAlgebra.ec': 'sim_known_lookup_challenge',
 'kem_fo_simulation/NTRUPlus768SimOracles.ec': 'sim_raw_actual_invariant',
 'kem_fo_simulation/NTRUPlus768SimPrefix.ec': 'sim_decaps_actual',
 'kem_fo_simulation/NTRUPlus768SimPublicError.ec': 'sim_public_raw_invariants',
 'kem_fo_simulation/NTRUPlus768SimSpreadHash.ec': 'sim_answer_actual_fresh_bound',
 'kem_fo_simulation/NTRUPlus768SimAnswerErasure.ec': 'sim_reject_never_probability',
 'kem_fo_simulation/NTRUPlus768SimGErasure.ec': 'sim_g_ghost_lookup_probability',
 'kem_fo_simulation/NTRUPlus768SimKnown.ec': 'sim_known_decap_challenge_correct',
 'kem_fo_simulation/NTRUPlus768SimPorts.ec': 'sim_adaptive_ll',
 'kem_fo_simulation/NTRUPlus768SimPublicBound.ec': 'sim_public_bounded_corr',
 'kem_fo_simulation/NTRUPlus768SimChallengeAnswer.ec': 'sim_answer_challenge_correct',
 'kem_fo_simulation/NTRUPlus768SimGames.ec': 'sim_observed_setup_ll',
 'kem_fo_simulation/NTRUPlus768SimPortContracts.ec': 'sim_leaks_fresh',
 'kem_fo_simulation/NTRUPlus768SimPublicCapRemoval.ec': 'sim_public_configured_phase_plain',
 'kem_fo_simulation/NTRUPlus768SimPublicGames.ec': 'sim_public_fresh_mu',
 'kem_fo_simulation/NTRUPlus768SimPublicInstances.ec': 'sim_public_known_uncapped_corr',
 'kem_fo_simulation/NTRUPlus768SimRealBridge.ec': 'sim_real_decap_original',
 'kem_fo_simulation/NTRUPlus768SimSelected.ec': 'sim_guarded_context_bad',
 'kem_fo_simulation/NTRUPlus768SimSetupBridge.ec': 'sim_observed_setup_correct',
 'kem_fo_simulation/NTRUPlus768SimKnownCoupling.ec': 'sim_known_lookup_phase_bound',
 'kem_fo_simulation/NTRUPlus768SimLookupGameBridge.ec': 'sim_lookup_observed_public_probability',
 'kem_fo_simulation/NTRUPlus768SimPhaseState.ec': 'sim_ready_kernel_probability',
 'kem_fo_simulation/NTRUPlus768SimRealGameBridge.ec': 'sim_observed_real_plain_probability',
 'kem_fo_simulation/NTRUPlus768SimSelectedCoupling.ec': 'sim_context_real_never_distance',
 'kem_fo_simulation/NTRUPlus768SimSelectedInvariant.ec': 'sim_selected_reject_guarded',
 'kem_fo_simulation/NTRUPlus768SimKnownBridge.ec': 'sim_observed_known_direct_probability',
 'kem_fo_simulation/NTRUPlus768SimSelectedBound.ec': 'sim_real_known_phase_distance',
 'kem_fo_simulation/NTRUPlus768SimPhaseBound.ec': 'sim_real_lookup_phase_distance',
 'kem_fo_simulation/NTRUPlus768SimKernelBound.ec': 'sim_plain_public_kernel_distance',
 'kem_fo_simulation/NTRUPlus768SimFinal.ec': 'sim_fo_public_distance'}

MODULE_BINDERS = {'kem_fo_simulation/NTRUPlus768SimAverage.ec': (),
 'kem_fo_simulation/NTRUPlus768SimCandidate.ec': (),
 'kem_fo_simulation/NTRUPlus768SimFreshHash.ec': (),
 'kem_fo_simulation/NTRUPlus768SimModel.ec': (),
 'kem_fo_simulation/NTRUPlus768SimSequentialDistance.ec': ('S',),
 'kem_fo_simulation/NTRUPlus768SimHybrid.ec': ('B', 'A', 'O', 'B0'),
 'kem_fo_simulation/NTRUPlus768SimLookup.ec': (),
 'kem_fo_simulation/NTRUPlus768SimSampling.ec': ('C',),
 'kem_fo_simulation/NTRUPlus768SimAnswer.ec': ('G', 'H'),
 'kem_fo_simulation/NTRUPlus768SimKnownAlgebra.ec': (),
 'kem_fo_simulation/NTRUPlus768SimOracles.ec': (),
 'kem_fo_simulation/NTRUPlus768SimPrefix.ec': ('G', 'H'),
 'kem_fo_simulation/NTRUPlus768SimPublicError.ec': (),
 'kem_fo_simulation/NTRUPlus768SimSpreadHash.ec': (),
 'kem_fo_simulation/NTRUPlus768SimAnswerErasure.ec': ('C',),
 'kem_fo_simulation/NTRUPlus768SimGErasure.ec': ('C',),
 'kem_fo_simulation/NTRUPlus768SimKnown.ec': (),
 'kem_fo_simulation/NTRUPlus768SimPorts.ec': ('A', 'B', 'U', 'H', 'D'),
 'kem_fo_simulation/NTRUPlus768SimPublicBound.ec': ('A', 'B'),
 'kem_fo_simulation/NTRUPlus768SimChallengeAnswer.ec': (),
 'kem_fo_simulation/NTRUPlus768SimGames.ec': (),
 'kem_fo_simulation/NTRUPlus768SimPortContracts.ec': (),
 'kem_fo_simulation/NTRUPlus768SimPublicCapRemoval.ec': ('A', 'B', 'H', 'D'),
 'kem_fo_simulation/NTRUPlus768SimPublicGames.ec': ('A',),
 'kem_fo_simulation/NTRUPlus768SimPublicInstances.ec': ('A', 'H', 'D'),
 'kem_fo_simulation/NTRUPlus768SimRealBridge.ec': (),
 'kem_fo_simulation/NTRUPlus768SimSelected.ec': ('C',),
 'kem_fo_simulation/NTRUPlus768SimSetupBridge.ec': (),
 'kem_fo_simulation/NTRUPlus768SimKnownCoupling.ec': ('A', 'H', 'D'),
 'kem_fo_simulation/NTRUPlus768SimLookupGameBridge.ec': ('A',),
 'kem_fo_simulation/NTRUPlus768SimPhaseState.ec': ('P',),
 'kem_fo_simulation/NTRUPlus768SimRealGameBridge.ec': ('A',),
 'kem_fo_simulation/NTRUPlus768SimSelectedCoupling.ec': ('C', 'G', 'H', 'D'),
 'kem_fo_simulation/NTRUPlus768SimSelectedInvariant.ec': ('A',),
 'kem_fo_simulation/NTRUPlus768SimKnownBridge.ec': ('A',),
 'kem_fo_simulation/NTRUPlus768SimSelectedBound.ec': ('A', 'H', 'D'),
 'kem_fo_simulation/NTRUPlus768SimPhaseBound.ec': ('A', 'H', 'D'),
 'kem_fo_simulation/NTRUPlus768SimKernelBound.ec': ('A', 'H', 'D'),
 'kem_fo_simulation/NTRUPlus768SimFinal.ec': ('A', 'H', 'D')}

NEGATIVE_PROOFS = ('kem_fo_simulation/NTRUPlus768SimAverage.ec',
 'kem_fo_simulation/NTRUPlus768SimCandidate.ec',
 'kem_fo_simulation/NTRUPlus768SimFreshHash.ec',
 'kem_fo_simulation/NTRUPlus768SimModel.ec',
 'kem_fo_simulation/NTRUPlus768SimSequentialDistance.ec',
 'kem_fo_simulation/NTRUPlus768SimHybrid.ec',
 'kem_fo_simulation/NTRUPlus768SimLookup.ec',
 'kem_fo_simulation/NTRUPlus768SimSampling.ec',
 'kem_fo_simulation/NTRUPlus768SimAnswer.ec',
 'kem_fo_simulation/NTRUPlus768SimKnownAlgebra.ec',
 'kem_fo_simulation/NTRUPlus768SimOracles.ec',
 'kem_fo_simulation/NTRUPlus768SimPrefix.ec',
 'kem_fo_simulation/NTRUPlus768SimPublicError.ec',
 'kem_fo_simulation/NTRUPlus768SimSpreadHash.ec',
 'kem_fo_simulation/NTRUPlus768SimAnswerErasure.ec',
 'kem_fo_simulation/NTRUPlus768SimGErasure.ec',
 'kem_fo_simulation/NTRUPlus768SimKnown.ec',
 'kem_fo_simulation/NTRUPlus768SimPorts.ec',
 'kem_fo_simulation/NTRUPlus768SimPublicBound.ec',
 'kem_fo_simulation/NTRUPlus768SimChallengeAnswer.ec',
 'kem_fo_simulation/NTRUPlus768SimGames.ec',
 'kem_fo_simulation/NTRUPlus768SimPortContracts.ec',
 'kem_fo_simulation/NTRUPlus768SimPublicCapRemoval.ec',
 'kem_fo_simulation/NTRUPlus768SimPublicGames.ec',
 'kem_fo_simulation/NTRUPlus768SimPublicInstances.ec',
 'kem_fo_simulation/NTRUPlus768SimRealBridge.ec',
 'kem_fo_simulation/NTRUPlus768SimSelected.ec',
 'kem_fo_simulation/NTRUPlus768SimSetupBridge.ec',
 'kem_fo_simulation/NTRUPlus768SimKnownCoupling.ec',
 'kem_fo_simulation/NTRUPlus768SimLookupGameBridge.ec',
 'kem_fo_simulation/NTRUPlus768SimPhaseState.ec',
 'kem_fo_simulation/NTRUPlus768SimRealGameBridge.ec',
 'kem_fo_simulation/NTRUPlus768SimSelectedCoupling.ec',
 'kem_fo_simulation/NTRUPlus768SimSelectedInvariant.ec',
 'kem_fo_simulation/NTRUPlus768SimKnownBridge.ec',
 'kem_fo_simulation/NTRUPlus768SimSelectedBound.ec',
 'kem_fo_simulation/NTRUPlus768SimPhaseBound.ec',
 'kem_fo_simulation/NTRUPlus768SimKernelBound.ec',
 'kem_fo_simulation/NTRUPlus768SimFinal.ec')

