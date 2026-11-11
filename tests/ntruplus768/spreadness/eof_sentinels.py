"""Static semantic EOF declarations; pins await final reviewed freeze."""

SENTINELS = {'kem_spreadness/NTRUPlus768SpreadCBD.ec': '\n'
                                           '\n'
                                           'lemma __spreadness_eof p :\n'
                                           ' mu uniform192(fun buf=>pke_cbd_field buf=p)<=1%r/(2%r^768).\n'
                                           'proof. exact (spread_cbd_field_buffer_point_bound p). qed.\n',
 'kem_spreadness/NTRUPlus768SpreadProcedures.ec': '\n'
                                                  '\n'
                                                  'lemma __spreadness_eof pk0 m0 event &m : pke_domain m0=>\n'
                                                  ' Pr[SpreadPKE.run(pk0,m0) @ &m:event res]=\n'
                                                  ' mu pke_psi1(fun r=>event(pke_enc_spec pk0 m0 r)).\n'
                                                  'proof. exact (spread_pke_probability pk0 m0 event &m). '
                                                  'qed.\n',
 'kem_spreadness/NTRUPlus768SpreadBase.ec': '\n'
                                            '\n'
                                            'lemma __spreadness_eof w m :\n'
                                            ' pke_key_relation w=>pke_domain m=>\n'
                                            ' mu pke_psi1 (fun r=>pke_enc_spec w.`kg_pk m r=\n'
                                            '   Some(pke_ciphertext w.`kg_pk m '
                                            'spread_cbd_zero))=1%r/(2%r^768).\n'
                                            'proof. exact (spread_base_zero_tight w m). qed.\n',
 'kem_spreadness/NTRUPlus768SpreadGenerated.ec': '\n'
                                                 '\n'
                                                 'lemma __spreadness_eof m0 ct0 &mem :\n'
                                                 ' pke_domain m0=>Pr[SpreadGeneratedROM.run(m0) @ '
                                                 '&mem:res=Some ct0]<=1%r/(2%r^768).\n'
                                                 'proof. exact (spread_generated_rom_bound m0 ct0 &mem). '
                                                 'qed.\n',
 'kem_spreadness/NTRUPlus768SpreadTransfer.ec': '\n'
                                                '\n'
                                                'lemma __spreadness_eof w msg ct : pke_key_relation w=>\n'
                                                ' E acwc2_gpads_law(fun pads=>spread_cipher_mass w '
                                                'msg(acwc2_gfun pads)ct)<=1%r/(2%r^768).\n'
                                                'proof. exact (spread_cipher_pads_average_bound w msg ct). '
                                                'qed.\n',
 'kem_spreadness/NTRUPlus768SpreadCache.ec': '\n'
                                             '\n'
                                             'lemma __spreadness_eof w msg g gm ct &m :\n'
                                             ' acwc2_cache_matches g gm=>ROG.m{m}=gm=>\n'
                                             ' Pr[SpreadEncodedValue.run(w.`kg_pk,msg) @ &m:res=Some '
                                             'ct]=spread_cipher_mass w msg g ct.\n'
                                             'proof. exact (spread_encoded_prepared_probability w msg g gm '
                                             'ct &m). qed.\n',
 'kem_spreadness/NTRUPlus768SpreadWeak.ec': '\n'
                                            '\n'
                                            'lemma __spreadness_eof &m :\n'
                                            ' E(mk(fun s=>Pr[FOSetupSource.guess(witness) @ &m:res=s]))\n'
                                            '   (fun (s:fo_setup_observation)=>spread_cipher_max '
                                            's.`1.`1(acwc2_gfun s.`3))<1%r/(2%r^352).\n'
                                            'proof. exact (spread_weak_setup_max_352 &m). qed.\n',
 'kem_spreadness/NTRUPlus768SpreadCalls.ec': '\n'
                                             '\n'
                                             'lemma __spreadness_eof w msg g gm ct &m :\n'
                                             ' acwc2_cache_matches g gm=>ROG.m{m}=gm=>\n'
                                             ' Pr[SpreadEncoded.run(w.`kg_pk,msg) @ &m:res=Some '
                                             'ct]=spread_cipher_mass w msg g ct.\n'
                                             'proof. exact (spread_encoded_prepared_actual w msg g gm ct '
                                             '&m). qed.\n'}

SEMANTIC_TARGETS = {'kem_spreadness/NTRUPlus768SpreadCBD.ec': 'spread_cbd_field_buffer_point_bound',
 'kem_spreadness/NTRUPlus768SpreadProcedures.ec': 'spread_pke_probability',
 'kem_spreadness/NTRUPlus768SpreadBase.ec': 'spread_base_zero_tight',
 'kem_spreadness/NTRUPlus768SpreadGenerated.ec': 'spread_generated_rom_bound',
 'kem_spreadness/NTRUPlus768SpreadTransfer.ec': 'spread_cipher_pads_average_bound',
 'kem_spreadness/NTRUPlus768SpreadCache.ec': 'spread_encoded_prepared_probability',
 'kem_spreadness/NTRUPlus768SpreadWeak.ec': 'spread_weak_setup_max_352',
 'kem_spreadness/NTRUPlus768SpreadCalls.ec': 'spread_encoded_prepared_actual'}

MODULE_BINDERS = {'kem_spreadness/NTRUPlus768SpreadCBD.ec': (),
 'kem_spreadness/NTRUPlus768SpreadProcedures.ec': (),
 'kem_spreadness/NTRUPlus768SpreadBase.ec': (),
 'kem_spreadness/NTRUPlus768SpreadGenerated.ec': (),
 'kem_spreadness/NTRUPlus768SpreadTransfer.ec': (),
 'kem_spreadness/NTRUPlus768SpreadCache.ec': (),
 'kem_spreadness/NTRUPlus768SpreadWeak.ec': (),
 'kem_spreadness/NTRUPlus768SpreadCalls.ec': ()}

NEGATIVE_PROOFS = ('kem_spreadness/NTRUPlus768SpreadCBD.ec',
 'kem_spreadness/NTRUPlus768SpreadProcedures.ec',
 'kem_spreadness/NTRUPlus768SpreadBase.ec',
 'kem_spreadness/NTRUPlus768SpreadGenerated.ec',
 'kem_spreadness/NTRUPlus768SpreadTransfer.ec',
 'kem_spreadness/NTRUPlus768SpreadCache.ec',
 'kem_spreadness/NTRUPlus768SpreadWeak.ec',
 'kem_spreadness/NTRUPlus768SpreadCalls.ec')

