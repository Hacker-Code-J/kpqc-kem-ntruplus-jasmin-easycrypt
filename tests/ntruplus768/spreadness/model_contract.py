"""Static spreadness call and quantifier contracts; finite diagnostics are separate."""

RULES = [('ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadCBD.ec',
  'unconditioned-CBD-point-mass',
  'lemma spread_cbd_point_bound r : mu1 pke_psi1 r<=1%r/(2%r^768).'),
 ('ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadCBD.ec',
  'zero-mass-attains-bound',
  'lemma spread_cbd_zero_point : mu1 pke_psi1 spread_cbd_zero=1%r/(2%r^768).'),
 ('ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadBase.ec',
  'generated-key-validity-not-byte-canonicity',
  'lemma spread_base_bound w m ct :\n'
  ' pke_key_relation w=>pke_domain m=>\n'
  ' mu pke_psi1 (fun r=>pke_enc_spec w.`kg_pk m r=Some ct)<=1%r/(2%r^768).'),
 ('ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadBase.ec',
  'no-added-no-wrap-premise',
  'lemma spread_base_bound w m ct :\n'
  ' pke_key_relation w=>pke_domain m=>\n'
  ' mu pke_psi1 (fun r=>pke_enc_spec w.`kg_pk m r=Some ct)<=1%r/(2%r^768).'),
 ('ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadBase.ec',
  'fixed-message-trit-fiber',
  'lemma spread_base_fiber_unique w m ct r1 r2 :\n'
  ' pke_key_relation w=>pke_domain m=>pke_domain r1=>pke_domain r2=>\n'
  ' pke_enc_spec w.`kg_pk m r1=Some ct=>pke_enc_spec w.`kg_pk m r2=Some ct=>r1=r2.'),
 ('ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadProcedures.ec',
  'actual-uniform-buffer-CBD-call',
  'buf <$ uniform192;\n'
  '  r <@ NTRUPlus768PolyCBD1Checked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(witness,buf);\n'
  '  return r;'),
 ('ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadProcedures.ec',
  'actual-fresh-randomness-and-PKE-call',
  'r <@ SpreadSample.run();\n  ct <@ PKEEnc.run(pk,m,r);\n  return ct;'),
 ('ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadProcedures.ec',
  'actual-encoded-G-SOTP-PKE-chain',
  'r <@ SpreadSample.run();\n'
  '  pad <@ ACWC2HashG.run(r);\n'
  '  code <@ SOTPEncode.run(msg,pad);\n'
  '  ct <@ PKEEnc.run(pk,code,r);\n'
  '  return ct;'),
 ('ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadCache.ec',
  'fresh-randomness-before-existing-cache-query',
  'r <$ pke_psi1;\n'
  '  pad <@ ROG.get(rr_G_input r);\n'
  '  return pke_enc_spec pk (poly_sotp_encode_spec msg pad) r;'),
 ('ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadCalls.ec',
  'complete-G-table-preserved',
  'lemma spread_encoded_equiv : equiv[SpreadEncoded.run ~ SpreadEncodedValue.run:\n'
  ' ={pk,msg,ROG.m} ==> ={res,ROG.m}].'),
 ('ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadCalls.ec',
  'nonempty-cache-cost-kept',
  'lemma spread_encoded_actual_bound w msg ct &m : pke_key_relation w=>\n'
  ' Pr[SpreadEncoded.run(w.`kg_pk,msg) @ &m:res=Some ct]<=\n'
  ' ((fsize ROG.m{m}+1)%r/(2%r^768)).'),
 ('ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadTransfer.ec',
  'fixed-message-and-ciphertext-G-average',
  'lemma spread_cipher_pads_average_bound w msg ct : pke_key_relation w=>\n'
  ' E acwc2_gpads_law(fun pads=>spread_cipher_mass w msg(acwc2_gfun pads)ct)<=1%r/(2%r^768).'),
 ('ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadWeak.ec',
  'actual-full-ciphertext-image',
  'op [opaque] spread_cipher_enum (w:keygen_witness) : W8.t Array1152.t list =\n'
  ' flatten(map(fun code=>map(pke_ciphertext w.`kg_pk code)acwc2_r_enum)acwc2_r_enum).'),
 ('ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadWeak.ec',
  'nested-message-and-ciphertext-maximum',
  'op [opaque] spread_cipher_max (w:keygen_witness) (g:acwc2_g_function) =\n'
  ' acwc2_finite_max acwc2_message_enum(fun msg=>\n'
  '  acwc2_finite_max (spread_cipher_enum w)(spread_cipher_mass w msg g)).'),
 ('ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadWeak.ec',
  'fixed-G-bound-keeps-error-term',
  'lemma spread_cipher_max_fixed w g : pke_key_relation w=>\n'
  ' spread_cipher_max w g<=1%r/(2%r^768)+fo_error w g.'),
 ('ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadWeak.ec',
  'actual-setup-expected-maximum-no-extra-premise',
  'lemma spread_weak_setup_max_352 &m :\n'
  ' E(mk(fun s=>Pr[FOSetupSource.guess(witness) @ &m:res=s]))\n'
  '   (fun (s:fo_setup_observation)=>spread_cipher_max s.`1.`1(acwc2_gfun s.`3))<1%r/(2%r^352).'),
 ('ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadGenerated.ec',
  'valid-public-key-has-generated-key-witness',
  'op [opaque] spread_valid_public_key (pk:W8.t Array1152.t) =\n'
  ' exists (w:keygen_witness),pke_key_relation w /\\ pk=w.`kg_pk.'),
 ('ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadGenerated.ec',
  'actual-public-Keygen-before-encryption',
  '(pk,sk)<@Keygen(UniformSeedRNG,E,SHAKEFROM).run();\n  ct<@SpreadPKE.run(pk,m);\n  return ct;'),
 ('ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadGenerated.ec',
  'ROM-initialization-and-actual-ROM-keygen',
  'ROE.init();ROF.init();\n  ct<@SpreadGenerated(ExpandROM).run(m);'),
 ('ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadGenerated.ec',
  'no-ROM-Keygen-losslessness-assumption',
  'lemma spread_generated_rom_bound m0 ct0 &mem :\n'
  ' pke_domain m0=>Pr[SpreadGeneratedROM.run(m0) @ &mem:res=Some ct0]<=1%r/(2%r^768).'),
 ('ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadCalls.ec',
  'fresh-G-is-a-distinct-explicit-reset-experiment',
  'ROG.init();ct <@ SpreadEncoded.run(pk,msg);return ct;'),
 ('ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadCalls.ec',
  'prepared-exact-law-needs-cache-agreement',
  'lemma spread_encoded_prepared_actual w msg g gm ct &m :\n'
  ' acwc2_cache_matches g gm=>ROG.m{m}=gm=>\n'
  ' Pr[SpreadEncoded.run(w.`kg_pk,msg) @ &m:res=Some ct]=spread_cipher_mass w msg g ct.')]

MUTATIONS = [('unconditioned-CBD-point-mass',
  'ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadCBD.ec',
  'lemma spread_cbd_point_bound r : mu1 pke_psi1 r<=1%r/(2%r^768).',
  'lemma spread_cbd_point_bound r : mu1 accepted_key_law r<=1%r/(2%r^768).'),
 ('zero-mass-attains-bound',
  'ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadCBD.ec',
  'lemma spread_cbd_zero_point : mu1 pke_psi1 spread_cbd_zero=1%r/(2%r^768).',
  'lemma spread_cbd_zero_point : mu1 pke_psi1 spread_cbd_zero<=1%r/(2%r^768).'),
 ('generated-key-validity-not-byte-canonicity',
  'ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadBase.ec',
  'lemma spread_base_bound w m ct :\n'
  ' pke_key_relation w=>pke_domain m=>\n'
  ' mu pke_psi1 (fun r=>pke_enc_spec w.`kg_pk m r=Some ct)<=1%r/(2%r^768).',
  'lemma spread_base_bound w m ct :\n'
  ' encap_key_canonical w.`kg_pk=>pke_domain m=>\n'
  ' mu pke_psi1 (fun r=>pke_enc_spec w.`kg_pk m r=Some ct)<=1%r/(2%r^768).'),
 ('no-added-no-wrap-premise',
  'ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadBase.ec',
  'lemma spread_base_bound w m ct :\n'
  ' pke_key_relation w=>pke_domain m=>\n'
  ' mu pke_psi1 (fun r=>pke_enc_spec w.`kg_pk m r=Some ct)<=1%r/(2%r^768).',
  'lemma spread_base_bound w m ct :\n'
  ' pke_key_relation w=>pke_domain m=>honest_no_wrap witness=>\n'
  ' mu pke_psi1 (fun r=>pke_enc_spec w.`kg_pk m r=Some ct)<=1%r/(2%r^768).'),
 ('fixed-message-trit-fiber',
  'ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadBase.ec',
  'lemma spread_base_fiber_unique w m ct r1 r2 :\n'
  ' pke_key_relation w=>pke_domain m=>pke_domain r1=>pke_domain r2=>\n'
  ' pke_enc_spec w.`kg_pk m r1=Some ct=>pke_enc_spec w.`kg_pk m r2=Some ct=>r1=r2.',
  'lemma spread_base_fiber_unique w m ct r1 r2 :\n'
  ' pke_key_relation w=>pke_domain m=>\n'
  ' pke_enc_spec w.`kg_pk m r1=Some ct=>pke_enc_spec w.`kg_pk m r2=Some ct=>r1=r2.'),
 ('actual-uniform-buffer-CBD-call',
  'ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadProcedures.ec',
  'buf <$ uniform192;\n'
  '  r <@ NTRUPlus768PolyCBD1Checked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(witness,buf);\n'
  '  return r;',
  'buf <$ uniform192;\n  r <- witness;\n  return r;'),
 ('actual-fresh-randomness-and-PKE-call',
  'ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadProcedures.ec',
  'r <@ SpreadSample.run();\n  ct <@ PKEEnc.run(pk,m,r);\n  return ct;',
  'r <@ SpreadSample.run();\n  ct <- pke_enc_spec pk m r;\n  return ct;'),
 ('actual-encoded-G-SOTP-PKE-chain',
  'ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadProcedures.ec',
  'r <@ SpreadSample.run();\n'
  '  pad <@ ACWC2HashG.run(r);\n'
  '  code <@ SOTPEncode.run(msg,pad);\n'
  '  ct <@ PKEEnc.run(pk,code,r);\n'
  '  return ct;',
  'r <@ SpreadSample.run();\n'
  '  pad <$ uniform192;\n'
  '  code <@ SOTPEncode.run(msg,pad);\n'
  '  ct <@ PKEEnc.run(pk,code,r);\n'
  '  return ct;'),
 ('fresh-randomness-before-existing-cache-query',
  'ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadCache.ec',
  'r <$ pke_psi1;\n'
  '  pad <@ ROG.get(rr_G_input r);\n'
  '  return pke_enc_spec pk (poly_sotp_encode_spec msg pad) r;',
  'r <$ pke_psi1;\n'
  '  ROG.init(); pad <@ ROG.get(rr_G_input r);\n'
  '  return pke_enc_spec pk (poly_sotp_encode_spec msg pad) r;'),
 ('complete-G-table-preserved',
  'ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadCalls.ec',
  'lemma spread_encoded_equiv : equiv[SpreadEncoded.run ~ SpreadEncodedValue.run:\n'
  ' ={pk,msg,ROG.m} ==> ={res,ROG.m}].',
  'lemma spread_encoded_equiv : equiv[SpreadEncoded.run ~ SpreadEncodedValue.run:\n'
  ' ={pk,msg,ROG.m} ==> ={res}].'),
 ('nonempty-cache-cost-kept',
  'ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadCalls.ec',
  'lemma spread_encoded_actual_bound w msg ct &m : pke_key_relation w=>\n'
  ' Pr[SpreadEncoded.run(w.`kg_pk,msg) @ &m:res=Some ct]<=\n'
  ' ((fsize ROG.m{m}+1)%r/(2%r^768)).',
  'lemma spread_encoded_actual_bound w msg ct &m : pke_key_relation w=>\n'
  ' Pr[SpreadEncoded.run(w.`kg_pk,msg) @ &m:res=Some ct]<=\n'
  ' ((1)%r/(2%r^768)).'),
 ('fixed-message-and-ciphertext-G-average',
  'ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadTransfer.ec',
  'lemma spread_cipher_pads_average_bound w msg ct : pke_key_relation w=>\n'
  ' E acwc2_gpads_law(fun pads=>spread_cipher_mass w msg(acwc2_gfun pads)ct)<=1%r/(2%r^768).',
  'lemma spread_cipher_pads_average_bound w msg ct : pke_key_relation w=>\n'
  ' spread_cipher_mass w msg (acwc2_gfun witness) ct<=1%r/(2%r^768).'),
 ('actual-full-ciphertext-image',
  'ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadWeak.ec',
  'op [opaque] spread_cipher_enum (w:keygen_witness) : W8.t Array1152.t list =\n'
  ' flatten(map(fun code=>map(pke_ciphertext w.`kg_pk code)acwc2_r_enum)acwc2_r_enum).',
  'op [opaque] spread_cipher_enum (w:keygen_witness) : W8.t Array1152.t list =\n [].'),
 ('nested-message-and-ciphertext-maximum',
  'ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadWeak.ec',
  'op [opaque] spread_cipher_max (w:keygen_witness) (g:acwc2_g_function) =\n'
  ' acwc2_finite_max acwc2_message_enum(fun msg=>\n'
  '  acwc2_finite_max (spread_cipher_enum w)(spread_cipher_mass w msg g)).',
  'op [opaque] spread_cipher_max (w:keygen_witness) (g:acwc2_g_function) =\n'
  ' acwc2_finite_max [witness](fun msg=>\n'
  '  acwc2_finite_max (spread_cipher_enum w)(spread_cipher_mass w msg g)).'),
 ('fixed-G-bound-keeps-error-term',
  'ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadWeak.ec',
  'lemma spread_cipher_max_fixed w g : pke_key_relation w=>\n'
  ' spread_cipher_max w g<=1%r/(2%r^768)+fo_error w g.',
  'lemma spread_cipher_max_fixed w g : pke_key_relation w=>\n spread_cipher_max w g<=1%r/(2%r^768).'),
 ('actual-setup-expected-maximum-no-extra-premise',
  'ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadWeak.ec',
  'lemma spread_weak_setup_max_352 &m :\n'
  ' E(mk(fun s=>Pr[FOSetupSource.guess(witness) @ &m:res=s]))\n'
  '   (fun (s:fo_setup_observation)=>spread_cipher_max s.`1.`1(acwc2_gfun s.`3))<1%r/(2%r^352).',
  'lemma spread_weak_setup_max_352 &m : (forall w g,fo_error w g=0%r)=>\n'
  ' E(mk(fun s=>Pr[FOSetupSource.guess(witness) @ &m:res=s]))\n'
  '   (fun (s:fo_setup_observation)=>spread_cipher_max s.`1.`1(acwc2_gfun s.`3))<1%r/(2%r^352).'),
 ('valid-public-key-has-generated-key-witness',
  'ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadGenerated.ec',
  'op [opaque] spread_valid_public_key (pk:W8.t Array1152.t) =\n'
  ' exists (w:keygen_witness),pke_key_relation w /\\ pk=w.`kg_pk.',
  'op [opaque] spread_valid_public_key (pk:W8.t Array1152.t) =\n encap_key_canonical pk.'),
 ('actual-public-Keygen-before-encryption',
  'ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadGenerated.ec',
  '(pk,sk)<@Keygen(UniformSeedRNG,E,SHAKEFROM).run();\n  ct<@SpreadPKE.run(pk,m);\n  return ct;',
  'pk<-witness;sk<-witness;\n  ct<@SpreadPKE.run(pk,m);\n  return ct;'),
 ('ROM-initialization-and-actual-ROM-keygen',
  'ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadGenerated.ec',
  'ROE.init();ROF.init();\n  ct<@SpreadGenerated(ExpandROM).run(m);',
  'ROE.init();ROF.init();\n  ct<@SpreadGenerated(FreshExpand).run(m);'),
 ('no-ROM-Keygen-losslessness-assumption',
  'ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadGenerated.ec',
  'lemma spread_generated_rom_bound m0 ct0 &mem :\n'
  ' pke_domain m0=>Pr[SpreadGeneratedROM.run(m0) @ &mem:res=Some ct0]<=1%r/(2%r^768).',
  'lemma spread_generated_rom_bound m0 ct0 &mem :\n'
  ' pke_domain m0=>islossless Keygen(UniformSeedRNG,ExpandROM,SHAKEFROM).run=>Pr[SpreadGeneratedROM.run(m0) '
  '@ &mem:res=Some ct0]<=1%r/(2%r^768).'),
 ('fresh-G-is-a-distinct-explicit-reset-experiment',
  'ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadCalls.ec',
  'ROG.init();ct <@ SpreadEncoded.run(pk,msg);return ct;',
  'ct <@ SpreadEncoded.run(pk,msg);return ct;'),
 ('prepared-exact-law-needs-cache-agreement',
  'ntruplus/proof/768/ref/kem_spreadness/NTRUPlus768SpreadCalls.ec',
  'lemma spread_encoded_prepared_actual w msg g gm ct &m :\n'
  ' acwc2_cache_matches g gm=>ROG.m{m}=gm=>\n'
  ' Pr[SpreadEncoded.run(w.`kg_pk,msg) @ &m:res=Some ct]=spread_cipher_mass w msg g ct.',
  'lemma spread_encoded_prepared_actual w msg g gm ct &m :\n'
  ' ROG.m{m}=gm=>\n'
  ' Pr[SpreadEncoded.run(w.`kg_pk,msg) @ &m:res=Some ct]=spread_cipher_mass w msg g ct.')]

def check_model(read, ordered, require):
    from check_spreadness import compact
    for relative, label, expected in RULES:
        require(compact(expected).replace('op[opaque]', 'op') in
                read(relative).replace('op[opaque]', 'op'), label)
