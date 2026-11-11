"""Frozen public-history, actual-call and concrete selected-query contracts."""

RULES = [('ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimOracles.ec',
  'history-records-full-backend-reply',
  'hout <@ H.get(input);\n  SimHistory.record(input,hout);\n  return hout;'),
 ('ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimOracles.ec',
  'raw-zero-still-executes-and-records-H',
  'if(0<=outlen<=raw_xof_max_output){\n'
  '   stream <@ full(input);\n'
  '   result<-Some(raw_xof_output outlen stream);\n'
  '  }'),
 ('ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimSampling.ec',
  'actual-H-is-the-existing-lazy-cache',
  'module SimHActual : SimHPort = {proc get=ROH.get}.'),
 ('ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimLookup.ec',
  'lookup-scans-public-history-not-physical-H',
  'module SimLookup(G:FOGPort) : CCADecapPort = {\n'
  ' proc decap(ct:W8.t Array1152.t) : cca_reply = {\n'
  '  var answer:cca_reply;var star:W8.t Array1152.t option;\n'
  '  var pk:W8.t Array1152.t;var suffix:W8.t Array32.t;\n'
  '  var log:(fo_h_input,W8.t Array224.t)fmap;var todo:fo_h_input list;\n'
  '  var input:fo_h_input;var hout:W8.t Array224.t;var candidate:W8.t Array1152.t option;\n'
  '  answer<-None;\n'
  '  SimPublic.count<-SimPublic.count+1;\n'
  '  star<-SimPublic.cstar;\n'
  '  if(star<>Some ct){\n'
  '   pk<-SimPublic.pk;suffix<-SimPublic.suffix;log<-SimHistory.h;\n'
  '   todo<-elems(fdom log);\n'
  '   while(todo<>[] /\\ answer=None){\n'
  '    input<-head witness todo;todo<-behead todo;\n'
  '    if(input.`2=suffix){\n'
  '     hout<-oget log.[input];\n'
  '     candidate<@SimEncrypt(G).run(pk,input.`1,hout);\n'
  '     if(candidate=Some ct){answer<-Some(payload_shared_key hout);}\n'
  '    }\n'
  '   }\n'
  '  }\n'
  '  return answer;\n'
  ' }\n'
  '}.'),
 ('ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimLookup.ec',
  'lookup-has-no-secret-key-read',
  'module SimLookup(G:FOGPort) : CCADecapPort = {\n'
  ' proc decap(ct:W8.t Array1152.t) : cca_reply = {\n'
  '  var answer:cca_reply;var star:W8.t Array1152.t option;\n'
  '  var pk:W8.t Array1152.t;var suffix:W8.t Array32.t;\n'
  '  var log:(fo_h_input,W8.t Array224.t)fmap;var todo:fo_h_input list;\n'
  '  var input:fo_h_input;var hout:W8.t Array224.t;var candidate:W8.t Array1152.t option;\n'
  '  answer<-None;\n'
  '  SimPublic.count<-SimPublic.count+1;\n'
  '  star<-SimPublic.cstar;\n'
  '  if(star<>Some ct){\n'
  '   pk<-SimPublic.pk;suffix<-SimPublic.suffix;log<-SimHistory.h;\n'
  '   todo<-elems(fdom log);\n'
  '   while(todo<>[] /\\ answer=None){\n'
  '    input<-head witness todo;todo<-behead todo;\n'
  '    if(input.`2=suffix){\n'
  '     hout<-oget log.[input];\n'
  '     candidate<@SimEncrypt(G).run(pk,input.`1,hout);\n'
  '     if(candidate=Some ct){answer<-Some(payload_shared_key hout);}\n'
  '    }\n'
  '   }\n'
  '  }\n'
  '  return answer;\n'
  ' }\n'
  '}.'),
 ('ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimLookup.ec',
  'lookup-rejects-the-exact-challenge',
  'module SimLookup(G:FOGPort) : CCADecapPort = {\n'
  ' proc decap(ct:W8.t Array1152.t) : cca_reply = {\n'
  '  var answer:cca_reply;var star:W8.t Array1152.t option;\n'
  '  var pk:W8.t Array1152.t;var suffix:W8.t Array32.t;\n'
  '  var log:(fo_h_input,W8.t Array224.t)fmap;var todo:fo_h_input list;\n'
  '  var input:fo_h_input;var hout:W8.t Array224.t;var candidate:W8.t Array1152.t option;\n'
  '  answer<-None;\n'
  '  SimPublic.count<-SimPublic.count+1;\n'
  '  star<-SimPublic.cstar;\n'
  '  if(star<>Some ct){\n'
  '   pk<-SimPublic.pk;suffix<-SimPublic.suffix;log<-SimHistory.h;\n'
  '   todo<-elems(fdom log);\n'
  '   while(todo<>[] /\\ answer=None){\n'
  '    input<-head witness todo;todo<-behead todo;\n'
  '    if(input.`2=suffix){\n'
  '     hout<-oget log.[input];\n'
  '     candidate<@SimEncrypt(G).run(pk,input.`1,hout);\n'
  '     if(candidate=Some ct){answer<-Some(payload_shared_key hout);}\n'
  '    }\n'
  '   }\n'
  '  }\n'
  '  return answer;\n'
  ' }\n'
  '}.'),
 ('ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimLookup.ec',
  'lookup-matches-the-public-F-suffix',
  'module SimLookup(G:FOGPort) : CCADecapPort = {\n'
  ' proc decap(ct:W8.t Array1152.t) : cca_reply = {\n'
  '  var answer:cca_reply;var star:W8.t Array1152.t option;\n'
  '  var pk:W8.t Array1152.t;var suffix:W8.t Array32.t;\n'
  '  var log:(fo_h_input,W8.t Array224.t)fmap;var todo:fo_h_input list;\n'
  '  var input:fo_h_input;var hout:W8.t Array224.t;var candidate:W8.t Array1152.t option;\n'
  '  answer<-None;\n'
  '  SimPublic.count<-SimPublic.count+1;\n'
  '  star<-SimPublic.cstar;\n'
  '  if(star<>Some ct){\n'
  '   pk<-SimPublic.pk;suffix<-SimPublic.suffix;log<-SimHistory.h;\n'
  '   todo<-elems(fdom log);\n'
  '   while(todo<>[] /\\ answer=None){\n'
  '    input<-head witness todo;todo<-behead todo;\n'
  '    if(input.`2=suffix){\n'
  '     hout<-oget log.[input];\n'
  '     candidate<@SimEncrypt(G).run(pk,input.`1,hout);\n'
  '     if(candidate=Some ct){answer<-Some(payload_shared_key hout);}\n'
  '    }\n'
  '   }\n'
  '  }\n'
  '  return answer;\n'
  ' }\n'
  '}.'),
 ('ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimLookup.ec',
  'lookup-regenerates-through-actual-CBD-G-SOTP-PKE',
  'r <@ '
  'NTRUPlus768PolyCBD1Checked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(witness,complete_hash_tail '
  'hout);\n'
  '  pad <@ FOHashG(FOGHash(G)).run(r);\n'
  '  code <@ SOTPEncode.run(msg,pad);\n'
  '  ct <@ PKEEnc.run(pk,code,r);\n'
  '  return ct;'),
 ('ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimCandidate.ec',
  'candidate-uniqueness-needs-good-cache',
  'lemma sim_table_matches_unique w g excluded hstar cstar\n'
  ' (tab:(fo_h_input,W8.t Array224.t)fmap) (x1 x2:fo_h_input) hout1 hout2 ct :\n'
  ' pke_key_relation w=>fo_hcache_good w g excluded tab=>\n'
  ' fo_challenge_invariant w g excluded hstar cstar tab=>ct<>cstar=>\n'
  ' x1.`2=complete_sk_suffix w.`kg_sk=>x2.`2=complete_sk_suffix w.`kg_sk=>\n'
  ' tab.[x1]=Some hout1=>tab.[x2]=Some hout2=>\n'
  ' fo_reencryption w g x1.`1 hout1=Some ct=>fo_reencryption w g x2.`1 hout2=Some ct=>\n'
  ' x1=x2 /\\ hout1=hout2 /\\ payload_shared_key hout1=payload_shared_key hout2.'),
 ('ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimCandidate.ec',
  'candidate-uniqueness-needs-actual-map-lookups',
  'lemma sim_table_matches_unique w g excluded hstar cstar\n'
  ' (tab:(fo_h_input,W8.t Array224.t)fmap) (x1 x2:fo_h_input) hout1 hout2 ct :\n'
  ' pke_key_relation w=>fo_hcache_good w g excluded tab=>\n'
  ' fo_challenge_invariant w g excluded hstar cstar tab=>ct<>cstar=>\n'
  ' x1.`2=complete_sk_suffix w.`kg_sk=>x2.`2=complete_sk_suffix w.`kg_sk=>\n'
  ' tab.[x1]=Some hout1=>tab.[x2]=Some hout2=>\n'
  ' fo_reencryption w g x1.`1 hout1=Some ct=>fo_reencryption w g x2.`1 hout2=Some ct=>\n'
  ' x1=x2 /\\ hout1=hout2 /\\ payload_shared_key hout1=payload_shared_key hout2.'),
 ('ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimSpreadHash.ec',
  'freshness-is-physical-H-membership',
  'lemma sim_answer_actual_fresh_bound w g q0 gm0 hm0 :\n'
  ' pke_key_relation w=>q0.`sr_pk=w.`kg_pk=>acwc2_cache_matches g gm0=>\n'
  ' sim_h_input q0 \\notin hm0=>\n'
  ' phoare[SimAnswerReal(FOGActual,SimHActual).answer:\n'
  ' q=q0 /\\ ROG.m=gm0 /\\ ROH.m=hm0 ==>res<>None]\n'
  ' <=(1%r/(2%r^768)+fo_error w g).'),
 ('ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimSpreadHash.ec',
  'fixed-setup-bound-retains-rho-plus-error',
  'lemma sim_answer_actual_fresh_bound w g q0 gm0 hm0 :\n'
  ' pke_key_relation w=>q0.`sr_pk=w.`kg_pk=>acwc2_cache_matches g gm0=>\n'
  ' sim_h_input q0 \\notin hm0=>\n'
  ' phoare[SimAnswerReal(FOGActual,SimHActual).answer:\n'
  ' q=q0 /\\ ROG.m=gm0 /\\ ROH.m=hm0 ==>res<>None]\n'
  ' <=(1%r/(2%r^768)+fo_error w g).'),
 ('ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimAnswer.ec',
  'hidden-sampling-does-not-clear-existing-H',
  'module SimAnswerSample(H:SimHRO.RO) : SimAnswer = {\n'
  ' proc answer(q:sim_request) : W8.t Array32.t option = {\n'
  '  H.sample(sim_h_input q);\n'
  '  return None;\n'
  ' }\n'
  '}.'),
 ('ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimAnswerErasure.ec',
  'erasure-context-cannot-read-private-bad-flag',
  'lemma sim_reject_never_probability\n'
  ' (C<:SimAnswerContext {-ROG,-ROH,-SimGRO.RO,-SimGRO.FRO,-SimHRO.RO,-SimHRO.FRO,-SimBad})\n'
  ' g &m s0 (event:bool->bool) : acwc2_cache_matches g ROG.m{m}=>\n'
  ' Pr[SimRejectWorld(C,SimHRO.RO).distinguish(s0) @ &m:event res]=\n'
  ' Pr[SimNeverWorld(C,SimHRO.RO).distinguish(s0) @ &m:event res].'),
 ('ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimGames.ec',
  'public-game-obtains-F-suffix-through-public-oracle',
  'module SimPublicChallenge(A:CCAExtendedAdversary,G:FOGPort,H:SimHPort) = {\n'
  ' proc run(pk:W8.t Array1152.t) : bool = {\n'
  '  var real:encap_result;var random,suffix:W8.t Array32.t;var bit,guess:bool;\n'
  '  real<@EncapRandom(SHAKEFROM,FOGHash(G),SimHShake(H),UniformCoins).run(pk,witness);\n'
  '  random<$uniform32;bit<$dbool;\n'
  '  suffix<@ROF.get(pk);\n'
  '  SimPublic.init(pk,suffix,real.`1);SimHistory.init();\n'
  '  guess<@A(SimOracles(G,H),SimLookup(G)).guess(pk,real.`1,if bit then random else real.`2);\n'
  '  return guess=bit;\n'
  ' }\n'
  '}.'),
 ('ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimGames.ec',
  'public-game-never-installs-secret-in-Decaps-state',
  'module SimPublicFreshGame(A:CCAExtendedAdversary) = {\n'
  ' proc run() : bool = {\n'
  '  var pk:W8.t Array1152.t;var sk:W8.t Array2336.t;var win:bool;\n'
  '  ROMInit.init();RawXOFStreams.init();\n'
  '  (pk,sk)<@Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run();\n'
  '  win<@SimPublicChallenge(A,FOGActual,SimHActual).run(pk);\n'
  '  return win;\n'
  ' }\n'
  '}.'),
 ('ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimAverage.ec',
  'two-hop-error-has-qD-and-qH-contributions',
  'lemma sim_setup_win_distance &m (K0 K1:fo_setup_observation->bool distr) qD qH :\n'
  ' 0<=qD=>0<=qH=>\n'
  ' (forall s,s \\in mk(fun z=>Pr[FOSetupSource.guess(witness) @ &m:res=z])=>\n'
  '  `|mu1(K0 s)true-mu1(K1 s)true|<=qD%r/(2%r^768)+(qH+qD)%r*fo_setup_error s)=>\n'
  ' `|mu1(dlet(mk(fun z=>Pr[FOSetupSource.guess(witness) @ &m:res=z]))K0)true-\n'
  '   mu1(dlet(mk(fun z=>Pr[FOSetupSource.guess(witness) @ &m:res=z]))K1)true|\n'
  ' <=qD%r/(2%r^768)+(qH+qD)%r/(2%r^353).'),
 ('ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimAverage.ec',
  'averaging-keeps-pointwise-support-obligation',
  'lemma sim_setup_win_distance &m (K0 K1:fo_setup_observation->bool distr) qD qH :\n'
  ' 0<=qD=>0<=qH=>\n'
  ' (forall s,s \\in mk(fun z=>Pr[FOSetupSource.guess(witness) @ &m:res=z])=>\n'
  '  `|mu1(K0 s)true-mu1(K1 s)true|<=qD%r/(2%r^768)+(qH+qD)%r*fo_setup_error s)=>\n'
  ' `|mu1(dlet(mk(fun z=>Pr[FOSetupSource.guess(witness) @ &m:res=z]))K0)true-\n'
  '   mu1(dlet(mk(fun z=>Pr[FOSetupSource.guess(witness) @ &m:res=z]))K1)true|\n'
  ' <=qD%r/(2%r^768)+(qH+qD)%r/(2%r^353).'),
 ('ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimSelectedInvariant.ec',
  'selected-guard-discharged-from-physical-cover',
  'lemma sim_selected_reject_guarded\n'
  ' (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,\n'
  '  -SimPublic,-SimHistory,-FOContext,-SimBad,-SimSelectedFixed,-SimPhaseInput,-FOBudgetState,\n'
  '  -SH.HB.Count,-SH.HB.HybOrcl}) w0 g0 :\n'
  ' equiv[SimSelectedReject(A).distinguish ~ SimSelectedGuarded(A).run:\n'
  ' w{2}=w0 /\\ g{2}=g0 /\\ ={s,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob '
  'SimPublic,glob SimHistory,glob FOContext,glob CCADecapOracle,glob SimBad,glob SH.HB.HybOrcl,glob '
  'FOBudgetState,glob SimPhaseInput} /\\\n'
  ' SimPublic.pk{1}=w0.`kg_pk /\\ acwc2_cache_matches g0 ROG.m{1} /\\\n'
  ' sim_log_included SimHistory.h{1} ROH.m{1} /\\ sim_h_cover SimHistory.h{1} ROH.m{1} '
  'FOContext.challenge_h{1} ==>\n'
  ' ={res,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob SimPublic,glob SimHistory,glob '
  'FOContext,glob CCADecapOracle,glob SimBad,glob SH.HB.HybOrcl,glob FOBudgetState,glob SimPhaseInput}].'),
 ('ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimSelectedBound.ec',
  'selected-win-projection-keeps-robust-losslessness',
  'lemma sim_selected_distance_bad\n'
  ' (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,\n'
  '  -FOPublicKey,-FOContext,-FOBadState,-FOBudgetState,-SimPublic,-SimHistory,-SimBad,\n'
  '  -SimSelectedFixed,-SimPhaseInput,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,\n'
  '  -SH.HB.Count,-SH.HB.HybOrcl}) g s0 &m :\n'
  ' acwc2_cache_matches g ROG.m{m}=>\n'
  ' (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),\n'
  '  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>\n'
  '  islossless D.decap=>islossless A(H,D).guess)=>\n'
  ' `|Pr[SimSelectedReal(A).distinguish(s0) @ &m:res]-\n'
  '   Pr[SimSelectedNever(A).distinguish(s0) @ &m:res]|\n'
  ' <=Pr[SimSelectedReject(A).distinguish(s0) @ &m:SimBad.hidden].')]

MUTATIONS = [('history-records-full-backend-reply',
  'ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimOracles.ec',
  'hout <@ H.get(input);\n  SimHistory.record(input,hout);\n  return hout;',
  'hout <@ H.get(input);\n  SimHistory.record(input,witness);\n  return hout;'),
 ('raw-zero-still-executes-and-records-H',
  'ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimOracles.ec',
  'if(0<=outlen<=raw_xof_max_output){\n'
  '   stream <@ full(input);\n'
  '   result<-Some(raw_xof_output outlen stream);\n'
  '  }',
  'if(0<outlen<=raw_xof_max_output){\n'
  '   stream <@ full(input);\n'
  '   result<-Some(raw_xof_output outlen stream);\n'
  '  }'),
 ('actual-H-is-the-existing-lazy-cache',
  'ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimSampling.ec',
  'module SimHActual : SimHPort = {proc get=ROH.get}.',
  'module SimHActual : SimHPort = {proc get=AlwaysFreshH.get}.'),
 ('lookup-scans-public-history-not-physical-H',
  'ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimLookup.ec',
  'module SimLookup(G:FOGPort) : CCADecapPort = {\n'
  ' proc decap(ct:W8.t Array1152.t) : cca_reply = {\n'
  '  var answer:cca_reply;var star:W8.t Array1152.t option;\n'
  '  var pk:W8.t Array1152.t;var suffix:W8.t Array32.t;\n'
  '  var log:(fo_h_input,W8.t Array224.t)fmap;var todo:fo_h_input list;\n'
  '  var input:fo_h_input;var hout:W8.t Array224.t;var candidate:W8.t Array1152.t option;\n'
  '  answer<-None;\n'
  '  SimPublic.count<-SimPublic.count+1;\n'
  '  star<-SimPublic.cstar;\n'
  '  if(star<>Some ct){\n'
  '   pk<-SimPublic.pk;suffix<-SimPublic.suffix;log<-SimHistory.h;\n'
  '   todo<-elems(fdom log);\n'
  '   while(todo<>[] /\\ answer=None){\n'
  '    input<-head witness todo;todo<-behead todo;\n'
  '    if(input.`2=suffix){\n'
  '     hout<-oget log.[input];\n'
  '     candidate<@SimEncrypt(G).run(pk,input.`1,hout);\n'
  '     if(candidate=Some ct){answer<-Some(payload_shared_key hout);}\n'
  '    }\n'
  '   }\n'
  '  }\n'
  '  return answer;\n'
  ' }\n'
  '}.',
  'module SimLookup(G:FOGPort) : CCADecapPort = {\n'
  ' proc decap(ct:W8.t Array1152.t) : cca_reply = {\n'
  '  var answer:cca_reply;var star:W8.t Array1152.t option;\n'
  '  var pk:W8.t Array1152.t;var suffix:W8.t Array32.t;\n'
  '  var log:(fo_h_input,W8.t Array224.t)fmap;var todo:fo_h_input list;\n'
  '  var input:fo_h_input;var hout:W8.t Array224.t;var candidate:W8.t Array1152.t option;\n'
  '  answer<-None;\n'
  '  SimPublic.count<-SimPublic.count+1;\n'
  '  star<-SimPublic.cstar;\n'
  '  if(star<>Some ct){\n'
  '   pk<-SimPublic.pk;suffix<-SimPublic.suffix;log<-ROH.m;\n'
  '   todo<-elems(fdom log);\n'
  '   while(todo<>[] /\\ answer=None){\n'
  '    input<-head witness todo;todo<-behead todo;\n'
  '    if(input.`2=suffix){\n'
  '     hout<-oget log.[input];\n'
  '     candidate<@SimEncrypt(G).run(pk,input.`1,hout);\n'
  '     if(candidate=Some ct){answer<-Some(payload_shared_key hout);}\n'
  '    }\n'
  '   }\n'
  '  }\n'
  '  return answer;\n'
  ' }\n'
  '}.'),
 ('lookup-has-no-secret-key-read',
  'ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimLookup.ec',
  'module SimLookup(G:FOGPort) : CCADecapPort = {\n'
  ' proc decap(ct:W8.t Array1152.t) : cca_reply = {\n'
  '  var answer:cca_reply;var star:W8.t Array1152.t option;\n'
  '  var pk:W8.t Array1152.t;var suffix:W8.t Array32.t;\n'
  '  var log:(fo_h_input,W8.t Array224.t)fmap;var todo:fo_h_input list;\n'
  '  var input:fo_h_input;var hout:W8.t Array224.t;var candidate:W8.t Array1152.t option;\n'
  '  answer<-None;\n'
  '  SimPublic.count<-SimPublic.count+1;\n'
  '  star<-SimPublic.cstar;\n'
  '  if(star<>Some ct){\n'
  '   pk<-SimPublic.pk;suffix<-SimPublic.suffix;log<-SimHistory.h;\n'
  '   todo<-elems(fdom log);\n'
  '   while(todo<>[] /\\ answer=None){\n'
  '    input<-head witness todo;todo<-behead todo;\n'
  '    if(input.`2=suffix){\n'
  '     hout<-oget log.[input];\n'
  '     candidate<@SimEncrypt(G).run(pk,input.`1,hout);\n'
  '     if(candidate=Some ct){answer<-Some(payload_shared_key hout);}\n'
  '    }\n'
  '   }\n'
  '  }\n'
  '  return answer;\n'
  ' }\n'
  '}.',
  'module SimLookup(G:FOGPort) : CCADecapPort = {\n'
  ' proc decap(ct:W8.t Array1152.t) : cca_reply = {\n'
  '  var answer:cca_reply;var star:W8.t Array1152.t option;\n'
  '  var pk:W8.t Array1152.t;var suffix:W8.t Array32.t;\n'
  '  var log:(fo_h_input,W8.t Array224.t)fmap;var todo:fo_h_input list;\n'
  '  var input:fo_h_input;var hout:W8.t Array224.t;var candidate:W8.t Array1152.t option;\n'
  '  answer<-None;\n'
  '  SimPublic.count<-SimPublic.count+1;\n'
  '  star<-SimPublic.cstar;\n'
  '  if(star<>Some ct){\n'
  '   pk<-SimPublic.pk;suffix<-complete_sk_suffix CCADecapOracle.sk;log<-SimHistory.h;\n'
  '   todo<-elems(fdom log);\n'
  '   while(todo<>[] /\\ answer=None){\n'
  '    input<-head witness todo;todo<-behead todo;\n'
  '    if(input.`2=suffix){\n'
  '     hout<-oget log.[input];\n'
  '     candidate<@SimEncrypt(G).run(pk,input.`1,hout);\n'
  '     if(candidate=Some ct){answer<-Some(payload_shared_key hout);}\n'
  '    }\n'
  '   }\n'
  '  }\n'
  '  return answer;\n'
  ' }\n'
  '}.'),
 ('lookup-rejects-the-exact-challenge',
  'ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimLookup.ec',
  'module SimLookup(G:FOGPort) : CCADecapPort = {\n'
  ' proc decap(ct:W8.t Array1152.t) : cca_reply = {\n'
  '  var answer:cca_reply;var star:W8.t Array1152.t option;\n'
  '  var pk:W8.t Array1152.t;var suffix:W8.t Array32.t;\n'
  '  var log:(fo_h_input,W8.t Array224.t)fmap;var todo:fo_h_input list;\n'
  '  var input:fo_h_input;var hout:W8.t Array224.t;var candidate:W8.t Array1152.t option;\n'
  '  answer<-None;\n'
  '  SimPublic.count<-SimPublic.count+1;\n'
  '  star<-SimPublic.cstar;\n'
  '  if(star<>Some ct){\n'
  '   pk<-SimPublic.pk;suffix<-SimPublic.suffix;log<-SimHistory.h;\n'
  '   todo<-elems(fdom log);\n'
  '   while(todo<>[] /\\ answer=None){\n'
  '    input<-head witness todo;todo<-behead todo;\n'
  '    if(input.`2=suffix){\n'
  '     hout<-oget log.[input];\n'
  '     candidate<@SimEncrypt(G).run(pk,input.`1,hout);\n'
  '     if(candidate=Some ct){answer<-Some(payload_shared_key hout);}\n'
  '    }\n'
  '   }\n'
  '  }\n'
  '  return answer;\n'
  ' }\n'
  '}.',
  'module SimLookup(G:FOGPort) : CCADecapPort = {\n'
  ' proc decap(ct:W8.t Array1152.t) : cca_reply = {\n'
  '  var answer:cca_reply;var star:W8.t Array1152.t option;\n'
  '  var pk:W8.t Array1152.t;var suffix:W8.t Array32.t;\n'
  '  var log:(fo_h_input,W8.t Array224.t)fmap;var todo:fo_h_input list;\n'
  '  var input:fo_h_input;var hout:W8.t Array224.t;var candidate:W8.t Array1152.t option;\n'
  '  answer<-None;\n'
  '  SimPublic.count<-SimPublic.count+1;\n'
  '  star<-SimPublic.cstar;\n'
  '  if(true){\n'
  '   pk<-SimPublic.pk;suffix<-SimPublic.suffix;log<-SimHistory.h;\n'
  '   todo<-elems(fdom log);\n'
  '   while(todo<>[] /\\ answer=None){\n'
  '    input<-head witness todo;todo<-behead todo;\n'
  '    if(input.`2=suffix){\n'
  '     hout<-oget log.[input];\n'
  '     candidate<@SimEncrypt(G).run(pk,input.`1,hout);\n'
  '     if(candidate=Some ct){answer<-Some(payload_shared_key hout);}\n'
  '    }\n'
  '   }\n'
  '  }\n'
  '  return answer;\n'
  ' }\n'
  '}.'),
 ('lookup-matches-the-public-F-suffix',
  'ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimLookup.ec',
  'module SimLookup(G:FOGPort) : CCADecapPort = {\n'
  ' proc decap(ct:W8.t Array1152.t) : cca_reply = {\n'
  '  var answer:cca_reply;var star:W8.t Array1152.t option;\n'
  '  var pk:W8.t Array1152.t;var suffix:W8.t Array32.t;\n'
  '  var log:(fo_h_input,W8.t Array224.t)fmap;var todo:fo_h_input list;\n'
  '  var input:fo_h_input;var hout:W8.t Array224.t;var candidate:W8.t Array1152.t option;\n'
  '  answer<-None;\n'
  '  SimPublic.count<-SimPublic.count+1;\n'
  '  star<-SimPublic.cstar;\n'
  '  if(star<>Some ct){\n'
  '   pk<-SimPublic.pk;suffix<-SimPublic.suffix;log<-SimHistory.h;\n'
  '   todo<-elems(fdom log);\n'
  '   while(todo<>[] /\\ answer=None){\n'
  '    input<-head witness todo;todo<-behead todo;\n'
  '    if(input.`2=suffix){\n'
  '     hout<-oget log.[input];\n'
  '     candidate<@SimEncrypt(G).run(pk,input.`1,hout);\n'
  '     if(candidate=Some ct){answer<-Some(payload_shared_key hout);}\n'
  '    }\n'
  '   }\n'
  '  }\n'
  '  return answer;\n'
  ' }\n'
  '}.',
  'module SimLookup(G:FOGPort) : CCADecapPort = {\n'
  ' proc decap(ct:W8.t Array1152.t) : cca_reply = {\n'
  '  var answer:cca_reply;var star:W8.t Array1152.t option;\n'
  '  var pk:W8.t Array1152.t;var suffix:W8.t Array32.t;\n'
  '  var log:(fo_h_input,W8.t Array224.t)fmap;var todo:fo_h_input list;\n'
  '  var input:fo_h_input;var hout:W8.t Array224.t;var candidate:W8.t Array1152.t option;\n'
  '  answer<-None;\n'
  '  SimPublic.count<-SimPublic.count+1;\n'
  '  star<-SimPublic.cstar;\n'
  '  if(star<>Some ct){\n'
  '   pk<-SimPublic.pk;suffix<-SimPublic.suffix;log<-SimHistory.h;\n'
  '   todo<-elems(fdom log);\n'
  '   while(todo<>[] /\\ answer=None){\n'
  '    input<-head witness todo;todo<-behead todo;\n'
  '    if(true){\n'
  '     hout<-oget log.[input];\n'
  '     candidate<@SimEncrypt(G).run(pk,input.`1,hout);\n'
  '     if(candidate=Some ct){answer<-Some(payload_shared_key hout);}\n'
  '    }\n'
  '   }\n'
  '  }\n'
  '  return answer;\n'
  ' }\n'
  '}.'),
 ('lookup-regenerates-through-actual-CBD-G-SOTP-PKE',
  'ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimLookup.ec',
  'r <@ '
  'NTRUPlus768PolyCBD1Checked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(witness,complete_hash_tail '
  'hout);\n'
  '  pad <@ FOHashG(FOGHash(G)).run(r);\n'
  '  code <@ SOTPEncode.run(msg,pad);\n'
  '  ct <@ PKEEnc.run(pk,code,r);\n'
  '  return ct;',
  'r <@ '
  'NTRUPlus768PolyCBD1Checked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(witness,complete_hash_tail '
  'hout);\n'
  '  pad <@ FOHashG(FOGHash(G)).run(r);\n'
  '  code <@ SOTPEncode.run(msg,pad);\n'
  '  ct <- Some witness;\n'
  '  return ct;'),
 ('candidate-uniqueness-needs-good-cache',
  'ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimCandidate.ec',
  'lemma sim_table_matches_unique w g excluded hstar cstar\n'
  ' (tab:(fo_h_input,W8.t Array224.t)fmap) (x1 x2:fo_h_input) hout1 hout2 ct :\n'
  ' pke_key_relation w=>fo_hcache_good w g excluded tab=>\n'
  ' fo_challenge_invariant w g excluded hstar cstar tab=>ct<>cstar=>\n'
  ' x1.`2=complete_sk_suffix w.`kg_sk=>x2.`2=complete_sk_suffix w.`kg_sk=>\n'
  ' tab.[x1]=Some hout1=>tab.[x2]=Some hout2=>\n'
  ' fo_reencryption w g x1.`1 hout1=Some ct=>fo_reencryption w g x2.`1 hout2=Some ct=>\n'
  ' x1=x2 /\\ hout1=hout2 /\\ payload_shared_key hout1=payload_shared_key hout2.',
  'lemma sim_table_matches_unique w g excluded hstar cstar\n'
  ' (tab:(fo_h_input,W8.t Array224.t)fmap) (x1 x2:fo_h_input) hout1 hout2 ct :\n'
  ' pke_key_relation w=>\n'
  ' fo_challenge_invariant w g excluded hstar cstar tab=>ct<>cstar=>\n'
  ' x1.`2=complete_sk_suffix w.`kg_sk=>x2.`2=complete_sk_suffix w.`kg_sk=>\n'
  ' tab.[x1]=Some hout1=>tab.[x2]=Some hout2=>\n'
  ' fo_reencryption w g x1.`1 hout1=Some ct=>fo_reencryption w g x2.`1 hout2=Some ct=>\n'
  ' x1=x2 /\\ hout1=hout2 /\\ payload_shared_key hout1=payload_shared_key hout2.'),
 ('candidate-uniqueness-needs-actual-map-lookups',
  'ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimCandidate.ec',
  'lemma sim_table_matches_unique w g excluded hstar cstar\n'
  ' (tab:(fo_h_input,W8.t Array224.t)fmap) (x1 x2:fo_h_input) hout1 hout2 ct :\n'
  ' pke_key_relation w=>fo_hcache_good w g excluded tab=>\n'
  ' fo_challenge_invariant w g excluded hstar cstar tab=>ct<>cstar=>\n'
  ' x1.`2=complete_sk_suffix w.`kg_sk=>x2.`2=complete_sk_suffix w.`kg_sk=>\n'
  ' tab.[x1]=Some hout1=>tab.[x2]=Some hout2=>\n'
  ' fo_reencryption w g x1.`1 hout1=Some ct=>fo_reencryption w g x2.`1 hout2=Some ct=>\n'
  ' x1=x2 /\\ hout1=hout2 /\\ payload_shared_key hout1=payload_shared_key hout2.',
  'lemma sim_table_matches_unique w g excluded hstar cstar\n'
  ' (tab:(fo_h_input,W8.t Array224.t)fmap) (x1 x2:fo_h_input) hout1 hout2 ct :\n'
  ' pke_key_relation w=>fo_hcache_good w g excluded tab=>\n'
  ' fo_challenge_invariant w g excluded hstar cstar tab=>ct<>cstar=>\n'
  ' x1.`2=complete_sk_suffix w.`kg_sk=>x2.`2=complete_sk_suffix w.`kg_sk=>\n'
  ' \n'
  ' fo_reencryption w g x1.`1 hout1=Some ct=>fo_reencryption w g x2.`1 hout2=Some ct=>\n'
  ' x1=x2 /\\ hout1=hout2 /\\ payload_shared_key hout1=payload_shared_key hout2.'),
 ('freshness-is-physical-H-membership',
  'ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimSpreadHash.ec',
  'lemma sim_answer_actual_fresh_bound w g q0 gm0 hm0 :\n'
  ' pke_key_relation w=>q0.`sr_pk=w.`kg_pk=>acwc2_cache_matches g gm0=>\n'
  ' sim_h_input q0 \\notin hm0=>\n'
  ' phoare[SimAnswerReal(FOGActual,SimHActual).answer:\n'
  ' q=q0 /\\ ROG.m=gm0 /\\ ROH.m=hm0 ==>res<>None]\n'
  ' <=(1%r/(2%r^768)+fo_error w g).',
  'lemma sim_answer_actual_fresh_bound w g q0 gm0 hm0 :\n'
  ' pke_key_relation w=>q0.`sr_pk=w.`kg_pk=>acwc2_cache_matches g gm0=>\n'
  ' sim_h_input q0 \\notin SimHistory.h=>\n'
  ' phoare[SimAnswerReal(FOGActual,SimHActual).answer:\n'
  ' q=q0 /\\ ROG.m=gm0 /\\ ROH.m=hm0 ==>res<>None]\n'
  ' <=(1%r/(2%r^768)+fo_error w g).'),
 ('fixed-setup-bound-retains-rho-plus-error',
  'ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimSpreadHash.ec',
  'lemma sim_answer_actual_fresh_bound w g q0 gm0 hm0 :\n'
  ' pke_key_relation w=>q0.`sr_pk=w.`kg_pk=>acwc2_cache_matches g gm0=>\n'
  ' sim_h_input q0 \\notin hm0=>\n'
  ' phoare[SimAnswerReal(FOGActual,SimHActual).answer:\n'
  ' q=q0 /\\ ROG.m=gm0 /\\ ROH.m=hm0 ==>res<>None]\n'
  ' <=(1%r/(2%r^768)+fo_error w g).',
  'lemma sim_answer_actual_fresh_bound w g q0 gm0 hm0 :\n'
  ' pke_key_relation w=>q0.`sr_pk=w.`kg_pk=>acwc2_cache_matches g gm0=>\n'
  ' sim_h_input q0 \\notin hm0=>\n'
  ' phoare[SimAnswerReal(FOGActual,SimHActual).answer:\n'
  ' q=q0 /\\ ROG.m=gm0 /\\ ROH.m=hm0 ==>res<>None]\n'
  ' <=(1%r/(2%r^352)).'),
 ('hidden-sampling-does-not-clear-existing-H',
  'ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimAnswer.ec',
  'module SimAnswerSample(H:SimHRO.RO) : SimAnswer = {\n'
  ' proc answer(q:sim_request) : W8.t Array32.t option = {\n'
  '  H.sample(sim_h_input q);\n'
  '  return None;\n'
  ' }\n'
  '}.',
  'module SimAnswerSample(H:SimHRO.RO) : SimAnswer = {\n'
  ' proc answer(q:sim_request) : W8.t Array32.t option = {\n'
  '  H.init();H.sample(sim_h_input q);\n'
  '  return None;\n'
  ' }\n'
  '}.'),
 ('erasure-context-cannot-read-private-bad-flag',
  'ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimAnswerErasure.ec',
  'lemma sim_reject_never_probability\n'
  ' (C<:SimAnswerContext {-ROG,-ROH,-SimGRO.RO,-SimGRO.FRO,-SimHRO.RO,-SimHRO.FRO,-SimBad})\n'
  ' g &m s0 (event:bool->bool) : acwc2_cache_matches g ROG.m{m}=>\n'
  ' Pr[SimRejectWorld(C,SimHRO.RO).distinguish(s0) @ &m:event res]=\n'
  ' Pr[SimNeverWorld(C,SimHRO.RO).distinguish(s0) @ &m:event res].',
  'lemma sim_reject_never_probability\n'
  ' (C<:SimAnswerContext {-ROG,-ROH,-SimGRO.RO,-SimGRO.FRO,-SimHRO.RO,-SimHRO.FRO})\n'
  ' g &m s0 (event:bool->bool) : acwc2_cache_matches g ROG.m{m}=>\n'
  ' Pr[SimRejectWorld(C,SimHRO.RO).distinguish(s0) @ &m:event res]=\n'
  ' Pr[SimNeverWorld(C,SimHRO.RO).distinguish(s0) @ &m:event res].'),
 ('public-game-obtains-F-suffix-through-public-oracle',
  'ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimGames.ec',
  'module SimPublicChallenge(A:CCAExtendedAdversary,G:FOGPort,H:SimHPort) = {\n'
  ' proc run(pk:W8.t Array1152.t) : bool = {\n'
  '  var real:encap_result;var random,suffix:W8.t Array32.t;var bit,guess:bool;\n'
  '  real<@EncapRandom(SHAKEFROM,FOGHash(G),SimHShake(H),UniformCoins).run(pk,witness);\n'
  '  random<$uniform32;bit<$dbool;\n'
  '  suffix<@ROF.get(pk);\n'
  '  SimPublic.init(pk,suffix,real.`1);SimHistory.init();\n'
  '  guess<@A(SimOracles(G,H),SimLookup(G)).guess(pk,real.`1,if bit then random else real.`2);\n'
  '  return guess=bit;\n'
  ' }\n'
  '}.',
  'module SimPublicChallenge(A:CCAExtendedAdversary,G:FOGPort,H:SimHPort) = {\n'
  ' proc run(pk:W8.t Array1152.t) : bool = {\n'
  '  var real:encap_result;var random,suffix:W8.t Array32.t;var bit,guess:bool;\n'
  '  real<@EncapRandom(SHAKEFROM,FOGHash(G),SimHShake(H),UniformCoins).run(pk,witness);\n'
  '  random<$uniform32;bit<$dbool;\n'
  '  suffix<-complete_sk_suffix CCADecapOracle.sk;\n'
  '  SimPublic.init(pk,suffix,real.`1);SimHistory.init();\n'
  '  guess<@A(SimOracles(G,H),SimLookup(G)).guess(pk,real.`1,if bit then random else real.`2);\n'
  '  return guess=bit;\n'
  ' }\n'
  '}.'),
 ('public-game-never-installs-secret-in-Decaps-state',
  'ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimGames.ec',
  'module SimPublicFreshGame(A:CCAExtendedAdversary) = {\n'
  ' proc run() : bool = {\n'
  '  var pk:W8.t Array1152.t;var sk:W8.t Array2336.t;var win:bool;\n'
  '  ROMInit.init();RawXOFStreams.init();\n'
  '  (pk,sk)<@Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run();\n'
  '  win<@SimPublicChallenge(A,FOGActual,SimHActual).run(pk);\n'
  '  return win;\n'
  ' }\n'
  '}.',
  'module SimPublicFreshGame(A:CCAExtendedAdversary) = {\n'
  ' proc run() : bool = {\n'
  '  var pk:W8.t Array1152.t;var sk:W8.t Array2336.t;var win:bool;\n'
  '  ROMInit.init();RawXOFStreams.init();\n'
  '  (pk,sk)<@Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run();\n'
  '  CCADecapOracle.sk<-sk;win<@SimPublicChallenge(A,FOGActual,SimHActual).run(pk);\n'
  '  return win;\n'
  ' }\n'
  '}.'),
 ('two-hop-error-has-qD-and-qH-contributions',
  'ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimAverage.ec',
  'lemma sim_setup_win_distance &m (K0 K1:fo_setup_observation->bool distr) qD qH :\n'
  ' 0<=qD=>0<=qH=>\n'
  ' (forall s,s \\in mk(fun z=>Pr[FOSetupSource.guess(witness) @ &m:res=z])=>\n'
  '  `|mu1(K0 s)true-mu1(K1 s)true|<=qD%r/(2%r^768)+(qH+qD)%r*fo_setup_error s)=>\n'
  ' `|mu1(dlet(mk(fun z=>Pr[FOSetupSource.guess(witness) @ &m:res=z]))K0)true-\n'
  '   mu1(dlet(mk(fun z=>Pr[FOSetupSource.guess(witness) @ &m:res=z]))K1)true|\n'
  ' <=qD%r/(2%r^768)+(qH+qD)%r/(2%r^353).',
  'lemma sim_setup_win_distance &m (K0 K1:fo_setup_observation->bool distr) qD qH :\n'
  ' 0<=qD=>0<=qH=>\n'
  ' (forall s,s \\in mk(fun z=>Pr[FOSetupSource.guess(witness) @ &m:res=z])=>\n'
  '  `|mu1(K0 s)true-mu1(K1 s)true|<=qD%r/(2%r^768)+(qH+qD)%r*fo_setup_error s)=>\n'
  ' `|mu1(dlet(mk(fun z=>Pr[FOSetupSource.guess(witness) @ &m:res=z]))K0)true-\n'
  '   mu1(dlet(mk(fun z=>Pr[FOSetupSource.guess(witness) @ &m:res=z]))K1)true|\n'
  ' <=qD%r/(2%r^768)+qD%r/(2%r^353).'),
 ('averaging-keeps-pointwise-support-obligation',
  'ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimAverage.ec',
  'lemma sim_setup_win_distance &m (K0 K1:fo_setup_observation->bool distr) qD qH :\n'
  ' 0<=qD=>0<=qH=>\n'
  ' (forall s,s \\in mk(fun z=>Pr[FOSetupSource.guess(witness) @ &m:res=z])=>\n'
  '  `|mu1(K0 s)true-mu1(K1 s)true|<=qD%r/(2%r^768)+(qH+qD)%r*fo_setup_error s)=>\n'
  ' `|mu1(dlet(mk(fun z=>Pr[FOSetupSource.guess(witness) @ &m:res=z]))K0)true-\n'
  '   mu1(dlet(mk(fun z=>Pr[FOSetupSource.guess(witness) @ &m:res=z]))K1)true|\n'
  ' <=qD%r/(2%r^768)+(qH+qD)%r/(2%r^353).',
  'lemma sim_setup_win_distance &m (K0 K1:fo_setup_observation->bool distr) qD qH :\n'
  ' 0<=qD=>0<=qH=>\n'
  ' (forall s,true=>\n'
  '  `|mu1(K0 s)true-mu1(K1 s)true|<=qD%r/(2%r^768)+(qH+qD)%r*fo_setup_error s)=>\n'
  ' `|mu1(dlet(mk(fun z=>Pr[FOSetupSource.guess(witness) @ &m:res=z]))K0)true-\n'
  '   mu1(dlet(mk(fun z=>Pr[FOSetupSource.guess(witness) @ &m:res=z]))K1)true|\n'
  ' <=qD%r/(2%r^768)+(qH+qD)%r/(2%r^353).'),
 ('selected-guard-discharged-from-physical-cover',
  'ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimSelectedInvariant.ec',
  'lemma sim_selected_reject_guarded\n'
  ' (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,\n'
  '  -SimPublic,-SimHistory,-FOContext,-SimBad,-SimSelectedFixed,-SimPhaseInput,-FOBudgetState,\n'
  '  -SH.HB.Count,-SH.HB.HybOrcl}) w0 g0 :\n'
  ' equiv[SimSelectedReject(A).distinguish ~ SimSelectedGuarded(A).run:\n'
  ' w{2}=w0 /\\ g{2}=g0 /\\ ={s,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob '
  'SimPublic,glob SimHistory,glob FOContext,glob CCADecapOracle,glob SimBad,glob SH.HB.HybOrcl,glob '
  'FOBudgetState,glob SimPhaseInput} /\\\n'
  ' SimPublic.pk{1}=w0.`kg_pk /\\ acwc2_cache_matches g0 ROG.m{1} /\\\n'
  ' sim_log_included SimHistory.h{1} ROH.m{1} /\\ sim_h_cover SimHistory.h{1} ROH.m{1} '
  'FOContext.challenge_h{1} ==>\n'
  ' ={res,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob SimPublic,glob SimHistory,glob '
  'FOContext,glob CCADecapOracle,glob SimBad,glob SH.HB.HybOrcl,glob FOBudgetState,glob SimPhaseInput}].',
  'lemma sim_selected_reject_guarded\n'
  ' (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,\n'
  '  -SimPublic,-SimHistory,-FOContext,-SimBad,-SimSelectedFixed,-SimPhaseInput,-FOBudgetState,\n'
  '  -SH.HB.Count,-SH.HB.HybOrcl}) w0 g0 :\n'
  ' equiv[SimSelectedReject(A).distinguish ~ SimSelectedGuarded(A).run:\n'
  ' w{2}=w0 /\\ g{2}=g0 /\\ ={s,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob '
  'SimPublic,glob SimHistory,glob FOContext,glob CCADecapOracle,glob SimBad,glob SH.HB.HybOrcl,glob '
  'FOBudgetState,glob SimPhaseInput} /\\\n'
  ' SimPublic.pk{1}=w0.`kg_pk /\\ acwc2_cache_matches g0 ROG.m{1} /\\\n'
  ' sim_log_included SimHistory.h{1} ROH.m{1} /\\ true ==>\n'
  ' ={res,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob SimPublic,glob SimHistory,glob '
  'FOContext,glob CCADecapOracle,glob SimBad,glob SH.HB.HybOrcl,glob FOBudgetState,glob SimPhaseInput}].'),
 ('selected-win-projection-keeps-robust-losslessness',
  'ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimSelectedBound.ec',
  'lemma sim_selected_distance_bad\n'
  ' (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,\n'
  '  -FOPublicKey,-FOContext,-FOBadState,-FOBudgetState,-SimPublic,-SimHistory,-SimBad,\n'
  '  -SimSelectedFixed,-SimPhaseInput,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,\n'
  '  -SH.HB.Count,-SH.HB.HybOrcl}) g s0 &m :\n'
  ' acwc2_cache_matches g ROG.m{m}=>\n'
  ' (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),\n'
  '  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>\n'
  '  islossless D.decap=>islossless A(H,D).guess)=>\n'
  ' `|Pr[SimSelectedReal(A).distinguish(s0) @ &m:res]-\n'
  '   Pr[SimSelectedNever(A).distinguish(s0) @ &m:res]|\n'
  ' <=Pr[SimSelectedReject(A).distinguish(s0) @ &m:SimBad.hidden].',
  'lemma sim_selected_distance_bad\n'
  ' (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,\n'
  '  -FOPublicKey,-FOContext,-FOBadState,-FOBudgetState,-SimPublic,-SimHistory,-SimBad,\n'
  '  -SimSelectedFixed,-SimPhaseInput,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,\n'
  '  -SH.HB.Count,-SH.HB.HybOrcl}) g s0 &m :\n'
  ' acwc2_cache_matches g ROG.m{m}=>\n'
  ' (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),\n'
  '  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>\n'
  '  true)=>\n'
  ' `|Pr[SimSelectedReal(A).distinguish(s0) @ &m:res]-\n'
  '   Pr[SimSelectedNever(A).distinguish(s0) @ &m:res]|\n'
  ' <=Pr[SimSelectedReject(A).distinguish(s0) @ &m:SimBad.hidden].')]

from transport_contract import RULES as TRANSPORT_RULES, MUTATIONS as TRANSPORT_MUTATIONS
RULES += TRANSPORT_RULES
MUTATIONS += TRANSPORT_MUTATIONS

def check_model(read, ordered, require):
    from check_fo_simulation import compact
    for relative, label, expected in RULES:
        require(compact(expected).replace('op[opaque]', 'op') in
                read(relative).replace('op[opaque]', 'op'), label)
