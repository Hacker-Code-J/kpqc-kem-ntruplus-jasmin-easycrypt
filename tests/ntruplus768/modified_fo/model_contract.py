"""Reviewed full modified-FO call and probability boundaries, not a proof parser."""
PREFIX = 'ntruplus/proof/768/ref/kem_modified_fo/'
RULES = []
MUTATIONS = []

def protects(file, label, expected, old, new):
    path = PREFIX+'NTRUPlus768'+file+'.ec'
    RULES.append((path, label, expected))
    MUTATIONS.append((label, path, old, new))

protects('FOModel', 'single-entry-base-event',
 r'''op fo_base_bad (w:keygen_witness) (g:acwc2_g_function)
 (msg:W8.t Array96.t) (hout:W8.t Array224.t) =
 acwc2_pad_bad w msg (fo_randomness hout) (g(fo_randomness hout)).''',
 'acwc2_pad_bad w msg (fo_randomness hout) (g(fo_randomness hout))',
 'acwc2_failure g w.`kg_pk w.`kg_sk msg (fo_randomness hout)')
protects('FOModel', 'fixed-key-and-G-before-message-max',
 r'''op fo_error (w:keygen_witness) (g:acwc2_g_function) =
 acwc2_finite_max acwc2_message_enum (fun msg=>acwc2_weighted_bad w msg g).''',
 'acwc2_finite_max acwc2_message_enum (fun msg=>acwc2_weighted_bad w msg g)',
 'acwc2_weighted_bad w witness g')
protects('FOErrorExpectation', 'actual-fresh-key-and-independent-G-mean',
 r'''lemma fo_fresh_expected_error_pads &m :
 E (mk(fun z=>Pr[KeygenSource(FreshExpand).guess(witness) @ &m:res=z]))
  (fun (out:keygen_output)=>E acwc2_gpads_law(fun (pads:W8.t Array192.t list)=>fo_error out.`1 (acwc2_gfun pads)))
 <1%r/(2%r^353).''',
 'lemma fo_fresh_expected_error_pads &m :',
 'lemma fo_fresh_expected_error_pads &m : (forall w g,fo_error w g<1%r/(2%r^353))=>')
protects('FOChallenge', 'challenge-reencryption-excludes-other-ciphertexts',
 r'''lemma fo_challenge_cached_other w g excluded hstar cstar hm input hout ct :
 fo_challenge_invariant w g excluded hstar cstar hm =>
 Some input=excluded =>hm.[input]=Some hout =>ct<>cstar =>
 pke_enc_spec w.`kg_pk
  (poly_sotp_encode_spec input.`1 (g(fo_randomness hout)))
  (fo_randomness hout)<>Some ct.''',
 'Some input=excluded =>hm.[input]=Some hout =>ct<>cstar =>',
 'Some input=excluded =>hm.[input]=Some hout =>')
protects('FOHMonitor', 'fresh-nonchallenge-only-monitor',
 r'''fresh <- input \notin ROH.m /\ Some input<>FOContext.challenge_h;
 result <@ ROH.get(input);
 if(fresh){
  FOBadState.fresh <- FOBadState.fresh+1;
  FOBadState.bad <- FOBadState.bad \/ fo_base_bad FOContext.w FOContext.g input.`1 result;
 }''',
 r'fresh <- input \notin ROH.m /\ Some input<>FOContext.challenge_h;',
 r'fresh <- Some input<>FOContext.challenge_h;')
protects('FOHMonitor', 'monitor-uses-existing-lazy-H',
 'result <@ ROH.get(input);',
 'result <@ ROH.get(input);', 'result <$ uniform224;')
protects('FOHMonitor', 'bad-event-latches',
 r'FOBadState.bad <- FOBadState.bad \/ fo_base_bad FOContext.w FOContext.g input.`1 result;',
 r'FOBadState.bad <- FOBadState.bad \/ fo_base_bad FOContext.w FOContext.g input.`1 result;',
 r'FOBadState.bad <- fo_base_bad FOContext.w FOContext.g input.`1 result;')
protects('FOAlgebra', 'official-recovered-randomness-membership',
 r'''op fo_full_accept (w:keygen_witness) (g:acwc2_g_function) (ct:W8.t Array1152.t)
 (pad:W8.t Array192.t) (hout:W8.t Array224.t) =
 complete_entry_accepts ct w.`kg_sk /\ !fo_candidate_failed w ct pad /\
 rrec_spec w.`kg_pk (rrec_native_message w ct) ct<>None /\
 fo_reencryption w g (fo_candidate_message w ct pad) hout=Some ct.''',
 'rrec_spec w.`kg_pk (rrec_native_message w ct) ct<>None', 'true')
protects('FOAlgebra', 'base-good-is-needed-for-reverse-comparison',
 r'''lemma fo_full_implies_native w g ct pad hout :pke_key_relation w=>
 fo_full_accept w g ct pad hout=>!fo_base_bad w g (fo_candidate_message w ct pad) hout=>
 fo_native_accept w ct pad hout.''',
 'lemma fo_full_implies_native w g ct pad hout :pke_key_relation w=>fo_full_accept w g ct pad hout=>!fo_base_bad w g (fo_candidate_message w ct pad) hout=>',
 'lemma fo_full_implies_native w g ct pad hout :pke_key_relation w=>fo_full_accept w g ct pad hout=>')
protects('FOProcedures', 'recovered-randomness-check-is-actual-call',
 'recovered <@ LinearRRec.run(pk,m1,ct);',
 'recovered <@ LinearRRec.run(pk,m1,ct);', 'recovered <- Some m1;')
protects('FOProcedures', 'full-regeneration-actual-G-SOTP-PKE-chain',
 r'''r1 <@ NTRUPlus768PolyCBD1Checked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(witness,complete_hash_tail hashout);
 pad <@ FOHashG(G).run(r1);
 code <@ SOTPEncode.run(msg,pad);
 ct2 <@ PKEEnc.run(pk,code,r1);''',
 'code <@ SOTPEncode.run(msg,pad);', 'code <- m1;')
protects('FOProcedures', 'regeneration-queries-G-at-rH',
 'pad <@ FOHashG(G).run(r1);',
 'pad <@ FOHashG(G).run(r1);', 'pad <@ FOHashG(G).run(oget recovered);')
protects('FOProcedures', 'both-option-rejections-reach-actual-finish',
 r'''failed <- W32.of_int(b2i(decoded=None \/ recovered=None));
 ss <- encap_zero_ss; status <- W32.one;
 if(ct2<>None){
 (ss,status) <@ NTRUPlus768DecapFinish.M.jade_ntruplus_ntruplus768_amd64_ref_decap_finish(witness,hashout,ct,oget ct2,failed);
 }''',
 r'failed <- W32.of_int(b2i(decoded=None \/ recovered=None));',
 r'failed <- W32.of_int(b2i(decoded=None));')
protects('FOProcedures', 'native-entry-reject-skips-hashes-but-decode-fail-keeps-H',
 r'''(rp,mp,ss,status) <@ GuardedR2.run(witness,witness,witness,witness,witness,encap_zero_ss,ct,complete_sk_poly sk);
 if(status=W32.zero){
 (bs,msg,status) <@ DecapMessage(G).run(witness,witness,witness,rp,mp);
 (ss,status) <@ FOTail(G,H).run(pk,ct,mp,msg,status,complete_sk_suffix sk);
 }''',
 '(ss,status) <@ FOTail(G,H).run(pk,ct,mp,msg,status,complete_sk_suffix sk);',
 'if(status=W32.zero){ (ss,status) <@ FOTail(G,H).run(pk,ct,mp,msg,status,complete_sk_suffix sk); }')
protects('FOProcedures', 'H-call-precedes-full-regeneration',
 r'''input <@ NTRUPlus768DecapHashHPrepare.M.jade_ntruplus_ntruplus768_amd64_ref_decap_hash_h_prepare(witness,msg,suffix);
 hashout <@ H.shake(input);
 result <@ FORegenerateFinish(G).run(pk,ct,m1,msg,hashout,decode_fail);''',
 'hashout <@ H.shake(input);', 'hashout <$ uniform224;')
protects('FOProcedures', 'actual-workspace-clear',
 'workspace <@ NTRUPlus768DecapClear.M.jade_ntruplus_ntruplus768_amd64_ref_decap_clear(workspace);',
 'workspace <@ NTRUPlus768DecapClear.M.jade_ntruplus_ntruplus768_amd64_ref_decap_clear(workspace);',
 'workspace <- witness;')
protects('FOEagerG', 'finite-trit-image-only',
 'op fo_g_inputs = map rr_G_input acwc2_r_enum.',
 'op fo_g_inputs = map rr_G_input acwc2_r_enum.',
 'op fo_g_inputs = all_byte_inputs.')
protects('FOEagerG', 'private-completion-respects-existing-sample-semantics',
 r'''todo <- fo_g_inputs;
 while(todo<>[]){
 G.sample(head witness todo);
 todo <- behead todo;
 }''',
 'G.sample(head witness todo);', 'G.init(); G.sample(head witness todo);')


protects('FOQueryBudget', 'effective-raw-H-tag-length-and-output-cap',
 r"""op fo_raw_h (input:W8.t list) (outlen:int) =
 0<=outlen<=raw_xof_max_output /\ size input=129 /\ nth W8.zero input 0=W8.of_int 2.""",
 '0<=outlen<=raw_xof_max_output', '0<outlen<=raw_xof_max_output')
protects('FOQueryBudget', 'H-and-D-share-one-admission-budget',
 'allowed <- FOBudgetState.nH+FOBudgetState.nD<FOBudgetState.limit; FOBudgetState.nH <- FOBudgetState.nH+1;',
 'allowed <- FOBudgetState.nH+FOBudgetState.nD<FOBudgetState.limit;',
 'allowed <- FOBudgetState.nH<FOBudgetState.limit;')
protects('FOQueryBudget', 'denied-H-has-no-backend-call',
 r"""allowed <@ FOQueryRequest.h(); result <- witness;
 if(allowed){result <@ H.h(input);}
 FOBudgetState.nH<-FOBudgetState.nH;
 return result;""",
 'if(allowed){result <@ H.h(input);}', 'result <@ H.h(input);')
protects('FOQueryBudget', 'denied-raw-H-has-no-backend-call',
 r"""allowed <- true;
 if(fo_raw_h input outlen){allowed <@ FOQueryRequest.h();}
 result <- None;
 if(allowed){result <@ H.raw(input,outlen);}
 FOBudgetState.nH<-FOBudgetState.nH;
 return result;""",
 'if(allowed){result <@ H.raw(input,outlen);}', 'result <@ H.raw(input,outlen);')
protects('FOQueryBudget', 'all-D-attempts-count-before-forward-or-denial',
 r"""allowed <@ FOQueryRequest.d(); result <- None;
 if(allowed){result <@ D.decap(ct);}
 FOBudgetState.nD<-FOBudgetState.nD;
 return result;""",
 'allowed <@ FOQueryRequest.d(); result <- None;', 'allowed <- true; result <- None;')
protects('FOKEMGame', 'blocked-challenge-counted-before-native-decapsulation',
 r"""CCADecapOracle.count<-CCADecapOracle.count+1;
 if(CCADecapOracle.cstar=Some ct){answer<-None;}
 else{
 result <@ CompleteDecaps(G,H).run(ct,CCADecapOracle.sk,witness);
 answer<-cca_status_result result.`1 result.`2;
 }""",
 'CCADecapOracle.count<-CCADecapOracle.count+1;',
 'CCADecapOracle.count<-CCADecapOracle.count;')

from endpoint_contract import RULES as ENDPOINT_RULES, MUTATIONS as ENDPOINT_MUTATIONS
RULES += ENDPOINT_RULES
MUTATIONS += ENDPOINT_MUTATIONS

def check_model(read, ordered, require):
    from check_modified_fo import compact
    for relative, label, expected in RULES:
        require(compact(expected).replace('op[opaque]', 'op') in
                read(relative).replace('op[opaque]', 'op'), label)
