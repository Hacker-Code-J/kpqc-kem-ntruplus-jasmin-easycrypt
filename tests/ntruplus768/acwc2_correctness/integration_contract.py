"""Actual failure probabilities, fixed-table maxima, and concrete key averaging."""
BASE='ntruplus/proof/768/ref/acwc2_correctness/'
ERROR=BASE+'NTRUPlus768ACWC2Error.ec'
EXECUTION=BASE+'NTRUPlus768ACWC2Execution.ec'
KEYMEAN=BASE+'NTRUPlus768ACWC2KeyMean.ec'
WORST=BASE+'NTRUPlus768ACWC2WorstCase.ec'
RULES=(
 (ERROR,'message error samples the biased CBD randomness after fixing the G table',r'op acwc2_message_error (w:keygen_witness) (g:acwc2_g_function) (msg:W8.t Array96.t) = mu pke_psi1 (fun r=>acwc2_failure g w.`kg_pk w.`kg_sk msg r).'),
 (ERROR,'message maximum is conditional on the same fixed key and fixed table',r'op acwc2_worst_error (w:keygen_witness) (g:acwc2_g_function) = acwc2_finite_max acwc2_message_enum (fun msg=>acwc2_message_error w g msg).'),
 (ERROR,'actual complete failure is bounded by the base envelope under the valid-key law only',r'lemma acwc2_message_error_bound w g msg : pke_key_relation w => acwc2_message_error w g msg<=acwc2_weighted_bad w msg g.'),
 (EXECUTION,'trial samples one fresh buffer and invokes the actual CBD and ROM roundtrip without resetting G',r'module ACWC2RandomTrial = { proc run(pk:W8.t Array1152.t,sk:W8.t Array2336.t,msg:W8.t Array96.t) : bool = { var buf:W8.t Array192.t; var r:pke_poly; var failed:bool; buf <$ uniform192; r <@ NTRUPlus768PolyCBD1Checked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(witness,buf); failed <@ ACWC2ROMRoundTrip.run(pk,sk,msg,r); return failed; } }.'),
 (EXECUTION,'conditional error is the actual random trial probability with cache agreement only',r'lemma acwc2_random_trial_error &m w g msg : acwc2_cache_matches g ROG.m{m} => Pr[ACWC2RandomTrial.run(w.`kg_pk,w.`kg_sk,msg) @ &m:res]=acwc2_message_error w g msg.'),
 (EXECUTION,'fixed-oracle trial installs exactly its supplied table before the actual random trial',r'module ACWC2FixedOracleTrial = { proc run(pads:W8.t Array192.t list,pk:W8.t Array1152.t,sk:W8.t Array2336.t,msg:W8.t Array96.t) : bool = { var failed:bool; ROG.init(); ACWC2EagerOracle.prepare(pads); failed <@ ACWC2RandomTrial.run(pk,sk,msg); return failed; } }.'),
 (EXECUTION,'fixed supplied table removes the cache premise without resampling G',r'lemma acwc2_fixed_oracle_trial_error &m w pads msg : Pr[ACWC2FixedOracleTrial.run(pads,w.`kg_pk,w.`kg_sk,msg) @ &m:res]=acwc2_message_error w (acwc2_gfun pads) msg.'),
 (KEYMEAN,'actual accepted fresh-key mean is identified with the existing actual PKE average',r'lemma acwc2_fresh_key_mean_identity &m : E (mk(fun z=>Pr[KeygenSource(FreshExpand).guess(witness) @ &m:res=z])) (fun (out:keygen_output)=>acwc2_base_mean out.`1)=Pr[PKEAverage(FreshExpand).run() @ &m:res].'),
 (KEYMEAN,'concrete actual fresh-key average bound has no additional assumptions',r'lemma acwc2_fresh_key_mean_bound &m : E (mk(fun z=>Pr[KeygenSource(FreshExpand).guess(witness) @ &m:res=z])) (fun (out:keygen_output)=>acwc2_base_mean out.`1)<1%r/(2%r^354).'),
 (WORST,'outer key and G expectations preserve the conditional message maximum',r'op acwc2_expected_worst_error (dk:keygen_output distr) = E dk(fun (out:keygen_output)=>E acwc2_eager_g_law(fun g=>acwc2_worst_error out.`1 g)).'),
 (WORST,'final unconditional bound names actual fresh KeyGen and actual trials below both expectations and the message maximum',r'lemma acwc2_fresh_worst_actual_calls &m : E (mk(fun z=>Pr[KeygenSource(FreshExpand).guess(witness) @ &m:res=z])) (fun (out:keygen_output)=>E acwc2_gpads_law (fun (pads:W8.t Array192.t list)=>acwc2_finite_max acwc2_message_enum (fun (msg:W8.t Array96.t)=> Pr[ACWC2FixedOracleTrial.run(pads,out.`1.`kg_pk,out.`1.`kg_sk,msg) @ &m:res]))) <1%r/(2%r^353).'),
)
MUTATIONS=(
 ('message-error-replaces-CBD-with-uniform-trits',ERROR,'mu pke_psi1 (fun r=>acwc2_failure','mu (duniform acwc2_r_enum) (fun r=>acwc2_failure'),
 ('actual-message-error-replaced-by-base-envelope',ERROR,'fun r=>acwc2_failure g w.`kg_pk w.`kg_sk msg r','fun r=>acwc2_pad_bad w msg r (g r)'),
 ('fixed-table-worst-error-moves-G-average-inside-message-maximum',ERROR,'fun msg=>acwc2_message_error w g msg','fun msg=>E acwc2_eager_g_law (fun g=>acwc2_message_error w g msg)'),
 ('failure-envelope-bound-assumed-as-an-extra-premise',ERROR,'lemma acwc2_message_error_bound w g msg : pke_key_relation w =>','lemma acwc2_message_error_bound w g msg : pke_key_relation w => acwc2_message_error w g msg<=acwc2_weighted_bad w msg g =>'),
 ('random-trial-replaces-actual-CBD-with-pure-spec',EXECUTION,'r <@ NTRUPlus768PolyCBD1Checked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(witness,buf);','r <- poly_cbd1_spec buf;'),
 ('random-trial-replaces-actual-ROM-roundtrip-with-pure-spec',EXECUTION,'failed <@ ACWC2ROMRoundTrip.run(pk,sk,msg,r);','failed <- acwc2_failure witness pk sk msg r;'),
 ('random-trial-resets-fixed-G-before-encryption',EXECUTION,'buf <$ uniform192;','ROG.m <- empty; buf <$ uniform192;'),
 ('actual-error-equality-drops-cache-agreement',EXECUTION,'lemma acwc2_random_trial_error &m w g msg : acwc2_cache_matches g ROG.m{m} =>','lemma acwc2_random_trial_error &m w g msg :'),
 ('actual-error-equality-smuggles-in-zero-error-premise',EXECUTION,'lemma acwc2_random_trial_error &m w g msg :','lemma acwc2_random_trial_error &m w g msg : acwc2_message_error w g msg=0%r =>'),
 ('fixed-oracle-trial-reuses-incompatible-prior-cache',EXECUTION,'ROG.init(); ACWC2EagerOracle.prepare(pads);','ACWC2EagerOracle.prepare(pads);'),
 ('fixed-oracle-trial-redraws-G-after-the-message-is-chosen',EXECUTION,'ROG.init(); ACWC2EagerOracle.prepare(pads);','ROG.init(); pads <$ acwc2_gpads_law; ACWC2EagerOracle.prepare(pads);'),
 ('key-mean-identity-substitutes-cached-ROM-keygen',KEYMEAN,'lemma acwc2_fresh_key_mean_identity &m : E (mk(fun z=>Pr[KeygenSource(FreshExpand).guess(witness)','lemma acwc2_fresh_key_mean_identity &m : E (mk(fun z=>Pr[KeygenSource(ExpandROM).guess(witness)'),
 ('concrete-key-average-bound-adds-an-assumed-average',KEYMEAN,'lemma acwc2_fresh_key_mean_bound &m :','lemma acwc2_fresh_key_mean_bound &m : Pr[PKEAverage(FreshExpand).run() @ &m:res]<1%r/(2%r^354) =>'),
 ('final-expectation-moves-key-and-G-inside-message-maximum',WORST,'E dk(fun (out:keygen_output)=>E acwc2_eager_g_law(fun g=>acwc2_worst_error out.`1 g)).','acwc2_finite_max acwc2_message_enum (fun msg=>E dk(fun (out:keygen_output)=>E acwc2_eager_g_law(fun g=>acwc2_message_error out.`1 g msg))).'),
 ('final-actual-bound-assumes-a-small-average',WORST,'lemma acwc2_fresh_worst_actual_calls &m :','lemma acwc2_fresh_worst_actual_calls &m : Pr[PKEAverage(FreshExpand).run() @ &m:res]<1%r/(2%r^354) =>'),
 ('final-actual-bound-substitutes-cached-ROM-keygen',WORST,'lemma acwc2_fresh_worst_actual_calls &m : E (mk(fun z=>Pr[KeygenSource(FreshExpand).guess(witness)','lemma acwc2_fresh_worst_actual_calls &m : E (mk(fun z=>Pr[KeygenSource(ExpandROM).guess(witness)'),
 ('final-actual-bound-replaced-by-reference-trial',WORST,'lemma acwc2_fresh_worst_actual_calls &m : E (mk(fun z=>Pr[KeygenSource(FreshExpand).guess(witness) @ &m:res=z])) (fun (out:keygen_output)=>E acwc2_gpads_law (fun (pads:W8.t Array192.t list)=>acwc2_finite_max acwc2_message_enum (fun (msg:W8.t Array96.t)=> Pr[ACWC2FixedOracleTrial.run','lemma acwc2_fresh_worst_actual_calls &m : E (mk(fun z=>Pr[KeygenSource(FreshExpand).guess(witness) @ &m:res=z])) (fun (out:keygen_output)=>E acwc2_gpads_law (fun (pads:W8.t Array192.t list)=>acwc2_finite_max acwc2_message_enum (fun (msg:W8.t Array96.t)=> Pr[ACWC2RandomSpec.run'),
)
