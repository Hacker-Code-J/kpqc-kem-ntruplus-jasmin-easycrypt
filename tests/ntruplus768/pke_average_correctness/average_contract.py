"""Mean failure events must be computed by the actual PKE array calls."""
BASE='ntruplus/proof/768/ref/pke_average_correctness/'
AVERAGE=BASE+'NTRUPlus768PKEAverageModel.ec'
RULES=(
 (AVERAGE,'actual CBD/Enc/Dec trial compares recovered message including rejection',r'module PKEAverageTrial = { proc run(x:kem_keygen_observation) : bool = { var r,m:pke_poly; var ct:W8.t Array1152.t option; var recovered:pke_poly option; var failed:bool; r <@ NTRUPlus768PolyCBD1Checked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(witness,x.`2); m <@ NTRUPlus768PolyCBD1Checked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(witness,x.`3); ct <@ PKEEnc.run(x.`1.`1.`kg_pk,m,r); failed <- true; if(ct<>None){ recovered <@ PKEDec.run(oget ct,pke_secret_bytes x.`1.`1); failed <- recovered<>Some m; } return failed; } }.'),
 (AVERAGE,'average experiment retains supplied key-expansion model',r'module PKEAverage(E:KeygenExpand) = { proc run() : bool = { var x:kem_keygen_observation; var failed:bool; x <@ KeygenThenUniform(E).run(); failed <@ PKEAverageTrial.run(x); return failed; } }.'),
 (AVERAGE,'ROM experiment initializes E/F then keeps actual ROM key generation',r'module PKEAverageROM = { proc run() : bool = { var failed:bool; ROE.init(); ROF.init(); failed <@ PKEAverage(ExpandROM).run(); return failed; } }.'),
 (AVERAGE,'losslessness belongs to fresh comparison experiment',r'lemma pke_average_fresh_lossless : islossless PKEAverage(FreshExpand).run.'),
)
MUTATIONS=(
 ('message-CBD-reuses-randomness-buffer',AVERAGE,'poly_cbd1(witness,x.`3);','poly_cbd1(witness,x.`2);'),
 ('average-trial-substitutes-pure-Enc-spec',AVERAGE,'ct <@ PKEEnc.run(x.`1.`1.`kg_pk,m,r);','ct <- pke_enc_spec x.`1.`1.`kg_pk m r;'),
 ('average-trial-skips-actual-Dec',AVERAGE,'recovered <@ PKEDec.run(oget ct,pke_secret_bytes x.`1.`1);','recovered <- Some m;'),
 ('average-trial-compares-input-to-itself',AVERAGE,'failed <- recovered<>Some m;','failed <- Some m<>Some m;'),
 ('average-trial-loses-None-rejection',AVERAGE,'failed <- recovered<>Some m;','failed <- oget recovered<>m;'),
 ('average-trial-counts-Enc-rejection-as-success',AVERAGE,'failed <- true;','failed <- false;'),
 ('ROM-average-substitutes-fresh-key-law',AVERAGE,'failed <@ PKEAverage(ExpandROM).run();','failed <@ PKEAverage(FreshExpand).run();'),
 ('ROM-average-retains-stale-initial-E-table',AVERAGE,'ROE.init(); ROF.init();','ROF.init();'),
 ('fresh-totality-misapplied-to-ROM',AVERAGE,'lemma pke_average_fresh_lossless : islossless PKEAverage(FreshExpand).run.','lemma pke_average_fresh_lossless : islossless PKEAverage(ExpandROM).run.'),
)

CORRECTNESS=BASE+'NTRUPlus768PKEAverageCorrectness.ec'
RULES+=(
 (CORRECTNESS,'observing arithmetic preserves the actual keygen return mass',r'lemma pke_average_return_probability (E<:KeygenExpand {-ROF}) &m : Pr[PKEAverage(E).run() @ &m:true]=Pr[KeygenThenUniform(E).run() @ &m:true].'),
 (CORRECTNESS,'fresh bad-event law uses accepted entire buffers',r'lemma pke_fresh_bad_probability &m : Pr[PKEAverageObserved(FreshExpand).run() @ &m:res.`2]= mu accepted_four_law four_buffers_bad.'),
 (CORRECTNESS,'dropping actual arithmetic explicitly discharges its losslessness',r'call{1} pke_average_trial_lossless.'),
)
MUTATIONS+=(
 ('average-observer-assumes-return-mass-one',CORRECTNESS,'Pr[PKEAverage(E).run() @ &m:true]=Pr[KeygenThenUniform(E).run() @ &m:true].','Pr[PKEAverage(E).run() @ &m:true]=1%r.'),
 ('accepted-key-bad-event-uses-unconditioned-buffers',CORRECTNESS,'mu accepted_four_law four_buffers_bad.','mu raw_four_law four_buffers_bad.'),
 ('actual-PKE-observer-calls-dropped-without-losslessness',CORRECTNESS,'call{1} pke_average_trial_lossless.',''),
)

RULES+=((AVERAGE,'observed bad event is integer no-wrap failure on sampled buffers',r'module PKEAverageObserved(E:KeygenExpand) = { proc run() : bool * bool = { var x:kem_keygen_observation; var failed:bool; x <@ KeygenThenUniform(E).run(); failed <@ PKEAverageTrial.run(x); return(failed,!honest_no_wrap x); } }.'),)
MUTATIONS+=(('bad-event-observer-replaced-with-PKE-failure-flag',AVERAGE,'return(failed,!honest_no_wrap x);','return(failed,failed);'),)

RULES+=((CORRECTNESS,'fresh mean bound is an event of actual PKE calls without extra premises',r'lemma pke_fresh_average_correctness &m : Pr[PKEAverage(FreshExpand).run() @ &m:res] < 1%r/(2%r^354).'),)
MUTATIONS+=(
 ('fresh-average-bound-substitutes-spec-only-game',CORRECTNESS,'Pr[PKEAverage(FreshExpand).run() @ &m:res] < 1%r/(2%r^354).','Pr[PKEReference.run() @ &m:res] < 1%r/(2%r^354).'),
 ('fresh-average-bound-assumes-acceptance-positivity',CORRECTNESS,'lemma pke_fresh_average_correctness &m :','lemma pke_fresh_average_correctness &m : 0%r<fresh_f_accept_mass =>'),
)

ROM=BASE+'NTRUPlus768PKEAverageROM.ec'
RULES+=(
 (ROM,'actual initialized ROM PKE error includes missing return mass without premises',r'lemma pke_rom_average_total &m : Pr[PKEAverageROM.run() @ &m:res] + (1%r-Pr[PKEAverageROM.run() @ &m:true]) < 1%r/(2%r^238).'),
 (ROM,'ROM transfer uses stateless observer error in addition to fresh conditional tail',r'lemma pke_rom_raw_bad_or_missing &m : ROE.m{m}=empty => Pr[PKEAverage(ExpandROM).run() @ &m:res] + (1%r-Pr[PKEAverage(ExpandROM).run() @ &m:true]) <= mu accepted_four_law four_buffers_bad+keygen_observer_error.'),
)
MUTATIONS+=(
 ('ROM-total-bound-omits-divergence',ROM,'Pr[PKEAverageROM.run() @ &m:res] + (1%r-Pr[PKEAverageROM.run() @ &m:true]) <','Pr[PKEAverageROM.run() @ &m:res] <'),
 ('ROM-total-bound-substitutes-fresh-model',ROM,'lemma pke_rom_average_total &m : Pr[PKEAverageROM.run()','lemma pke_rom_average_total &m : Pr[PKEAverage(FreshExpand).run()'),
 ('ROM-total-bound-assumes-unbounded-keygen-termination',ROM,'lemma pke_rom_average_total &m :','lemma pke_rom_average_total &m : islossless PKEAverageROM.run =>'),
 ('initialized-ROM-bound-assumes-empty-table',ROM,'lemma pke_rom_average_total &m :','lemma pke_rom_average_total &m : ROE.m{m}=empty =>'),
 ('ROM-error-forgets-key-generation-transfer-cost',ROM,'mu accepted_four_law four_buffers_bad+keygen_observer_error.','mu accepted_four_law four_buffers_bad.'),
)
