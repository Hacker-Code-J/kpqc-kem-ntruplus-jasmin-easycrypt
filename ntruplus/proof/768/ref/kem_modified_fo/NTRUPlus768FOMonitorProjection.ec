require import AllCore List Distr DBool FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array129 Array192 Array224 Array1152 Array2336 Array13506 Array13634.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions NTRUPlus768EncapCompleteRNG.
require import NTRUPlus768CCAOraclePorts NTRUPlus768CCAQueryCodec NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
require import NTRUPlus768CCADecapOracle NTRUPlus768CCAGame NTRUPlus768CCAStatusAdapter.
require import NTRUPlus768DecapCompleteTailProof NTRUPlus768DecapCompleteProof.
require import NTRUPlus768DecapMessageSpec NTRUPlus768DecapMessageProof.
require import NTRUPlus768FOModel NTRUPlus768FOHMonitor NTRUPlus768FOProcedures NTRUPlus768FOKEMGame.
require import NTRUPlus768FOQueryBudget NTRUPlus768FOCapRemoval NTRUPlus768FOBadBound.
require import NTRUPlus768FOChallengeBridge NTRUPlus768FOFixedGames NTRUPlus768FOJointGames NTRUPlus768FOSetupDistribution.
require import NTRUPlus768ACWC2Oracle NTRUPlus768NumericalDFRModel.

(* Monitoring never affects the actual H reply or the arithmetic path.
   These identities cover arbitrary keys and ciphertexts, including every
   entry rejection and the H call made after SOTP decoding failure. *)
lemma fo_monitor_native_tail :
 equiv[CompleteTail(FOSHAKEH).run ~ CompleteTail(SHAKEHROM).run:
 ={arg,ROG.m,ROH.m} ==> ={res,ROG.m,ROH.m}].
proof.
 proc; do 4!(call(_:true); first by sim).
 call fo_shakeh_projection; call(_:true); first by sim.
 auto.
qed.
lemma fo_monitor_native_core :
 equiv[CompleteCore(SHAKEGROM,FOSHAKEH).run ~ CompleteCore(SHAKEGROM,SHAKEHROM).run:
 ={arg,ROG.m,ROH.m} ==> ={res,ROG.m,ROH.m}].
proof.
 proc; seq 1 1:(={ct,sk,rp,mp,ss,status,ROG.m,ROH.m}).
 + call(_:true); first by sim. auto.
 if; 1,3:by auto.
 call fo_monitor_native_tail.
 call(_: ={arg,ROG.m} ==> ={res,ROG.m}); first by sim.
 auto.
qed.
lemma fo_monitor_native_decaps :
 equiv[CompleteDecaps(SHAKEGROM,FOSHAKEH).run ~ CompleteDecaps(SHAKEGROM,SHAKEHROM).run:
 ={arg,ROG.m,ROH.m} ==> ={res,ROG.m,ROH.m}].
proof.
 proc; call(_:true); first by sim.
 call fo_monitor_native_core; auto.
qed.
lemma fo_monitor_native_decap :
 equiv[FONativeDecap(SHAKEGROM,FOSHAKEH).decap ~ FONativeDecap(SHAKEGROM,SHAKEHROM).decap:
 ={arg,ROG.m,ROH.m,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk} ==>
 ={res,ROG.m,ROH.m,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk}].
proof.
 proc; sp; if; 1,2:by auto.
 wp; call fo_monitor_native_decaps; auto.
qed.

lemma fo_monitor_full_tail :
 equiv[FOTail(SHAKEGROM,FOSHAKEH).run ~ FOTail(SHAKEGROM,SHAKEHROM).run:
 ={arg,ROG.m,ROH.m} ==> ={res,ROG.m,ROH.m}].
proof.
 proc; call(_: ={arg,ROG.m} ==> ={res,ROG.m}); first by sim.
 call fo_shakeh_projection; call(_:true); first by sim.
 auto.
qed.
lemma fo_monitor_full_core :
 equiv[FOCore(SHAKEGROM,FOSHAKEH).run ~ FOCore(SHAKEGROM,SHAKEHROM).run:
 ={arg,ROG.m,ROH.m} ==> ={res,ROG.m,ROH.m}].
proof.
 proc; seq 1 1:(={pk,ct,sk,rp,mp,ss,status,ROG.m,ROH.m}).
 + call(_:true); first by sim. auto.
 if; 1,3:by auto.
 call fo_monitor_full_tail.
 call(_: ={arg,ROG.m} ==> ={res,ROG.m}); first by sim.
 auto.
qed.
lemma fo_monitor_full_decaps :
 equiv[FODecaps(SHAKEGROM,FOSHAKEH).run ~ FODecaps(SHAKEGROM,SHAKEHROM).run:
 ={arg,ROG.m,ROH.m} ==> ={res,ROG.m,ROH.m}].
proof.
 proc; call(_:true); first by sim.
 call fo_monitor_full_core; auto.
qed.
lemma fo_monitor_full_decap :
 equiv[FOReencryptDecap(SHAKEGROM,FOSHAKEH).decap ~ FOReencryptDecap(SHAKEGROM,SHAKEHROM).decap:
 ={arg,ROG.m,ROH.m,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk} ==>
 ={res,ROG.m,ROH.m,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk}].
proof.
 proc; sp; if; 1,2:by auto.
 wp; call fo_monitor_full_decaps; auto.
qed.

lemma fo_monitor_public_h :
 equiv[FOSharedOracles.h ~ SharedCCAExtendedOracles.h:
 ={arg,ROH.m} ==> ={res,ROH.m}].
proof.
 proc*; inline{2} SharedCCAOracles.h.
 wp; call fo_hmonitor_projection; auto.
qed.
lemma fo_monitor_raw_full :
 equiv[FOHRawXOF.full ~ RawXOF.full:
 ={input,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other} ==>
 ={res,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other}].
proof.
 proc; match; 1,2:by auto; smt().
 + by sim.
 move=>q1 q2; match; 1..4:by auto; smt().
 + move=>x y; call(_: ={arg,ROE.m,RawXOFStreams.es} ==> ={res,ROE.m,RawXOFStreams.es}); first by sim.
   auto=> />; smt().
 + move=>x y; call(_: ={arg,ROF.m,RawXOFStreams.fs} ==> ={res,ROF.m,RawXOFStreams.fs}); first by sim.
   auto=> />; smt().
 + move=>x y; call(_: ={arg,ROG.m,RawXOFStreams.gs} ==> ={res,ROG.m,RawXOFStreams.gs}); first by sim.
   auto=> />; smt().
 move=>x y; inline{2} RawXOFStreams.h SharedCCAOracles.h.
 wp; call fo_hmonitor_projection; auto=> />; smt().
qed.
lemma fo_monitor_raw :
 equiv[FOSharedOracles.raw ~ SharedCCAExtendedOracles.raw:
 ={input,outlen,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other} ==>
 ={res,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other}].
proof. proc; sp; if; 1,3:by auto. wp; call fo_monitor_raw_full; auto. qed.

lemma fo_monitor_cap_h (D<:CCADecapPort) :
 equiv[FOCapHPort(FOHashView(FOBackendPair(FOSharedOracles,D))).h ~ FOCapHPort(SharedCCAExtendedOracles).h:
 ={arg,glob FOBudgetState,ROH.m} ==> ={res,glob FOBudgetState,ROH.m}].
proof.
 proc; inline FOQueryRequest.h; sp; wp; if; 1,3:by auto; smt().
 call fo_monitor_public_h; auto.
qed.
lemma fo_monitor_cap_raw (D<:CCADecapPort) :
 equiv[FOCapHPort(FOHashView(FOBackendPair(FOSharedOracles,D))).raw ~ FOCapHPort(SharedCCAExtendedOracles).raw:
 ={arg,glob FOBudgetState,ROE.m,ROF.m,ROG.m,ROH.m,
 RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other} ==>
 ={res,glob FOBudgetState,ROE.m,ROF.m,ROG.m,ROH.m,
 RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other}].
proof.
 proc; seq 3 3:(={input,outlen,allowed,result,glob FOBudgetState,ROE.m,ROF.m,ROG.m,ROH.m,
 RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other}).
 + inline FOQueryRequest.h; auto=> />; smt().
 wp; if; 1,3:by auto.
 call fo_monitor_raw; auto.
qed.
lemma fo_monitor_cap_native_d :
 equiv[FOCapDPort(FODecapView(FOBackendPair(FOSharedOracles,FONativeDecap(SHAKEGROM,FOSHAKEH)))).decap ~
 FOCapDPort(FONativeDecap(SHAKEGROM,SHAKEHROM)).decap:
 ={arg,glob FOBudgetState,ROG.m,ROH.m,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk} ==>
 ={res,glob FOBudgetState,ROG.m,ROH.m,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk}].
proof.
 proc; inline FOQueryRequest.d; sp; wp; if; 1,3:by auto; smt().
 call fo_monitor_native_decap; auto.
qed.
lemma fo_monitor_cap_full_d :
 equiv[FOCapDPort(FODecapView(FOBackendPair(FOSharedOracles,FOReencryptDecap(SHAKEGROM,FOSHAKEH)))).decap ~
 FOCapDPort(FOReencryptDecap(SHAKEGROM,SHAKEHROM)).decap:
 ={arg,glob FOBudgetState,ROG.m,ROH.m,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk} ==>
 ={res,glob FOBudgetState,ROG.m,ROH.m,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk}].
proof.
 proc; inline FOQueryRequest.d; sp; wp; if; 1,3:by auto; smt().
 call fo_monitor_full_decap; auto.
qed.

lemma fo_monitor_encap_projection :
 equiv[FOChallengeEncap.run ~ EncapRandom(SHAKEFROM,SHAKEGROM,SHAKEHROM,UniformCoins).run:
 ={pk,workspace,ROF.m,ROG.m,ROH.m} ==> ={res,ROF.m,ROG.m,ROH.m}].
proof. symmetry; conseq fo_challenge_encap_projection; smt(). qed.

lemma fo_monitor_native_adversary
 (A<:CCAExtendedAdversary {-FOContext,-FOBadState,-FOBudgetState,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey}) :
 equiv[FOCappedA(A,FOHashView(FOBackendPair(FOSharedOracles,FONativeDecap(SHAKEGROM,FOSHAKEH))),FODecapView(FOBackendPair(FOSharedOracles,FONativeDecap(SHAKEGROM,FOSHAKEH)))).guess ~
 FOCappedA(A,SharedCCAExtendedOracles,FONativeDecap(SHAKEGROM,SHAKEHROM)).guess:
 ={pk,ct,key,glob A,glob FOBudgetState,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk} ==>
 ={res,glob A,glob FOBudgetState,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk}].
proof.
 proc(={glob FOBudgetState,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk}); 1,2:by auto.
 + by sim.
 + by sim.
 + by sim.
 + conseq(fo_monitor_cap_h (FONativeDecap(SHAKEGROM,FOSHAKEH))); smt().
 + conseq(fo_monitor_cap_raw (FONativeDecap(SHAKEGROM,FOSHAKEH))); smt().
 conseq fo_monitor_cap_native_d; smt().
qed.
lemma fo_monitor_native_phase
 (A<:CCAExtendedAdversary {-FOContext,-FOBadState,-FOBudgetState,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey}) :
 equiv[FOBadPhase(A,FOBackendPair(FOSharedOracles,FONativeDecap(SHAKEGROM,FOSHAKEH))).run ~
 FOConfiguredA(A,SharedCCAExtendedOracles,FONativeDecap(SHAKEGROM,SHAKEHROM)).guess:
 ={pk,ct,key,glob A,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk} /\ q{1}=FOBudgetState.limit{2} ==>
 ={res,glob A,glob FOBudgetState,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk}].
proof.
 proc; call(fo_monitor_native_adversary A).
 inline FOBadState.init FOBudgetState.configure; auto.
qed.
lemma fo_monitor_native_challenge
 (A<:CCAExtendedAdversary {-FOContext,-FOBadState,-FOBudgetState,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey}) :
 equiv[FOObservedChallenge(A,FOBackendPair(FOSharedOracles,FONativeDecap(SHAKEGROM,FOSHAKEH))).run ~
 FOCCAChallenge(SHAKEGROM,SHAKEHROM,SharedCCAExtendedOracles,FONativeDecap(SHAKEGROM,SHAKEHROM),FOConfiguredA(A)).run:
 ={pk,sk,glob A,FOBudgetState.limit,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count} ==>
 ={res,glob A,glob FOBudgetState,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk}].
proof.
 proc; call(fo_monitor_native_phase A); wp.
 inline FOPublicKey.init CCADecapOracle.init; wp; rnd; rnd.
 call fo_monitor_encap_projection; auto.
qed.

(* Arbitrary snapshots are permitted: monitoring records private data but
   never uses it to choose a response or control the public computation. *)
lemma fo_native_kernel_monitor_projection
 (A<:CCAExtendedAdversary {-FOContext,-FOBadState,-FOBudgetState,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey}) :
 equiv[FOPlainKernel(FOConfiguredA(A),FONativeDecap(SHAKEGROM,SHAKEHROM)).guess ~ FOObservedNativeKernel(A).guess:
 ={s,glob A,FOBudgetState.limit} ==>
 ={res,glob A,glob FOBudgetState,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk}].
proof.
 symmetry; proc; call(fo_monitor_native_challenge A).
 inline FOContext.init ROE.init ROG.init ROH.init RawXOFStreams.init CCADecapOracle.reset.
 auto=> />; smt().
qed.
lemma fo_native_kernel_monitor_event
 (A<:CCAExtendedAdversary {-FOContext,-FOBadState,-FOBudgetState,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey}) &m s (event:bool->bool) :
 Pr[FOPlainKernel(FOConfiguredA(A),FONativeDecap(SHAKEGROM,SHAKEHROM)).guess(s) @ &m:event res]=
 Pr[FOObservedNativeKernel(A).guess(s) @ &m:event res].
proof. byequiv(fo_native_kernel_monitor_projection A)=> //. qed.

lemma fo_monitor_full_adversary
 (A<:CCAExtendedAdversary {-FOContext,-FOBadState,-FOBudgetState,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey}) :
 equiv[FOCappedA(A,FOHashView(FOBackendPair(FOSharedOracles,FOReencryptDecap(SHAKEGROM,FOSHAKEH))),FODecapView(FOBackendPair(FOSharedOracles,FOReencryptDecap(SHAKEGROM,FOSHAKEH)))).guess ~
 FOCappedA(A,SharedCCAExtendedOracles,FOReencryptDecap(SHAKEGROM,SHAKEHROM)).guess:
 ={pk,ct,key,glob A,glob FOBudgetState,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk} ==>
 ={res,glob A,glob FOBudgetState,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk}].
proof.
 proc(={glob FOBudgetState,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk}); 1,2:by auto.
 + by sim.
 + by sim.
 + by sim.
 + conseq(fo_monitor_cap_h (FOReencryptDecap(SHAKEGROM,FOSHAKEH))); smt().
 + conseq(fo_monitor_cap_raw (FOReencryptDecap(SHAKEGROM,FOSHAKEH))); smt().
 conseq fo_monitor_cap_full_d; smt().
qed.
lemma fo_monitor_full_phase
 (A<:CCAExtendedAdversary {-FOContext,-FOBadState,-FOBudgetState,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey}) :
 equiv[FOBadPhase(A,FOBackendPair(FOSharedOracles,FOReencryptDecap(SHAKEGROM,FOSHAKEH))).run ~
 FOConfiguredA(A,SharedCCAExtendedOracles,FOReencryptDecap(SHAKEGROM,SHAKEHROM)).guess:
 ={pk,ct,key,glob A,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk} /\ q{1}=FOBudgetState.limit{2} ==>
 ={res,glob A,glob FOBudgetState,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk}].
proof.
 proc; call(fo_monitor_full_adversary A).
 inline FOBadState.init FOBudgetState.configure; auto.
qed.
lemma fo_monitor_full_challenge
 (A<:CCAExtendedAdversary {-FOContext,-FOBadState,-FOBudgetState,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey}) :
 equiv[FOObservedChallenge(A,FOBackendPair(FOSharedOracles,FOReencryptDecap(SHAKEGROM,FOSHAKEH))).run ~
 FOCCAChallenge(SHAKEGROM,SHAKEHROM,SharedCCAExtendedOracles,FOReencryptDecap(SHAKEGROM,SHAKEHROM),FOConfiguredA(A)).run:
 ={pk,sk,glob A,FOBudgetState.limit,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count} ==>
 ={res,glob A,glob FOBudgetState,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk}].
proof.
 proc; call(fo_monitor_full_phase A); wp.
 inline FOPublicKey.init CCADecapOracle.init; wp; rnd; rnd.
 call fo_monitor_encap_projection; auto.
qed.

(* Arbitrary snapshots are permitted: monitoring records private data but
   never uses it to choose a response or control the public computation. *)
lemma fo_full_kernel_monitor_projection
 (A<:CCAExtendedAdversary {-FOContext,-FOBadState,-FOBudgetState,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey}) :
 equiv[FOPlainKernel(FOConfiguredA(A),FOReencryptDecap(SHAKEGROM,SHAKEHROM)).guess ~ FOObservedFullKernel(A).guess:
 ={s,glob A,FOBudgetState.limit} ==>
 ={res,glob A,glob FOBudgetState,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk}].
proof.
 symmetry; proc; call(fo_monitor_full_challenge A).
 inline FOContext.init ROE.init ROG.init ROH.init RawXOFStreams.init CCADecapOracle.reset.
 auto=> />; smt().
qed.
lemma fo_full_kernel_monitor_event
 (A<:CCAExtendedAdversary {-FOContext,-FOBadState,-FOBudgetState,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey}) &m s (event:bool->bool) :
 Pr[FOPlainKernel(FOConfiguredA(A),FOReencryptDecap(SHAKEGROM,SHAKEHROM)).guess(s) @ &m:event res]=
 Pr[FOObservedFullKernel(A).guess(s) @ &m:event res].
proof. byequiv(fo_full_kernel_monitor_projection A)=> //. qed.
