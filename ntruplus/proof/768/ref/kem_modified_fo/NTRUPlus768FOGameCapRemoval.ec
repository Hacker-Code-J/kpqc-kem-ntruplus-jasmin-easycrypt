require import AllCore Distr FMap DBool.
from Jasmin require import JWord.
require import Array32 Array1152 Array2336.
require import NTRUPlus768FOModel NTRUPlus768FOQueryBudget NTRUPlus768FOCapRemoval NTRUPlus768FOKEMGame.
require import NTRUPlus768CCAGame NTRUPlus768CCASetupGame NTRUPlus768CCADecapOracle.
require import NTRUPlus768CCAOraclePorts NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
require import NTRUPlus768ROMOracles NTRUPlus768FreshRetryLaw.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768EncapCompleteRNG.

(* These are the unmonitored backends of the two actual fresh-setup games.
   Query bounds below concern each backend separately and do not imply
   adversary termination. The robust losslessness contract is explicit. *)
module FONativePlainBackend = FOBackendPair(SharedCCAExtendedOracles,FONativeDecap(SHAKEGROM,SHAKEHROM)).
module FOFullPlainBackend = FOBackendPair(SharedCCAExtendedOracles,FOReencryptDecap(SHAKEGROM,SHAKEHROM)).

lemma fo_native_pair_projection
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey}) :
 equiv[A(SharedCCAExtendedOracles,FONativeDecap(SHAKEGROM,SHAKEHROM)).guess ~
       A(FOHashView(FONativePlainBackend),FODecapView(FONativePlainBackend)).guess:
 ={arg,glob A,glob FONativePlainBackend} ==> ={res,glob A,glob FONativePlainBackend}].
proof.
 proc(={glob FONativePlainBackend}); 1,2:by auto.
 + by sim.
 + by sim.
 + by sim.
 + by sim.
 + by sim.
 by sim.
qed.

lemma fo_full_pair_projection
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey}) :
 equiv[A(SharedCCAExtendedOracles,FOReencryptDecap(SHAKEGROM,SHAKEHROM)).guess ~
       A(FOHashView(FOFullPlainBackend),FODecapView(FOFullPlainBackend)).guess:
 ={arg,glob A,glob FOFullPlainBackend} ==> ={res,glob A,glob FOFullPlainBackend}].
proof.
 proc(={glob FOFullPlainBackend}); 1,2:by auto.
 + by sim.
 + by sim.
 + by sim.
 + by sim.
 + by sim.
 by sim.
qed.

lemma fo_native_configured_phase
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOBudgetState}) q0 :
 0<=q0=>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess)=>
 hoare[FOCountedA(A,FOHashView(FONativePlainBackend),FODecapView(FONativePlainBackend)).guess:
 fo_budget_initial q0 FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit FOBudgetState.overflow ==>
 fo_query_count FOBudgetState.nH FOBudgetState.nD<=q0]=>
 equiv[FOConfiguredA(A,SharedCCAExtendedOracles,FONativeDecap(SHAKEGROM,SHAKEHROM)).guess ~
       A(SharedCCAExtendedOracles,FONativeDecap(SHAKEGROM,SHAKEHROM)).guess:
 ={arg,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle} /\
 FOBudgetState.limit{1}=q0 ==>
 ={res,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle}].
proof.
 move=>hq all bounded.
 transitivity FOConfiguredA(A,FOHashView(FONativePlainBackend),FODecapView(FONativePlainBackend)).guess
  (={arg,glob A,glob FONativePlainBackend,glob FOBudgetState} ==>
   ={res,glob A,glob FONativePlainBackend,glob FOBudgetState})
  (={arg,glob A,glob FONativePlainBackend} /\ FOBudgetState.limit{1}=q0 ==>
   ={res,glob A,glob FONativePlainBackend}).
 + smt().
 + smt().
 + conseq(fo_native_pair_projection (FOConfiguredA(A)))=> //.
 transitivity A(FOHashView(FONativePlainBackend),FODecapView(FONativePlainBackend)).guess
  (={arg,glob A,glob FONativePlainBackend} /\ FOBudgetState.limit{1}=q0 ==>
   ={res,glob A,glob FONativePlainBackend})
  (={arg,glob A,glob FONativePlainBackend} ==> ={res,glob A,glob FONativePlainBackend}).
 + smt().
 + smt().
 + exact(fo_configured_phase_plain A FONativePlainBackend q0 hq
    cca_extended_e_ll cca_extended_f_ll cca_extended_g_ll cca_extended_h_ll cca_extended_raw_ll
    (fo_native_decap_ll SHAKEGROM SHAKEHROM ro_g_shake_ll ro_h_shake_ll) all bounded).
 symmetry; conseq(fo_native_pair_projection A); smt().
qed.

lemma fo_full_configured_phase
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOBudgetState}) q0 :
 0<=q0=>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess)=>
 hoare[FOCountedA(A,FOHashView(FOFullPlainBackend),FODecapView(FOFullPlainBackend)).guess:
 fo_budget_initial q0 FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit FOBudgetState.overflow ==>
 fo_query_count FOBudgetState.nH FOBudgetState.nD<=q0]=>
 equiv[FOConfiguredA(A,SharedCCAExtendedOracles,FOReencryptDecap(SHAKEGROM,SHAKEHROM)).guess ~
       A(SharedCCAExtendedOracles,FOReencryptDecap(SHAKEGROM,SHAKEHROM)).guess:
 ={arg,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle,glob FOPublicKey} /\
 FOBudgetState.limit{1}=q0 ==>
 ={res,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle,glob FOPublicKey}].
proof.
 move=>hq all bounded.
 transitivity FOConfiguredA(A,FOHashView(FOFullPlainBackend),FODecapView(FOFullPlainBackend)).guess
  (={arg,glob A,glob FOFullPlainBackend,glob FOBudgetState} ==>
   ={res,glob A,glob FOFullPlainBackend,glob FOBudgetState})
  (={arg,glob A,glob FOFullPlainBackend} /\ FOBudgetState.limit{1}=q0 ==>
   ={res,glob A,glob FOFullPlainBackend}).
 + smt().
 + smt().
 + conseq(fo_full_pair_projection (FOConfiguredA(A)))=> //.
 transitivity A(FOHashView(FOFullPlainBackend),FODecapView(FOFullPlainBackend)).guess
  (={arg,glob A,glob FOFullPlainBackend} /\ FOBudgetState.limit{1}=q0 ==>
   ={res,glob A,glob FOFullPlainBackend})
  (={arg,glob A,glob FOFullPlainBackend} ==> ={res,glob A,glob FOFullPlainBackend}).
 + smt().
 + smt().
 + exact(fo_configured_phase_plain A FOFullPlainBackend q0 hq
    cca_extended_e_ll cca_extended_f_ll cca_extended_g_ll cca_extended_h_ll cca_extended_raw_ll
    (fo_reencrypt_decap_ll SHAKEGROM SHAKEHROM ro_g_shake_ll ro_h_shake_ll) all bounded).
 symmetry; conseq(fo_full_pair_projection A); smt().
qed.

lemma fo_native_configured_challenge
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOBudgetState}) q0 :
 0<=q0=>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess)=>
 hoare[FOCountedA(A,FOHashView(FONativePlainBackend),FODecapView(FONativePlainBackend)).guess:
 fo_budget_initial q0 FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit FOBudgetState.overflow ==>
 fo_query_count FOBudgetState.nH FOBudgetState.nD<=q0]=>
 equiv[FOCCAChallenge(SHAKEGROM,SHAKEHROM,SharedCCAExtendedOracles,FONativeDecap(SHAKEGROM,SHAKEHROM),FOConfiguredA(A)).run ~
       FOCCAChallenge(SHAKEGROM,SHAKEHROM,SharedCCAExtendedOracles,FONativeDecap(SHAKEGROM,SHAKEHROM),A).run:
 ={pk,sk,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle} /\ FOBudgetState.limit{1}=q0 ==>
 ={res,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle,glob FOPublicKey}].
proof.
 move=>hq all bounded; proc.
 call(fo_native_configured_phase A q0 hq all bounded).
 inline FOPublicKey.init CCADecapOracle.init; wp; rnd; rnd.
 call(_: ={pk,workspace,glob ROF,glob ROG,glob ROH} ==> ={res,glob ROF,glob ROG,glob ROH}); first by sim.
 auto.
qed.

lemma fo_native_configured_game_equiv
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOBudgetState}) q0 :
 0<=q0=>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess)=>
 hoare[FOCountedA(A,FOHashView(FONativePlainBackend),FODecapView(FONativePlainBackend)).guess:
 fo_budget_initial q0 FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit FOBudgetState.overflow ==>
 fo_query_count FOBudgetState.nH FOBudgetState.nD<=q0]=>
 equiv[FOFreshNativeGame(FOConfiguredA(A)).run ~ FOFreshNativeGame(A).run:
 ={glob A} /\ FOBudgetState.limit{1}=q0 ==>
 ={res,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle,glob FOPublicKey}].
proof.
 move=>hq all bounded; proc.
 call(fo_native_configured_challenge A q0 hq all bounded).
 call(_: ={glob ROF} ==> ={res,glob ROF}); first by sim.
 inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init CCADecapOracle.reset.
 auto.
qed.

lemma fo_native_configured_event
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOBudgetState}) &m q0 (event:bool->bool) :
 0<=q0=>FOBudgetState.limit{m}=q0=>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess)=>
 hoare[FOCountedA(A,FOHashView(FONativePlainBackend),FODecapView(FONativePlainBackend)).guess:
 fo_budget_initial q0 FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit FOBudgetState.overflow ==>
 fo_query_count FOBudgetState.nH FOBudgetState.nD<=q0]=>
 Pr[CCASharedSetupGame(FreshExpand,FOConfiguredA(A)).run() @ &m:event res]=
 Pr[CCASharedSetupGame(FreshExpand,A).run() @ &m:event res].
proof.
 move=>hq hlim all bounded.
 rewrite -(fo_fresh_native_game_event (FOConfiguredA(A)) &m event)
   -(fo_fresh_native_game_event A &m event).
 byequiv(fo_native_configured_game_equiv A q0 hq all bounded)=> //.
qed.

lemma fo_full_configured_challenge
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOBudgetState}) q0 :
 0<=q0=>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess)=>
 hoare[FOCountedA(A,FOHashView(FOFullPlainBackend),FODecapView(FOFullPlainBackend)).guess:
 fo_budget_initial q0 FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit FOBudgetState.overflow ==>
 fo_query_count FOBudgetState.nH FOBudgetState.nD<=q0]=>
 equiv[FOCCAChallenge(SHAKEGROM,SHAKEHROM,SharedCCAExtendedOracles,FOReencryptDecap(SHAKEGROM,SHAKEHROM),FOConfiguredA(A)).run ~
       FOCCAChallenge(SHAKEGROM,SHAKEHROM,SharedCCAExtendedOracles,FOReencryptDecap(SHAKEGROM,SHAKEHROM),A).run:
 ={pk,sk,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle} /\ FOBudgetState.limit{1}=q0 ==>
 ={res,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle,glob FOPublicKey}].
proof.
 move=>hq all bounded; proc.
 call(fo_full_configured_phase A q0 hq all bounded).
 inline FOPublicKey.init CCADecapOracle.init; wp; rnd; rnd.
 call(_: ={pk,workspace,glob ROF,glob ROG,glob ROH} ==> ={res,glob ROF,glob ROG,glob ROH}); first by sim.
 auto.
qed.

lemma fo_full_configured_game_equiv
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOBudgetState}) q0 :
 0<=q0=>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess)=>
 hoare[FOCountedA(A,FOHashView(FOFullPlainBackend),FODecapView(FOFullPlainBackend)).guess:
 fo_budget_initial q0 FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit FOBudgetState.overflow ==>
 fo_query_count FOBudgetState.nH FOBudgetState.nD<=q0]=>
 equiv[FOFreshReencryptGame(FOConfiguredA(A)).run ~ FOFreshReencryptGame(A).run:
 ={glob A} /\ FOBudgetState.limit{1}=q0 ==>
 ={res,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle,glob FOPublicKey}].
proof.
 move=>hq all bounded; proc.
 call(fo_full_configured_challenge A q0 hq all bounded).
 call(_: ={glob ROF} ==> ={res,glob ROF}); first by sim.
 inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init CCADecapOracle.reset.
 auto.
qed.

lemma fo_full_configured_event
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOBudgetState}) &m q0 (event:bool->bool) :
 0<=q0=>FOBudgetState.limit{m}=q0=>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess)=>
 hoare[FOCountedA(A,FOHashView(FOFullPlainBackend),FODecapView(FOFullPlainBackend)).guess:
 fo_budget_initial q0 FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit FOBudgetState.overflow ==>
 fo_query_count FOBudgetState.nH FOBudgetState.nD<=q0]=>
 Pr[FOFreshReencryptGame(FOConfiguredA(A)).run() @ &m:event res]=
 Pr[FOFreshReencryptGame(A).run() @ &m:event res].
proof.
 move=>hq hlim all bounded.
 byequiv(fo_full_configured_game_equiv A q0 hq all bounded)=> //.
qed.
