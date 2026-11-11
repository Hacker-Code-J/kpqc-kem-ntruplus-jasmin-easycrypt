require import AllCore List Distr FMap SDist StdOrder.
from Jasmin require import JWord.
require import Array32 Array192 Array1152 Array14466.
require import NTRUPlus768FOModel NTRUPlus768FOQueryBudget NTRUPlus768FOCapRemoval NTRUPlus768FOGameCapRemoval.
require import NTRUPlus768FOEagerG NTRUPlus768FOGAdapters NTRUPlus768FOJointGames NTRUPlus768FOMonitorProjection.
require import NTRUPlus768FOFixedGames NTRUPlus768FOSetupDistribution NTRUPlus768FOKEMGame.
require import NTRUPlus768ROMOracles NTRUPlus768FreshRetryLaw NTRUPlus768CCAGame NTRUPlus768CCASetupGame.
require import NTRUPlus768CCAOraclePorts NTRUPlus768CCADecapOracle NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
import RealOrder RField.

(* Exact transports preserve the actual shared hash calls and adversary
   state. The later numerical statements compare these games; they do not
   assert a complete IND-CCA reduction to an underlying hardness problem. *)
lemma fo_kernel_win_mu (K<:FOJointDist.GenDist.Distinguisher) &m s :
 mu1(mk(fun b=>Pr[K.guess(s) @ &m:res=b]))true=Pr[K.guess(s) @ &m:res].
proof.
 rewrite -(FOJointDist.GenDist.adv_mu1 K &m true s).
 by rewrite Pr[mu_eq]; smt().
qed.

lemma fo_native_configured_observed_mu
 (A<:CCAExtendedAdversary {-FOContext,-FOBadState,-FOBudgetState,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOGRO.RO,-FOGRO.FRO}) &m :
 Pr[CCASharedSetupGame(FreshExpand,FOConfiguredA(A)).run() @ &m:res]=
 mu1(dlet(mk(fun s=>Pr[FOSetupSource.guess(witness) @ &m:res=s]))
   (fun s=>mk(fun b=>Pr[FOObservedNativeKernel(A).guess(s) @ &m:res=b])))true.
proof.
 have he:(fun s=>mk(fun b=>Pr[FOPlainKernel(FOConfiguredA(A),FONativeDecap(SHAKEGROM,SHAKEHROM)).guess(s) @ &m:res=b]))=
   (fun s=>mk(fun b=>Pr[FOObservedNativeKernel(A).guess(s) @ &m:res=b])).
 + apply fun_ext=>s; congr; apply fun_ext=>b.
   exact(fo_native_kernel_monitor_event A &m s (fun z=>z=b)).
 rewrite(fo_g_native_eager_probability (FOConfiguredA(A)) &m (fun b=>b)) /=
   (fo_native_eager_mu (FOConfiguredA(A)) &m) he.
 done.
qed.

lemma fo_native_plain_observed_mu
 (A<:CCAExtendedAdversary {-FOContext,-FOBadState,-FOBudgetState,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOGRO.RO,-FOGRO.FRO}) &m q0 :
 0<=q0=>FOBudgetState.limit{m}=q0=>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess)=>
 hoare[FOCountedA(A,FOHashView(FONativePlainBackend),FODecapView(FONativePlainBackend)).guess:
 fo_budget_initial q0 FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit FOBudgetState.overflow ==>
 fo_query_count FOBudgetState.nH FOBudgetState.nD<=q0]=>
 Pr[CCASharedSetupGame(FreshExpand,A).run() @ &m:res]=
 mu1(dlet(mk(fun s=>Pr[FOSetupSource.guess(witness) @ &m:res=s]))
   (fun s=>mk(fun b=>Pr[FOObservedNativeKernel(A).guess(s) @ &m:res=b])))true.
proof.
 move=>hq hi all bounded.
 rewrite -(fo_native_configured_event A &m q0 (fun b=>b) hq hi all bounded).
 exact(fo_native_configured_observed_mu A &m).
qed.

lemma fo_full_configured_observed_mu
 (A<:CCAExtendedAdversary {-FOContext,-FOBadState,-FOBudgetState,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOGRO.RO,-FOGRO.FRO}) &m :
 Pr[FOFreshReencryptGame(FOConfiguredA(A)).run() @ &m:res]=
 mu1(dlet(mk(fun s=>Pr[FOSetupSource.guess(witness) @ &m:res=s]))
   (fun s=>mk(fun b=>Pr[FOObservedFullKernel(A).guess(s) @ &m:res=b])))true.
proof.
 have he:(fun s=>mk(fun b=>Pr[FOPlainKernel(FOConfiguredA(A),FOReencryptDecap(SHAKEGROM,SHAKEHROM)).guess(s) @ &m:res=b]))=
   (fun s=>mk(fun b=>Pr[FOObservedFullKernel(A).guess(s) @ &m:res=b])).
 + apply fun_ext=>s; congr; apply fun_ext=>b.
   exact(fo_full_kernel_monitor_event A &m s (fun z=>z=b)).
 rewrite(fo_g_full_eager_probability (FOConfiguredA(A)) &m (fun b=>b)) /=
   (fo_full_eager_mu (FOConfiguredA(A)) &m) he.
 done.
qed.

lemma fo_full_plain_observed_mu
 (A<:CCAExtendedAdversary {-FOContext,-FOBadState,-FOBudgetState,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOGRO.RO,-FOGRO.FRO}) &m q0 :
 0<=q0=>FOBudgetState.limit{m}=q0=>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess)=>
 hoare[FOCountedA(A,FOHashView(FOFullPlainBackend),FODecapView(FOFullPlainBackend)).guess:
 fo_budget_initial q0 FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit FOBudgetState.overflow ==>
 fo_query_count FOBudgetState.nH FOBudgetState.nD<=q0]=>
 Pr[FOFreshReencryptGame(A).run() @ &m:res]=
 mu1(dlet(mk(fun s=>Pr[FOSetupSource.guess(witness) @ &m:res=s]))
   (fun s=>mk(fun b=>Pr[FOObservedFullKernel(A).guess(s) @ &m:res=b])))true.
proof.
 move=>hq hi all bounded.
 rewrite -(fo_full_configured_event A &m q0 (fun b=>b) hq hi all bounded).
 exact(fo_full_configured_observed_mu A &m).
qed.

require import NTRUPlus768FOGameAverage NTRUPlus768FOGameHop NTRUPlus768FOSetupExpectation.

lemma fo_observed_setup_distance
 (A<:CCAExtendedAdversary {-FOContext,-FOBadState,-FOBudgetState,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOGRO.RO,-FOGRO.FRO}) &m q0 :
 0<=q0=>FOBudgetState.limit{m}=q0=>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess)=>
 `|mu1(dlet(mk(fun s=>Pr[FOSetupSource.guess(witness) @ &m:res=s]))
   (fun s=>mk(fun b=>Pr[FOObservedNativeKernel(A).guess(s) @ &m:res=b])))true-
   mu1(dlet(mk(fun s=>Pr[FOSetupSource.guess(witness) @ &m:res=s]))
   (fun s=>mk(fun b=>Pr[FOObservedFullKernel(A).guess(s) @ &m:res=b])))true|
 <=q0%r/(2%r^353).
proof.
 move=>hq hi all; apply(fo_setup_kernel_win_distance &m _ _ q0 hq).
 move=>s hs.
 rewrite -(FOJointDist.GenDist.adv_mu1 (FOObservedNativeKernel(A)) &m true s)
   -(FOJointDist.GenDist.adv_mu1 (FOObservedFullKernel(A)) &m true s).
 exact(fo_observed_kernel_distance A s q0 &m (fo_setup_law_support &m witness s hs) hq hi all).
qed.

lemma fo_fresh_native_full_distance
 (A<:CCAExtendedAdversary {-FOContext,-FOBadState,-FOBudgetState,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOGRO.RO,-FOGRO.FRO}) &m q0 :
 0<=q0=>FOBudgetState.limit{m}=q0=>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess)=>
 hoare[FOCountedA(A,FOHashView(FONativePlainBackend),FODecapView(FONativePlainBackend)).guess:
 fo_budget_initial q0 FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit FOBudgetState.overflow ==>
 fo_query_count FOBudgetState.nH FOBudgetState.nD<=q0]=>
 hoare[FOCountedA(A,FOHashView(FOFullPlainBackend),FODecapView(FOFullPlainBackend)).guess:
 fo_budget_initial q0 FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit FOBudgetState.overflow ==>
 fo_query_count FOBudgetState.nH FOBudgetState.nD<=q0]=>
 `|Pr[CCASharedSetupGame(FreshExpand,A).run() @ &m:res]-
   Pr[FOFreshReencryptGame(A).run() @ &m:res]|<=q0%r/(2%r^353).
proof.
 move=>hq hi all boundedN boundedF.
 rewrite(fo_native_plain_observed_mu A &m q0 hq hi all boundedN)
   (fo_full_plain_observed_mu A &m q0 hq hi all boundedF).
 exact(fo_observed_setup_distance A &m q0 hq hi all).
qed.

require import NTRUPlus768ErasureModel NTRUPlus768ErasureBudget NTRUPlus768ErasureSeedTape.
require import NTRUPlus768ErasureGames NTRUPlus768ErasureSecurity.

(* This compares the actual original ROM game with the full-FO game.
   The first error term already includes setup retry and E-query erasure.
   In particular, no losslessness premise is imposed on actual ROM KeyGen. *)
lemma fo_original_full_distance_256
 (A<:CCAExtendedAdversary {-FOContext,-FOBadState,-FOBudgetState,-ROE,-ROF,-ROG,-ROH,
  -RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOGRO.RO,-FOGRO.FRO,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState,-ErasureTape}) &m qE q0 :
 0<=q0=>FOBudgetState.limit{m}=q0=>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess)=>
 hoare[CountedA(A,SharedCCAExtendedOracles,CCADecapOracle).guess:
 EBudgetState.requests=0 /\ EBudgetState.forwarded=0 /\ EBudgetState.limit=qE /\
 !EBudgetState.overflow /\ EBudgetState.queries=[] ==> EBudgetState.requests<=qE]=>
 erasure_budget_initial qE EBudgetState.requests{m} EBudgetState.forwarded{m}
  EBudgetState.limit{m} EBudgetState.overflow{m} EBudgetState.queries{m}=>
 hoare[FOCountedA(A,FOHashView(FONativePlainBackend),FODecapView(FONativePlainBackend)).guess:
 fo_budget_initial q0 FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit FOBudgetState.overflow ==>
 fo_query_count FOBudgetState.nH FOBudgetState.nD<=q0]=>
 hoare[FOCountedA(A,FOHashView(FOFullPlainBackend),FODecapView(FOFullPlainBackend)).guess:
 fo_budget_initial q0 FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit FOBudgetState.overflow ==>
 fo_query_count FOBudgetState.nH FOBudgetState.nD<=q0]=>
 `|Pr[CCAOriginalGame(A).run() @ &m:res]-
   Pr[FOFreshReencryptGame(A).run() @ &m:res]|<=
 (130820%r+512%r*qE%r)/(2%r^256)+q0%r/(2%r^353).
proof.
 move=>hq hlim all boundedE hi boundedN boundedF.
 have he:=erasure_original_independent_256 A &m qE all boundedE hi.
 have hf:=fo_fresh_native_full_distance A &m q0 hq hlim all boundedN boundedF.
 exact(erasure_triangle_bound _ _ _ _ _ he hf).
qed.

