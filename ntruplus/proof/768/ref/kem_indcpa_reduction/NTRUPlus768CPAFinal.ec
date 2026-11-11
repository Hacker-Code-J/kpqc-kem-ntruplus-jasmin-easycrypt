require import AllCore List Distr FMap SDist StdOrder.
require import Array32 Array192 Array1152 Array14466.
require import NTRUPlus768FOModel NTRUPlus768FOQueryBudget NTRUPlus768FOCapRemoval NTRUPlus768FOGameCapRemoval.
require import NTRUPlus768FOEagerG NTRUPlus768FOGAdapters NTRUPlus768FOJointGames NTRUPlus768FOMonitorProjection.
require import NTRUPlus768FOFixedGames NTRUPlus768FOSetupDistribution NTRUPlus768FOKEMGame.
require import NTRUPlus768ROMOracles NTRUPlus768FreshRetryLaw NTRUPlus768CCAGame NTRUPlus768CCASetupGame.
require import NTRUPlus768CCAOraclePorts NTRUPlus768CCADecapOracle NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
require import NTRUPlus768FOGameAverage NTRUPlus768FOGameHop NTRUPlus768FOSetupExpectation.
require import NTRUPlus768ErasureModel NTRUPlus768ErasureBudget NTRUPlus768ErasureSeedTape.
require import NTRUPlus768ErasureGames NTRUPlus768ErasureSecurity.
require import AllCore Distr FMap StdOrder.
require import NTRUPlus768FOModel NTRUPlus768FOEagerG NTRUPlus768FOGAdapters NTRUPlus768FOKEMGame NTRUPlus768FOJointGames.
require import NTRUPlus768FOSetupDistribution NTRUPlus768FOSetupExpectation NTRUPlus768FOQueryBudget.
require import NTRUPlus768ROMOracles NTRUPlus768RawXOFStreams NTRUPlus768RawXOF NTRUPlus768CCAGame NTRUPlus768CCADecapOracle.
require import NTRUPlus768SimModel NTRUPlus768SimPorts NTRUPlus768SimGames NTRUPlus768SimPublicGames.
require import NTRUPlus768SimSelected NTRUPlus768SimPublicBound NTRUPlus768SimPublicInstances NTRUPlus768SimAverage NTRUPlus768SimKernelBound.
require import NTRUPlus768SimPublicCapRemoval.
require import NTRUPlus768FOSecurity NTRUPlus768SimFinal NTRUPlus768ErasureSecurity NTRUPlus768ErasureBudget NTRUPlus768ErasureModel.
require import AllCore Distr FMap StdOrder.
require import NTRUPlus768CPAModel NTRUPlus768CPAReduction NTRUPlus768CPACrossHit.
require import NTRUPlus768CPAChallenge NTRUPlus768CPAChallengeBridge NTRUPlus768CPAUnbiased.
require import NTRUPlus768CPAHitOracles NTRUPlus768CPAProgramming NTRUPlus768CPAProgrammingBridge.
require import NTRUPlus768SimGames NTRUPlus768SimModel NTRUPlus768SimSampling NTRUPlus768SimOracles NTRUPlus768SimLookup.
require import NTRUPlus768ROMOracles NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
require import NTRUPlus768CCAGame NTRUPlus768CCAOraclePorts NTRUPlus768CCADecapOracle.
require import NTRUPlus768FOGAdapters NTRUPlus768FOEagerG.
import RealOrder RField.

lemma cpa_hit_success_bound p h cross eps :
 p=(1%r+h-cross)/2%r=>cross<=eps=>h<=2%r*`|p-1%r/2%r|+eps.
proof. smt(ler_norm). qed.

(* qC bounds the concrete unprogrammed CPA phase's distinct public H
   records. It is separate from the prior Known-backend H count. *)
lemma cpa_public_indcpa
 (A<:CCAExtendedAdversary {-CPAReduction,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,
 -SimPublic,-SimHistory,-CPAHitState,-CCADecapOracle}) qC &m :
 0<=qC=>
 (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
 islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
 islossless D.decap=>islossless A(H,D).guess)=>
 hoare[CPAPhase(A).run:true ==>fsize SimHistory.h<=qC]=>
 `|Pr[SimPublicFreshGame(A).run()@&m:res]-1%r/2%r|
 <=2%r*`|Pr[CPAGame(CPAReduction(A)).run()@&m:res]-1%r/2%r|+qC%r/(2%r^768).
proof.
 move=>hq all count.
 have ah:forall(H<:SimHPort {-A}),islossless H.get=>
 islossless A(SimOracles(FOGActual,H),SimLookup(FOGActual)).guess.
 + move=>H hl;apply(all (SimOracles(FOGActual,H)) (SimLookup(FOGActual))).
   - exact cca_e_ll.
   - exact cca_f_ll.
   - proc;call rog_get_ll;auto.
   - exact(sim_logged_h_ll H hl).
   - exact(sim_raw_get_ll FOGActual H rog_get_ll hl).
   exact(sim_lookup_lossless FOGActual rog_get_ll).
 have gap:=cpa_programming_game_distance A &m ah.
 move:gap;rewrite(cpa_programming_programmed_probability A &m)
 (cpa_programming_erased_probability A &m (fun (r:bool*bool)=>r.`1))
 (cpa_programming_erased_probability A &m (fun (r:bool*bool)=>r.`2)) /=
 (cpa_erased_unbiased A &m all) (cpa_erased_hit A &m)
 -(cpa_actual_programmed_probability A &m)=>gap.
 have reduction:=cpa_reduction_success A &m all.
 have cross:=cpa_cross_hit A qC &m hq count.
 have bound:=cpa_hit_success_bound _ _ _ _ reduction cross.
 exact(ler_trans _ _ _ gap bound).
qed.

import SimSelectedBudget.

(* The concrete original IND-CCA game is reduced to CPAReduction(A).
   Each backend's query contract is retained explicitly; no native/full/
   Known/public count is silently substituted for another. *)
lemma cpa_original_indcca
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,
  -FOContext,-FOBadState,-FOBudgetState,-FOGRO.RO,-FOGRO.FRO,-SimPublic,-SimHistory,-SimBad,
  -SimPhaseInput,-SimSelectedFixed,-SimPublicBudget,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,
  -SH.HB.Count,-SH.HB.HybOrcl,-ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState,-ErasureTape,
  -CPAReduction,-CPAHitState}) &m qE q0 qH qC :
 0<=q0=>FOBudgetState.limit{m}=q0=>0<=qH=>0<=qC=>
 (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess)=>
 hoare[CountedA(A,SharedCCAExtendedOracles,CCADecapOracle).guess:
 EBudgetState.requests=0 /\ EBudgetState.forwarded=0 /\ EBudgetState.limit=qE /\
 !EBudgetState.overflow /\ EBudgetState.queries=[] ==>EBudgetState.requests<=qE]=>
 erasure_budget_initial qE EBudgetState.requests{m} EBudgetState.forwarded{m}
 EBudgetState.limit{m} EBudgetState.overflow{m} EBudgetState.queries{m}=>
 hoare[FOCountedA(A,FOHashView(FONativePlainBackend),FODecapView(FONativePlainBackend)).guess:
 fo_budget_initial q0 FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit FOBudgetState.overflow ==>
 fo_query_count FOBudgetState.nH FOBudgetState.nD<=q0]=>
 hoare[FOCountedA(A,FOHashView(FOFullPlainBackend),FODecapView(FOFullPlainBackend)).guess:
 fo_budget_initial q0 FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit FOBudgetState.overflow ==>
 fo_query_count FOBudgetState.nH FOBudgetState.nD<=q0]=>
 (forall(H<:CCAExtendedOraclePort {-A,-FOBudgetState})(D<:CCADecapPort {-A,-FOBudgetState}),
 hoare[FOCountedA(A,H,D).guess:FOBudgetState.nD=0 ==>FOBudgetState.nD<=max 0 budget])=>
 hoare[SimPublicCountedA(A,FOHashView(SimKnownPublicBackend),FODecapView(SimKnownPublicBackend)).guess:
 sim_public_budget_initial qH SimPublicBudget.nh SimPublicBudget.limit SimPublicBudget.overflow ==>
 SimPublicBudget.nh<=qH]=>
 hoare[CPAPhase(A).run:true ==>fsize SimHistory.h<=qC]=>
 `|Pr[CCAOriginalGame(A).run()@&m:res]-1%r/2%r| <=
 ((130820%r+512%r*qE%r)/(2%r^256)+q0%r/(2%r^353))+
 ((max 0 budget)%r/(2%r^768)+(qH+max 0 budget)%r/(2%r^353))+
 (2%r*`|Pr[CPAGame(CPAReduction(A)).run()@&m:res]-1%r/2%r|+qC%r/(2%r^768)).
proof.
 move=>h0 lim hH hC all ecount ei native full dcount known ccount.
 have first:=fo_original_full_distance_256 A &m qE q0 h0 lim all ecount ei native full.
 have second:=sim_fo_public_distance A qH &m hH all dcount known.
 have third:=cpa_public_indcpa A qC &m hC all ccount.
 have combined:=erasure_triangle_bound _ _ _ _ _ first second.
 exact(erasure_triangle_bound _ _ _ _ _ combined third).
qed.
