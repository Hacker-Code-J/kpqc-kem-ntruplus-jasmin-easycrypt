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
require import NTRUPlus768CPAFinal.
require import NTRUPlus768SecModel NTRUPlus768SecGames NTRUPlus768SecGOracles.
require import NTRUPlus768SecProgramming NTRUPlus768SecChallengeBridge NTRUPlus768SecHiding.
require import NTRUPlus768SecExtractModel NTRUPlus768SecExtract NTRUPlus768SecReduction.
require import NTRUPlus768SecKeygen NTRUPlus768SecBaseGames.
import RealOrder RField SimSelectedBudget.

(* The CPA adversary is the concrete one constructed in the preceding
   original-KEM reduction. Its choose stage makes no G oracle query. *)
lemma sec_cpa_base
 (A<:CCAExtendedAdversary {-CPAReduction,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,
 -SimPublic,-SimHistory,-SecGHistory,-SecGMark}) &m :
 (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
 islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
 islossless D.decap=>islossless A(H,D).guess)=>
 `|Pr[CPAGame(CPAReduction(A)).run()@&m:res]-1%r/2%r| <=
 Pr[SecBaseINJGame(SecINJAuxAdapter(SecINJReducer(A))).run()@&m:res]+
 Pr[SecBaseOWGame(SecOWAuxAdapter(SecOWReducer(A))).run()@&m:res].
proof.
 move=>all.
 have gl:forall(G<:FOGPort {-SecRun(A)}),islossless G.get=>islossless SecRun(A,G).run.
 + move=>G hG;exact(sec_run_ll A G all hG).
 have gap:=sec_programming_distance A &m gl.
 move:gap;rewrite
 (sec_unprogrammed_random_law A &m (fun (s:sec_observation)=>s.`so_win))
 (sec_unprogrammed_random_law A &m sec_hit)
 (sec_random_unbiased A &m all)
 -(sec_cpa_programmed_probability A &m)=>gap.
 have hit:=sec_hit_reduction A &m.
 move:hit;rewrite(sec_inj_base_probability A &m)(sec_ow_base_probability A &m)=>hit.
 exact(ler_trans _ _ _ gap hit).
qed.

lemma sec_add_lift (u v x y a b:real) :
 u<=a+(2%r*v+b)=>v<=x+y=>u<=a+(2%r*(x+y)+b).
proof. smt(). qed.

(* The final base challengers contain no ROM calls. All auxiliary hashes
   are simulated within the explicit finite-query reducers.
   No INJ, OW-CPA, NTRU, or RLWE hardness assumption is asserted here. *)
lemma sec_original_inj_ow
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,
  -FOContext,-FOBadState,-FOBudgetState,-FOGRO.RO,-FOGRO.FRO,-SimPublic,-SimHistory,-SimBad,
  -SimPhaseInput,-SimSelectedFixed,-SimPublicBudget,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,
  -SH.HB.Count,-SH.HB.HybOrcl,-ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState,-ErasureTape,
  -CPAReduction,-CPAHitState,-SecGHistory,-SecGMark}) &m qE q0 qH qC :
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
 (2%r*(Pr[SecBaseINJGame(SecINJAuxAdapter(SecINJReducer(A))).run()@&m:res]+
 Pr[SecBaseOWGame(SecOWAuxAdapter(SecOWReducer(A))).run()@&m:res])+qC%r/(2%r^768)).
proof.
 move=>h0 lim hH hC all ecount ei native full dcount known ccount.
 have previous:=cpa_original_indcca A &m qE q0 qH qC h0 lim hH hC all ecount ei native full dcount known ccount.
 have reduced:=sec_cpa_base A &m all.
 exact(sec_add_lift _ _ _ _ _ _ previous reduced).
qed.
