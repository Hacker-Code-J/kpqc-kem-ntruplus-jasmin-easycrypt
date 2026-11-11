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

require import NTRUPlus768SecFinal NTRUPlus768OWGames NTRUPlus768OWReduction NTRUPlus768OWKeyConditioning.

require import NTRUPlus768OWFinal NTRUPlus768INJGames NTRUPlus768INJReduction NTRUPlus768INJExistence.

lemma inj_bound_lift (u a b i w h:real):
 u<=a+(2%r*(i+w)+b)=>i<=h=>u<=a+(2%r*(h+w)+b).
proof. smt(). qed.

(* Exact reduction to an explicit uniform short-relation experiment.
   No theorem here bounds that experiment by a number, assumes it hard,
   identifies [a,1] with iid Ring-SIS, or equates it to decisional NTRU. *)
lemma inj_original_short_relation
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
 (2%r*(((Pr[OWNTRURealGame(INJNTRUReduction(SecINJAuxAdapter(SecINJReducer(A)))).run()@&m:res]-
 Pr[OWNTRUUniformGame(INJNTRUReduction(SecINJAuxAdapter(SecINJReducer(A)))).run()@&m:res]+
 Pr[INJShortRelationGame(INJShortSolver(SecINJAuxAdapter(SecINJReducer(A)))).run()@&m:res])/ow_alpha_g)+
 ((Pr[OWNTRURealGame(OWNTRUReduction(SecOWAuxAdapter(SecOWReducer(A)))).run()@&m:res]-
 Pr[OWNTRUUniformGame(OWNTRUReduction(SecOWAuxAdapter(SecOWReducer(A)))).run()@&m:res]+
 Pr[OWRLWEGame(OWRLWESolver(SecOWAuxAdapter(SecOWReducer(A)))).run()@&m:res])/ow_alpha_g))+qC%r/(2%r^768)).
proof.
 move=>h0 lim hH hC all ecount ei native full dcount known ccount.
 have previous:=ow_original_hardness A &m qE q0 qH qC h0 lim hH hC all ecount ei native full dcount known ccount.
 have reduced:=inj_base_hardness (SecINJAuxAdapter(SecINJReducer(A))) &m.
 exact(inj_bound_lift _ _ _ _ _ _ previous reduced).
qed.

lemma inj_division_upper (gap sr mass alpha:real):
 0%r<alpha=>sr<=mass=>(gap+sr)/alpha<=(gap+mass)/alpha.
proof.
 move=>ha hs;rewrite ler_pmul2r 1:invr_gt0 1:ha;smt().
qed.
lemma inj_statistical_lift (u a b gap sr w mass alpha:real):
 0%r<alpha=>u<=a+(2%r*((gap+sr)/alpha+w)+b)=>sr<=mass=>
 u<=a+(2%r*((gap+mass)/alpha+w)+b).
proof.
 move=>ha hb hs.
 exact(inj_bound_lift _ _ _ _ _ _ hb (inj_division_upper gap sr mass alpha ha hs)).
qed.

(* The residual quantity is a probability of existence, not a supplied
   numerical bound. No termination of the short-relation solver is used. *)
lemma inj_original_statistical
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
 (2%r*(((Pr[OWNTRURealGame(INJNTRUReduction(SecINJAuxAdapter(SecINJReducer(A)))).run()@&m:res]-
 Pr[OWNTRUUniformGame(INJNTRUReduction(SecINJAuxAdapter(SecINJReducer(A)))).run()@&m:res]+
 inj_uniform_bad_mass)/ow_alpha_g)+
 ((Pr[OWNTRURealGame(OWNTRUReduction(SecOWAuxAdapter(SecOWReducer(A)))).run()@&m:res]-
 Pr[OWNTRUUniformGame(OWNTRUReduction(SecOWAuxAdapter(SecOWReducer(A)))).run()@&m:res]+
 Pr[OWRLWEGame(OWRLWESolver(SecOWAuxAdapter(SecOWReducer(A)))).run()@&m:res])/ow_alpha_g))+qC%r/(2%r^768)).
proof.
 move=>h0 lim hH hC all ecount ei native full dcount known ccount.
 have previous:=inj_original_short_relation A &m qE q0 qH qC h0 lim hH hC all ecount ei native full dcount known ccount.
 have existence:=inj_uniform_existence_bound (INJShortSolver(SecINJAuxAdapter(SecINJReducer(A)))) &m.
 exact(inj_statistical_lift _ _ _ _ _ _ _ _ ow_alpha_g_positive previous existence).
qed.
