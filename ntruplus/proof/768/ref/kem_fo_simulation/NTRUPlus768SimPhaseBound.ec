require import AllCore Distr FMap StdOrder.
from Jasmin require import JWord.
require import NTRUPlus768FOModel NTRUPlus768FOError NTRUPlus768FOEagerG NTRUPlus768FOGAdapters NTRUPlus768FOQueryBudget NTRUPlus768FOKEMGame NTRUPlus768FOChallenge.
require import NTRUPlus768ROMOracles NTRUPlus768RawXOFStreams NTRUPlus768RawXOF NTRUPlus768CCAGame NTRUPlus768CCADecapOracle.
require import NTRUPlus768PKEModel NTRUPlus768ACWC2Oracle NTRUPlus768DecapCompleteSpec.
require import NTRUPlus768SimModel NTRUPlus768SimSampling NTRUPlus768SimAnswer NTRUPlus768SimPorts NTRUPlus768SimGames NTRUPlus768SimOracles NTRUPlus768SimLookup NTRUPlus768SimKnown.
require import NTRUPlus768SimSelected NTRUPlus768SimSelectedBound NTRUPlus768SimKnownBridge NTRUPlus768SimKnownCoupling.
require import NTRUPlus768SimPublicCapRemoval.
require import NTRUPlus768SimPublicBound NTRUPlus768SimPublicInstances.
import RealOrder SimSelectedBudget.

lemma sim_two_distances (x y z a b:real) : `|x-y|<=a=>`|y-z|<=b=>`|x-z|<=a+b.
proof. smt(ler_dist_add). qed.
lemma sim_two_costs qD qH e :
 qD%r*(1%r/(2%r^768)+e)+qH%r*e=qD%r/(2%r^768)+(qH+qD)%r*e.
proof. rewrite fromintD;ring. qed.

lemma sim_real_lookup_phase_distance
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,
  -FOContext,-FOBadState,-FOBudgetState,-FOGRO.RO,-FOGRO.FRO,-SimPublic,-SimHistory,-SimBad,
  -SimPhaseInput,-SimSelectedFixed,-SimPublicBudget,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,
  -SH.HB.Count,-SH.HB.HybOrcl}) w g ex hs cs qH s0 &m :
 pke_key_relation w=>
 (SimPublic.pk{m}=w.`kg_pk /\ SimPublic.suffix{m}=complete_sk_suffix w.`kg_sk /\
 CCADecapOracle.sk{m}=w.`kg_sk /\ SimPublic.cstar{m}=Some cs /\
 FOContext.w{m}=w /\ FOContext.g{m}=g /\ FOContext.challenge_h{m}=ex /\
 sim_known_invariant w g ex hs cs ROG.m{m} ROH.m{m} SimHistory.h{m} SimBad.corr{m} /\ !SimBad.corr{m})=>
 0<=qH=>
 (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess)=>
 (forall(H<:CCAExtendedOraclePort {-A,-FOBudgetState})(D<:CCADecapPort {-A,-FOBudgetState}),
  hoare[FOCountedA(A,H,D).guess:FOBudgetState.nD=0 ==>FOBudgetState.nD<=max 0 budget])=>
 hoare[SimPublicCountedA(A,FOHashView(SimKnownPublicBackend),FODecapView(SimKnownPublicBackend)).guess:
  sim_public_budget_initial qH SimPublicBudget.nh SimPublicBudget.limit SimPublicBudget.overflow ==>
  SimPublicBudget.nh<=qH]=>
 `|Pr[SimAdaptive(A,SimLeaksBackend(FOGActual,SimHActual),SimAnswerReal(FOGActual,SimHActual)).distinguish(s0) @ &m:res]-
   Pr[SimDirectPhase(A,SimOracles(FOGActual,SimHActual),SimLookup(FOGActual)).distinguish(s0) @ &m:res]|
 <=(max 0 budget)%r/(2%r^768)+(qH+max 0 budget)%r*fo_error w g.
proof.
 move=>hk hi hq all qd qh.
 have [hpk [hsuf [hsk [hstar [hw [hg [hex [hinv hcorr]]]]]]]]:=hi.
 have [hcache [hlog [hcover [hchallenge hgood]]]]:
  acwc2_cache_matches g ROG.m{m} /\ sim_log_included SimHistory.h{m} ROH.m{m} /\
  sim_h_cover SimHistory.h{m} ROH.m{m} ex /\
  fo_challenge_invariant w g ex hs cs ROH.m{m} /\
  (!SimBad.corr{m}=>fo_hcache_good w g ex SimHistory.h{m}).
 + by move:hinv;rewrite /sim_known_invariant.
 have hbridge:Pr[SimAdaptive(A,SimLeaksBackend(FOGActual,SimHActual),SimAnswerNever).distinguish(s0) @ &m:res]=
 Pr[SimDirectPhase(A,SimOracles(FOGActual,SimHActual),SimKnownDecap(FOGActual,SimHActual)).distinguish(s0) @ &m:res].
 + byequiv(sim_adaptive_known_phase A w g ex hs cs hk)=> //.
   by rewrite /sim_known_phase_state hpk hsk hstar hex hcache hchallenge.
 have hfirst:=sim_real_known_phase_distance A w g s0 &m hk hpk hcache hlog _ all qd.
 + by rewrite hex.
 have hsecond:=sim_known_lookup_phase_bound A w g ex hs cs qH &m s0 hk hi hq all qh.
 move:hfirst;rewrite hbridge=>hfirst.
 have h:=sim_two_distances _ _ _ _ _ hfirst hsecond.
 by move:h;rewrite sim_two_costs.
qed.
