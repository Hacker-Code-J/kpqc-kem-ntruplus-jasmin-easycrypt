require import AllCore Distr FMap StdOrder.
require import NTRUPlus768FOModel NTRUPlus768FOEagerG NTRUPlus768FOGAdapters NTRUPlus768FOKEMGame NTRUPlus768FOJointGames.
require import NTRUPlus768FOSetupDistribution NTRUPlus768FOSetupExpectation NTRUPlus768FOQueryBudget.
require import NTRUPlus768ROMOracles NTRUPlus768RawXOFStreams NTRUPlus768RawXOF NTRUPlus768CCAGame NTRUPlus768CCADecapOracle.
require import NTRUPlus768SimModel NTRUPlus768SimPorts NTRUPlus768SimGames NTRUPlus768SimPublicGames.
require import NTRUPlus768SimSelected NTRUPlus768SimPublicBound NTRUPlus768SimPublicInstances NTRUPlus768SimAverage NTRUPlus768SimKernelBound.
require import NTRUPlus768SimPublicCapRemoval.
import RealOrder SimSelectedBudget.

(* Complete adaptive-game comparison for this milestone. The endpoints
   have no artificial query cap and the public simulator has no secret-key
   interface. The explicit count and robust termination contracts are
   adversary conditions, not an assumed security-game distance.
   IND-CPA/hardness reduction and the resulting full IND-CCA advantage
   theorem are separate, subsequent obligations. *)
lemma sim_fo_public_distance
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,
  -FOContext,-FOBadState,-FOBudgetState,-FOGRO.RO,-FOGRO.FRO,-SimPublic,-SimHistory,-SimBad,
  -SimPhaseInput,-SimSelectedFixed,-SimPublicBudget,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,
  -SH.HB.Count,-SH.HB.HybOrcl}) qH &m :
 0<=qH=>
 (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess)=>
 (forall(H<:CCAExtendedOraclePort {-A,-FOBudgetState})(D<:CCADecapPort {-A,-FOBudgetState}),
  hoare[FOCountedA(A,H,D).guess:FOBudgetState.nD=0 ==>FOBudgetState.nD<=max 0 budget])=>
 hoare[SimPublicCountedA(A,FOHashView(SimKnownPublicBackend),FODecapView(SimKnownPublicBackend)).guess:
  sim_public_budget_initial qH SimPublicBudget.nh SimPublicBudget.limit SimPublicBudget.overflow ==>
  SimPublicBudget.nh<=qH]=>
 `|Pr[FOFreshReencryptGame(A).run() @ &m:res]-Pr[SimPublicFreshGame(A).run() @ &m:res]|
 <=(max 0 budget)%r/(2%r^768)+(qH+max 0 budget)%r/(2%r^353).
proof.
 move=>hq all qd qh.
 rewrite (fo_g_full_eager_probability A &m (fun b=>b)) /= (fo_full_eager_mu A &m) (sim_public_fresh_mu A &m).
 apply(sim_setup_win_distance &m _ _ (max 0 budget) qH);first by smt().
 + exact hq.
 move=>s hs.
 have hv:=fo_setup_law_support &m witness s hs.
 rewrite -(FOJointDist.GenDist.adv_mu1 (FOPlainKernel(A,FOReencryptDecap(SHAKEGROM,SHAKEHROM))) &m true s)
  -(FOJointDist.GenDist.adv_mu1 (SimPublicKernel(A)) &m true s) /=.
 have h0:Pr[FOPlainKernel(A,FOReencryptDecap(SHAKEGROM,SHAKEHROM)).guess(s) @ &m:res=true]=
 Pr[FOPlainKernel(A,FOReencryptDecap(SHAKEGROM,SHAKEHROM)).guess(s) @ &m:res].
 + clear hq all qd qh hv hs;rewrite Pr[mu_eq];smt().
 have h1:Pr[SimPublicKernel(A).guess(s) @ &m:res=true]=Pr[SimPublicKernel(A).guess(s) @ &m:res].
 + clear hq all qd qh hv hs;rewrite Pr[mu_eq];smt().
 rewrite h0 h1.
 exact(sim_plain_public_kernel_distance A s qH &m hv hq all qd qh).
qed.
