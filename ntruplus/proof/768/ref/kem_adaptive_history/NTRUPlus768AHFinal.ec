require import AllCore StdOrder.
import RealOrder RField.

lemma ah_adv_transfer (p q eps:real) :
 `|p-q|<=eps=>`|p-1%r/2%r|<=`|q-1%r/2%r|+eps.
proof.
 move=>hb.
 have he:p-1%r/2%r=(p-q)+(q-1%r/2%r) by ring.
 rewrite he;have ht:=ler_norm_add (p-q) (q-1%r/2%r);smt().
qed.
lemma ah_final_lift (u v vnew eps hard a b c:real) :
 u<=a+b+(2%r*v+c)=>v<=vnew+eps=>vnew<=hard=>
 u<=a+b+(2%r*hard+c)+2%r*eps.
proof. smt(). qed.

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

require import NTRUPlus768INJFinal NTRUPlus768SRBound.


from Jasmin require import JWord.
require import Array224 NTRUPlus768HistModel.
require import NTRUPlus768AHState NTRUPlus768AHAdapter NTRUPlus768HistTable.
require import NTRUPlus768AHCPABound NTRUPlus768AHActualReduction.

(* The adversary is declared before a genuinely local store. EasyCrypt
   makes this store fresh for A; a local alias of a pre-existing global
   module would not provide the same property. The final existential
   witnesses are fixed before the initial memory and query budgets. *)
section.
declare module A <: CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,
  -FOContext,-FOBadState,-FOBudgetState,-FOGRO.RO,-FOGRO.FRO,-SimPublic,-SimHistory,-SimBad,
  -SimPhaseInput,-SimSelectedFixed,-SimPublicBudget,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,
  -SH.HB.Count,-SH.HB.HybOrcl,-ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState,-ErasureTape,
  -CPAReduction,-CPAHitState,-SecGHistory,-SecGMark}.

local module AHPrivateStore : AHStore = {
 var st:ah_state
 proc init(pk:W8.t Array1152.t,suffix:W8.t Array32.t,cstar:W8.t Array1152.t option):unit = {
  st<-{|ah_rows=[];ah_pk=pk;ah_suffix=suffix;ah_cstar=cstar|};
 }
 proc snapshot():ah_state = {return st;}
 proc record(input:fo_h_input,hout:W8.t Array224.t):unit = {
  var updated:hist_table*int*int;
  updated<@HistTable.put(input,hout,st.`ah_rows);
  st<-{|ah_rows=updated.`1;ah_pk=st.`ah_pk;ah_suffix=st.`ah_suffix;ah_cstar=st.`ah_cstar|};
 }
}.

local lemma ah_private_init_ll : islossless AHPrivateStore.init.
proof. proc;auto. qed.
local lemma ah_private_snapshot_ll : islossless AHPrivateStore.snapshot.
proof. proc;auto. qed.
local lemma ah_private_record_ll : islossless AHPrivateStore.record.
proof. proc;wp;call hist_table_put_lossless;auto. qed.

local lemma ah_private_init pk0 suffix0 star0 :
 hoare[AHPrivateStore.init:pk=pk0 /\ suffix=suffix0 /\ cstar=star0 ==>
 AHPrivateStore.st=ah_initial pk0 suffix0 star0].
proof. proc;auto=> />;by rewrite /ah_initial. qed.
local lemma ah_private_snapshot st0 :
 hoare[AHPrivateStore.snapshot:AHPrivateStore.st=st0 ==>
 res=st0 /\ AHPrivateStore.st=st0].
proof. proc;auto. qed.
local lemma ah_private_record st0 input0 hout0 :
 hoare[AHPrivateStore.record:AHPrivateStore.st=st0 /\ input=input0 /\ hout=hout0 ==>
 AHPrivateStore.st=ah_record_state st0 input0 hout0].
proof.
 proc;wp;call(hist_table_put_spec input0 hout0 st0.`ah_rows).
 auto=> />;by rewrite /ah_record_state /ah_with_rows.
qed.

(* The adversary cannot read or overwrite the new private store. Its
   declared restrictions above are the original ones, with no AHStore
   exclusion appended. Oracle parameters have the usual state frame. *)
local lemma ah_private_frame
 (O<:CCAExtendedOraclePort {-AHPrivateStore})(D<:CCADecapPort {-AHPrivateStore}) st0 :
 hoare[A(O,D).guess:AHPrivateStore.st=st0 ==>AHPrivateStore.st=st0].
proof. proc(AHPrivateStore.st=st0)=> //;proc(AHPrivateStore.st=st0);auto. qed.

(* The concrete witnesses are chosen once for A, before the initial
   memory and every query budget. The additional adaptive list-history
   loss is outside the key-acceptance factor ow_alpha_g. *)
lemma ah_original_adaptive_history :
 exists(DI<:OWNTRUAdversary)(DO<:OWNTRUAdversary)(CO<:OWRLWEAdversary),
 forall &m qE q0 qH qC,
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
 (2%r*(((Pr[OWNTRURealGame(DI).run()@&m:res]-
 Pr[OWNTRUUniformGame(DI).run()@&m:res]+
 (1%r/(2%r^244)))/ow_alpha_g)+
 ((Pr[OWNTRURealGame(DO).run()@&m:res]-
 Pr[OWNTRUUniformGame(DO).run()@&m:res]+
 Pr[OWRLWEGame(CO).run()@&m:res])/ow_alpha_g))+qC%r/(2%r^768))+2%r*(qC%r/(2%r^353)).
proof.
 exists (AHActual_DI(AHPrivateStore,A)) (AHActual_DO(AHPrivateStore,A))
        (AHActual_CO(AHPrivateStore,A)).
 move=> &m qE q0 qH qC h0 lim hH hC all ecount ei native full dcount known ccount.
 have original:=cpa_original_indcca A &m qE q0 qH qC
  h0 lim hH hC all ecount ei native full dcount known ccount.
 have hi:forall pk suffix star,hoare[AHPrivateStore.init:arg=(pk,suffix,star) ==>
  AHPrivateStore.st=ah_initial pk suffix star].
 + move=>pk suffix star;conseq(ah_private_init pk suffix star)=> //.
 have gap:=ah_cpa_distance AHPrivateStore A (fun(s:glob AHPrivateStore)=>s) qC &m
  ah_private_init_ll ah_private_snapshot_ll ah_private_record_ll
  hi ah_private_snapshot ah_private_record all hC ccount.
 have hardness:=ah_actual_cpa_hardness AHPrivateStore A &m
  ah_private_init_ll ah_private_snapshot_ll ah_private_record_ll all.
 have advantage:=ah_adv_transfer _ _ _ gap.
 exact(ah_final_lift _ _ _ _ _ _ _ _ original advantage hardness).
qed.
end section.
