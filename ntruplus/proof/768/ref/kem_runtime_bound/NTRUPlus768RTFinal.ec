require import AllCore List Distr FMap.
from Jasmin require import JWord.
require import Array32 Array224 Array1152.
require import NTRUPlus768AHState.
require import NTRUPlus768RTModel NTRUPlus768RTStore.
require import NTRUPlus768ROMOracles NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
require import NTRUPlus768CCAGame NTRUPlus768CCADecapOracle.
require import NTRUPlus768FOModel NTRUPlus768FOQueryBudget NTRUPlus768FOEagerG NTRUPlus768FOKEMGame.
require import NTRUPlus768SimModel NTRUPlus768SimPorts NTRUPlus768SimSelected NTRUPlus768SimPublicBound.
require import NTRUPlus768ErasureModel NTRUPlus768ErasureBudget NTRUPlus768ErasureSeedTape.
require import NTRUPlus768CPAModel NTRUPlus768CPAHitOracles NTRUPlus768SecGOracles.
import SimSelectedBudget.
require import StdOrder.
require import NTRUPlus768RTAdaptive NTRUPlus768RTView NTRUPlus768RTProjection NTRUPlus768RTReduction.
require import NTRUPlus768RTKernelTypes NTRUPlus768RTWordReduction NTRUPlus768RTWordGames.
require import NTRUPlus768AHAdapter NTRUPlus768AHActualReduction NTRUPlus768AHCPABound NTRUPlus768AHFinal.
require import NTRUPlus768CPAFinal NTRUPlus768CPAReduction NTRUPlus768CCAOraclePorts.
require import NTRUPlus768FOGameCapRemoval NTRUPlus768SimPublicInstances NTRUPlus768SimSampling.
require import NTRUPlus768OWGames NTRUPlus768OWCodec NTRUPlus768OWKeyConditioning.
require import NTRUPlus768ErasureGames.
require import NTRUPlus768FOCapRemoval NTRUPlus768SimPublicCapRemoval.
require import NTRUPlus768RTCompleteCost.
import RealOrder RField.


(* Keep the original adversary declaration before the actual local
   storage. A local alias of a global store would not be fresh for A. *)
section.
declare module A <: CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,
  -FOContext,-FOBadState,-FOBudgetState,-FOGRO.RO,-FOGRO.FRO,-SimPublic,-SimHistory,-SimBad,
  -SimPhaseInput,-SimSelectedFixed,-SimPublicBudget,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,
  -SH.HB.Count,-SH.HB.HybOrcl,-ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState,-ErasureTape,
  -CPAReduction,-CPAHitState,-SecGHistory,-SecGMark}.

local module RTPrivateStore : RTHistory = {
 var st:ah_state
 var ledger:rt_profile
 proc init(pk:W8.t Array1152.t,suffix:W8.t Array32.t,cstar:W8.t Array1152.t option):unit = {
  (st,ledger)<@RTStoreOps.init(ledger,pk,suffix,cstar);
 }
 proc snapshot():ah_state = {return st;}
 proc record(input:fo_h_input,hout:W8.t Array224.t):unit = {
  (st,ledger)<@RTStoreOps.record(st,ledger,input,hout);
 }
 proc reset_cost():unit = {ledger<@RTStoreOps.reset_cost();}
 proc metrics():rt_profile = {return ledger;}
 proc charge_call(is_g:bool,bytes:int):unit = {
  ledger<@RTStoreOps.charge_call(ledger,is_g,bytes);
 }
 proc charge_decap(visits encryptions comparisons:int):unit = {
  ledger<@RTStoreOps.charge_decap(ledger,visits,encryptions,comparisons);
 }
 proc charge_extract(visits:int):unit = {
  ledger<@RTStoreOps.charge_extract(ledger,visits);
 }
}.

(* EasyCrypt orders these global components by variable name:
   (ledger,st). These typed projections and all contracts below check
   this representation; no state-view axiom is introduced. *)
local op rt_private_view (s:glob RTPrivateStore):ah_state = s.`2.
local op rt_private_cost (s:glob RTPrivateStore):rt_profile = s.`1.

local lemma rt_private_init_ll : islossless RTPrivateStore.init.
proof. proc;call rt_ops_init_ll;auto. qed.
local lemma rt_private_snapshot_ll : islossless RTPrivateStore.snapshot.
proof. proc;auto. qed.
local lemma rt_private_record_ll : islossless RTPrivateStore.record.
proof. proc;call rt_ops_record_ll;auto. qed.
local lemma rt_private_reset_ll : islossless RTPrivateStore.reset_cost.
proof. proc;call rt_ops_reset_ll;auto. qed.
local lemma rt_private_metrics_ll : islossless RTPrivateStore.metrics.
proof. proc;auto. qed.
local lemma rt_private_call_ll : islossless RTPrivateStore.charge_call.
proof. proc;call rt_ops_call_ll;auto. qed.
local lemma rt_private_decap_ll : islossless RTPrivateStore.charge_decap.
proof. proc;call rt_ops_decap_ll;auto. qed.
local lemma rt_private_extract_ll : islossless RTPrivateStore.charge_extract.
proof. proc;call rt_ops_extract_ll;auto. qed.

local lemma rt_private_init p pk suffix star :
 hoare[RTPrivateStore.init:
 rt_private_cost(glob RTPrivateStore)=p /\ arg=(pk,suffix,star) ==>
 rt_private_view(glob RTPrivateStore)=ah_initial pk suffix star /\
 rt_private_cost(glob RTPrivateStore)=p].
proof. proc;call(rt_ops_init_spec p pk suffix star);auto. qed.

local lemma rt_private_snapshot st p :
 hoare[RTPrivateStore.snapshot:
 rt_private_view(glob RTPrivateStore)=st /\ rt_private_cost(glob RTPrivateStore)=p ==>
 res=st /\ rt_private_view(glob RTPrivateStore)=st /\
 rt_private_cost(glob RTPrivateStore)=p].
proof. proc;auto. qed.

local lemma rt_private_record st p x y :
 hoare[RTPrivateStore.record:
 rt_private_view(glob RTPrivateStore)=st /\ rt_private_cost(glob RTPrivateStore)=p /\
 input=x /\ hout=y ==>
 rt_private_view(glob RTPrivateStore)=ah_record_state st x y /\
 rt_private_cost(glob RTPrivateStore)=rt_record_cost st p x].
proof. proc;call(rt_ops_record_spec st p x y);auto. qed.

local lemma rt_private_reset st :
 hoare[RTPrivateStore.reset_cost:rt_private_view(glob RTPrivateStore)=st ==>
 rt_private_view(glob RTPrivateStore)=st /\ rt_private_cost(glob RTPrivateStore)=rt_zero].
proof. proc;call rt_ops_reset_spec;auto. qed.

local lemma rt_private_metrics st p :
 hoare[RTPrivateStore.metrics:
 rt_private_view(glob RTPrivateStore)=st /\ rt_private_cost(glob RTPrivateStore)=p ==>
 res=p /\ rt_private_view(glob RTPrivateStore)=st /\
 rt_private_cost(glob RTPrivateStore)=p].
proof. proc;auto. qed.

local lemma rt_private_call st p ig b :
 hoare[RTPrivateStore.charge_call:
 rt_private_view(glob RTPrivateStore)=st /\ rt_private_cost(glob RTPrivateStore)=p /\
 arg=(ig,b) ==>
 rt_private_view(glob RTPrivateStore)=st /\
 rt_private_cost(glob RTPrivateStore)=rt_call p ig b].
proof. proc;call(rt_ops_call_spec p ig b);auto. qed.

local lemma rt_private_decap st p v k c :
 hoare[RTPrivateStore.charge_decap:
 rt_private_view(glob RTPrivateStore)=st /\ rt_private_cost(glob RTPrivateStore)=p /\
 arg=(v,k,c) ==>
 rt_private_view(glob RTPrivateStore)=st /\
 rt_private_cost(glob RTPrivateStore)=rt_decap p v k c].
proof. proc;call(rt_ops_decap_spec p v k c);auto. qed.

local lemma rt_private_extract st p v :
 hoare[RTPrivateStore.charge_extract:
 rt_private_view(glob RTPrivateStore)=st /\ rt_private_cost(glob RTPrivateStore)=p /\
 visits=v ==>
 rt_private_view(glob RTPrivateStore)=st /\
 rt_private_cost(glob RTPrivateStore)=rt_extract p v].
proof. proc;call(rt_ops_extract_spec p v);auto. qed.

(* Security projections quantify over the protocol view alone. They
   require no initial value, bound, or equality of the cost ledger. *)
local lemma rt_private_init_view pk suffix star :
 hoare[RTPrivateStore.init:arg=(pk,suffix,star) ==>
 rt_private_view(glob RTPrivateStore)=ah_initial pk suffix star].
proof.
 exists* RTPrivateStore.ledger;elim*=>p.
 conseq(rt_private_init p pk suffix star)=> //.
qed.

local lemma rt_private_snapshot_view st :
 hoare[RTPrivateStore.snapshot:rt_private_view(glob RTPrivateStore)=st ==>
 res=st /\ rt_private_view(glob RTPrivateStore)=st].
proof. proc;auto. qed.

local lemma rt_private_record_view st x y :
 hoare[RTPrivateStore.record:
 rt_private_view(glob RTPrivateStore)=st /\ input=x /\ hout=y ==>
 rt_private_view(glob RTPrivateStore)=ah_record_state st x y].
proof.
 exists* RTPrivateStore.ledger;elim*=>p.
 conseq(rt_private_record st p x y)=> //.
qed.

(* The unchanged original A declaration suffices: the private storage
   was created afterwards. Only the supplied oracle parameters receive
   the usual frame exclusion. This proves both protocol and ledger
   preservation when those oracles preserve the storage. *)
local lemma rt_private_frame
 (O<:CCAExtendedOraclePort {-RTPrivateStore})
 (D<:CCADecapPort {-RTPrivateStore}) st p :
 hoare[A(O,D).guess:
 rt_private_view(glob RTPrivateStore)=st /\ rt_private_cost(glob RTPrivateStore)=p ==>
 rt_private_view(glob RTPrivateStore)=st /\ rt_private_cost(glob RTPrivateStore)=p].
proof.
 proc(rt_private_view(glob RTPrivateStore)=st /\ rt_private_cost(glob RTPrivateStore)=p)=> //;
 proc(rt_private_view(glob RTPrivateStore)=st /\ rt_private_cost(glob RTPrivateStore)=p);auto.
qed.


(* Every hypothesis of the generic transcript theorems is discharged by
   the actual local store above. A retains its original declaration. *)
local lemma rt_private_transcript_projection :
 equiv[RTTranscript(RTPrivateStore,A).run ~ AHActualTranscript(RTPrivateStore,A).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\
 rt_private_view(glob RTPrivateStore){1}=rt_private_view(glob RTPrivateStore){2} ==>
 res{1}.`1=res{2} /\ ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\
 rt_private_view(glob RTPrivateStore){1}=rt_private_view(glob RTPrivateStore){2}].
proof.
 exact(rt_transcript_projection RTPrivateStore A rt_private_view rt_private_cost
 rt_private_init_ll rt_private_snapshot_ll rt_private_record_ll
 rt_private_call_ll rt_private_decap_ll rt_private_metrics_ll
 rt_private_init rt_private_call rt_private_snapshot rt_private_record rt_private_decap rt_private_metrics).
qed.
local lemma rt_private_transcript_bound :
 hoare[RTTranscript(RTPrivateStore,A).run:rt_private_cost(glob RTPrivateStore)=rt_zero ==>
 rt_transcript_ok res.`1 res.`2 /\ rt_private_cost(glob RTPrivateStore)=res.`2 /\
 SecGHistory.queries=res.`1].
proof.
 exact(rt_transcript_bound RTPrivateStore A rt_private_view rt_private_cost
 rt_private_init rt_private_call rt_private_snapshot rt_private_record rt_private_decap rt_private_metrics).
qed.
local lemma rt_private_extract_view st n :
 hoare[RTPrivateStore.charge_extract:rt_private_view(glob RTPrivateStore)=st /\ visits=n ==>
 rt_private_view(glob RTPrivateStore)=st].
proof.
 exists* RTPrivateStore.ledger;elim*=>p.
 conseq(rt_private_extract st p n)=> //.
qed.
local lemma rt_private_reset_view st :
 hoare[RTPrivateStore.reset_cost:rt_private_view(glob RTPrivateStore)=st ==>
 rt_private_view(glob RTPrivateStore)=st].
proof. conseq(rt_private_reset st)=> //. qed.
local lemma rt_private_metrics_view st :
 hoare[RTPrivateStore.metrics:rt_private_view(glob RTPrivateStore)=st ==>
 rt_private_view(glob RTPrivateStore)=st].
proof. proc;auto. qed.
local lemma rt_private_reset_zero :
 hoare[RTPrivateStore.reset_cost:true ==>rt_private_cost(glob RTPrivateStore)=rt_zero].
proof. proc;call rt_ops_reset_spec;auto. qed.

local lemma rt_private_di_projection :
 equiv[RT_DI(RTPrivateStore,A).run ~ AHActual_DI(RTPrivateStore,A).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\
 rt_private_view(glob RTPrivateStore){1}=rt_private_view(glob RTPrivateStore){2} ==>
 ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\
 rt_private_view(glob RTPrivateStore){1}=rt_private_view(glob RTPrivateStore){2}].
proof.
 exact(rt_di_projection RTPrivateStore A rt_private_view
 rt_private_extract_ll rt_private_extract_view rt_private_transcript_projection
 rt_private_reset_ll rt_private_metrics_ll rt_private_reset_view rt_private_metrics_view).
qed.

local lemma rt_private_word_di_resources p0 :
 hoare[RTWord_DI(RTPrivateStore,A).measure:h=ow_coeff_words p0 ==>
 rt_invocation_profile res.`3.`rtk_adversary res.`2 /\ rtk_le res.`3 rt_di_kernel_bound].
proof.
 conseq [-frame]
 (rt_word_di_history_profile RTPrivateStore A rt_private_view rt_private_cost p0
  rt_private_extract rt_private_transcript_bound rt_private_reset_zero rt_private_metrics)
 (rt_word_di_kernel_profile RTPrivateStore A p0);smt().
qed.

local lemma rt_private_do_projection :
 equiv[RT_DO(RTPrivateStore,A).run ~ AHActual_DO(RTPrivateStore,A).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\
 rt_private_view(glob RTPrivateStore){1}=rt_private_view(glob RTPrivateStore){2} ==>
 ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\
 rt_private_view(glob RTPrivateStore){1}=rt_private_view(glob RTPrivateStore){2}].
proof.
 exact(rt_do_projection RTPrivateStore A rt_private_view
 rt_private_extract_ll rt_private_extract_view rt_private_transcript_projection
 rt_private_reset_ll rt_private_metrics_ll rt_private_reset_view rt_private_metrics_view).
qed.

local lemma rt_private_word_do_resources p0 :
 hoare[RTWord_DO(RTPrivateStore,A).measure:h=ow_coeff_words p0 ==>
 rt_invocation_profile res.`3.`rtk_adversary res.`2 /\ rtk_le res.`3 rt_do_kernel_bound].
proof.
 conseq [-frame]
 (rt_word_do_history_profile RTPrivateStore A rt_private_view rt_private_cost p0
  rt_private_extract rt_private_transcript_bound rt_private_reset_zero rt_private_metrics)
 (rt_word_do_kernel_profile RTPrivateStore A p0);smt().
qed.

local lemma rt_private_co_projection :
 equiv[RT_CO(RTPrivateStore,A).run ~ AHActual_CO(RTPrivateStore,A).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\
 rt_private_view(glob RTPrivateStore){1}=rt_private_view(glob RTPrivateStore){2} ==>
 ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\
 rt_private_view(glob RTPrivateStore){1}=rt_private_view(glob RTPrivateStore){2}].
proof.
 exact(rt_co_projection RTPrivateStore A rt_private_view
 rt_private_extract_ll rt_private_extract_view rt_private_transcript_projection
 rt_private_reset_ll rt_private_metrics_ll rt_private_reset_view rt_private_metrics_view).
qed.

local lemma rt_private_word_co_resources p0 q0 :
 hoare[RTWord_CO(RTPrivateStore,A).measure:a=ow_coeff_words p0 /\ b=ow_coeff_words q0 ==>
 rt_invocation_profile res.`3.`rtk_adversary res.`2 /\ rtk_le res.`3 rt_co_kernel_bound].
proof.
 conseq [-frame]
 (rt_word_co_history_profile RTPrivateStore A rt_private_view rt_private_cost p0 q0
  rt_private_extract rt_private_transcript_bound rt_private_reset_zero rt_private_metrics)
 (rt_word_co_kernel_profile RTPrivateStore A p0 q0);smt().
qed.

local lemma rt_private_word_di_real_probability &m :
 Pr[RTWordNTRURealGame(RTWord_DI(RTPrivateStore,A)).run()@&m:res]=
 Pr[OWNTRURealGame(AHActual_DI(RTPrivateStore,A)).run()@&m:res].
proof.
 rewrite(rt_word_di_real_probability RTPrivateStore A &m).
 exact(rt_di_real_probability RTPrivateStore A rt_private_view &m rt_private_di_projection).
qed.

local lemma rt_private_word_di_uniform_probability &m :
 Pr[RTWordNTRUUniformGame(RTWord_DI(RTPrivateStore,A)).run()@&m:res]=
 Pr[OWNTRUUniformGame(AHActual_DI(RTPrivateStore,A)).run()@&m:res].
proof.
 rewrite(rt_word_di_uniform_probability RTPrivateStore A &m).
 exact(rt_di_uniform_probability RTPrivateStore A rt_private_view &m rt_private_di_projection).
qed.

local lemma rt_private_word_do_real_probability &m :
 Pr[RTWordNTRURealGame(RTWord_DO(RTPrivateStore,A)).run()@&m:res]=
 Pr[OWNTRURealGame(AHActual_DO(RTPrivateStore,A)).run()@&m:res].
proof.
 rewrite(rt_word_do_real_probability RTPrivateStore A &m).
 exact(rt_do_real_probability RTPrivateStore A rt_private_view &m rt_private_do_projection).
qed.

local lemma rt_private_word_do_uniform_probability &m :
 Pr[RTWordNTRUUniformGame(RTWord_DO(RTPrivateStore,A)).run()@&m:res]=
 Pr[OWNTRUUniformGame(AHActual_DO(RTPrivateStore,A)).run()@&m:res].
proof.
 rewrite(rt_word_do_uniform_probability RTPrivateStore A &m).
 exact(rt_do_uniform_probability RTPrivateStore A rt_private_view &m rt_private_do_projection).
qed.

local lemma rt_private_word_co_rlwe_probability &m :
 Pr[RTWordRLWEGame(RTWord_CO(RTPrivateStore,A)).run()@&m:res]=
 Pr[OWRLWEGame(AHActual_CO(RTPrivateStore,A)).run()@&m:res].
proof.
 rewrite(rt_word_co_rlwe_probability RTPrivateStore A &m).
 exact(rt_co_rlwe_probability RTPrivateStore A rt_private_view &m rt_private_co_projection).
qed.

(* The original adversary assumptions and all old loss terms are
   unchanged. Instrumentation and word representation add no loss. *)
local lemma rt_private_original_word_bound &m qE q0 qH qC :
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
 (2%r*(((Pr[RTWordNTRURealGame(RTWord_DI(RTPrivateStore,A)).run()@&m:res]-
 Pr[RTWordNTRUUniformGame(RTWord_DI(RTPrivateStore,A)).run()@&m:res]+
 (1%r/(2%r^244)))/ow_alpha_g)+
 ((Pr[RTWordNTRURealGame(RTWord_DO(RTPrivateStore,A)).run()@&m:res]-
 Pr[RTWordNTRUUniformGame(RTWord_DO(RTPrivateStore,A)).run()@&m:res]+
 Pr[RTWordRLWEGame(RTWord_CO(RTPrivateStore,A)).run()@&m:res])/ow_alpha_g))+qC%r/(2%r^768))+2%r*(qC%r/(2%r^353)).
proof.
 move=>h0 lim hH hC all ecount ei native full dcount known ccount.
 rewrite(rt_private_word_di_real_probability &m)
  (rt_private_word_di_uniform_probability &m)
  (rt_private_word_do_real_probability &m)
  (rt_private_word_do_uniform_probability &m)
  (rt_private_word_co_rlwe_probability &m).
 have original:=cpa_original_indcca A &m qE q0 qH qC
  h0 lim hH hC all ecount ei native full dcount known ccount.
 have gap:=ah_cpa_distance RTPrivateStore A rt_private_view qC &m
  rt_private_init_ll rt_private_snapshot_ll rt_private_record_ll
  rt_private_init_view rt_private_snapshot_view rt_private_record_view all hC ccount.
 have hardness:=ah_actual_cpa_hardness RTPrivateStore A &m
  rt_private_init_ll rt_private_snapshot_ll rt_private_record_ll all.
 have advantage:=ah_adv_transfer _ _ _ gap.
 exact(ah_final_lift _ _ _ _ _ _ _ _ original advantage hardness).
qed.

(* The same three concrete word reducers carry both conclusions below.
   Cost means the fixed-768 source-calibrated, ghost-erased operational
   model. Its source-calibration gate is part of the trusted frontend;
   ideal ROM calls remain model primitives. tA reserves an upper bound
   on A's own work, excluding the supplied oracle and decapsulation
   bodies, which are charged separately. No native CPU-cycle, integer
   bit-complexity or parameter-family PPT claim is made here. *)

local lemma rt_private_word_di_complete_cost p0 tA : 0<=tA=>
 hoare[RTWord_DI(RTPrivateStore,A).measure:h=ow_coeff_words p0 ==>
 rt_complete_di_charge tA res.`2 res.`3<=
 rt_complete_di_bound tA res.`2.`rp_q res.`2.`rp_b].
proof.
 move=>ht;conseq(rt_private_word_di_resources p0)=> //.
 move=> &hr _ result [hp hk];exact(rt_complete_di_cap tA result.`2 result.`3 ht hp hk).
qed.

local lemma rt_private_word_di_run_measure :
 equiv[RTWord_DI(RTPrivateStore,A).run ~ RTWord_DI(RTPrivateStore,A).measure:
 ={arg,glob RTWord_DI(RTPrivateStore,A)} ==>res{1}=res{2}.`1].
proof.
 proc*;inline{1} RTWord_DI(RTPrivateStore,A).run;wp.
 call(rt_word_ntru_measure_same (RTWord_DI(RTPrivateStore,A)));auto.
qed.

local lemma rt_private_word_do_complete_cost p0 tA : 0<=tA=>
 hoare[RTWord_DO(RTPrivateStore,A).measure:h=ow_coeff_words p0 ==>
 rt_complete_do_charge tA res.`2 res.`3<=
 rt_complete_do_bound tA res.`2.`rp_q res.`2.`rp_b].
proof.
 move=>ht;conseq(rt_private_word_do_resources p0)=> //.
 move=> &hr _ result [hp hk];exact(rt_complete_do_cap tA result.`2 result.`3 ht hp hk).
qed.

local lemma rt_private_word_do_run_measure :
 equiv[RTWord_DO(RTPrivateStore,A).run ~ RTWord_DO(RTPrivateStore,A).measure:
 ={arg,glob RTWord_DO(RTPrivateStore,A)} ==>res{1}=res{2}.`1].
proof.
 proc*;inline{1} RTWord_DO(RTPrivateStore,A).run;wp.
 call(rt_word_ntru_measure_same (RTWord_DO(RTPrivateStore,A)));auto.
qed.

local lemma rt_private_word_co_complete_cost p0 q0 tA : 0<=tA=>
 hoare[RTWord_CO(RTPrivateStore,A).measure:a=ow_coeff_words p0 /\ b=ow_coeff_words q0 ==>
 rt_complete_co_charge tA res.`2 res.`3<=
 rt_complete_co_bound tA res.`2.`rp_q res.`2.`rp_b].
proof.
 move=>ht;conseq(rt_private_word_co_resources p0 q0)=> //.
 move=> &hr _ result [hp hk];exact(rt_complete_co_cap tA result.`2 result.`3 ht hp hk).
qed.

local lemma rt_private_word_co_run_measure :
 equiv[RTWord_CO(RTPrivateStore,A).run ~ RTWord_CO(RTPrivateStore,A).measure:
 ={arg,glob RTWord_CO(RTPrivateStore,A)} ==>res{1}=res{2}.`1].
proof.
 proc*;inline{1} RTWord_CO(RTPrivateStore,A).run;wp.
 call(rt_word_rlwe_measure_same (RTWord_CO(RTPrivateStore,A)));auto.
qed.

(* A is universally quantified outside this existential package. These
   witnesses are chosen once, before every initial memory, security
   budget, represented word input and self-work reserve. *)
lemma rt_original_runtime_bound :
 exists(DI<:RTWordNTRUMeasured)(DO<:RTWordNTRUMeasured)(CO<:RTWordRLWEMeasured),
 (forall p0 tA,0<=tA=>
  hoare[DI.measure:h=ow_coeff_words p0 ==>
  rt_complete_di_charge tA res.`2 res.`3<=rt_complete_di_bound tA res.`2.`rp_q res.`2.`rp_b]) /\
 (forall p0 tA,0<=tA=>
  hoare[DO.measure:h=ow_coeff_words p0 ==>
  rt_complete_do_charge tA res.`2 res.`3<=rt_complete_do_bound tA res.`2.`rp_q res.`2.`rp_b]) /\
 (forall p0 q0 tA,0<=tA=>
  hoare[CO.measure:a=ow_coeff_words p0 /\ b=ow_coeff_words q0 ==>
  rt_complete_co_charge tA res.`2 res.`3<=rt_complete_co_bound tA res.`2.`rp_q res.`2.`rp_b]) /\
 equiv[DI.run ~ DI.measure: ={arg,glob DI} ==>res{1}=res{2}.`1] /\
 equiv[DO.run ~ DO.measure: ={arg,glob DO} ==>res{1}=res{2}.`1] /\
 equiv[CO.run ~ CO.measure: ={arg,glob CO} ==>res{1}=res{2}.`1] /\
 (forall &m qE q0 qH qC,
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
 (2%r*(((Pr[RTWordNTRURealGame(DI).run()@&m:res]-
 Pr[RTWordNTRUUniformGame(DI).run()@&m:res]+
 (1%r/(2%r^244)))/ow_alpha_g)+
 ((Pr[RTWordNTRURealGame(DO).run()@&m:res]-
 Pr[RTWordNTRUUniformGame(DO).run()@&m:res]+
 Pr[RTWordRLWEGame(CO).run()@&m:res])/ow_alpha_g))+qC%r/(2%r^768))+2%r*(qC%r/(2%r^353))).
proof.
 exists (RTWord_DI(RTPrivateStore,A)) (RTWord_DO(RTPrivateStore,A))
        (RTWord_CO(RTPrivateStore,A)).
 split;first by move=>p0 tA;exact(rt_private_word_di_complete_cost p0 tA).
 split;first by move=>p0 tA;exact(rt_private_word_do_complete_cost p0 tA).
 split;first by move=>p0 q0 tA;exact(rt_private_word_co_complete_cost p0 q0 tA).
 split;first exact rt_private_word_di_run_measure.
 split;first exact rt_private_word_do_run_measure.
 split;first exact rt_private_word_co_run_measure.
 move=> &m qE q0 qH qC;exact(rt_private_original_word_bound &m qE q0 qH qC).
qed.

end section.
