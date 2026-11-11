require import AllCore Distr FMap DInterval StdOrder.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152.
require import NTRUPlus768SimModel NTRUPlus768SimSampling NTRUPlus768SimAnswer.
require import NTRUPlus768SimPorts NTRUPlus768SimPortContracts NTRUPlus768SimSelected NTRUPlus768SimHybrid.
require import NTRUPlus768FOModel NTRUPlus768FOQueryBudget NTRUPlus768FOEagerG NTRUPlus768FOGAdapters.
require import NTRUPlus768ROMOracles NTRUPlus768RawXOF NTRUPlus768RawXOFStreams NTRUPlus768CCAGame NTRUPlus768CCADecapOracle.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768ACWC2Oracle NTRUPlus768FOSetupDistribution.
import SimSelectedBudget.

(* The selected answer is reached at most once, even for a partial
   adversary and independently of the adversary's total query count. *)
lemma sim_guarded_oracle_count n0 :
 hoare[SH.SimOracleOfAnswer(SimGuardedReject).orcl:
 SimBad.selected_calls=n0 ==>SimBad.selected_calls=n0+1].
proof. proc;call(sim_guarded_count n0);auto. qed.

lemma sim_hybrid_selected_once
 (B<:SH.HB.Orclb {-SH.HB.HybOrcl,-SimBad})
 (A<:SH.HB.AdvOrclb {-SH.HB.HybOrcl,-B,-SimBad,-ROG,-ROH,-SimSelectedFixed}) :
 hoare[SH.HB.HybGame(A,B,SH.SimOracleOfAnswer(SimGuardedReject)).main:
 SimBad.selected_calls=0 ==>SimBad.selected_calls<=1].
proof.
 proc.
 call(_:0<=SH.HB.HybOrcl.l /\ 0<=SH.HB.HybOrcl.l0 /\
  SimBad.selected_calls=b2i(SH.HB.HybOrcl.l0<SH.HB.HybOrcl.l)).
 + proc;wp;if.
   - call(_:true ==>true);first by trivial. auto;smt().
   if.
   - ecall(sim_guarded_oracle_count SimBad.selected_calls);auto;smt().
   call(_:true ==>true);first by trivial. auto;smt().
 + proc*;call(_:true ==>true);first by trivial. auto.
 + proc*;call(_:true ==>true);first by trivial. auto.
 + proc*;call(_:true ==>true);first by trivial. auto.
 wp;rnd;auto=> />.
 move=>i hi;have h0:0<=i by move:hi;rewrite supp_dinter;smt().
 have hn:(i<0)=false by smt().
 rewrite hn b2i0 /=;split;first exact h0.
 move=>_ l _;exact(b2i_le1 _).
qed.

lemma sim_guarded_selected_once
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
  -SimPublic,-SimHistory,-FOContext,-SimBad,-SimSelectedFixed,-SimPhaseInput,-FOBudgetState,
  -SH.HB.Count,-SH.HB.HybOrcl}) :
 hoare[SimSelectedGuarded(A).run:true ==>SimBad.selected_calls<=1].
proof.
 proc;inline SimSelectedContext(A,FOGActual,SimHActual,SimGuardedReject).distinguish;wp.
 call(sim_hybrid_selected_once (SimBackend(FOGActual,SimHActual)) (SimCaller(A))).
 inline SimBad.init;auto.
qed.

(* Count.c counts only unknown-answer calls. A public Decaps request
   invokes that port at most once, after its nD counter is incremented. *)
lemma sim_counted_answer_step
 (O<:SH.HB.Orcl {-SH.HB.Count,-FOBudgetState}) c0 d0 :
 hoare[SH.SimAnswerOfOracle(SH.HB.OrclCount(O)).answer:
 SH.HB.Count.c=c0 /\ FOBudgetState.nD=d0 ==>
 SH.HB.Count.c=c0+1 /\ FOBudgetState.nD=d0].
proof.
 proc;inline SH.HB.OrclCount(O).orcl SH.HB.Count.incr;wp.
 call(_:true ==>true);first by trivial. auto.
qed.
lemma sim_leak_counted_decap_step
 (O<:SH.HB.Orcl {-SH.HB.Count,-FOBudgetState}) c0 d0 :
 hoare[SimLeakDecaps(SimBackend(FOGActual,SimHActual),SH.SimAnswerOfOracle(SH.HB.OrclCount(O))).decap:
 SH.HB.Count.c=c0 /\ FOBudgetState.nD=d0 ==>
 SH.HB.Count.c<=c0+1 /\ FOBudgetState.nD=d0].
proof.
 proc;seq 2:(SH.HB.Count.c=c0 /\ FOBudgetState.nD=d0).
 + wp;call(_:true ==>true);first by trivial. auto.
 if;last by auto;smt().
 call(sim_counted_answer_step O c0 d0);auto;smt().
qed.
lemma sim_counted_d_step
 (O<:SH.HB.Orcl {-SH.HB.Count,-FOBudgetState}) :
 hoare[FOCountDPort(SimLeakDecaps(SimBackend(FOGActual,SimHActual),
  SH.SimAnswerOfOracle(SH.HB.OrclCount(O)))).decap:
 SH.HB.Count.c<=FOBudgetState.nD ==>SH.HB.Count.c<=FOBudgetState.nD].
proof.
 proc;exists* SH.HB.Count.c,FOBudgetState.nD;elim*=>c0 d0.
 call(sim_leak_counted_decap_step O c0 (d0+1)).
 inline FOQueryRequest.d;auto;smt().
qed.

lemma sim_counted_adversary_relation
 (A<:CCAExtendedAdversary {-SH.HB.Count,-FOBudgetState})
 (O<:SH.HB.Orcl {-SH.HB.Count,-FOBudgetState}) :
 hoare[FOCountedA(A,SimLeakHashes(SimBackend(FOGActual,SimHActual)),
  SimLeakDecaps(SimBackend(FOGActual,SimHActual),SH.SimAnswerOfOracle(SH.HB.OrclCount(O)))).guess:
 SH.HB.Count.c<=FOBudgetState.nD ==>SH.HB.Count.c<=FOBudgetState.nD].
proof.
 proc(SH.HB.Count.c<=FOBudgetState.nD);1,2:by auto.
 + proc*;call(_:true ==>true);first by trivial. auto.
 + proc*;call(_:true ==>true);first by trivial. auto.
 + proc*;call(_:true ==>true);first by trivial. auto.
 + proc;call(_:true ==>true);first by trivial. inline FOQueryRequest.h;auto.
 + proc;call(_:true ==>true);first by trivial. inline FOQueryRequest.h;auto.
 exact(sim_counted_d_step O).
qed.

lemma sim_hybrid_count_le_decap
 (A<:CCAExtendedAdversary {-SH.HB.Count,-FOBudgetState})
 (O<:SH.HB.Orcl {-SH.HB.Count,-FOBudgetState}) :
 hoare[SH.HB.Orcln(SimCaller(A,SimBackend(FOGActual,SimHActual)),O).main:
 true ==>SH.HB.Count.c<=FOBudgetState.nD].
proof.
 proc;inline SimCaller(A,SimBackend(FOGActual,SimHActual),SH.HB.OrclCount(O)).main;wp.
 call(sim_counted_adversary_relation A O).
 inline FOBudgetState.configure SH.HB.Count.init;auto.
qed.

lemma sim_hybrid_counted_query_bound
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
  -SimPublic,-SimHistory,-FOContext,-SimBad,-SimSelectedFixed,-SimPhaseInput,-FOBudgetState,
  -SH.HB.Count,-SH.HB.HybOrcl}) :
 (forall (H<:CCAExtendedOraclePort {-A,-FOBudgetState})(D<:CCADecapPort {-A,-FOBudgetState}),
  hoare[FOCountedA(A,H,D).guess:FOBudgetState.nD=0 ==>FOBudgetState.nD<=max 0 budget])=>
 (forall (O<:SH.HB.Orcl {-SH.HB.Count,-SimCaller(A)}),
  hoare[SH.HB.Orcln(SimCaller(A,SimBackend(FOGActual,SimHActual)),O).main:
  true ==>SH.HB.Count.c<=max 0 budget]).
proof.
 move=>hD O.
 have hd:hoare[SH.HB.Orcln(SimCaller(A,SimBackend(FOGActual,SimHActual)),O).main:
 true ==>FOBudgetState.nD<=max 0 budget].
 + proc;inline SimCaller(A,SimBackend(FOGActual,SimHActual),SH.HB.OrclCount(O)).main;wp.
   call(hD (SimLeakHashes(SimBackend(FOGActual,SimHActual)))
    (SimLeakDecaps(SimBackend(FOGActual,SimHActual),SH.SimAnswerOfOracle(SH.HB.OrclCount(O))))).
   inline FOBudgetState.configure SH.HB.Count.init;auto.
 conseq hd (sim_hybrid_count_le_decap A O);smt().
qed.

(* The H-cover condition is needed only before the selected position.
   Selected and subsequent Real answers may create unlogged H entries. *)
op sim_selected_prefix (w:keygen_witness) g pk gm hm history ex (l l0:int) =
 pk=w.`kg_pk /\ acwc2_cache_matches g gm /\
 (l<=l0=>sim_log_included history hm /\ sim_h_cover history hm ex).

lemma sim_selected_public_pk pk0 : hoare[SimLeaksBackend(FOGActual,SimHActual).leaks:
 SimPublic.pk=pk0 ==>SimPublic.pk=pk0].
proof. proc*;call(_:true ==>true);first by trivial. auto. qed.
lemma sim_selected_h_before : hoare[SimLeaksBackend(FOGActual,SimHActual).leaks:
 (SH.HB.HybOrcl.l<=SH.HB.HybOrcl.l0=>
  sim_log_included SimHistory.h ROH.m /\ sim_h_cover SimHistory.h ROH.m FOContext.challenge_h) ==>
 (SH.HB.HybOrcl.l<=SH.HB.HybOrcl.l0=>
  sim_log_included SimHistory.h ROH.m /\ sim_h_cover SimHistory.h ROH.m FOContext.challenge_h)].
proof.
 proc*;case(SH.HB.HybOrcl.l<=SH.HB.HybOrcl.l0).
 + call sim_leaks_h_invariant;auto;smt().
 call(_:true ==>true);first by trivial. auto;smt().
qed.
lemma sim_selected_leaks_invariant w g : hoare[SimLeaksBackend(FOGActual,SimHActual).leaks:
 sim_selected_prefix w g SimPublic.pk ROG.m ROH.m SimHistory.h FOContext.challenge_h SH.HB.HybOrcl.l SH.HB.HybOrcl.l0 ==>
 sim_selected_prefix w g SimPublic.pk ROG.m ROH.m SimHistory.h FOContext.challenge_h SH.HB.HybOrcl.l SH.HB.HybOrcl.l0].
proof.
 rewrite /sim_selected_prefix.
 conseq [-frame] (sim_selected_public_pk w.`kg_pk)
 (_:acwc2_cache_matches g ROG.m /\ (SH.HB.HybOrcl.l<=SH.HB.HybOrcl.l0=>
  sim_log_included SimHistory.h ROH.m /\ sim_h_cover SimHistory.h ROH.m FOContext.challenge_h) ==>
 acwc2_cache_matches g ROG.m /\ (SH.HB.HybOrcl.l<=SH.HB.HybOrcl.l0=>
  sim_log_included SimHistory.h ROH.m /\ sim_h_cover SimHistory.h ROH.m FOContext.challenge_h));try by progress.
 conseq(sim_leaks_cache g) sim_selected_h_before;progress.
qed.
lemma sim_selected_leaks_fresh w g : hoare[SimLeaksBackend(FOGActual,SimHActual).leaks:
 sim_selected_prefix w g SimPublic.pk ROG.m ROH.m SimHistory.h FOContext.challenge_h SH.HB.HybOrcl.l SH.HB.HybOrcl.l0 ==>
 SH.HB.HybOrcl.l<=SH.HB.HybOrcl.l0=>(sim_out_decap res).`1<>None=>
 let q=oget(sim_out_decap res).`1 in q.`sr_pk=w.`kg_pk /\ sim_h_input q \notin ROH.m].
proof.
 rewrite /sim_selected_prefix;proc*;case(SH.HB.HybOrcl.l<=SH.HB.HybOrcl.l0).
 + ecall(sim_leaks_fresh w.`kg_pk SimHistory.h FOContext.challenge_h);auto;smt().
 call(_:true ==>true);first by trivial. auto;smt().
qed.
lemma sim_selected_leaks_state_fresh w g : hoare[SimLeaksBackend(FOGActual,SimHActual).leaks:
 sim_selected_prefix w g SimPublic.pk ROG.m ROH.m SimHistory.h FOContext.challenge_h SH.HB.HybOrcl.l SH.HB.HybOrcl.l0 ==>
 sim_selected_prefix w g SimPublic.pk ROG.m ROH.m SimHistory.h FOContext.challenge_h SH.HB.HybOrcl.l SH.HB.HybOrcl.l0 /\
 (SH.HB.HybOrcl.l<=SH.HB.HybOrcl.l0=>(sim_out_decap res).`1<>None=>
 let q=oget(sim_out_decap res).`1 in q.`sr_pk=w.`kg_pk /\ sim_h_input q \notin ROH.m)].
proof. conseq(sim_selected_leaks_invariant w g)(sim_selected_leaks_fresh w g);progress. qed.

lemma sim_selected_reject_cache g : hoare[SimAnswerRejectGet(FOGActual,SimHActual).answer:
 acwc2_cache_matches g ROG.m ==>acwc2_cache_matches g ROG.m].
proof. proc;wp;call(sim_answer_cache g);auto. qed.

lemma sim_selected_leaks_equiv w g :
 equiv[SimLeaksBackend(FOGActual,SimHActual).leaks ~ SimLeaksBackend(FOGActual,SimHActual).leaks:
 ={arg,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob SimPublic,glob SimHistory,glob FOContext,glob CCADecapOracle} /\
 sim_selected_prefix w g SimPublic.pk{1} ROG.m{1} ROH.m{1} SimHistory.h{1} FOContext.challenge_h{1} SH.HB.HybOrcl.l{1} SH.HB.HybOrcl.l0{1} ==>
 ={res,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob SimPublic,glob SimHistory,glob FOContext,glob CCADecapOracle} /\
 sim_selected_prefix w g SimPublic.pk{1} ROG.m{1} ROH.m{1} SimHistory.h{1} FOContext.challenge_h{1} SH.HB.HybOrcl.l{1} SH.HB.HybOrcl.l0{1} /\
 (SH.HB.HybOrcl.l{1}<=SH.HB.HybOrcl.l0{1}=>(sim_out_decap res{1}).`1<>None=>
 let q=oget(sim_out_decap res{1}).`1 in q.`sr_pk=w.`kg_pk /\ sim_h_input q \notin ROH.m{1})].
proof.
 conseq (_: ={arg,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob SimPublic,glob SimHistory,glob FOContext,glob CCADecapOracle} ==>
 ={res,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob SimPublic,glob SimHistory,glob FOContext,glob CCADecapOracle})
 (sim_selected_leaks_state_fresh w g) _=> //.
 by sim.
qed.

lemma sim_selected_oracle_guarded w g :
 equiv[SH.HB.HybOrcl(SimBackend(FOGActual,SimHActual),SH.SimOracleOfAnswer(SimAnswerRejectGet(FOGActual,SimHActual))).orcl ~
 SH.HB.HybOrcl(SimBackend(FOGActual,SimHActual),SH.SimOracleOfAnswer(SimGuardedReject)).orcl:
 ={arg,ROG.m,ROH.m,glob SimBad,glob SH.HB.HybOrcl} /\ SimSelectedFixed.key{2}=w /\
 sim_selected_prefix w g SimPublic.pk{1} ROG.m{1} ROH.m{1} SimHistory.h{1} FOContext.challenge_h{1} SH.HB.HybOrcl.l{1} SH.HB.HybOrcl.l0{1} /\
 (SH.HB.HybOrcl.l{1}=SH.HB.HybOrcl.l0{1}=>m{1}.`sr_pk=w.`kg_pk /\ sim_h_input m{1} \notin ROH.m{1}) ==>
 ={res,ROG.m,ROH.m,glob SimBad,glob SH.HB.HybOrcl} /\
 sim_selected_prefix w g SimPublic.pk{1} ROG.m{1} ROH.m{1} SimHistory.h{1} FOContext.challenge_h{1} SH.HB.HybOrcl.l{1} SH.HB.HybOrcl.l0{1}].
proof.
 proc;wp;if;first by auto.
 + call(_: ={arg,ROG.m,ROH.m} /\ acwc2_cache_matches g ROG.m{1} ==>
     ={res,ROG.m,ROH.m} /\ acwc2_cache_matches g ROG.m{1}).
   - conseq (_: ={arg,ROG.m,ROH.m} ==> ={res,ROG.m,ROH.m}) (sim_answer_cache g) _=> //;by sim.
   auto=> />;smt().
 if;first by auto.
 + inline SH.SimOracleOfAnswer(SimAnswerRejectGet(FOGActual,SimHActual)).orcl SH.SimOracleOfAnswer(SimGuardedReject).orcl;wp.
   call(_: ={q,ROG.m,ROH.m,glob SimBad} /\ SimSelectedFixed.key{2}=w /\
    q{1}.`sr_pk=w.`kg_pk /\ sim_h_input q{1} \notin ROH.m{1} /\ acwc2_cache_matches g ROG.m{1} ==>
    ={res,ROG.m,ROH.m,glob SimBad} /\ acwc2_cache_matches g ROG.m{1}).
   - conseq(sim_reject_guarded_step w)(sim_selected_reject_cache g) _;progress.
   auto=> />;smt().
 inline SimAnswerNever.answer;auto=> />;smt().
qed.

module SimInvariantRejectOracle=SH.HB.HybOrcl(SimBackend(FOGActual,SimHActual),SH.SimOracleOfAnswer(SimAnswerRejectGet(FOGActual,SimHActual))).
module SimInvariantGuardedOracle=SH.HB.HybOrcl(SimBackend(FOGActual,SimHActual),SH.SimOracleOfAnswer(SimGuardedReject)).
module SimInvariantRejectD=SimLeakDecaps(SimBackend(FOGActual,SimHActual),SH.SimAnswerOfOracle(SimInvariantRejectOracle)).
module SimInvariantGuardedD=SimLeakDecaps(SimBackend(FOGActual,SimHActual),SH.SimAnswerOfOracle(SimInvariantGuardedOracle)).

lemma sim_selected_answer_guarded w g :
 equiv[SH.SimAnswerOfOracle(SimInvariantRejectOracle).answer ~ SH.SimAnswerOfOracle(SimInvariantGuardedOracle).answer:
 ={q,ROG.m,ROH.m,glob SimBad,glob SH.HB.HybOrcl} /\ SimSelectedFixed.key{2}=w /\
 sim_selected_prefix w g SimPublic.pk{1} ROG.m{1} ROH.m{1} SimHistory.h{1} FOContext.challenge_h{1} SH.HB.HybOrcl.l{1} SH.HB.HybOrcl.l0{1} /\
 (SH.HB.HybOrcl.l{1}=SH.HB.HybOrcl.l0{1}=>q{1}.`sr_pk=w.`kg_pk /\ sim_h_input q{1} \notin ROH.m{1}) ==>
 ={res,ROG.m,ROH.m,glob SimBad,glob SH.HB.HybOrcl} /\ sim_selected_prefix w g SimPublic.pk{1} ROG.m{1} ROH.m{1} SimHistory.h{1} FOContext.challenge_h{1} SH.HB.HybOrcl.l{1} SH.HB.HybOrcl.l0{1}].
proof. proc;call(sim_selected_oracle_guarded w g);auto. qed.

lemma sim_selected_decap_guarded w g :
 equiv[SimInvariantRejectD.decap ~ SimInvariantGuardedD.decap:
 ={ct,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob SimPublic,glob SimHistory,glob FOContext,glob CCADecapOracle,glob SimBad,glob SH.HB.HybOrcl} /\ SimSelectedFixed.key{2}=w /\ sim_selected_prefix w g SimPublic.pk{1} ROG.m{1} ROH.m{1} SimHistory.h{1} FOContext.challenge_h{1} SH.HB.HybOrcl.l{1} SH.HB.HybOrcl.l0{1} ==>
 ={res,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob SimPublic,glob SimHistory,glob FOContext,glob CCADecapOracle,glob SimBad,glob SH.HB.HybOrcl} /\ sim_selected_prefix w g SimPublic.pk{1} ROG.m{1} ROH.m{1} SimHistory.h{1} FOContext.challenge_h{1} SH.HB.HybOrcl.l{1} SH.HB.HybOrcl.l0{1}].
proof.
 proc;seq 2 2:(={request,reply,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob SimPublic,glob SimHistory,glob FOContext,glob CCADecapOracle,glob SimBad,glob SH.HB.HybOrcl} /\ SimSelectedFixed.key{2}=w /\ sim_selected_prefix w g SimPublic.pk{1} ROG.m{1} ROH.m{1} SimHistory.h{1} FOContext.challenge_h{1} SH.HB.HybOrcl.l{1} SH.HB.HybOrcl.l0{1} /\
  (SH.HB.HybOrcl.l{1}<=SH.HB.HybOrcl.l0{1}=>request{1}<>None=>
   (oget request{1}).`sr_pk=w.`kg_pk /\ sim_h_input(oget request{1}) \notin ROH.m{1})).
 + wp;call(sim_selected_leaks_equiv w g);auto;progress.
 if;first by auto.
 + call(sim_selected_answer_guarded w g);auto;smt().
 auto.
qed.

lemma sim_selected_caller_guarded
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
  -SimPublic,-SimHistory,-FOContext,-SimBad,-SimSelectedFixed,-SimPhaseInput,-FOBudgetState,
  -SH.HB.Count,-SH.HB.HybOrcl}) w g :
 equiv[SimCaller(A,SimBackend(FOGActual,SimHActual),SimInvariantRejectOracle).main ~ SimCaller(A,SimBackend(FOGActual,SimHActual),SimInvariantGuardedOracle).main:
 ={glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob SimPublic,glob SimHistory,glob FOContext,glob CCADecapOracle,glob SimBad,glob SH.HB.HybOrcl,glob FOBudgetState,glob SimPhaseInput} /\ SimSelectedFixed.key{2}=w /\ sim_selected_prefix w g SimPublic.pk{1} ROG.m{1} ROH.m{1} SimHistory.h{1} FOContext.challenge_h{1} SH.HB.HybOrcl.l{1} SH.HB.HybOrcl.l0{1} ==>
 ={res,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob SimPublic,glob SimHistory,glob FOContext,glob CCADecapOracle,glob SimBad,glob SH.HB.HybOrcl,glob FOBudgetState,glob SimPhaseInput} /\ sim_selected_prefix w g SimPublic.pk{1} ROG.m{1} ROH.m{1} SimHistory.h{1} FOContext.challenge_h{1} SH.HB.HybOrcl.l{1} SH.HB.HybOrcl.l0{1}].
proof.
 proc;wp;call(_: ={glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob SimPublic,glob SimHistory,glob FOContext,glob CCADecapOracle,glob SimBad,glob SH.HB.HybOrcl,glob FOBudgetState,glob SimPhaseInput} /\ SimSelectedFixed.key{2}=w /\ sim_selected_prefix w g SimPublic.pk{1} ROG.m{1} ROH.m{1} SimHistory.h{1} FOContext.challenge_h{1} SH.HB.HybOrcl.l{1} SH.HB.HybOrcl.l0{1}).
 + proc;wp;call(sim_selected_leaks_equiv w g);auto;progress.
 + proc;wp;call(sim_selected_leaks_equiv w g);auto;progress.
 + proc;wp;call(sim_selected_leaks_equiv w g);auto;progress.
 + proc;inline SimLeakHashes(SimBackend(FOGActual,SimHActual)).h;wp.
   call(sim_selected_leaks_equiv w g);inline FOQueryRequest.h;auto;progress.
 + proc;inline SimLeakHashes(SimBackend(FOGActual,SimHActual)).raw;wp.
   call(sim_selected_leaks_equiv w g);inline FOQueryRequest.h;auto;progress.
 + proc;call(sim_selected_decap_guarded w g);inline FOQueryRequest.d;auto;progress.
 inline FOBudgetState.configure;auto.
qed.

lemma sim_selected_context_guarded
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
  -SimPublic,-SimHistory,-FOContext,-SimBad,-SimSelectedFixed,-SimPhaseInput,-FOBudgetState,
  -SH.HB.Count,-SH.HB.HybOrcl}) w g :
 equiv[SimSelectedContext(A,FOGActual,SimHActual,SimAnswerRejectGet(FOGActual,SimHActual)).distinguish ~
 SimSelectedContext(A,FOGActual,SimHActual,SimGuardedReject).distinguish:
 ={s,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob SimPublic,glob SimHistory,glob FOContext,glob CCADecapOracle,glob SimBad,glob SH.HB.HybOrcl,glob FOBudgetState,glob SimPhaseInput} /\ SimSelectedFixed.key{2}=w /\
 SimPublic.pk{1}=w.`kg_pk /\ acwc2_cache_matches g ROG.m{1} /\
 sim_log_included SimHistory.h{1} ROH.m{1} /\ sim_h_cover SimHistory.h{1} ROH.m{1} FOContext.challenge_h{1} ==>
 ={res,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob SimPublic,glob SimHistory,glob FOContext,glob CCADecapOracle,glob SimBad,glob SH.HB.HybOrcl,glob FOBudgetState,glob SimPhaseInput}].
proof.
 proc;inline SH.HB.HybGame(SimCaller(A),SimBackend(FOGActual,SimHActual),SH.SimOracleOfAnswer(SimAnswerRejectGet(FOGActual,SimHActual))).main
  SH.HB.HybGame(SimCaller(A),SimBackend(FOGActual,SimHActual),SH.SimOracleOfAnswer(SimGuardedReject)).main;wp.
 call(sim_selected_caller_guarded A w g).
 wp;rnd;auto=> />;rewrite /sim_selected_prefix;progress.
qed.

(* Both programs initialize the hidden marker, and only the guarded side
   initializes its private fixed witness. Physical tables are not reset. *)
lemma sim_selected_reject_guarded
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
  -SimPublic,-SimHistory,-FOContext,-SimBad,-SimSelectedFixed,-SimPhaseInput,-FOBudgetState,
  -SH.HB.Count,-SH.HB.HybOrcl}) w0 g0 :
 equiv[SimSelectedReject(A).distinguish ~ SimSelectedGuarded(A).run:
 w{2}=w0 /\ g{2}=g0 /\ ={s,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob SimPublic,glob SimHistory,glob FOContext,glob CCADecapOracle,glob SimBad,glob SH.HB.HybOrcl,glob FOBudgetState,glob SimPhaseInput} /\
 SimPublic.pk{1}=w0.`kg_pk /\ acwc2_cache_matches g0 ROG.m{1} /\
 sim_log_included SimHistory.h{1} ROH.m{1} /\ sim_h_cover SimHistory.h{1} ROH.m{1} FOContext.challenge_h{1} ==>
 ={res,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob SimPublic,glob SimHistory,glob FOContext,glob CCADecapOracle,glob SimBad,glob SH.HB.HybOrcl,glob FOBudgetState,glob SimPhaseInput}].
proof.
 proc;call(sim_selected_context_guarded A w0 g0).
 inline SimBad.init;auto.
qed.
