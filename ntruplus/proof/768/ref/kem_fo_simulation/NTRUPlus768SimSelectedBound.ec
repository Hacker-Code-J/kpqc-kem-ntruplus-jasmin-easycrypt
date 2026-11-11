require import AllCore Distr DInterval FMap StdOrder.
from Jasmin require import JWord.
require import Array32.
require import NTRUPlus768SimModel NTRUPlus768SimSampling NTRUPlus768SimAnswer.
require import NTRUPlus768SimAnswerErasure NTRUPlus768SimPorts NTRUPlus768SimSelected.
require import NTRUPlus768FOModel NTRUPlus768FOQueryBudget NTRUPlus768FOEagerG.
require import NTRUPlus768FOCapRemoval NTRUPlus768RawXOF.
require import NTRUPlus768FOGAdapters NTRUPlus768FOKEMGame NTRUPlus768FOSetupDistribution.
require import NTRUPlus768ROMOracles NTRUPlus768RawXOFStreams NTRUPlus768CCADecapOracle NTRUPlus768CCAGame.
require import NTRUPlus768PKEModel NTRUPlus768ACWC2Oracle NTRUPlus768FOError.
import RealOrder SimSelectedBudget.

lemma sim_hyb_oracle_ll (B<:SH.HB.Orclb)(O<:SH.HB.Orcl) :
 islossless B.orclL=>islossless B.orclR=>islossless O.orcl=>
 islossless SH.HB.HybOrcl(B,O).orcl.
proof.
 move=>hl hr ho;proc;wp;if;first by call hl;auto.
 if;[call ho|call hr];auto.
qed.

lemma sim_counted_adaptive_ll
 (A<:CCAExtendedAdversary {-FOBudgetState})
 (B<:SimLeaks {-A,-FOBudgetState})(U<:SimAnswer {-A,-FOBudgetState}) :
 islossless B.leaks=>islossless U.answer=>
 (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess)=>
 islossless FOCountedA(A,SimLeakHashes(B),SimLeakDecaps(B,U)).guess.
proof.
 move=>hb hu ha.
 exact(ha (FOCountHPort(SimLeakHashes(B))) (FOCountDPort(SimLeakDecaps(B,U)))
  (sim_leak_e_ll B hb)(sim_leak_f_ll B hb)(sim_leak_g_ll B hb)
  (fo_count_h_ll (SimLeakHashes(B)) (sim_leak_h_ll B hb))
  (fo_count_raw_ll (SimLeakHashes(B)) (sim_leak_raw_ll B hb))
  (fo_count_d_ll (SimLeakDecaps(B,U)) (sim_leak_decap_ll B U hb hu))).
qed.

lemma sim_caller_lossless
 (A<:CCAExtendedAdversary {-FOBudgetState})
 (B<:SH.HB.Orclb {-A,-FOBudgetState})(O<:SH.HB.Orcl {-A,-FOBudgetState}) :
 islossless B.leaks=>islossless O.orcl=>
 (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess)=>
 islossless SimCaller(A,B,O).main.
proof.
 move=>hb ho ha;proc.
 call(sim_counted_adaptive_ll A B (SH.SimAnswerOfOracle(O)) hb
  (SH.sim_answer_of_oracle_ll O ho) ha).
 call fo_budget_configure_ll;auto.
qed.

(* The standard Hybrid game samples [0..max 0 (q-1)]. Its selection
   distribution remains lossless when q=0; no positive-budget premise
   or termination inference from a query bound is used here. *)
lemma sim_selected_context_ll
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
  -FOPublicKey,-FOContext,-FOBadState,-FOBudgetState,-SimPublic,-SimHistory,-SimBad,
  -SimSelectedFixed,-SimPhaseInput,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,
  -SH.HB.Count,-SH.HB.HybOrcl}) :
 (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess)=>
 forall(G<:FOGPort {-SimSelectedContext(A)})(H<:SimHPort {-SimSelectedContext(A)})
       (D<:SimAnswer {-SimSelectedContext(A)}),
 islossless G.get=>islossless H.get=>islossless D.answer=>
 islossless SimSelectedContext(A,G,H,D).distinguish.
proof.
 move=>ha G H D hg hh hd.
 have hb:=sim_leaks_backend_ll G H hg hh.
 have hl:=sim_answer_real_ll G H hg hh.
 have hr:=sim_answer_never_ll.
 have ho:=SH.sim_oracle_of_answer_ll D hd.
 have hs:=sim_hyb_oracle_ll (SimBackend(G,H)) (SH.SimOracleOfAnswer(D)) hl hr ho.
 have hc:=sim_caller_lossless A (SimBackend(G,H))
  (SH.HB.HybOrcl(SimBackend(G,H),SH.SimOracleOfAnswer(D))) hb hs ha.
 proc;inline SH.HB.HybGame(SimCaller(A),SimBackend(G,H),SH.SimOracleOfAnswer(D)).main.
 wp;call hc;wp;rnd;auto=> />;rewrite dinter_ll;smt().
qed.

require import NTRUPlus768SimSelectedCoupling.

lemma sim_real_context_self
 (C<:SimAnswerContext {-ROG,-ROH,-SimBad}) :
 equiv[C(FOGActual,SimHActual,SimAnswerReal(FOGActual,SimHActual)).distinguish ~
       C(FOGActual,SimHActual,SimAnswerReal(FOGActual,SimHActual)).distinguish:
 ={arg,glob C,ROG.m,ROH.m} ==> ={res,glob C,ROG.m,ROH.m}].
proof.
 proc(={ROG.m,ROH.m});1,2:by auto.
 + by sim.
 + by sim.
 by sim.
qed.

lemma sim_never_context_self
 (C<:SimAnswerContext {-ROG,-ROH,-SimBad}) :
 equiv[C(FOGActual,SimHActual,SimAnswerNever).distinguish ~
       C(FOGActual,SimHActual,SimAnswerNever).distinguish:
 ={arg,glob C,ROG.m,ROH.m} ==> ={res,glob C,ROG.m,ROH.m}].
proof.
 proc(={ROG.m,ROH.m});1,2:by auto.
 + by sim.
 + by sim.
 by sim.
qed.

lemma sim_reject_context_self
 (C<:SimAnswerContext {-ROG,-ROH,-SimBad}) :
 equiv[C(FOGActual,SimHActual,SimAnswerRejectGet(FOGActual,SimHActual)).distinguish ~
       C(FOGActual,SimHActual,SimAnswerRejectGet(FOGActual,SimHActual)).distinguish:
 ={arg,glob C,ROG.m,ROH.m,glob SimBad} ==> ={res,glob C,ROG.m,ROH.m,glob SimBad}].
proof.
 proc(={ROG.m,ROH.m,glob SimBad});1,2:by auto.
 + by sim.
 + by sim.
 by sim.
qed.

lemma sim_selected_real_context (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
  -FOPublicKey,-FOContext,-FOBadState,-FOBudgetState,-SimPublic,-SimHistory,-SimBad,
  -SimSelectedFixed,-SimPhaseInput,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,
  -SH.HB.Count,-SH.HB.HybOrcl}) &m s0 :
 Pr[SimSelectedReal(A).distinguish(s0) @ &m:res]=
 Pr[SimRealContext(SimSelectedContext(A)).run(s0) @ &m:res].
proof.
 byequiv(_: ={arg,glob SimSelectedReal(A)} ==> ={res})=> //.
 proc;call(sim_real_context_self (SimSelectedContext(A)));inline SimBad.init;auto.
qed.
lemma sim_selected_never_context (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
  -FOPublicKey,-FOContext,-FOBadState,-FOBudgetState,-SimPublic,-SimHistory,-SimBad,
  -SimSelectedFixed,-SimPhaseInput,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,
  -SH.HB.Count,-SH.HB.HybOrcl}) &m s0 :
 Pr[SimSelectedNever(A).distinguish(s0) @ &m:res]=
 Pr[SimNeverContext(SimSelectedContext(A)).run(s0) @ &m:res].
proof.
 byequiv(_: ={arg,glob SimSelectedNever(A)} ==> ={res})=> //.
 proc;call(sim_never_context_self (SimSelectedContext(A)));inline SimBad.init;auto.
qed.
lemma sim_selected_reject_context (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
  -FOPublicKey,-FOContext,-FOBadState,-FOBudgetState,-SimPublic,-SimHistory,-SimBad,
  -SimSelectedFixed,-SimPhaseInput,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,
  -SH.HB.Count,-SH.HB.HybOrcl}) &m s0 :
 Pr[SimSelectedReject(A).distinguish(s0) @ &m:SimBad.hidden]=
 Pr[SimRejectContext(SimSelectedContext(A)).run(s0) @ &m:SimBad.hidden].
proof.
 byequiv(_: ={arg,glob SimSelectedReject(A)} ==> ={SimBad.hidden})=> //.
 proc;call(sim_reject_context_self (SimSelectedContext(A)));inline SimBad.init;auto.
qed.

lemma sim_selected_distance_bad
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
  -FOPublicKey,-FOContext,-FOBadState,-FOBudgetState,-SimPublic,-SimHistory,-SimBad,
  -SimSelectedFixed,-SimPhaseInput,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,
  -SH.HB.Count,-SH.HB.HybOrcl}) g s0 &m :
 acwc2_cache_matches g ROG.m{m}=>
 (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess)=>
 `|Pr[SimSelectedReal(A).distinguish(s0) @ &m:res]-
   Pr[SimSelectedNever(A).distinguish(s0) @ &m:res]|
 <=Pr[SimSelectedReject(A).distinguish(s0) @ &m:SimBad.hidden].
proof.
 move=>hg ha.
 rewrite(sim_selected_real_context A &m s0)(sim_selected_never_context A &m s0)
  (sim_selected_reject_context A &m s0).
 exact(sim_context_real_never_distance (SimSelectedContext(A)) g &m s0 hg
  (sim_selected_context_ll A ha)).
qed.

lemma sim_hyb_real_adapter
 (A<:SH.HB.AdvOrclb {-SH.HB.HybOrcl,-SimBackend(FOGActual,SimHActual)}) :
 equiv[SH.HB.HybGame(A,SimBackend(FOGActual,SimHActual),SH.SimOracleOfAnswer(SimAnswerReal(FOGActual,SimHActual))).main ~
       SH.HB.HybGame(A,SimBackend(FOGActual,SimHActual),SH.HB.L(SimBackend(FOGActual,SimHActual))).main:
 ={glob A,glob SimBackend(FOGActual,SimHActual)} ==> ={res,glob A,glob SimBackend(FOGActual,SimHActual)}].
proof.
 proc;call(_: ={glob SimBackend(FOGActual,SimHActual),glob SH.HB.HybOrcl}).
 + proc;wp;if=> //.
   - by sim.
   if=> //.
   - inline{1} SH.SimOracleOfAnswer(SimAnswerReal(FOGActual,SimHActual)).orcl;sim.
   by sim.
 + by sim.
 + by sim.
 + by sim.
 wp;rnd;auto.
qed.

lemma sim_hyb_never_adapter
 (A<:SH.HB.AdvOrclb {-SH.HB.HybOrcl,-SimBackend(FOGActual,SimHActual)}) :
 equiv[SH.HB.HybGame(A,SimBackend(FOGActual,SimHActual),SH.SimOracleOfAnswer(SimAnswerNever)).main ~
       SH.HB.HybGame(A,SimBackend(FOGActual,SimHActual),SH.HB.R(SimBackend(FOGActual,SimHActual))).main:
 ={glob A,glob SimBackend(FOGActual,SimHActual)} ==> ={res,glob A,glob SimBackend(FOGActual,SimHActual)}].
proof.
 proc;call(_: ={glob SimBackend(FOGActual,SimHActual),glob SH.HB.HybOrcl}).
 + proc;wp;if=> //.
   - by sim.
   if=> //.
   - inline{1} SH.SimOracleOfAnswer(SimAnswerNever).orcl;sim.
   by sim.
 + by sim.
 + by sim.
 + by sim.
 wp;rnd;auto.
qed.

lemma sim_selected_real_hybrid (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
  -FOPublicKey,-FOContext,-FOBadState,-FOBudgetState,-SimPublic,-SimHistory,-SimBad,
  -SimSelectedFixed,-SimPhaseInput,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,
  -SH.HB.Count,-SH.HB.HybOrcl}) &m s0 :
 Pr[SimSelectedReal(A).distinguish(s0) @ &m:res]=
 Pr[SH.HB.HybGame(SimCaller(A),SimBackend(FOGActual,SimHActual),
  SH.HB.L(SimBackend(FOGActual,SimHActual))).main() @ &m:res].
proof.
 byequiv(_: ={glob SimCaller(A),glob SimBackend(FOGActual,SimHActual)} ==> ={res})=> //.
 proc*;inline SimSelectedExperiment(A,FOGActual,SimHActual,SimAnswerReal(FOGActual,SimHActual)).distinguish
  SimSelectedContext(A,FOGActual,SimHActual,SimAnswerReal(FOGActual,SimHActual)).distinguish SimBad.init.
 wp;call(sim_hyb_real_adapter (SimCaller(A)));auto.
qed.
lemma sim_selected_never_hybrid (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
  -FOPublicKey,-FOContext,-FOBadState,-FOBudgetState,-SimPublic,-SimHistory,-SimBad,
  -SimSelectedFixed,-SimPhaseInput,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,
  -SH.HB.Count,-SH.HB.HybOrcl}) &m s0 :
 Pr[SimSelectedNever(A).distinguish(s0) @ &m:res]=
 Pr[SH.HB.HybGame(SimCaller(A),SimBackend(FOGActual,SimHActual),
  SH.HB.R(SimBackend(FOGActual,SimHActual))).main() @ &m:res].
proof.
 byequiv(_: ={glob SimCaller(A),glob SimBackend(FOGActual,SimHActual)} ==> ={res})=> //.
 proc*;inline SimSelectedExperiment(A,FOGActual,SimHActual,SimAnswerNever).distinguish
  SimSelectedContext(A,FOGActual,SimHActual,SimAnswerNever).distinguish SimBad.init.
 wp;call(sim_hyb_never_adapter (SimCaller(A)));auto.
qed.

lemma sim_hybrid_real_phase (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
  -FOPublicKey,-FOContext,-FOBadState,-FOBudgetState,-SimPublic,-SimHistory,-SimBad,
  -SimSelectedFixed,-SimPhaseInput,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,
  -SH.HB.Count,-SH.HB.HybOrcl}) &m s0 :
 Pr[SH.HB.Ln(SimBackend(FOGActual,SimHActual),SimCaller(A)).main() @ &m:res]=
 Pr[SimAdaptive(A,SimLeaksBackend(FOGActual,SimHActual),SimAnswerReal(FOGActual,SimHActual)).distinguish(s0) @ &m:res].
proof.
 byequiv(_: ={glob A,glob SimBackend(FOGActual,SimHActual),glob SimPhaseInput} ==> ={res})=> //.
 proc;inline{1} SimCaller(A,SimBackend(FOGActual,SimHActual),SH.HB.OrclCount(SH.HB.L(SimBackend(FOGActual,SimHActual)))).main;wp.
 call(_: ={glob SimBackend(FOGActual,SimHActual),glob SimPhaseInput}).
 + by sim.
 + by sim.
 + by sim.
 + proc;inline{1} SimLeakHashes(SimBackend(FOGActual,SimHActual)).h.
   inline FOQueryRequest.h;wp;sp.
   call(_: ={arg,glob SimBackend(FOGActual,SimHActual)} ==> ={res,glob SimBackend(FOGActual,SimHActual)});first by sim.
   auto.
 + proc;inline{1} SimLeakHashes(SimBackend(FOGActual,SimHActual)).raw.
   wp;call(_: ={arg,glob SimBackend(FOGActual,SimHActual)} ==> ={res,glob SimBackend(FOGActual,SimHActual)});first by sim.
   inline FOQueryRequest.h;auto.
 + proc;inline{1} SimLeakDecaps(SimBackend(FOGActual,SimHActual),SH.SimAnswerOfOracle(SH.HB.OrclCount(SH.HB.L(SimBackend(FOGActual,SimHActual))))).decap.
   inline FOQueryRequest.d;wp;sp 5 0.
   seq 2 2:(={request,reply,glob SimBackend(FOGActual,SimHActual),glob SimPhaseInput}).
   - wp;call(_: ={arg,glob SimBackend(FOGActual,SimHActual)} ==> ={res,glob SimBackend(FOGActual,SimHActual)});first by sim.
     auto.
   if=> //.
   - inline{1} SH.SimAnswerOfOracle(SH.HB.OrclCount(SH.HB.L(SimBackend(FOGActual,SimHActual)))).answer
      SH.HB.OrclCount(SH.HB.L(SimBackend(FOGActual,SimHActual))).orcl SH.HB.Count.incr;wp;sp.
     call(_: ={arg,ROG.m,ROH.m} ==> ={res,ROG.m,ROH.m});first by sim.
     auto.
   auto.
 inline FOBudgetState.configure SH.HB.Count.init;auto.
qed.

lemma sim_hybrid_never_phase (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
  -FOPublicKey,-FOContext,-FOBadState,-FOBudgetState,-SimPublic,-SimHistory,-SimBad,
  -SimSelectedFixed,-SimPhaseInput,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,
  -SH.HB.Count,-SH.HB.HybOrcl}) &m s0 :
 Pr[SH.HB.Rn(SimBackend(FOGActual,SimHActual),SimCaller(A)).main() @ &m:res]=
 Pr[SimAdaptive(A,SimLeaksBackend(FOGActual,SimHActual),SimAnswerNever).distinguish(s0) @ &m:res].
proof.
 byequiv(_: ={glob A,glob SimBackend(FOGActual,SimHActual),glob SimPhaseInput} ==> ={res})=> //.
 proc;inline{1} SimCaller(A,SimBackend(FOGActual,SimHActual),SH.HB.OrclCount(SH.HB.R(SimBackend(FOGActual,SimHActual)))).main;wp.
 call(_: ={glob SimBackend(FOGActual,SimHActual),glob SimPhaseInput}).
 + by sim.
 + by sim.
 + by sim.
 + proc;inline{1} SimLeakHashes(SimBackend(FOGActual,SimHActual)).h.
   inline FOQueryRequest.h;wp;sp.
   call(_: ={arg,glob SimBackend(FOGActual,SimHActual)} ==> ={res,glob SimBackend(FOGActual,SimHActual)});first by sim.
   auto.
 + proc;inline{1} SimLeakHashes(SimBackend(FOGActual,SimHActual)).raw.
   wp;call(_: ={arg,glob SimBackend(FOGActual,SimHActual)} ==> ={res,glob SimBackend(FOGActual,SimHActual)});first by sim.
   inline FOQueryRequest.h;auto.
 + proc;inline{1} SimLeakDecaps(SimBackend(FOGActual,SimHActual),SH.SimAnswerOfOracle(SH.HB.OrclCount(SH.HB.R(SimBackend(FOGActual,SimHActual))))).decap.
   inline FOQueryRequest.d;wp;sp 5 0.
   seq 2 2:(={request,reply,glob SimBackend(FOGActual,SimHActual),glob SimPhaseInput}).
   - wp;call(_: ={arg,glob SimBackend(FOGActual,SimHActual)} ==> ={res,glob SimBackend(FOGActual,SimHActual)});first by sim.
     auto.
   if=> //.
   - inline{1} SH.SimAnswerOfOracle(SH.HB.OrclCount(SH.HB.R(SimBackend(FOGActual,SimHActual)))).answer
      SH.HB.OrclCount(SH.HB.R(SimBackend(FOGActual,SimHActual))).orcl SH.HB.Count.incr;wp;sp.
     call(_: ={arg,ROG.m,ROH.m} ==> ={res,ROG.m,ROH.m});first by sim.
     auto.
   auto.
 inline FOBudgetState.configure SH.HB.Count.init;auto.
qed.

require import NTRUPlus768SimSelectedInvariant.

lemma sim_guard_context_self
 (C<:SimAnswerContext {-ROG,-ROH,-SimBad,-SimSelectedFixed}) :
 equiv[C(FOGActual,SimHActual,SimGuardedReject).distinguish ~
       C(FOGActual,SimHActual,SimGuardedReject).distinguish:
 ={arg,glob C,ROG.m,ROH.m,glob SimBad,glob SimSelectedFixed} ==>
 ={res,glob C,ROG.m,ROH.m,glob SimBad,glob SimSelectedFixed}].
proof.
 proc(={ROG.m,ROH.m,glob SimBad,glob SimSelectedFixed});1,2:by auto.
 + by sim.
 + by sim.
 by sim.
qed.

lemma sim_actual_guarded_bad (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
  -FOPublicKey,-FOContext,-FOBadState,-FOBudgetState,-SimPublic,-SimHistory,-SimBad,
  -SimSelectedFixed,-SimPhaseInput,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,
  -SH.HB.Count,-SH.HB.HybOrcl}) w g s0 &m :
 pke_key_relation w=>acwc2_cache_matches g ROG.m{m}=>
 Pr[SimSelectedGuarded(A).run(w,g,s0) @ &m:SimBad.hidden]
 <=1%r/(2%r^768)+fo_error w g.
proof.
 move=>hk hg.
 have he:equiv[SimSelectedGuarded(A).run ~ SimSelectedGuarded(A).run:
  ={arg,glob SimSelectedGuarded(A)} ==> ={SimBad.hidden} /\ SimBad.selected_calls{2}<=1].
 + conseq(_: ={arg,glob SimSelectedGuarded(A)} ==> ={SimBad.hidden})
    _ (sim_guarded_selected_once A)=> //.
   proc;call(sim_guard_context_self (SimSelectedContext(A)));inline SimBad.init;auto.
 have hp:Pr[SimSelectedGuarded(A).run(w,g,s0) @ &m:SimBad.hidden]=
  Pr[SimSelectedGuarded(A).run(w,g,s0) @ &m:SimBad.hidden /\ SimBad.selected_calls<=1]
  by byequiv he=> //;smt().
 rewrite hp.
 exact(sim_guarded_context_bad (SimSelectedContext(A)) w g s0 &m hk hg).
qed.

lemma sim_actual_selected_bad (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
  -FOPublicKey,-FOContext,-FOBadState,-FOBudgetState,-SimPublic,-SimHistory,-SimBad,
  -SimSelectedFixed,-SimPhaseInput,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,
  -SH.HB.Count,-SH.HB.HybOrcl}) w g s0 &m :
 pke_key_relation w=>SimPublic.pk{m}=w.`kg_pk=>
 acwc2_cache_matches g ROG.m{m}=>
 sim_log_included SimHistory.h{m} ROH.m{m}=>
 sim_h_cover SimHistory.h{m} ROH.m{m} FOContext.challenge_h{m}=>
 Pr[SimSelectedReject(A).distinguish(s0) @ &m:SimBad.hidden]
 <=1%r/(2%r^768)+fo_error w g.
proof.
 move=>hk hp hg hi hc.
 have he:Pr[SimSelectedReject(A).distinguish(s0) @ &m:SimBad.hidden]=
  Pr[SimSelectedGuarded(A).run(w,g,s0) @ &m:SimBad.hidden]
  by byequiv(sim_selected_reject_guarded A w g)=> //.
 rewrite he;exact(sim_actual_guarded_bad A w g s0 &m hk hg).
qed.

lemma sim_actual_selected_distance (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
  -FOPublicKey,-FOContext,-FOBadState,-FOBudgetState,-SimPublic,-SimHistory,-SimBad,
  -SimSelectedFixed,-SimPhaseInput,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,
  -SH.HB.Count,-SH.HB.HybOrcl}) w g s0 &m :
 pke_key_relation w=>SimPublic.pk{m}=w.`kg_pk=>
 acwc2_cache_matches g ROG.m{m}=>
 sim_log_included SimHistory.h{m} ROH.m{m}=>
 sim_h_cover SimHistory.h{m} ROH.m{m} FOContext.challenge_h{m}=>
 (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess)=>
 `|Pr[SimSelectedReal(A).distinguish(s0) @ &m:res]-
   Pr[SimSelectedNever(A).distinguish(s0) @ &m:res]|
 <=1%r/(2%r^768)+fo_error w g.
proof.
 move=>hk hp hg hi hc ha.
 exact(ler_trans _ _ _ (sim_selected_distance_bad A g s0 &m hg ha)
  (sim_actual_selected_bad A w g s0 &m hk hp hg hi hc)).
qed.

(* Counted wrappers never cap a request. Both final endpoints below are
   the original adaptive phases, after erasing their proof counters. *)
lemma sim_real_known_phase_distance (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
  -FOPublicKey,-FOContext,-FOBadState,-FOBudgetState,-SimPublic,-SimHistory,-SimBad,
  -SimSelectedFixed,-SimPhaseInput,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,
  -SH.HB.Count,-SH.HB.HybOrcl}) w g s0 &m :
 pke_key_relation w=>SimPublic.pk{m}=w.`kg_pk=>
 acwc2_cache_matches g ROG.m{m}=>
 sim_log_included SimHistory.h{m} ROH.m{m}=>
 sim_h_cover SimHistory.h{m} ROH.m{m} FOContext.challenge_h{m}=>
 (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess)=>
 (forall(H<:CCAExtendedOraclePort {-A,-FOBudgetState})(D<:CCADecapPort {-A,-FOBudgetState}),
  hoare[FOCountedA(A,H,D).guess:FOBudgetState.nD=0 ==>
   FOBudgetState.nD<=max 0 budget])=>
 `|Pr[SimAdaptive(A,SimLeaksBackend(FOGActual,SimHActual),SimAnswerReal(FOGActual,SimHActual)).distinguish(s0) @ &m:res]-
   Pr[SimAdaptive(A,SimLeaksBackend(FOGActual,SimHActual),SimAnswerNever).distinguish(s0) @ &m:res]|
 <=(max 0 budget)%r*(1%r/(2%r^768)+fo_error w g).
proof.
 move=>hk hp hg hi hc ha hD.
 have hcalls:=sim_hybrid_counted_query_bound A hD.
 have hlk:=sim_leaks_backend_ll FOGActual SimHActual rog_get_ll roh_get_ll.
 have hleft:=sim_answer_real_ll FOGActual SimHActual rog_get_ll roh_get_ll.
 have hright:=sim_answer_never_ll.
 have hall:forall(B<:SH.HB.Orclb {-SimCaller(A)})(O<:SH.HB.Orcl {-SimCaller(A)}),
  islossless O.orcl=>islossless B.leaks=>islossless B.orclL=>islossless B.orclR=>
  islossless SimCaller(A,B,O).main.
 + move=>B O ho hb hL hR;exact(sim_caller_lossless A B O hb ho ha).
 have hs:=sim_actual_selected_distance A w g s0 &m hk hp hg hi hc ha.
 move:hs;rewrite(sim_selected_real_hybrid A &m s0)(sim_selected_never_hybrid A &m s0)=>hs.
 have h:=SH.sim_hybrid_distance (SimBackend(FOGActual,SimHActual)) (SimCaller(A)) &m
  (1%r/(2%r^768)+fo_error w g) hcalls hlk hleft hright hall hs.
 by move:h;rewrite(sim_hybrid_real_phase A &m s0)(sim_hybrid_never_phase A &m s0).
qed.
