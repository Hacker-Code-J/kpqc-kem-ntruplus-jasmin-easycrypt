require import AllCore Distr FMap StdOrder.
from Jasmin require import JWord.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768PKEModel NTRUPlus768ACWC2Oracle NTRUPlus768DecapCompleteSpec.
require import NTRUPlus768FOModel NTRUPlus768FOError NTRUPlus768FOEagerG NTRUPlus768FOGAdapters NTRUPlus768FOQueryBudget NTRUPlus768FOHMonitor.
require import NTRUPlus768FOSetupDistribution NTRUPlus768FOSetupExpectation NTRUPlus768FOKEMGame NTRUPlus768FOJointGames.
require import NTRUPlus768ROMOracles NTRUPlus768RawXOFStreams NTRUPlus768RawXOF NTRUPlus768CCAOraclePorts NTRUPlus768CCADecapOracle NTRUPlus768CCAGame.
require import NTRUPlus768SimModel NTRUPlus768SimSampling NTRUPlus768SimAnswer NTRUPlus768SimPorts NTRUPlus768SimGames NTRUPlus768SimOracles NTRUPlus768SimLookup.
require import NTRUPlus768SimSelected NTRUPlus768SimKnownCoupling NTRUPlus768SimPublicBound NTRUPlus768SimPublicCapRemoval NTRUPlus768SimPublicInstances.
require import NTRUPlus768SimPhaseBound NTRUPlus768SimPhaseState NTRUPlus768SimSequentialDistance.
require import NTRUPlus768SimRealGameBridge NTRUPlus768SimLookupGameBridge.
import RealOrder SimSelectedBudget.

module SimKernelRealPhase(A:CCAExtendedAdversary)=
 SimAdaptive(A,SimLeaksBackend(FOGActual,SimHActual),SimAnswerReal(FOGActual,SimHActual)).
module SimKernelLookupPhase(A:CCAExtendedAdversary)=
 SimDirectPhase(A,SimOracles(FOGActual,SimHActual),SimLookup(FOGActual)).
module SimKernelChoice(P:SimBoolPhase,Q:SimBoolPhase) : SimSequentialPhases = {
 proc phase(i:fo_setup_observation,b:bool):bool = {
  var result;
  if(b){result<@P.distinguish(i);}else{result<@Q.distinguish(i);}
  return result;
 }
}.
module SimKernelSystem(A:CCAExtendedAdversary) : SimSequentialSystem = {
 proc setup=SimObservedSetup.run
 proc phase=SimKernelChoice(SimReadyPhase(SimKernelRealPhase(A)),SimReadyPhase(SimKernelLookupPhase(A))).phase
}.

lemma sim_kernel_setup_same (S<:SimSequentialSystem) :
 equiv[S.setup ~ S.setup: ={arg,glob S} ==> ={glob S}].
proof. proc true;auto. qed.
lemma sim_kernel_phase_same (P<:SimBoolPhase) :
 equiv[P.distinguish ~ P.distinguish: ={arg,glob P} ==> ={res,glob P}].
proof. proc true;auto. qed.
lemma sim_kernel_choice_true (P<:SimBoolPhase)(Q<:SimBoolPhase) :
 equiv[SimKernelChoice(P,Q).phase ~ P.distinguish:
 i{1}=s{2} /\ b{1}=true /\ ={glob P} ==> ={res,glob P}].
proof.
 proc*;inline{1} SimKernelChoice(P,Q).phase;sp;rcondt{1} 1;first by auto.
 wp;call(sim_kernel_phase_same P);auto.
qed.
lemma sim_kernel_choice_false (P<:SimBoolPhase)(Q<:SimBoolPhase) :
 equiv[SimKernelChoice(P,Q).phase ~ Q.distinguish:
 i{1}=s{2} /\ b{1}=false /\ ={glob Q} ==> ={res,glob Q}].
proof.
 proc*;inline{1} SimKernelChoice(P,Q).phase;sp;rcondf{1} 1;first by auto.
 wp;call(sim_kernel_phase_same Q);auto.
qed.

lemma sim_kernel_cost_nonnegative (qd qh:int) (e:real) :
 0<=qd=>0<=qh=>0%r<=e=>0%r<=qd%r/(2%r^768)+(qh+qd)%r*e.
proof.
 move=>hd hh he;apply addr_ge0.
 + apply divr_ge0;first by smt().
   by apply ltrW;apply expr_gt0.
 apply mulr_ge0;smt().
qed.

lemma sim_kernel_real_phase_ll (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,
  -FOContext,-FOBadState,-FOBudgetState,-FOGRO.RO,-FOGRO.FRO,-SimPublic,-SimHistory,-SimBad,
  -SimPhaseInput,-SimSelectedFixed,-SimPublicBudget,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,
  -SH.HB.Count,-SH.HB.HybOrcl}) : (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
 islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
 islossless D.decap=>islossless A(H,D).guess)=>islossless SimKernelRealPhase(A).distinguish.
proof.
 move=>all;exact(sim_adaptive_ll A (SimLeaksBackend(FOGActual,SimHActual)) (SimAnswerReal(FOGActual,SimHActual))
  (sim_leaks_backend_ll FOGActual SimHActual rog_get_ll roh_get_ll)
  (sim_answer_real_ll FOGActual SimHActual rog_get_ll roh_get_ll) all).
qed.
lemma sim_kernel_lookup_phase_ll (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,
  -FOContext,-FOBadState,-FOBudgetState,-FOGRO.RO,-FOGRO.FRO,-SimPublic,-SimHistory,-SimBad,
  -SimPhaseInput,-SimSelectedFixed,-SimPublicBudget,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,
  -SH.HB.Count,-SH.HB.HybOrcl}) : (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
 islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
 islossless D.decap=>islossless A(H,D).guess)=>islossless SimKernelLookupPhase(A).distinguish.
proof.
 move=>all;proc;call(all (SimOracles(FOGActual,SimHActual)) (SimLookup(FOGActual)) _ _ _ _ _ _).
 + exact cca_e_ll.
 + exact cca_f_ll.
 + proc;call rog_get_ll;auto.
 + exact(sim_logged_h_ll SimHActual roh_get_ll).
 + exact(sim_raw_get_ll FOGActual SimHActual rog_get_ll roh_get_ll).
 + exact(sim_lookup_lossless FOGActual rog_get_ll).
 auto.
qed.
lemma sim_kernel_system_ll (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,
  -FOContext,-FOBadState,-FOBudgetState,-FOGRO.RO,-FOGRO.FRO,-SimPublic,-SimHistory,-SimBad,
  -SimPhaseInput,-SimSelectedFixed,-SimPublicBudget,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,
  -SH.HB.Count,-SH.HB.HybOrcl}) : (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
 islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
 islossless D.decap=>islossless A(H,D).guess)=>islossless SimKernelSystem(A).phase.
proof.
 move=>all;proc;if.
 + call(sim_ready_phase_ll (SimKernelRealPhase(A)) (sim_kernel_real_phase_ll A all));auto.
 call(sim_ready_phase_ll (SimKernelLookupPhase(A)) (sim_kernel_lookup_phase_ll A all));auto.
qed.

lemma sim_kernel_ready_true (P<:SimBoolPhase) s0 &m : sim_phase_ready s0 SimPublic.pk{m} SimPublic.suffix{m} CCADecapOracle.sk{m} SimPublic.cstar{m}
 FOContext.w{m} FOContext.g{m} FOContext.challenge_h{m} FOContext.challenge_hash{m} FOContext.challenge_ct{m}
 ROG.m{m} ROH.m{m} SimHistory.h{m} SimBad.corr{m}=>
 Pr[SimReadyPhase(P).distinguish(s0) @ &m:res]=Pr[P.distinguish(s0) @ &m:res].
proof. move=>hr;apply/eq_sym;byequiv(sim_ready_phase_projection P s0)=> //. qed.
lemma sim_kernel_ready_false (P<:SimBoolPhase) s0 &m : !sim_phase_ready s0 SimPublic.pk{m} SimPublic.suffix{m} CCADecapOracle.sk{m} SimPublic.cstar{m}
 FOContext.w{m} FOContext.g{m} FOContext.challenge_h{m} FOContext.challenge_hash{m} FOContext.challenge_ct{m}
 ROG.m{m} ROH.m{m} SimHistory.h{m} SimBad.corr{m}=>
 Pr[SimReadyPhase(P).distinguish(s0) @ &m:res]=0%r.
proof.
 move=>hn;byphoare(_:s=s0 /\ !sim_phase_ready s0 SimPublic.pk SimPublic.suffix CCADecapOracle.sk SimPublic.cstar
 FOContext.w FOContext.g FOContext.challenge_h FOContext.challenge_hash FOContext.challenge_ct
 ROG.m ROH.m SimHistory.h SimBad.corr ==>res)=> //.
 hoare;proc;rcondf 2;auto.
qed.

lemma sim_kernel_ready_distance (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,
  -FOContext,-FOBadState,-FOBudgetState,-FOGRO.RO,-FOGRO.FRO,-SimPublic,-SimHistory,-SimBad,
  -SimPhaseInput,-SimSelectedFixed,-SimPublicBudget,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,
  -SH.HB.Count,-SH.HB.HybOrcl}) s0 qH &m :
 0<=qH=>(forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
 islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
 islossless D.decap=>islossless A(H,D).guess)=>(forall(H<:CCAExtendedOraclePort {-A,-FOBudgetState})(D<:CCADecapPort {-A,-FOBudgetState}),
 hoare[FOCountedA(A,H,D).guess:FOBudgetState.nD=0 ==>FOBudgetState.nD<=max 0 budget])=>
 hoare[SimPublicCountedA(A,FOHashView(SimKnownPublicBackend),FODecapView(SimKnownPublicBackend)).guess:
 sim_public_budget_initial qH SimPublicBudget.nh SimPublicBudget.limit SimPublicBudget.overflow ==>
 SimPublicBudget.nh<=qH]=>
 `|Pr[SimReadyPhase(SimKernelRealPhase(A)).distinguish(s0) @ &m:res]-
   Pr[SimReadyPhase(SimKernelLookupPhase(A)).distinguish(s0) @ &m:res]|
 <=(max 0 budget)%r/(2%r^768)+(qH+max 0 budget)%r*fo_setup_error s0.
proof.
 move=>hq all qd qh;case(sim_phase_ready s0 SimPublic.pk{m} SimPublic.suffix{m} CCADecapOracle.sk{m} SimPublic.cstar{m}
 FOContext.w{m} FOContext.g{m} FOContext.challenge_h{m} FOContext.challenge_hash{m} FOContext.challenge_ct{m}
 ROG.m{m} ROH.m{m} SimHistory.h{m} SimBad.corr{m})=>hr.
 + rewrite(sim_kernel_ready_true (SimKernelRealPhase(A)) s0 &m hr)
    (sim_kernel_ready_true (SimKernelLookupPhase(A)) s0 &m hr).
   move:hr;rewrite /sim_phase_ready.
   move=>hr.
   have hv:fo_setup_valid s0 by smt().
   have hw:FOContext.w{m}=s0.`1.`1 by smt().
   have hg:FOContext.g{m}=acwc2_gfun s0.`3 by smt().
   have hk:pke_key_relation FOContext.w{m}.
   - rewrite hw;by have [_ [_ [hk _]]]:=hv.
   have hi:
    SimPublic.pk{m}=FOContext.w{m}.`kg_pk /\ SimPublic.suffix{m}=complete_sk_suffix FOContext.w{m}.`kg_sk /\
    CCADecapOracle.sk{m}=FOContext.w{m}.`kg_sk /\ SimPublic.cstar{m}=Some FOContext.challenge_ct{m} /\
    FOContext.w{m}=FOContext.w{m} /\ FOContext.g{m}=FOContext.g{m} /\ FOContext.challenge_h{m}=FOContext.challenge_h{m} /\
    sim_known_invariant FOContext.w{m} FOContext.g{m} FOContext.challenge_h{m} FOContext.challenge_hash{m} FOContext.challenge_ct{m}
     ROG.m{m} ROH.m{m} SimHistory.h{m} SimBad.corr{m} /\ !SimBad.corr{m}.
   - clear hk hv;rewrite /sim_known_invariant;smt().
   have hb:=sim_real_lookup_phase_distance A FOContext.w{m} FOContext.g{m} FOContext.challenge_h{m}
    FOContext.challenge_hash{m} FOContext.challenge_ct{m} qH s0 &m hk hi hq all qd qh.
   by move:hb;rewrite hw hg /fo_setup_error.
 rewrite(sim_kernel_ready_false (SimKernelRealPhase(A)) s0 &m hr)
  (sim_kernel_ready_false (SimKernelLookupPhase(A)) s0 &m hr) ?subrr ?normr0.
 have hd:0<=max 0 budget by smt().
 have [he _]:=fo_setup_error_range s0.
 exact(sim_kernel_cost_nonnegative (max 0 budget) qH (fo_setup_error s0) hd hq he).
qed.

lemma sim_kernel_phase_true (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,
  -FOContext,-FOBadState,-FOBudgetState,-FOGRO.RO,-FOGRO.FRO,-SimPublic,-SimHistory,-SimBad,
  -SimPhaseInput,-SimSelectedFixed,-SimPublicBudget,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,
  -SH.HB.Count,-SH.HB.HybOrcl}) :
 equiv[SimKernelSystem(A).phase ~ SimReadyPhase(SimKernelRealPhase(A)).distinguish:
 i{1}=s{2} /\ b{1}=true /\ ={glob SimKernelSystem(A)} ==>
 ={res}].
proof.
 conseq(sim_kernel_choice_true (SimReadyPhase(SimKernelRealPhase(A))) (SimReadyPhase(SimKernelLookupPhase(A))));smt().
qed.
lemma sim_kernel_prefix_true (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,
  -FOContext,-FOBadState,-FOBudgetState,-FOGRO.RO,-FOGRO.FRO,-SimPublic,-SimHistory,-SimBad,
  -SimPhaseInput,-SimSelectedFixed,-SimPublicBudget,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,
  -SH.HB.Count,-SH.HB.HybOrcl}) :
 equiv[SimSequentialKernel(SimKernelSystem(A)).phase ~ SimReadyKernel(SimKernelRealPhase(A)).guess:
 i{1}=s{2} /\ b{1}=true /\ ={glob SimKernelSystem(A)} ==>
 ={res}].
proof.
 proc;call(sim_kernel_phase_true A).
 call(sim_kernel_setup_same (SimKernelSystem(A))).
 auto.
qed.

lemma sim_kernel_phase_false (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,
  -FOContext,-FOBadState,-FOBudgetState,-FOGRO.RO,-FOGRO.FRO,-SimPublic,-SimHistory,-SimBad,
  -SimPhaseInput,-SimSelectedFixed,-SimPublicBudget,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,
  -SH.HB.Count,-SH.HB.HybOrcl}) :
 equiv[SimKernelSystem(A).phase ~ SimReadyPhase(SimKernelLookupPhase(A)).distinguish:
 i{1}=s{2} /\ b{1}=false /\ ={glob SimKernelSystem(A)} ==>
 ={res}].
proof.
 conseq(sim_kernel_choice_false (SimReadyPhase(SimKernelRealPhase(A))) (SimReadyPhase(SimKernelLookupPhase(A))));smt().
qed.
lemma sim_kernel_prefix_false (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,
  -FOContext,-FOBadState,-FOBudgetState,-FOGRO.RO,-FOGRO.FRO,-SimPublic,-SimHistory,-SimBad,
  -SimPhaseInput,-SimSelectedFixed,-SimPublicBudget,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,
  -SH.HB.Count,-SH.HB.HybOrcl}) :
 equiv[SimSequentialKernel(SimKernelSystem(A)).phase ~ SimReadyKernel(SimKernelLookupPhase(A)).guess:
 i{1}=s{2} /\ b{1}=false /\ ={glob SimKernelSystem(A)} ==>
 ={res}].
proof.
 proc;call(sim_kernel_phase_false A).
 call(sim_kernel_setup_same (SimKernelSystem(A))).
 auto.
qed.

lemma sim_kernel_guarded_distance (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,
  -FOContext,-FOBadState,-FOBudgetState,-FOGRO.RO,-FOGRO.FRO,-SimPublic,-SimHistory,-SimBad,
  -SimPhaseInput,-SimSelectedFixed,-SimPublicBudget,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,
  -SH.HB.Count,-SH.HB.HybOrcl}) s0 qH &m :
 0<=qH=>(forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
 islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
 islossless D.decap=>islossless A(H,D).guess)=>(forall(H<:CCAExtendedOraclePort {-A,-FOBudgetState})(D<:CCADecapPort {-A,-FOBudgetState}),
 hoare[FOCountedA(A,H,D).guess:FOBudgetState.nD=0 ==>FOBudgetState.nD<=max 0 budget])=>
 hoare[SimPublicCountedA(A,FOHashView(SimKnownPublicBackend),FODecapView(SimKnownPublicBackend)).guess:
 sim_public_budget_initial qH SimPublicBudget.nh SimPublicBudget.limit SimPublicBudget.overflow ==>
 SimPublicBudget.nh<=qH]=>
 `|Pr[SimSequentialKernel(SimKernelSystem(A)).phase(s0,true) @ &m:res]-
   Pr[SimSequentialKernel(SimKernelSystem(A)).phase(s0,false) @ &m:res]|
 <=(max 0 budget)%r/(2%r^768)+(qH+max 0 budget)%r*fo_setup_error s0.
proof.
 move=>hq all qd qh.
 apply(sim_sequential_unconditional (SimKernelSystem(A)) s0
  ((max 0 budget)%r/(2%r^768)+(qH+max 0 budget)%r*fo_setup_error s0) &m
  sim_observed_setup_ll (sim_kernel_system_ll A all) _).
 move=> &n.
 have ht:Pr[SimKernelSystem(A).phase(s0,true) @ &n:res]=
  Pr[SimReadyPhase(SimKernelRealPhase(A)).distinguish(s0) @ &n:res]
  by byequiv(sim_kernel_phase_true A)=> //.
 have hf:Pr[SimKernelSystem(A).phase(s0,false) @ &n:res]=
  Pr[SimReadyPhase(SimKernelLookupPhase(A)).distinguish(s0) @ &n:res]
  by byequiv(sim_kernel_phase_false A)=> //.
 rewrite ht hf;exact(sim_kernel_ready_distance A s0 qH &n hq all qd qh).
qed.

lemma sim_kernel_real_probability (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,
  -FOContext,-FOBadState,-FOBudgetState,-FOGRO.RO,-FOGRO.FRO,-SimPublic,-SimHistory,-SimBad,
  -SimPhaseInput,-SimSelectedFixed,-SimPublicBudget,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,
  -SH.HB.Count,-SH.HB.HybOrcl}) s0 &m : fo_setup_valid s0=>
 Pr[SimObservedRealKernel(A).guess(s0) @ &m:res]=
 Pr[SimSequentialKernel(SimKernelSystem(A)).phase(s0,true) @ &m:res].
proof.
 move=>hv.
 have he:Pr[SimObservedRealKernel(A).guess(s0) @ &m:res]=
  Pr[SimSetupPhase(SimKernelRealPhase(A)).guess(s0) @ &m:res].
 + byequiv(_: ={arg,glob SimKernelSystem(A)} ==> ={res})=> //.
   proc;call(sim_kernel_phase_same (SimKernelRealPhase(A)));
   call(sim_kernel_setup_same (SimKernelSystem(A)));auto.
 rewrite he (sim_ready_kernel_probability (SimKernelRealPhase(A)) s0 (fun b=>b) &m hv).
 apply/eq_sym;byequiv(sim_kernel_prefix_true A)=> //.
qed.

lemma sim_kernel_lookup_probability (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,
  -FOContext,-FOBadState,-FOBudgetState,-FOGRO.RO,-FOGRO.FRO,-SimPublic,-SimHistory,-SimBad,
  -SimPhaseInput,-SimSelectedFixed,-SimPublicBudget,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,
  -SH.HB.Count,-SH.HB.HybOrcl}) s0 &m : fo_setup_valid s0=>
 Pr[SimObservedLookupKernel(A).guess(s0) @ &m:res]=
 Pr[SimSequentialKernel(SimKernelSystem(A)).phase(s0,false) @ &m:res].
proof.
 move=>hv.
 have he:Pr[SimObservedLookupKernel(A).guess(s0) @ &m:res]=
  Pr[SimSetupPhase(SimKernelLookupPhase(A)).guess(s0) @ &m:res].
 + byequiv(_: ={arg,glob SimKernelSystem(A)} ==> ={res})=> //.
   proc;call(sim_kernel_phase_same (SimKernelLookupPhase(A)));
   call(sim_kernel_setup_same (SimKernelSystem(A)));auto.
 rewrite he (sim_ready_kernel_probability (SimKernelLookupPhase(A)) s0 (fun b=>b) &m hv).
 apply/eq_sym;byequiv(sim_kernel_prefix_false A)=> //.
qed.

(* The hypotheses are exactly the scheme-level adversary termination and
   query contracts. Setup validity discharges every internal ready guard. *)
lemma sim_plain_public_kernel_distance (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,
  -FOContext,-FOBadState,-FOBudgetState,-FOGRO.RO,-FOGRO.FRO,-SimPublic,-SimHistory,-SimBad,
  -SimPhaseInput,-SimSelectedFixed,-SimPublicBudget,-SimHRO.RO,-SimHRO.FRO,-SimGRO.RO,-SimGRO.FRO,
  -SH.HB.Count,-SH.HB.HybOrcl}) s0 qH &m :
 fo_setup_valid s0=>0<=qH=>(forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
 islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
 islossless D.decap=>islossless A(H,D).guess)=>(forall(H<:CCAExtendedOraclePort {-A,-FOBudgetState})(D<:CCADecapPort {-A,-FOBudgetState}),
 hoare[FOCountedA(A,H,D).guess:FOBudgetState.nD=0 ==>FOBudgetState.nD<=max 0 budget])=>
 hoare[SimPublicCountedA(A,FOHashView(SimKnownPublicBackend),FODecapView(SimKnownPublicBackend)).guess:
 sim_public_budget_initial qH SimPublicBudget.nh SimPublicBudget.limit SimPublicBudget.overflow ==>
 SimPublicBudget.nh<=qH]=>
 `|Pr[FOPlainKernel(A,FOReencryptDecap(SHAKEGROM,SHAKEHROM)).guess(s0) @ &m:res]-
   Pr[SimPublicKernel(A).guess(s0) @ &m:res]|
 <=(max 0 budget)%r/(2%r^768)+(qH+max 0 budget)%r*fo_setup_error s0.
proof.
 move=>hv hq all qd qh.
 have hb:=sim_kernel_guarded_distance A s0 qH &m hq all qd qh.
 rewrite -(sim_kernel_real_probability A s0 &m hv)
  -(sim_kernel_lookup_probability A s0 &m hv) in hb.
 have hr:=sim_observed_real_plain_probability A &m s0 (fun b=>b).
 have hl:=sim_lookup_observed_public_probability A s0 &m (fun b=>b) hv.
 by move:hb;rewrite hr hl.
qed.
