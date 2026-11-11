require import AllCore Distr FMap.
from Jasmin require import JWord.
require import Array32 Array1152 Array2336.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768PKEModel NTRUPlus768ACWC2Oracle.
require import NTRUPlus768FOModel NTRUPlus768FOChallenge NTRUPlus768FOEagerG NTRUPlus768FOGAdapters.
require import NTRUPlus768ROMOracles NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
require import NTRUPlus768CCAGame NTRUPlus768CCADecapOracle NTRUPlus768FOKEMGame.
require import NTRUPlus768CCAStatusAdapter NTRUPlus768CCAOraclePorts.
require import NTRUPlus768SimModel NTRUPlus768SimSampling NTRUPlus768SimAnswer NTRUPlus768SimPrefix.
require import NTRUPlus768SimOracles NTRUPlus768SimPorts NTRUPlus768SimPortContracts NTRUPlus768SimGames.
require import NTRUPlus768SimKnown NTRUPlus768SimChallengeAnswer NTRUPlus768SimRealBridge.
require import NTRUPlus768SimAnswerErasure.
require import NTRUPlus768SimRealGameBridge NTRUPlus768SimSetupBridge NTRUPlus768FOSetupDistribution.

op [opaque] sim_known_phase_state (w:keygen_witness) (g:acwc2_g_function) ex hs cs pk sk star ctxex gm hm =
 pk=w.`kg_pk /\ sk=w.`kg_sk /\ star=Some cs /\ ctxex=ex /\
 acwc2_cache_matches g gm /\ fo_challenge_invariant w g ex hs cs hm.

(* An outline of the hybrid endpoint: known and challenge inputs are
   answered normally, while every other private H request returns None. *)
module SimExpandedKnownAnswer : SimAnswer = {
 proc answer(q:sim_request) : W8.t Array32.t option = {
  var result:W8.t Array32.t option;
  result<-None;
  if(sim_h_input q \in SimHistory.h \/ Some(sim_h_input q)=FOContext.challenge_h){
   result<@SimAnswerReal(FOGActual,SimHActual).answer(q);
  }
  return result;
 }
}.
module SimExpandedKnownDecap : CCADecapPort = {
 proc decap(ct:W8.t Array1152.t) : cca_reply = {
  var result:cca_reply;
  SimPublic.count<-SimPublic.count+1;result<-None;
  if(SimPublic.cstar<>Some ct){
   result<@SimCore(FOGActual,SimExpandedKnownAnswer).run(SimPublic.pk,ct,CCADecapOracle.sk);
  }
  return result;
 }
}.

lemma sim_known_roh_challenge w g ex hs cs : hoare[ROH.get:
 fo_challenge_invariant w g ex hs cs ROH.m ==>fo_challenge_invariant w g ex hs cs ROH.m].
proof.
 proc*;ecall(roh_get_value ROH.m input);auto=> />;smt(fo_challenge_cache_extends).
qed.
lemma sim_known_answer_challenge_frame w g ex hs cs :
 hoare[SimAnswerReal(FOGActual,SimHActual).answer:
 acwc2_cache_matches g ROG.m /\ fo_challenge_invariant w g ex hs cs ROH.m ==>
 acwc2_cache_matches g ROG.m /\ fo_challenge_invariant w g ex hs cs ROH.m].
proof.
 proc;call(sim_regenerate_cache g);call(sim_known_roh_challenge w g ex hs cs);auto.
qed.
lemma sim_known_answer_self w g ex hs cs :
 equiv[SimAnswerReal(FOGActual,SimHActual).answer ~ SimAnswerReal(FOGActual,SimHActual).answer:
 ={arg,ROG.m,ROH.m} /\ acwc2_cache_matches g ROG.m{1} /\
 fo_challenge_invariant w g ex hs cs ROH.m{1} ==>
 ={res,ROG.m,ROH.m} /\ acwc2_cache_matches g ROG.m{1} /\
 fo_challenge_invariant w g ex hs cs ROH.m{1}].
proof.
 conseq(_: ={arg,ROG.m,ROH.m} ==> ={res,ROG.m,ROH.m})
 (sim_known_answer_challenge_frame w g ex hs cs) _.
 + auto=> />.
 by sim.
qed.

lemma sim_answer_challenge_pre w g q0 gm0 hm0 ex hs cs : pke_key_relation w=>
 phoare[SimAnswerReal(FOGActual,SimHActual).answer:
 q=q0 /\ ROG.m=gm0 /\ ROH.m=hm0 /\ acwc2_cache_matches g gm0 /\
 fo_challenge_invariant w g ex hs cs hm0 /\ q0.`sr_pk=w.`kg_pk /\
 q0.`sr_ct<>cs /\ Some(sim_h_input q0)=ex ==>
 res=None /\ ROG.m=gm0 /\ ROH.m=hm0]=1%r.
proof.
 move=>hk;bypr=> &m [hq [hgm [hhm [hg [hc [hp [hn he]]]]]]].
 byphoare(sim_answer_challenge_correct w g q0 gm0 hm0 ex hs cs hk hg hc hp hn he)=> //.
qed.

lemma sim_expanded_known_answer w g ex hs cs : pke_key_relation w=>
 equiv[SimExpandedKnownAnswer.answer ~ SimKnownAnswer(FOGActual,SimHActual).answer:
 ={q,ROG.m,ROH.m,SimHistory.h,glob FOContext} /\
 q{1}.`sr_pk=w.`kg_pk /\ q{1}.`sr_ct<>cs /\ FOContext.challenge_h{1}=ex /\
 acwc2_cache_matches g ROG.m{1} /\ fo_challenge_invariant w g ex hs cs ROH.m{1} ==>
 ={res,ROG.m,ROH.m,SimHistory.h,glob FOContext} /\
 acwc2_cache_matches g ROG.m{1} /\ fo_challenge_invariant w g ex hs cs ROH.m{1}].
proof.
 move=>hk;proc;sp;if{2}.
 + rcondt{1} 1;first by auto=> />;smt().
   call(sim_known_answer_self w g ex hs cs);auto.
 if{1}.
 + ecall{1}(sim_answer_challenge_pre w g q{1} ROG.m{1} ROH.m{1} ex hs cs hk).
   auto=> />;smt().
 auto.
qed.

lemma sim_leak_never_expanded :
 equiv[SimLeakDecaps(SimLeaksBackend(FOGActual,SimHActual),SimAnswerNever).decap ~ SimExpandedKnownDecap.decap:
 ={ct,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,glob FOContext,glob CCADecapOracle,glob FOPublicKey,glob SimBad,glob SimPhaseInput} ==>
 ={res,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,glob FOContext,glob CCADecapOracle,glob FOPublicKey,glob SimBad,glob SimPhaseInput}].
proof.
 proc;inline{1} SimLeaksBackend(FOGActual,SimHActual).leaks;sp.
 match{1};1..5:by exfalso=> />;smt().
 inline{1} SimPrepare(FOGActual,SimHActual).run.
 inline{2} SimCore(FOGActual,SimExpandedKnownAnswer).run.
 sp;if;first by auto=> />;smt().
 + sp 0 3.
   seq 1 2:(request0{1}=request{2} /\ result{1}=None /\ result0{2}=None /\
    ={ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,glob FOContext,glob CCADecapOracle,glob FOPublicKey,glob SimBad,glob SimPhaseInput}).
   - wp;call(_: ={arg,ROG.m} ==> ={res,ROG.m});first by sim.
     auto=> />;smt().
   if;first by auto.
   - inline{2} SimExpandedKnownAnswer.answer;sp 1 2.
     if;first by auto.
     + rcondf{1} 7.
       - move=> &m;wp;call(_:true ==>true);first by trivial. auto=> />;rewrite /sim_out_decap;done.
       wp;call(_: ={arg,ROG.m,ROH.m} ==> ={res,ROG.m,ROH.m});first by sim.
       auto=> />;rewrite /sim_out_decap;auto.
     rcondt{1} 5;first by auto=> />;rewrite /sim_out_decap;auto.
     inline{1} SimAnswerNever.answer;auto=> />;rewrite /sim_out_decap;auto.
   rcondf{1} 5;first by auto=> />;rewrite /sim_out_decap;auto.
   auto=> />;rewrite /sim_out_decap;auto.
 rcondf{1} 5;first by auto=> />;rewrite /sim_out_decap;auto.
 auto=> />;rewrite /sim_out_decap;auto.
qed.

lemma sim_known_prefix_fields w g ct0 :
 hoare[SimPrefix(FOGActual).run:
 pk=w.`kg_pk /\ ct=ct0 /\ sk=w.`kg_sk /\ acwc2_cache_matches g ROG.m ==>
 acwc2_cache_matches g ROG.m /\
 (res<>None=>(oget res).`sr_pk=w.`kg_pk /\ (oget res).`sr_ct=ct0)].
proof.
 conseq(sim_prefix_cache g)(sim_prefix_fields FOGActual w.`kg_pk ct0 w.`kg_sk);smt().
qed.
lemma sim_known_prefix_self w g ct0 :
 equiv[SimPrefix(FOGActual).run ~ SimPrefix(FOGActual).run:
 ={arg,ROG.m} /\ pk{1}=w.`kg_pk /\ ct{1}=ct0 /\ sk{1}=w.`kg_sk /\ acwc2_cache_matches g ROG.m{1} ==>
 ={res,ROG.m} /\ acwc2_cache_matches g ROG.m{1} /\
 (res{1}<>None=>(oget res{1}).`sr_pk=w.`kg_pk /\ (oget res{1}).`sr_ct=ct0)].
proof.
 conseq(_: ={arg,ROG.m} ==> ={res,ROG.m})(sim_known_prefix_fields w g ct0) _.
 + auto=> />.
 by sim.
qed.

lemma sim_expanded_known_decap w g ex hs cs : pke_key_relation w=>
 equiv[SimExpandedKnownDecap.decap ~ SimKnownDecap(FOGActual,SimHActual).decap:
 ={ct,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,glob FOContext,glob CCADecapOracle,glob FOPublicKey,glob SimBad,glob SimPhaseInput} /\
 SimPublic.pk{1}=w.`kg_pk /\ CCADecapOracle.sk{1}=w.`kg_sk /\ SimPublic.cstar{1}=Some cs /\
 FOContext.challenge_h{1}=ex /\ acwc2_cache_matches g ROG.m{1} /\
 fo_challenge_invariant w g ex hs cs ROH.m{1} ==>
 ={res,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,glob FOContext,glob CCADecapOracle,glob FOPublicKey,glob SimBad,glob SimPhaseInput} /\
 acwc2_cache_matches g ROG.m{1} /\ fo_challenge_invariant w g ex hs cs ROH.m{1}].
proof.
 move=>hk;exists* ct{1};elim*=>ct0.
 proc;sp;if;first by auto.
 + inline SimCore(FOGActual,SimExpandedKnownAnswer).run SimCore(FOGActual,SimKnownAnswer(FOGActual,SimHActual)).run.
   sp;seq 1 1:(={request,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,glob FOContext,glob CCADecapOracle,glob FOPublicKey,glob SimBad,glob SimPhaseInput} /\
    FOContext.challenge_h{1}=ex /\ acwc2_cache_matches g ROG.m{1} /\
    fo_challenge_invariant w g ex hs cs ROH.m{1} /\ ct0<>cs /\
    (request{1}<>None=>(oget request{1}).`sr_pk=w.`kg_pk /\ (oget request{1}).`sr_ct=ct0)).
   - call(sim_known_prefix_self w g ct0);auto=> />;smt().
   sp;if;first by auto.
   - wp;call(sim_expanded_known_answer w g ex hs cs hk);auto=> />;smt().
   auto.
 auto.
qed.

lemma sim_leak_never_known_decap w g ex hs cs : pke_key_relation w=>
 equiv[SimLeakDecaps(SimLeaksBackend(FOGActual,SimHActual),SimAnswerNever).decap ~
 SimKnownDecap(FOGActual,SimHActual).decap:
 ={ct,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,glob FOContext,glob CCADecapOracle,glob FOPublicKey,glob SimBad,glob SimPhaseInput} /\
 SimPublic.pk{1}=w.`kg_pk /\ CCADecapOracle.sk{1}=w.`kg_sk /\ SimPublic.cstar{1}=Some cs /\
 FOContext.challenge_h{1}=ex /\ acwc2_cache_matches g ROG.m{1} /\
 fo_challenge_invariant w g ex hs cs ROH.m{1} ==>
 ={res,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,glob FOContext,glob CCADecapOracle,glob FOPublicKey,glob SimBad,glob SimPhaseInput} /\
 acwc2_cache_matches g ROG.m{1} /\ fo_challenge_invariant w g ex hs cs ROH.m{1}].
proof.
 move=>hk;transitivity SimExpandedKnownDecap.decap
  (={ct,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,glob FOContext,glob CCADecapOracle,glob FOPublicKey,glob SimBad,glob SimPhaseInput} ==>
   ={res,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,glob FOContext,glob CCADecapOracle,glob FOPublicKey,glob SimBad,glob SimPhaseInput})
  (={ct,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,glob FOContext,glob CCADecapOracle,glob FOPublicKey,glob SimBad,glob SimPhaseInput} /\
   SimPublic.pk{1}=w.`kg_pk /\ CCADecapOracle.sk{1}=w.`kg_sk /\ SimPublic.cstar{1}=Some cs /\
   FOContext.challenge_h{1}=ex /\ acwc2_cache_matches g ROG.m{1} /\
   fo_challenge_invariant w g ex hs cs ROH.m{1} ==>
   ={res,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,glob FOContext,glob CCADecapOracle,glob FOPublicKey,glob SimBad,glob SimPhaseInput} /\
   acwc2_cache_matches g ROG.m{1} /\ fo_challenge_invariant w g ex hs cs ROH.m{1}).
 + move=> &ml &mr h.
   exists CCADecapOracle.count{ml} CCADecapOracle.cstar{ml} CCADecapOracle.sk{ml}
    FOPublicKey.pk{ml} FOContext.challenge_ct{ml} FOContext.challenge_h{ml} FOContext.challenge_hash{ml}
    FOContext.g{ml} FOContext.w{ml} ROE.m{ml} ROF.m{ml} ROG.m{ml} ROH.m{ml}
    RawXOFStreams.es{ml} RawXOFStreams.fs{ml} RawXOFStreams.gs{ml} RawXOFStreams.other{ml}
    SimBad.corr{ml} SimBad.hidden{ml} SimBad.selected_calls{ml} SimHistory.h{ml}
    SimPublic.count{ml} SimPublic.cstar{ml} SimPublic.pk{ml} SimPublic.suffix{ml}
    SimPhaseInput.bit{ml} SimPhaseInput.ct{ml} SimPhaseInput.key{ml} SimPhaseInput.pk{ml} arg{ml}.
   split;first by trivial. exact h.
 + clear hk;smt().
 + exact sim_leak_never_expanded.
 exact(sim_expanded_known_decap w g ex hs cs hk).
qed.

lemma sim_known_e_state w g ex hs cs : hoare[SimOracles(FOGActual,SimHActual).e:
 sim_known_phase_state w g ex hs cs SimPublic.pk CCADecapOracle.sk SimPublic.cstar FOContext.challenge_h ROG.m ROH.m ==>
 sim_known_phase_state w g ex hs cs SimPublic.pk CCADecapOracle.sk SimPublic.cstar FOContext.challenge_h ROG.m ROH.m].
proof. rewrite /sim_known_phase_state;proc;call(_:true ==>true);first by trivial. auto. qed.
lemma sim_known_f_state w g ex hs cs : hoare[SimOracles(FOGActual,SimHActual).f:
 sim_known_phase_state w g ex hs cs SimPublic.pk CCADecapOracle.sk SimPublic.cstar FOContext.challenge_h ROG.m ROH.m ==>
 sim_known_phase_state w g ex hs cs SimPublic.pk CCADecapOracle.sk SimPublic.cstar FOContext.challenge_h ROG.m ROH.m].
proof. rewrite /sim_known_phase_state;proc;call(_:true ==>true);first by trivial. auto. qed.
lemma sim_known_g_state w g ex hs cs : hoare[SimOracles(FOGActual,SimHActual).g:
 sim_known_phase_state w g ex hs cs SimPublic.pk CCADecapOracle.sk SimPublic.cstar FOContext.challenge_h ROG.m ROH.m ==>
 sim_known_phase_state w g ex hs cs SimPublic.pk CCADecapOracle.sk SimPublic.cstar FOContext.challenge_h ROG.m ROH.m].
proof. rewrite /sim_known_phase_state;proc;call(sim_g_cache_preserves g);auto. qed.
lemma sim_known_h_state w g ex hs cs : hoare[SimOracles(FOGActual,SimHActual).h:
 sim_known_phase_state w g ex hs cs SimPublic.pk CCADecapOracle.sk SimPublic.cstar FOContext.challenge_h ROG.m ROH.m ==>
 sim_known_phase_state w g ex hs cs SimPublic.pk CCADecapOracle.sk SimPublic.cstar FOContext.challenge_h ROG.m ROH.m].
proof.
 rewrite /sim_known_phase_state;proc;inline SimHistory.record;wp.
 call(sim_known_roh_challenge w g ex hs cs);auto.
qed.
lemma sim_known_raw_full_state w g ex hs cs : hoare[SimRaw(FOGActual,SimHActual).full:
 sim_known_phase_state w g ex hs cs SimPublic.pk CCADecapOracle.sk SimPublic.cstar FOContext.challenge_h ROG.m ROH.m ==>
 sim_known_phase_state w g ex hs cs SimPublic.pk CCADecapOracle.sk SimPublic.cstar FOContext.challenge_h ROG.m ROH.m].
proof.
 proc;match.
 + call(_:true ==>true);first by trivial. auto.
 match.
 + call(_:true ==>true);first by trivial. auto.
 + call(_:true ==>true);first by trivial. auto.
 + rewrite /sim_known_phase_state;call(sim_raw_g_cache g);auto.
 call(sim_known_h_state w g ex hs cs);auto.
qed.
lemma sim_known_raw_state w g ex hs cs : hoare[SimOracles(FOGActual,SimHActual).raw:
 sim_known_phase_state w g ex hs cs SimPublic.pk CCADecapOracle.sk SimPublic.cstar FOContext.challenge_h ROG.m ROH.m ==>
 sim_known_phase_state w g ex hs cs SimPublic.pk CCADecapOracle.sk SimPublic.cstar FOContext.challenge_h ROG.m ROH.m].
proof. proc;sp;if;last by auto. wp;call(sim_known_raw_full_state w g ex hs cs);auto. qed.

lemma sim_known_answer_state w g ex hs cs : hoare[SimKnownAnswer(FOGActual,SimHActual).answer:
 sim_known_phase_state w g ex hs cs SimPublic.pk CCADecapOracle.sk SimPublic.cstar FOContext.challenge_h ROG.m ROH.m ==>
 sim_known_phase_state w g ex hs cs SimPublic.pk CCADecapOracle.sk SimPublic.cstar FOContext.challenge_h ROG.m ROH.m].
proof.
 rewrite /sim_known_phase_state;proc;sp;if;last by auto.
 call(sim_known_answer_challenge_frame w g ex hs cs);auto.
qed.
lemma sim_known_core_state w g ex hs cs : hoare[SimCore(FOGActual,SimKnownAnswer(FOGActual,SimHActual)).run:
 sim_known_phase_state w g ex hs cs SimPublic.pk CCADecapOracle.sk SimPublic.cstar FOContext.challenge_h ROG.m ROH.m ==>
 sim_known_phase_state w g ex hs cs SimPublic.pk CCADecapOracle.sk SimPublic.cstar FOContext.challenge_h ROG.m ROH.m].
proof.
 proc;seq 2:(sim_known_phase_state w g ex hs cs SimPublic.pk CCADecapOracle.sk SimPublic.cstar FOContext.challenge_h ROG.m ROH.m).
 + rewrite /sim_known_phase_state;wp;call(sim_prefix_cache g);auto.
 if;last by auto. call(sim_known_answer_state w g ex hs cs);auto.
qed.
lemma sim_known_decap_state w g ex hs cs : hoare[SimKnownDecap(FOGActual,SimHActual).decap:
 sim_known_phase_state w g ex hs cs SimPublic.pk CCADecapOracle.sk SimPublic.cstar FOContext.challenge_h ROG.m ROH.m ==>
 sim_known_phase_state w g ex hs cs SimPublic.pk CCADecapOracle.sk SimPublic.cstar FOContext.challenge_h ROG.m ROH.m].
proof. proc;sp;if;last by auto. call(sim_known_core_state w g ex hs cs);auto. qed.

lemma sim_adaptive_known_phase
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOContext,-SimPublic,-SimHistory,-SimBad,-SimPhaseInput})
 w g ex hs cs : pke_key_relation w=>
 equiv[SimAdaptive(A,SimLeaksBackend(FOGActual,SimHActual),SimAnswerNever).distinguish ~
 SimDirectPhase(A,SimOracles(FOGActual,SimHActual),SimKnownDecap(FOGActual,SimHActual)).distinguish:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,glob FOContext,glob CCADecapOracle,glob FOPublicKey,glob SimBad,glob SimPhaseInput} /\
 sim_known_phase_state w g ex hs cs SimPublic.pk{1} CCADecapOracle.sk{1} SimPublic.cstar{1} FOContext.challenge_h{1} ROG.m{1} ROH.m{1} ==>
 ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,glob FOContext,glob CCADecapOracle,glob FOPublicKey,glob SimBad,glob SimPhaseInput} /\
 sim_known_phase_state w g ex hs cs SimPublic.pk{1} CCADecapOracle.sk{1} SimPublic.cstar{1} FOContext.challenge_h{1} ROG.m{1} ROH.m{1}].
proof.
 move=>hk;proc;call(_: ={ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,glob FOContext,glob CCADecapOracle,glob FOPublicKey,glob SimBad,glob SimPhaseInput} /\
 sim_known_phase_state w g ex hs cs SimPublic.pk{1} CCADecapOracle.sk{1} SimPublic.cstar{1} FOContext.challenge_h{1} ROG.m{1} ROH.m{1}).
 + conseq sim_leak_e_complete _ (sim_known_e_state w g ex hs cs);clear hk;smt().
 + conseq sim_leak_f_complete _ (sim_known_f_state w g ex hs cs);clear hk;smt().
 + conseq sim_leak_g_complete _ (sim_known_g_state w g ex hs cs);clear hk;smt().
 + conseq sim_leak_h_complete _ (sim_known_h_state w g ex hs cs);clear hk;smt().
 + conseq sim_leak_raw_complete _ (sim_known_raw_state w g ex hs cs);clear hk;smt().
 + conseq(sim_leak_never_known_decap w g ex hs cs hk) _ (sim_known_decap_state w g ex hs cs);
   clear hk;rewrite /sim_known_phase_state;smt().
 clear hk;auto=> />;smt().
qed.

module SimObservedDirectKnownKernel(A:CCAExtendedAdversary) = {
 proc guess(s:fo_setup_observation) : bool = {
  var win;
  SimObservedSetup.run(s);
  win<@SimDirectPhase(A,SimOracles(FOGActual,SimHActual),SimKnownDecap(FOGActual,SimHActual)).distinguish(s);
  return win;
 }
}.

lemma sim_known_setup_self s0 : fo_setup_valid s0=>
 equiv[SimObservedSetup.run ~ SimObservedSetup.run:
 ={s} /\ s{1}=s0 ==>
 ={ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,glob FOContext,glob CCADecapOracle,glob FOPublicKey,glob SimBad,glob SimPhaseInput} /\
 sim_known_phase_state s0.`1.`1 (acwc2_gfun s0.`3)
 FOContext.challenge_h{1} FOContext.challenge_hash{1} FOContext.challenge_ct{1}
 SimPublic.pk{1} CCADecapOracle.sk{1} SimPublic.cstar{1} FOContext.challenge_h{1} ROG.m{1} ROH.m{1}].
proof.
 move=>hv;conseq(_: ={arg} ==>
 ={ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,glob FOContext,glob CCADecapOracle,glob FOPublicKey,glob SimBad,glob SimPhaseInput})
 (sim_observed_setup_state s0 hv) _.
 + rewrite /sim_known_phase_state;auto=> />;smt().
 by sim.
qed.

lemma sim_observed_known_direct
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOContext,-SimPublic,-SimHistory,-SimBad,-SimPhaseInput})
 s0 : fo_setup_valid s0=>
 equiv[SimObservedKnownKernel(A).guess ~ SimObservedDirectKnownKernel(A).guess:
 ={s,glob A} /\ s{1}=s0 ==>
 ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,glob FOContext,glob CCADecapOracle,glob FOPublicKey,glob SimBad,glob SimPhaseInput}].
proof.
 move=>hv;have hk:pke_key_relation s0.`1.`1 by move:hv;rewrite /fo_setup_valid;smt().
 proc;ecall(sim_adaptive_known_phase A s0.`1.`1 (acwc2_gfun s0.`3)
  FOContext.challenge_h{1} FOContext.challenge_hash{1} FOContext.challenge_ct{1} hk).
 call(sim_known_setup_self s0 hv);auto.
qed.

lemma sim_observed_known_direct_probability
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOContext,-SimPublic,-SimHistory,-SimBad,-SimPhaseInput})
 s0 event &m : fo_setup_valid s0=>
 Pr[SimObservedKnownKernel(A).guess(s0) @ &m:event res]=
 Pr[SimObservedDirectKnownKernel(A).guess(s0) @ &m:event res].
proof. move=>hv;byequiv(sim_observed_known_direct A s0 hv)=> //. qed.
