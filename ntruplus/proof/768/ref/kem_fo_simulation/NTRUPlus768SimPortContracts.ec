require import AllCore Distr List FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152.
require import NTRUPlus768SimModel NTRUPlus768SimSampling NTRUPlus768SimAnswer.
require import NTRUPlus768SimPrefix NTRUPlus768SimPorts NTRUPlus768SimOracles NTRUPlus768SimAnswerErasure.
require import NTRUPlus768FOModel NTRUPlus768FOEagerG NTRUPlus768FOGAdapters NTRUPlus768FOProcedures NTRUPlus768FONativeBridge.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions NTRUPlus768ACWC2Oracle.
require import NTRUPlus768RawXOF NTRUPlus768RawXOFStreams NTRUPlus768CCADecapOracle.
require import NTRUPlus768DecapMessageProof NTRUPlus768DecapR2CompCaller.

lemma sim_cover_fresh log table ex x :
 sim_h_cover log table ex=>x \notin log=>Some x<>ex=>x \notin table.
proof. rewrite /sim_h_cover;smt(). qed.
lemma sim_cover_known_set log table ex x y :
 sim_h_cover log table ex=>(x \in log \/ Some x=ex)=>sim_h_cover log table.[x<-y] ex.
proof. rewrite /sim_h_cover;move=>hc hx z;rewrite mem_set;smt(). qed.
lemma sim_cover_public_set log table ex x y :
 sim_h_cover log table ex=>sim_h_cover log.[x<-y] table.[x<-y] ex.
proof. rewrite /sim_h_cover;move=>hc z;rewrite !mem_set;smt(). qed.
lemma sim_cover_log_set log table ex x y :
 sim_h_cover log table ex=>sim_h_cover log.[x<-y] table ex.
proof. rewrite /sim_h_cover;move=>hc z;rewrite mem_set;smt(). qed.

lemma sim_gshake_cache g : hoare[FOGHash(FOGActual).shake:
 acwc2_cache_matches g ROG.m ==>acwc2_cache_matches g ROG.m].
proof. proc;call(sim_g_cache_preserves g);auto. qed.
lemma sim_message_cache g : hoare[DecapMessage(FOGHash(FOGActual)).run:
 acwc2_cache_matches g ROG.m ==>acwc2_cache_matches g ROG.m].
proof.
 proc;call(_:true ==>true);first by trivial.
 call(sim_gshake_cache g);call(_:true ==>true);first by trivial. auto.
qed.
lemma sim_prefix_cache g : hoare[SimPrefix(FOGActual).run:
 acwc2_cache_matches g ROG.m ==>acwc2_cache_matches g ROG.m].
proof.
 proc;seq 2:(acwc2_cache_matches g ROG.m).
 + wp;call(_:true ==>true);first by trivial. auto.
 if;last by auto. wp;call(sim_message_cache g);auto.
qed.
lemma sim_regenerate_cache g : hoare[FORegenerateFinish(FOGHash(FOGActual)).run:
 acwc2_cache_matches g ROG.m ==>acwc2_cache_matches g ROG.m].
proof.
 proc;seq 6:(acwc2_cache_matches g ROG.m).
 + do 2!(call(_:true ==>true);first by trivial).
   call(_:acwc2_cache_matches g ROG.m ==>acwc2_cache_matches g ROG.m).
   - proc;call(sim_gshake_cache g);call(_:true ==>true);first by trivial. auto.
   call(_:true ==>true);first by trivial.
   wp;call(_:true ==>true);first by trivial. auto.
 sp;if;last by auto. call(_:true ==>true);first by trivial. auto.
qed.
lemma sim_answer_cache g : hoare[SimAnswerReal(FOGActual,SimHActual).answer:
 acwc2_cache_matches g ROG.m ==>acwc2_cache_matches g ROG.m].
proof. proc;call(sim_regenerate_cache g);call(_:true ==>true);first by trivial. auto. qed.

(* A private H call is allowed only at a public-log entry or at the single
   challenge entry. No assumption that the challenge is already cached. *)
lemma sim_h_known_cover : hoare[ROH.get:
 sim_h_cover SimHistory.h ROH.m FOContext.challenge_h /\
 (input \in SimHistory.h \/ Some input=FOContext.challenge_h) ==>
 sim_h_cover SimHistory.h ROH.m FOContext.challenge_h].
proof.
 proc;if;auto=> />.
 move=> &hr hc hx _ r0 _;exact(sim_cover_known_set _ _ _ _ r0 hc hx).
qed.
lemma sim_h_known_invariant : hoare[ROH.get:
 sim_log_included SimHistory.h ROH.m /\ sim_h_cover SimHistory.h ROH.m FOContext.challenge_h /\
 (input \in SimHistory.h \/ Some input=FOContext.challenge_h) ==>
 sim_log_included SimHistory.h ROH.m /\ sim_h_cover SimHistory.h ROH.m FOContext.challenge_h].
proof.
 conseq sim_h_known_cover (_:sim_log_included SimHistory.h ROH.m ==>sim_log_included SimHistory.h ROH.m)=> //.
 proc*;ecall(roh_get_value ROH.m input);auto=> />;smt(sim_log_included_extends).
qed.
lemma sim_answer_h_invariant : hoare[SimAnswerReal(FOGActual,SimHActual).answer:
 sim_log_included SimHistory.h ROH.m /\ sim_h_cover SimHistory.h ROH.m FOContext.challenge_h /\
 (sim_h_input q \in SimHistory.h \/ Some(sim_h_input q)=FOContext.challenge_h) ==>
 sim_log_included SimHistory.h ROH.m /\ sim_h_cover SimHistory.h ROH.m FOContext.challenge_h].
proof.
 proc;call(_:true ==>true);first by trivial.
 call sim_h_known_invariant;auto.
qed.
lemma sim_logged_h_cover : hoare[SimLoggedH(SimHActual).get:
 sim_h_cover SimHistory.h ROH.m FOContext.challenge_h ==>
 sim_h_cover SimHistory.h ROH.m FOContext.challenge_h].
proof.
 proc;inline SimHistory.record ROH.get;sp;if;auto=> />.
 + move=> &hr hc _ r0 _;rewrite get_set_sameE /=;exact(sim_cover_public_set _ _ _ _ r0 hc).
 move=> &hr hc _;exact(sim_cover_log_set _ _ _ _ _ hc).
qed.
lemma sim_logged_h_h_invariant : hoare[SimLoggedH(SimHActual).get:
 sim_log_included SimHistory.h ROH.m /\ sim_h_cover SimHistory.h ROH.m FOContext.challenge_h ==>
 sim_log_included SimHistory.h ROH.m /\ sim_h_cover SimHistory.h ROH.m FOContext.challenge_h].
proof. conseq sim_logged_h_actual_invariant sim_logged_h_cover;smt(). qed.

lemma sim_prepare_cache g : hoare[SimPrepare(FOGActual,SimHActual).run:
 acwc2_cache_matches g ROG.m ==>acwc2_cache_matches g ROG.m].
proof.
 proc;sp 3;if;last by auto.
 seq 1:(acwc2_cache_matches g ROG.m);first by call(sim_prefix_cache g);auto.
 if;last by auto. sp 1;if;last by auto.
 wp;call(sim_answer_cache g);auto.
qed.
lemma sim_prepare_h_invariant : hoare[SimPrepare(FOGActual,SimHActual).run:
 sim_log_included SimHistory.h ROH.m /\ sim_h_cover SimHistory.h ROH.m FOContext.challenge_h ==>
 sim_log_included SimHistory.h ROH.m /\ sim_h_cover SimHistory.h ROH.m FOContext.challenge_h].
proof.
 proc;sp 3;if;last by auto.
 seq 1:(sim_log_included SimHistory.h ROH.m /\ sim_h_cover SimHistory.h ROH.m FOContext.challenge_h).
 + call(_:true ==>true);first by trivial. auto.
 if;last by auto. sp 1;if;last by auto.
 wp;call sim_answer_h_invariant;auto.
qed.
lemma sim_prepare_unknown pk0 log0 ex0 : hoare[SimPrepare(FOGActual,SimHActual).run:
 SimPublic.pk=pk0 /\ SimHistory.h=log0 /\ FOContext.challenge_h=ex0 ==>
 res.`1<>None=>let q=oget res.`1 in
 q.`sr_pk=pk0 /\ sim_h_input q \notin log0 /\ Some(sim_h_input q)<>ex0].
proof.
 proc;sp 3;if;last by auto.
 seq 1:(SimPublic.pk=pk0 /\ SimHistory.h=log0 /\ FOContext.challenge_h=ex0 /\
 (request<>None=>(oget request).`sr_pk=pk0)).
 + ecall(sim_prefix_fields FOGActual pk0 ct CCADecapOracle.sk);auto=> />;smt().
 if;last by auto. sp 1;if.
 + wp;call(_:true ==>true);first by trivial. auto.
 auto;smt().
qed.
lemma sim_prepare_frame pk0 suffix0 star0 n0 log0 ctx0 bad0 :
 hoare[SimPrepare(FOGActual,SimHActual).run:
 SimPublic.pk=pk0 /\ SimPublic.suffix=suffix0 /\ SimPublic.cstar=star0 /\ SimPublic.count=n0 /\
 SimHistory.h=log0 /\ glob FOContext=ctx0 /\ glob SimBad=bad0 ==>
 SimPublic.pk=pk0 /\ SimPublic.suffix=suffix0 /\ SimPublic.cstar=star0 /\ SimPublic.count=n0+1 /\
 SimHistory.h=log0 /\ glob FOContext=ctx0 /\ glob SimBad=bad0].
proof.
 proc;sp 3;if;last by auto.
 seq 1:(SimPublic.pk=pk0 /\ SimPublic.suffix=suffix0 /\ SimPublic.cstar=star0 /\ SimPublic.count=n0+1 /\
 SimHistory.h=log0 /\ glob FOContext=ctx0 /\ glob SimBad=bad0).
 + call(_:true ==>true);first by trivial. auto.
 if;last by auto. sp 1;if;last by auto.
 wp;call(_:true ==>true);first by trivial. auto.
qed.

lemma sim_raw_g_cache g : hoare[FOGRawStreams(FOGActual).g:
 acwc2_cache_matches g ROG.m ==>acwc2_cache_matches g ROG.m].
proof.
 proc;seq 1:(acwc2_cache_matches g ROG.m);first by call(sim_g_cache_preserves g);auto.
 if;auto.
qed.
lemma sim_raw_full_cache g : hoare[SimRaw(FOGActual,SimHActual).full:
 acwc2_cache_matches g ROG.m ==>acwc2_cache_matches g ROG.m].
proof.
 proc;match.
 + call(_:true ==>true);first by trivial. auto.
 match.
 + call(_:true ==>true);first by trivial. auto.
 + call(_:true ==>true);first by trivial. auto.
 + call(sim_raw_g_cache g);auto.
 call(_:true ==>true);first by trivial. auto.
qed.
lemma sim_raw_cache g : hoare[SimRaw(FOGActual,SimHActual).get:
 acwc2_cache_matches g ROG.m ==>acwc2_cache_matches g ROG.m].
proof. proc;sp 1;if;last by auto. wp;call(sim_raw_full_cache g);auto. qed.
lemma sim_raw_full_h_invariant : hoare[SimRaw(FOGActual,SimHActual).full:
 sim_log_included SimHistory.h ROH.m /\ sim_h_cover SimHistory.h ROH.m FOContext.challenge_h ==>
 sim_log_included SimHistory.h ROH.m /\ sim_h_cover SimHistory.h ROH.m FOContext.challenge_h].
proof.
 proc;match.
 + call(_:true ==>true);first by trivial. auto.
 match.
 + call(_:true ==>true);first by trivial. auto.
 + call(_:true ==>true);first by trivial. auto.
 + call(_:true ==>true);first by trivial. auto.
 call sim_logged_h_h_invariant;auto.
qed.
lemma sim_raw_h_invariant : hoare[SimRaw(FOGActual,SimHActual).get:
 sim_log_included SimHistory.h ROH.m /\ sim_h_cover SimHistory.h ROH.m FOContext.challenge_h ==>
 sim_log_included SimHistory.h ROH.m /\ sim_h_cover SimHistory.h ROH.m FOContext.challenge_h].
proof. proc;sp 1;if;last by auto. wp;call sim_raw_full_h_invariant;auto. qed.

lemma sim_leaks_cache g : hoare[SimLeaksBackend(FOGActual,SimHActual).leaks:
 acwc2_cache_matches g ROG.m ==>acwc2_cache_matches g ROG.m].
proof.
 proc;match;wp.
 + call(_:true ==>true);first by trivial. auto.
 + call(_:true ==>true);first by trivial. auto.
 + inline SimOracles(FOGActual,SimHActual).g;wp;call(sim_g_cache_preserves g);auto.
 + call(_:true ==>true);first by trivial. auto.
 + call(sim_raw_cache g);auto.
 call(sim_prepare_cache g);auto.
qed.
lemma sim_leaks_h_invariant : hoare[SimLeaksBackend(FOGActual,SimHActual).leaks:
 sim_log_included SimHistory.h ROH.m /\ sim_h_cover SimHistory.h ROH.m FOContext.challenge_h ==>
 sim_log_included SimHistory.h ROH.m /\ sim_h_cover SimHistory.h ROH.m FOContext.challenge_h].
proof.
 proc;match;wp.
 + call(_:true ==>true);first by trivial. auto.
 + call(_:true ==>true);first by trivial. auto.
 + call(_:true ==>true);first by trivial. auto.
 + call sim_logged_h_h_invariant;auto.
 + call sim_raw_h_invariant;auto.
 call sim_prepare_h_invariant;auto.
qed.
lemma sim_leaks_frame pk0 suffix0 star0 ctx0 bad0 :
 hoare[SimLeaksBackend(FOGActual,SimHActual).leaks:
 SimPublic.pk=pk0 /\ SimPublic.suffix=suffix0 /\ SimPublic.cstar=star0 /\
 glob FOContext=ctx0 /\ glob SimBad=bad0 ==>
 SimPublic.pk=pk0 /\ SimPublic.suffix=suffix0 /\ SimPublic.cstar=star0 /\
 glob FOContext=ctx0 /\ glob SimBad=bad0].
proof.
 proc;match;wp;call(_:true ==>true);try by trivial.
qed.

lemma sim_prepare_fresh pk0 log0 ex0 : hoare[SimPrepare(FOGActual,SimHActual).run:
 SimPublic.pk=pk0 /\ SimHistory.h=log0 /\ FOContext.challenge_h=ex0 /\ sim_h_cover log0 ROH.m ex0 ==>
 res.`1<>None=>let q=oget res.`1 in q.`sr_pk=pk0 /\ sim_h_input q \notin ROH.m].
proof.
 proc;sp 3;if;last by auto.
 seq 1:(SimPublic.pk=pk0 /\ SimHistory.h=log0 /\ FOContext.challenge_h=ex0 /\
 sim_h_cover log0 ROH.m ex0 /\ (request<>None=>(oget request).`sr_pk=pk0)).
 + ecall(sim_prefix_fields FOGActual pk0 ct CCADecapOracle.sk);auto=> />;smt().
 if;last by auto. sp 1;if.
 + wp;call(_:true ==>true);first by trivial. auto.
 auto;smt(sim_cover_fresh).
qed.
lemma sim_leaks_unknown pk0 log0 ex0 : hoare[SimLeaksBackend(FOGActual,SimHActual).leaks:
 SimPublic.pk=pk0 /\ SimHistory.h=log0 /\ FOContext.challenge_h=ex0 ==>
 (sim_out_decap res).`1<>None=>let q=oget(sim_out_decap res).`1 in
 q.`sr_pk=pk0 /\ sim_h_input q \notin log0 /\ Some(sim_h_input q)<>ex0].
proof.
 proc;match;wp.
 + call(_:true ==>true);first by trivial. auto.
 + call(_:true ==>true);first by trivial. auto.
 + call(_:true ==>true);first by trivial. auto.
 + call(_:true ==>true);first by trivial. auto.
 + call(_:true ==>true);first by trivial. auto.
 call(sim_prepare_unknown pk0 log0 ex0);auto.
qed.
lemma sim_leaks_fresh pk0 log0 ex0 : hoare[SimLeaksBackend(FOGActual,SimHActual).leaks:
 SimPublic.pk=pk0 /\ SimHistory.h=log0 /\ FOContext.challenge_h=ex0 /\ sim_h_cover log0 ROH.m ex0 ==>
 (sim_out_decap res).`1<>None=>let q=oget(sim_out_decap res).`1 in
 q.`sr_pk=pk0 /\ sim_h_input q \notin ROH.m].
proof.
 proc;match;wp.
 + call(_:true ==>true);first by trivial. auto.
 + call(_:true ==>true);first by trivial. auto.
 + call(_:true ==>true);first by trivial. auto.
 + call(_:true ==>true);first by trivial. auto.
 + call(_:true ==>true);first by trivial. auto.
 call(sim_prepare_fresh pk0 log0 ex0);auto.
qed.
