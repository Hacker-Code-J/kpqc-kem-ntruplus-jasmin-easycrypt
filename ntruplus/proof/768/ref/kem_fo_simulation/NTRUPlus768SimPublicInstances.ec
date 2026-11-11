require import AllCore List Distr FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152.
require import NTRUPlus768ROMDomains NTRUPlus768ROMOracles NTRUPlus768RawXOFStreams NTRUPlus768RawXOF NTRUPlus768CCAGame NTRUPlus768CCADecapOracle.
require import NTRUPlus768CCAQueryCodec NTRUPlus768FOModel NTRUPlus768FOError NTRUPlus768FOEagerG NTRUPlus768FOQueryBudget.
require import NTRUPlus768SimModel NTRUPlus768SimSampling NTRUPlus768SimOracles NTRUPlus768SimPublicError NTRUPlus768SimPublicBound.

lemma sim_public_e_frame w0 g0 ex0 b : hoare[SimOracles(SimGActual,SimPublicErrorH(SimHActual)).e:
 sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ SimBad.corr=b ==> sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ SimBad.corr=b].
proof. proc*;call(_:true ==>true);first by trivial. auto. qed.
lemma sim_public_f_frame w0 g0 ex0 b : hoare[SimOracles(SimGActual,SimPublicErrorH(SimHActual)).f:
 sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ SimBad.corr=b ==> sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ SimBad.corr=b].
proof. proc*;call(_:true ==>true);first by trivial. auto. qed.
lemma sim_public_g_frame w0 g0 ex0 b : hoare[SimOracles(SimGActual,SimPublicErrorH(SimHActual)).g:
 sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ SimBad.corr=b ==> sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ SimBad.corr=b].
proof. proc*;call(_:true ==>true);first by trivial. auto. qed.
lemma sim_public_h_context w0 g0 ex0 : hoare[SimOracles(SimGActual,SimPublicErrorH(SimHActual)).h:FOContext.w=w0 /\ FOContext.g=g0 /\ FOContext.challenge_h=ex0 ==> FOContext.w=w0 /\ FOContext.g=g0 /\ FOContext.challenge_h=ex0].
proof. proc;inline SimHistory.record;wp;call(_:true ==>true);first by trivial. auto. qed.
lemma sim_public_h_state w0 g0 ex0 : hoare[SimOracles(SimGActual,SimPublicErrorH(SimHActual)).h:sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) ==> sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m)].
proof.
 conseq [-frame](sim_public_h_context w0 g0 ex0)
  (_:sim_log_included SimHistory.h ROH.m /\ sim_h_cover SimHistory.h ROH.m ex0 ==> sim_log_included SimHistory.h ROH.m /\ sim_h_cover SimHistory.h ROH.m ex0);1,2:by rewrite /sim_public_inv /=;progress.
 conseq [-frame] sim_public_logged_included (sim_public_logged_cover ex0);smt().
qed.
lemma sim_public_h_latched : hoare[SimOracles(SimGActual,SimPublicErrorH(SimHActual)).h:SimBad.corr ==>SimBad.corr].
proof.
 proc;inline SimHistory.record;wp;call(sim_public_error_latched SimHActual);auto.
qed.
lemma sim_public_h_frame w0 g0 ex0 b : hoare[SimOracles(SimGActual,SimPublicErrorH(SimHActual)).h:
 sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ SimBad.corr=b ==> sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ (b=>SimBad.corr)].
proof.
 case b=>_.
 + conseq [-frame](sim_public_h_state w0 g0 ex0) sim_public_h_latched;smt().
 conseq [-frame](sim_public_h_state w0 g0 ex0);smt().
qed.
lemma sim_public_raw_full_state w0 g0 ex0 : hoare[SimRaw(SimGActual,SimPublicErrorH(SimHActual)).full:sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) ==> sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m)].
proof.
 proc;match.
 + call(_:true ==>true);first by trivial. auto.
 match.
 + call(_:true ==>true);first by trivial. auto.
 + call(_:true ==>true);first by trivial. auto.
 + call(_:true ==>true);first by trivial. auto.
 call(sim_public_h_state w0 g0 ex0);auto.
qed.
lemma sim_public_raw_state w0 g0 ex0 : hoare[SimOracles(SimGActual,SimPublicErrorH(SimHActual)).raw:sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) ==> sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m)].
proof. proc;sp 1;if;last by auto. wp;call(sim_public_raw_full_state w0 g0 ex0);auto. qed.
lemma sim_public_raw_full_latched : hoare[SimRaw(SimGActual,SimPublicErrorH(SimHActual)).full:SimBad.corr ==>SimBad.corr].
proof.
 proc;match.
 + call(_:true ==>true);first by trivial. auto.
 match.
 + call(_:true ==>true);first by trivial. auto.
 + call(_:true ==>true);first by trivial. auto.
 + call(_:true ==>true);first by trivial. auto.
 call sim_public_h_latched;auto.
qed.
lemma sim_public_raw_latched : hoare[SimOracles(SimGActual,SimPublicErrorH(SimHActual)).raw:SimBad.corr ==>SimBad.corr].
proof. proc;sp 1;if;last by auto. wp;call sim_public_raw_full_latched;auto. qed.
lemma sim_public_raw_frame w0 g0 ex0 b : hoare[SimOracles(SimGActual,SimPublicErrorH(SimHActual)).raw:
 sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ SimBad.corr=b ==> sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ (b=>SimBad.corr)].
proof.
 case b=>_.
 + conseq [-frame](sim_public_raw_state w0 g0 ex0) sim_public_raw_latched;smt().
 conseq [-frame](sim_public_raw_state w0 g0 ex0);smt().
qed.
lemma sim_public_raw_full_non_h_corr b : hoare[SimRaw(SimGActual,SimPublicErrorH(SimHActual)).full:
 SimBad.corr=b /\ (forall x,decode_typed input<>Some(H x)) ==>SimBad.corr=b].
proof.
 proc;match.
 + call(_:true ==>true);first by trivial. auto.
 match.
 + call(_:true ==>true);first by trivial. auto.
 + call(_:true ==>true);first by trivial. auto.
 + call(_:true ==>true);first by trivial. auto.
 conseq [-frame](_:false ==>_)=> //;smt().
qed.
lemma sim_public_raw_non_h_corr b : hoare[SimOracles(SimGActual,SimPublicErrorH(SimHActual)).raw:
 SimBad.corr=b /\ !fo_raw_h input outlen ==>SimBad.corr=b].
proof.
 proc;sp 1;if;last by auto. wp;call(sim_public_raw_full_non_h_corr b);auto=> />;smt(fo_raw_h_classification).
qed.
lemma sim_public_raw_non_h_frame w0 g0 ex0 b : hoare[SimOracles(SimGActual,SimPublicErrorH(SimHActual)).raw:
 sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ SimBad.corr=b /\ !fo_raw_h input outlen ==> sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ SimBad.corr=b].
proof.
 conseq [-frame](sim_public_raw_state w0 g0 ex0)(sim_public_raw_non_h_corr b);smt().
qed.
lemma sim_public_h_cost w0 g0 ex0 : phoare[SimOracles(SimGActual,SimPublicErrorH(SimHActual)).h:
 sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ !SimBad.corr ==>SimBad.corr]<=(fo_error w0 g0).
proof. conseq [-frame](sim_public_logged_error_bad_bound w0 g0);rewrite /sim_public_inv;smt(). qed.
lemma sim_public_raw_cost w0 g0 ex0 : phoare[SimOracles(SimGActual,SimPublicErrorH(SimHActual)).raw:
 sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ !SimBad.corr /\ fo_raw_h input outlen ==>SimBad.corr]<=(fo_error w0 g0).
proof. conseq [-frame](sim_public_raw_bad_bound w0 g0);rewrite /sim_public_inv;smt(). qed.

require import NTRUPlus768SimKnown NTRUPlus768SimLookup NTRUPlus768SimGErasure.
module SimKnownPublicBackend = FOBackendPair(SimOracles(SimGActual,SimPublicErrorH(SimHActual)),SimKnownDecap(SimGActual,SimHActual)).
module SimGhostPublicBackend = FOBackendPair(SimOracles(SimGActual,SimPublicErrorH(SimHActual)),SimGhostLookup(SimGActual)).
module SimLookupPublicBackend = FOBackendPair(SimOracles(SimGActual,SimPublicErrorH(SimHActual)),SimLookup(SimGActual)).

lemma sim_public_known_d_frame w0 g0 ex0 b : hoare[SimKnownPublicBackend.decap:
 sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ SimBad.corr=b ==> sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ SimBad.corr=b].
proof.
 proc*;exists* SimHistory.h,ROH.m;elim*=>log0 hm0.
 call(sim_known_decap_h_frame_pre log0 hm0);auto=> />;rewrite /sim_public_inv;smt().
qed.
lemma sim_public_lookup_d_frame w0 g0 ex0 b : hoare[SimLookupPublicBackend.decap:
 sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ SimBad.corr=b ==> sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ SimBad.corr=b].
proof. proc*;call(_:true ==>true);first by trivial. auto. qed.

lemma sim_public_ghost_d_frame w0 g0 ex0 b : hoare[SimGhostPublicBackend.decap:
 sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ SimBad.corr=b ==> sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ SimBad.corr=b].
proof. proc*;call(_:true ==>true);first by trivial. auto. qed.


(* Actual known backend; no valid-key/prepared-G or adversary-LL premise
   is needed for this returned public-correction bad mass. *)
lemma sim_public_known_bounded_corr
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
  -FOContext,-SimPublic,-SimHistory,-SimBad,-SimPublicBudget})
 w0 g0 ex0 q0 pk0 ct0 key0 &m :
 0<=q0 =>sim_public_inv w0 g0 ex0
 (FOContext.w{m},FOContext.g{m},FOContext.challenge_h{m},SimHistory.h{m},ROH.m{m})=>
 Pr[SimPublicBoundedPhase(A,SimKnownPublicBackend).run(q0,pk0,ct0,key0) @ &m:SimBad.corr]<=q0%r*fo_error w0 g0.
proof.
 move=>hq hi;apply(sim_public_bounded_corr A SimKnownPublicBackend w0 g0 ex0 q0 pk0 ct0 key0 &m hq hi).
 + move=>b;exact(sim_public_e_frame w0 g0 ex0 b).
 + move=>b;exact(sim_public_f_frame w0 g0 ex0 b).
 + move=>b;exact(sim_public_g_frame w0 g0 ex0 b).
 + move=>b;exact(sim_public_h_frame w0 g0 ex0 b).
 + move=>b;exact(sim_public_raw_frame w0 g0 ex0 b).
 + move=>b;exact(sim_public_raw_non_h_frame w0 g0 ex0 b).
 + move=>b;exact(sim_public_known_d_frame w0 g0 ex0 b).
 + exact(sim_public_h_cost w0 g0 ex0).
 exact(sim_public_raw_cost w0 g0 ex0).
qed.

(* Actual lookup backend; no valid-key/prepared-G or adversary-LL premise
   is needed for this returned public-correction bad mass. *)
lemma sim_public_lookup_bounded_corr
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
  -FOContext,-SimPublic,-SimHistory,-SimBad,-SimPublicBudget})
 w0 g0 ex0 q0 pk0 ct0 key0 &m :
 0<=q0 =>sim_public_inv w0 g0 ex0
 (FOContext.w{m},FOContext.g{m},FOContext.challenge_h{m},SimHistory.h{m},ROH.m{m})=>
 Pr[SimPublicBoundedPhase(A,SimLookupPublicBackend).run(q0,pk0,ct0,key0) @ &m:SimBad.corr]<=q0%r*fo_error w0 g0.
proof.
 move=>hq hi;apply(sim_public_bounded_corr A SimLookupPublicBackend w0 g0 ex0 q0 pk0 ct0 key0 &m hq hi).
 + move=>b;exact(sim_public_e_frame w0 g0 ex0 b).
 + move=>b;exact(sim_public_f_frame w0 g0 ex0 b).
 + move=>b;exact(sim_public_g_frame w0 g0 ex0 b).
 + move=>b;exact(sim_public_h_frame w0 g0 ex0 b).
 + move=>b;exact(sim_public_raw_frame w0 g0 ex0 b).
 + move=>b;exact(sim_public_raw_non_h_frame w0 g0 ex0 b).
 + move=>b;exact(sim_public_lookup_d_frame w0 g0 ex0 b).
 + exact(sim_public_h_cost w0 g0 ex0).
 exact(sim_public_raw_cost w0 g0 ex0).
qed.

(* Actual ghost backend; no valid-key/prepared-G or adversary-LL premise
   is needed for this returned public-correction bad mass. *)
lemma sim_public_ghost_bounded_corr
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
  -FOContext,-SimPublic,-SimHistory,-SimBad,-SimPublicBudget})
 w0 g0 ex0 q0 pk0 ct0 key0 &m :
 0<=q0 =>sim_public_inv w0 g0 ex0
 (FOContext.w{m},FOContext.g{m},FOContext.challenge_h{m},SimHistory.h{m},ROH.m{m})=>
 Pr[SimPublicBoundedPhase(A,SimGhostPublicBackend).run(q0,pk0,ct0,key0) @ &m:SimBad.corr]<=q0%r*fo_error w0 g0.
proof.
 move=>hq hi;apply(sim_public_bounded_corr A SimGhostPublicBackend w0 g0 ex0 q0 pk0 ct0 key0 &m hq hi).
 + move=>b;exact(sim_public_e_frame w0 g0 ex0 b).
 + move=>b;exact(sim_public_f_frame w0 g0 ex0 b).
 + move=>b;exact(sim_public_g_frame w0 g0 ex0 b).
 + move=>b;exact(sim_public_h_frame w0 g0 ex0 b).
 + move=>b;exact(sim_public_raw_frame w0 g0 ex0 b).
 + move=>b;exact(sim_public_raw_non_h_frame w0 g0 ex0 b).
 + move=>b;exact(sim_public_ghost_d_frame w0 g0 ex0 b).
 + exact(sim_public_h_cost w0 g0 ex0).
 exact(sim_public_raw_cost w0 g0 ex0).
qed.

require import NTRUPlus768CCAOraclePorts NTRUPlus768SimPublicCapRemoval.
lemma sim_public_e_ll : islossless SimOracles(SimGActual,SimPublicErrorH(SimHActual)).e.
proof. exact cca_e_ll. qed.
lemma sim_public_f_ll : islossless SimOracles(SimGActual,SimPublicErrorH(SimHActual)).f.
proof. exact cca_f_ll. qed.
lemma sim_public_g_ll : islossless SimOracles(SimGActual,SimPublicErrorH(SimHActual)).g.
proof. proc;call rog_get_ll;auto. qed.
lemma sim_public_h_ll : islossless SimOracles(SimGActual,SimPublicErrorH(SimHActual)).h.
proof. exact(sim_logged_h_ll (SimPublicErrorH(SimHActual)) (sim_public_error_ll SimHActual roh_get_ll)). qed.
lemma sim_public_raw_ll : islossless SimOracles(SimGActual,SimPublicErrorH(SimHActual)).raw.
proof. exact(sim_raw_get_ll SimGActual (SimPublicErrorH(SimHActual)) rog_get_ll (sim_public_error_ll SimHActual roh_get_ll)). qed.
lemma sim_public_known_d_ll : islossless SimKnownPublicBackend.decap.
proof. exact(sim_known_decap_ll SimGActual SimHActual rog_get_ll roh_get_ll). qed.
lemma sim_public_ghost_d_ll : islossless SimGhostPublicBackend.decap.
proof. exact(sim_ghost_lookup_ll SimGActual rog_get_ll). qed.
lemma sim_public_lookup_d_ll : islossless SimLookupPublicBackend.decap.
proof. exact(sim_lookup_lossless SimGActual rog_get_ll). qed.

(* This backend has its own count contract. No other endpoint's query
   bound is silently reused, and robust termination is a separate premise. *)
lemma sim_public_known_phase_uncapped
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
  -FOContext,-SimPublic,-SimHistory,-SimBad,-SimPublicBudget}) q0 : 0<=q0 =>
 (forall (H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess) =>
 hoare[SimPublicCountedA(A,FOHashView(SimKnownPublicBackend),FODecapView(SimKnownPublicBackend)).guess:
 sim_public_budget_initial q0 SimPublicBudget.nh SimPublicBudget.limit SimPublicBudget.overflow ==>
 SimPublicBudget.nh<=q0] =>
 equiv[SimPublicBoundedPhase(A,SimKnownPublicBackend).run ~ A(FOHashView(SimKnownPublicBackend),FODecapView(SimKnownPublicBackend)).guess:
 q{1}=q0 /\ ={pk,ct,key,glob A,glob SimKnownPublicBackend} /\ !SimBad.corr{2} ==>
 ={res,glob A,glob SimKnownPublicBackend}].
proof.
 move=>hq all bounded;proc*;inline{1} SimPublicBoundedPhase(A,SimKnownPublicBackend).run;wp.
 call(sim_public_capped_phase_plain A SimKnownPublicBackend q0
   sim_public_e_ll sim_public_f_ll sim_public_g_ll sim_public_h_ll sim_public_raw_ll
   sim_public_known_d_ll all bounded).
 inline SimPublicBudget.init;auto=> />;smt().
qed.

lemma sim_public_known_uncapped_corr
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
  -FOContext,-SimPublic,-SimHistory,-SimBad,-SimPublicBudget}) w0 g0 ex0 q0 pk0 ct0 key0 &m :
 0<=q0 =>sim_public_inv w0 g0 ex0
 (FOContext.w{m},FOContext.g{m},FOContext.challenge_h{m},SimHistory.h{m},ROH.m{m})=>
 !SimBad.corr{m} =>
 (forall (H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess) =>
 hoare[SimPublicCountedA(A,FOHashView(SimKnownPublicBackend),FODecapView(SimKnownPublicBackend)).guess:
 sim_public_budget_initial q0 SimPublicBudget.nh SimPublicBudget.limit SimPublicBudget.overflow ==>
 SimPublicBudget.nh<=q0] =>
 Pr[A(FOHashView(SimKnownPublicBackend),FODecapView(SimKnownPublicBackend)).guess(pk0,ct0,key0) @ &m:SimBad.corr]
 <=q0%r*fo_error w0 g0.
proof.
 move=>hq hi hc all bounded.
 have he:Pr[SimPublicBoundedPhase(A,SimKnownPublicBackend).run(q0,pk0,ct0,key0) @ &m:SimBad.corr]=
 Pr[A(FOHashView(SimKnownPublicBackend),FODecapView(SimKnownPublicBackend)).guess(pk0,ct0,key0) @ &m:SimBad.corr].
 + by byequiv(sim_public_known_phase_uncapped A q0 hq all bounded)=> //.
 rewrite -he;exact(sim_public_known_bounded_corr A w0 g0 ex0 q0 pk0 ct0 key0 &m hq hi).
qed.

(* This backend has its own count contract. No other endpoint's query
   bound is silently reused, and robust termination is a separate premise. *)
lemma sim_public_ghost_phase_uncapped
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
  -FOContext,-SimPublic,-SimHistory,-SimBad,-SimPublicBudget}) q0 : 0<=q0 =>
 (forall (H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess) =>
 hoare[SimPublicCountedA(A,FOHashView(SimGhostPublicBackend),FODecapView(SimGhostPublicBackend)).guess:
 sim_public_budget_initial q0 SimPublicBudget.nh SimPublicBudget.limit SimPublicBudget.overflow ==>
 SimPublicBudget.nh<=q0] =>
 equiv[SimPublicBoundedPhase(A,SimGhostPublicBackend).run ~ A(FOHashView(SimGhostPublicBackend),FODecapView(SimGhostPublicBackend)).guess:
 q{1}=q0 /\ ={pk,ct,key,glob A,glob SimGhostPublicBackend} /\ !SimBad.corr{2} ==>
 ={res,glob A,glob SimGhostPublicBackend}].
proof.
 move=>hq all bounded;proc*;inline{1} SimPublicBoundedPhase(A,SimGhostPublicBackend).run;wp.
 call(sim_public_capped_phase_plain A SimGhostPublicBackend q0
   sim_public_e_ll sim_public_f_ll sim_public_g_ll sim_public_h_ll sim_public_raw_ll
   sim_public_ghost_d_ll all bounded).
 inline SimPublicBudget.init;auto=> />;smt().
qed.

lemma sim_public_ghost_uncapped_corr
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
  -FOContext,-SimPublic,-SimHistory,-SimBad,-SimPublicBudget}) w0 g0 ex0 q0 pk0 ct0 key0 &m :
 0<=q0 =>sim_public_inv w0 g0 ex0
 (FOContext.w{m},FOContext.g{m},FOContext.challenge_h{m},SimHistory.h{m},ROH.m{m})=>
 !SimBad.corr{m} =>
 (forall (H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess) =>
 hoare[SimPublicCountedA(A,FOHashView(SimGhostPublicBackend),FODecapView(SimGhostPublicBackend)).guess:
 sim_public_budget_initial q0 SimPublicBudget.nh SimPublicBudget.limit SimPublicBudget.overflow ==>
 SimPublicBudget.nh<=q0] =>
 Pr[A(FOHashView(SimGhostPublicBackend),FODecapView(SimGhostPublicBackend)).guess(pk0,ct0,key0) @ &m:SimBad.corr]
 <=q0%r*fo_error w0 g0.
proof.
 move=>hq hi hc all bounded.
 have he:Pr[SimPublicBoundedPhase(A,SimGhostPublicBackend).run(q0,pk0,ct0,key0) @ &m:SimBad.corr]=
 Pr[A(FOHashView(SimGhostPublicBackend),FODecapView(SimGhostPublicBackend)).guess(pk0,ct0,key0) @ &m:SimBad.corr].
 + by byequiv(sim_public_ghost_phase_uncapped A q0 hq all bounded)=> //.
 rewrite -he;exact(sim_public_ghost_bounded_corr A w0 g0 ex0 q0 pk0 ct0 key0 &m hq hi).
qed.

(* This backend has its own count contract. No other endpoint's query
   bound is silently reused, and robust termination is a separate premise. *)
lemma sim_public_lookup_phase_uncapped
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
  -FOContext,-SimPublic,-SimHistory,-SimBad,-SimPublicBudget}) q0 : 0<=q0 =>
 (forall (H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess) =>
 hoare[SimPublicCountedA(A,FOHashView(SimLookupPublicBackend),FODecapView(SimLookupPublicBackend)).guess:
 sim_public_budget_initial q0 SimPublicBudget.nh SimPublicBudget.limit SimPublicBudget.overflow ==>
 SimPublicBudget.nh<=q0] =>
 equiv[SimPublicBoundedPhase(A,SimLookupPublicBackend).run ~ A(FOHashView(SimLookupPublicBackend),FODecapView(SimLookupPublicBackend)).guess:
 q{1}=q0 /\ ={pk,ct,key,glob A,glob SimLookupPublicBackend} /\ !SimBad.corr{2} ==>
 ={res,glob A,glob SimLookupPublicBackend}].
proof.
 move=>hq all bounded;proc*;inline{1} SimPublicBoundedPhase(A,SimLookupPublicBackend).run;wp.
 call(sim_public_capped_phase_plain A SimLookupPublicBackend q0
   sim_public_e_ll sim_public_f_ll sim_public_g_ll sim_public_h_ll sim_public_raw_ll
   sim_public_lookup_d_ll all bounded).
 inline SimPublicBudget.init;auto=> />;smt().
qed.

lemma sim_public_lookup_uncapped_corr
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
  -FOContext,-SimPublic,-SimHistory,-SimBad,-SimPublicBudget}) w0 g0 ex0 q0 pk0 ct0 key0 &m :
 0<=q0 =>sim_public_inv w0 g0 ex0
 (FOContext.w{m},FOContext.g{m},FOContext.challenge_h{m},SimHistory.h{m},ROH.m{m})=>
 !SimBad.corr{m} =>
 (forall (H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess) =>
 hoare[SimPublicCountedA(A,FOHashView(SimLookupPublicBackend),FODecapView(SimLookupPublicBackend)).guess:
 sim_public_budget_initial q0 SimPublicBudget.nh SimPublicBudget.limit SimPublicBudget.overflow ==>
 SimPublicBudget.nh<=q0] =>
 Pr[A(FOHashView(SimLookupPublicBackend),FODecapView(SimLookupPublicBackend)).guess(pk0,ct0,key0) @ &m:SimBad.corr]
 <=q0%r*fo_error w0 g0.
proof.
 move=>hq hi hc all bounded.
 have he:Pr[SimPublicBoundedPhase(A,SimLookupPublicBackend).run(q0,pk0,ct0,key0) @ &m:SimBad.corr]=
 Pr[A(FOHashView(SimLookupPublicBackend),FODecapView(SimLookupPublicBackend)).guess(pk0,ct0,key0) @ &m:SimBad.corr].
 + by byequiv(sim_public_lookup_phase_uncapped A q0 hq all bounded)=> //.
 rewrite -he;exact(sim_public_lookup_bounded_corr A w0 g0 ex0 q0 pk0 ct0 key0 &m hq hi).
qed.
