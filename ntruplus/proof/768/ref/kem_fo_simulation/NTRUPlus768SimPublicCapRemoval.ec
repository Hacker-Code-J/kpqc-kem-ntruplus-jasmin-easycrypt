require import AllCore List Distr FMap.
from Jasmin require import JWord.
require import Array32 Array1152.
require import NTRUPlus768CCAGame NTRUPlus768RawXOF NTRUPlus768CCADecapOracle.
require import NTRUPlus768FOModel NTRUPlus768ROMOracles NTRUPlus768SimModel.
require import NTRUPlus768FOQueryBudget NTRUPlus768SimPublicBound.

(* Generic backend-specific cap removal. Each concrete Known/Ghost/Lookup
   endpoint supplies its own counted-query contract and robust LL premises.
   Typed H, valid raw H, repetitions and length zero share this one counter. *)
op sim_public_budget_initial (q nh lim:int) (over:bool) =
 0<=q /\ nh=0 /\ lim=q /\ !over.

module SimPublicConfiguredA(A:CCAExtendedAdversary,H:CCAExtendedOraclePort,D:CCADecapPort) = {
 proc guess(pk:W8.t Array1152.t,ct:W8.t Array1152.t,key:W8.t Array32.t) : bool = {
  var q:int; var answer:bool;
  q<-SimPublicBudget.limit;
  SimPublicBudget.init(q);
  answer <@ SimPublicCappedA(A,H,D).guess(pk,ct,key);
  return answer;
 }
}.

lemma sim_public_budget_initialize q0 :0<=q0=>
 hoare[SimPublicBudget.init:q=q0 ==>
 sim_public_budget_initial q0 SimPublicBudget.nh SimPublicBudget.limit SimPublicBudget.overflow].
proof. move=>hq; proc; auto; rewrite /sim_public_budget_initial; smt(). qed.

lemma sim_public_count_h_overflow_latched (B<:FOBackend {-SimPublicBudget}) :
 hoare[SimPublicCountH(FOHashView(B)).h:SimPublicBudget.overflow ==>SimPublicBudget.overflow].
proof.
 proc; inline SimPublicBudget.request.
 call(_:true ==>true); first by trivial. auto; smt().
qed.

lemma sim_public_cap_h_overflow_latched (B<:FOBackend {-SimPublicBudget}) :
 hoare[SimPublicCapH(FOHashView(B)).h:SimPublicBudget.overflow ==>SimPublicBudget.overflow].
proof.
 proc; inline SimPublicBudget.request.
 sp; if; last by auto; smt().
 wp; call(_:true ==>true); first by trivial. auto; smt().
qed.

lemma sim_public_count_h_overflow_exact (B<:FOBackend {-SimPublicBudget}) q0 :
 hoare[SimPublicCountH(FOHashView(B)).h:SimPublicBudget.limit=q0 /\ SimPublicBudget.overflow=(q0<SimPublicBudget.nh) ==>SimPublicBudget.limit=q0 /\ SimPublicBudget.overflow=(q0<SimPublicBudget.nh)].
proof.
 proc; call(_:true ==>true); first by trivial.
 inline SimPublicBudget.request; auto; smt().
qed.

lemma sim_public_count_cap_h_step (B<:FOBackend {-SimPublicBudget}) :
 islossless B.h =>
 equiv[SimPublicCountH(FOHashView(B)).h ~ SimPublicCapH(FOHashView(B)).h:
 ={arg,glob B,glob SimPublicBudget} /\ !SimPublicBudget.overflow{2} ==>
 ={SimPublicBudget.overflow} /\ (!SimPublicBudget.overflow{2} => ={res,glob B,glob SimPublicBudget})].
proof.
 move=>hll; proc; inline SimPublicBudget.request; sp; if{2}.
 + wp; call(_: ={arg,glob B} ==> ={res,glob B}); first by proc true; auto.
   auto; smt().
 wp; call{1} hll; auto; smt().
qed.

lemma sim_public_count_raw_overflow_latched (B<:FOBackend {-SimPublicBudget}) :
 hoare[SimPublicCountH(FOHashView(B)).raw:SimPublicBudget.overflow ==>SimPublicBudget.overflow].
proof.
 proc; inline SimPublicBudget.request.
 call(_:true ==>true); first by trivial. auto; smt().
qed.

lemma sim_public_cap_raw_overflow_latched (B<:FOBackend {-SimPublicBudget}) :
 hoare[SimPublicCapH(FOHashView(B)).raw:SimPublicBudget.overflow ==>SimPublicBudget.overflow].
proof.
 proc; inline SimPublicBudget.request.
 sp; if; last by auto; smt().
 wp; call(_:true ==>true); first by trivial. auto; smt().
qed.

lemma sim_public_count_raw_overflow_exact (B<:FOBackend {-SimPublicBudget}) q0 :
 hoare[SimPublicCountH(FOHashView(B)).raw:SimPublicBudget.limit=q0 /\ SimPublicBudget.overflow=(q0<SimPublicBudget.nh) ==>SimPublicBudget.limit=q0 /\ SimPublicBudget.overflow=(q0<SimPublicBudget.nh)].
proof.
 proc; call(_:true ==>true); first by trivial.
 inline SimPublicBudget.request; auto; smt().
qed.

lemma sim_public_count_cap_raw_step (B<:FOBackend {-SimPublicBudget}) :
 islossless B.raw =>
 equiv[SimPublicCountH(FOHashView(B)).raw ~ SimPublicCapH(FOHashView(B)).raw:
 ={arg,glob B,glob SimPublicBudget} /\ !SimPublicBudget.overflow{2} ==>
 ={SimPublicBudget.overflow} /\ (!SimPublicBudget.overflow{2} => ={res,glob B,glob SimPublicBudget})].
proof.
 move=>hll; proc; inline SimPublicBudget.request; sp; if{2}.
 + wp; call(_: ={arg,glob B} ==> ={res,glob B}); first by proc true; auto.
   auto; smt().
 wp; call{1} hll; auto; smt().
qed.

lemma sim_public_count_d_overflow_latched (B<:FOBackend {-SimPublicBudget}) :
 hoare[SimPublicD(FODecapView(B)).decap:SimPublicBudget.overflow ==>SimPublicBudget.overflow].
proof.
 proc;wp;call(_:true ==>true);first by trivial. auto.
qed.

lemma sim_public_cap_d_overflow_latched (B<:FOBackend {-SimPublicBudget}) :
 hoare[SimPublicD(FODecapView(B)).decap:SimPublicBudget.overflow ==>SimPublicBudget.overflow].
proof.
 proc;wp;call(_:true ==>true);first by trivial. auto.
qed.

lemma sim_public_count_d_overflow_exact (B<:FOBackend {-SimPublicBudget}) q0 :
 hoare[SimPublicD(FODecapView(B)).decap:SimPublicBudget.limit=q0 /\ SimPublicBudget.overflow=(q0<SimPublicBudget.nh) ==>SimPublicBudget.limit=q0 /\ SimPublicBudget.overflow=(q0<SimPublicBudget.nh)].
proof.
 proc;wp;call(_:true ==>true);first by trivial. auto.
qed.

lemma sim_public_count_cap_d_step (B<:FOBackend {-SimPublicBudget}) :
 islossless B.decap =>
 equiv[SimPublicD(FODecapView(B)).decap ~ SimPublicD(FODecapView(B)).decap:
 ={arg,glob B,glob SimPublicBudget} /\ !SimPublicBudget.overflow{2} ==>
 ={SimPublicBudget.overflow} /\ (!SimPublicBudget.overflow{2} => ={res,glob B,glob SimPublicBudget})].
proof.
 move=>hll;proc;wp.
 call(_: ={arg,glob B} ==> ={res,glob B});first by proc true;auto.
 auto;smt().
qed.

lemma sim_public_counted_overflow_exact
 (A<:CCAExtendedAdversary {-SimPublicBudget}) (B<:FOBackend {-A,-SimPublicBudget}) q0 :
 hoare[SimPublicCountedA(A,FOHashView(B),FODecapView(B)).guess:
 SimPublicBudget.limit=q0 /\ SimPublicBudget.overflow=(q0<SimPublicBudget.nh) ==>
 SimPublicBudget.limit=q0 /\ SimPublicBudget.overflow=(q0<SimPublicBudget.nh)].
proof.
 proc(SimPublicBudget.limit=q0 /\ SimPublicBudget.overflow=(q0<SimPublicBudget.nh)); 1,2:by auto.
 + proc*; call(_:true ==>true); first by trivial. auto.
 + proc*; call(_:true ==>true); first by trivial. auto.
 + proc*; call(_:true ==>true); first by trivial. auto.
 + exact(sim_public_count_h_overflow_exact B q0).
 + exact(sim_public_count_raw_overflow_exact B q0).
 exact(sim_public_count_d_overflow_exact B q0).
qed.

lemma sim_public_count_d_projection (D<:CCADecapPort {-SimPublicBudget}) :
 equiv[SimPublicD(D).decap ~ D.decap: ={arg,glob D} ==> ={res,glob D}].
proof.
 proc*;inline{1} SimPublicD(D).decap;wp.
 call(_: ={arg,glob D} ==> ={res,glob D});first by proc true;auto. auto.
qed.

lemma sim_public_counted_adversary_projection
 (A<:CCAExtendedAdversary {-SimPublicBudget}) (B<:FOBackend {-A,-SimPublicBudget}) :
 equiv[SimPublicCountedA(A,FOHashView(B),FODecapView(B)).guess ~ A(FOHashView(B),FODecapView(B)).guess:
 ={arg,glob A,glob B} ==> ={res,glob A,glob B}].
proof.
 proc(={glob B}); 1,2:by auto.
 + proc true; auto.
 + proc true; auto.
 + proc true; auto.
 + conseq(sim_public_count_h_projection (FOHashView(B))); smt().
 + conseq(sim_public_count_raw_projection (FOHashView(B))); smt().
 conseq(sim_public_count_d_projection (FODecapView(B))); smt().
qed.

lemma sim_public_counted_no_overflow
 (A<:CCAExtendedAdversary {-SimPublicBudget}) (B<:FOBackend {-A,-SimPublicBudget}) q0 :
 hoare[SimPublicCountedA(A,FOHashView(B),FODecapView(B)).guess:
 sim_public_budget_initial q0 SimPublicBudget.nh SimPublicBudget.limit SimPublicBudget.overflow ==>
 SimPublicBudget.nh<=q0] =>
 hoare[SimPublicCountedA(A,FOHashView(B),FODecapView(B)).guess:
 sim_public_budget_initial q0 SimPublicBudget.nh SimPublicBudget.limit SimPublicBudget.overflow ==>
 !SimPublicBudget.overflow].
proof.
 move=>hb; conseq hb (sim_public_counted_overflow_exact A B q0); rewrite /sim_public_budget_initial; smt().
qed.

lemma sim_public_backend_e_same (B<:FOBackend {-SimPublicBudget}) :
 equiv[B.e ~ B.e: ={arg,glob B} ==> ={res,glob B}].
proof. proc true; auto. qed.

lemma sim_public_backend_f_same (B<:FOBackend {-SimPublicBudget}) :
 equiv[B.f ~ B.f: ={arg,glob B} ==> ={res,glob B}].
proof. proc true; auto. qed.

lemma sim_public_backend_g_same (B<:FOBackend {-SimPublicBudget}) :
 equiv[B.g ~ B.g: ={arg,glob B} ==> ={res,glob B}].
proof. proc true; auto. qed.

lemma sim_public_counted_phase_ll
 (A<:CCAExtendedAdversary {-SimPublicBudget}) (B<:FOBackend {-A,-SimPublicBudget}) :
 islossless B.e=>islossless B.f=>islossless B.g=>islossless B.h=>islossless B.raw=>islossless B.decap=>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess) =>
 islossless SimPublicCountedA(A,FOHashView(B),FODecapView(B)).guess.
proof.
 move=>he hf hg hh hr hd all.
 exact(all (SimPublicCountH(FOHashView(B))) (SimPublicD(FODecapView(B)))
   he hf hg (sim_public_count_h_ll (FOHashView(B)) hh)
   (sim_public_count_raw_ll (FOHashView(B)) hr) (sim_public_d_ll (FODecapView(B)) hd)).
qed.

lemma sim_public_count_cap_phase_upto
 (A<:CCAExtendedAdversary {-SimPublicBudget}) (B<:FOBackend {-A,-SimPublicBudget}) :
 islossless B.e=>islossless B.f=>islossless B.g=>islossless B.h=>islossless B.raw=>islossless B.decap=>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess) =>
 equiv[SimPublicCountedA(A,FOHashView(B),FODecapView(B)).guess ~
       SimPublicCappedA(A,FOHashView(B),FODecapView(B)).guess:
 ={arg,glob A,glob B,glob SimPublicBudget} /\ !SimPublicBudget.overflow{2} ==>
 ={SimPublicBudget.overflow} /\ (!SimPublicBudget.overflow{2} => ={res,glob A,glob B,glob SimPublicBudget})].
proof.
 move=>he hf hg hh hr hd all.
 have al:=sim_public_counted_phase_ll A B he hf hg hh hr hd all.
 have ar:=sim_public_capped_phase_ll A B he hf hg hh hr hd all.
 proc*; call(_:SimPublicBudget.overflow, ={glob B,glob SimPublicBudget}, ={SimPublicBudget.overflow}).
 + symmetry; conseq(sim_public_cap_e_projection (FOHashView(B))); smt().
 + move=> &2 h; proc*; call he; auto; smt().
 + move=> &1; proc; wp; call he; auto; smt().
 + symmetry; conseq(sim_public_cap_f_projection (FOHashView(B))); smt().
 + move=> &2 h; proc*; call hf; auto; smt().
 + move=> &1; proc; wp; call hf; auto; smt().
 + symmetry; conseq(sim_public_cap_g_projection (FOHashView(B))); smt().
 + move=> &2 h; proc*; call hg; auto; smt().
 + move=> &1; proc; wp; call hg; auto; smt().
 + conseq(sim_public_count_cap_h_step B hh); smt().
 + move=> &2 h; conseq(sim_public_count_h_ll (FOHashView(B)) hh) (sim_public_count_h_overflow_latched B); smt().
 + move=> &1; conseq(sim_public_cap_h_ll (FOHashView(B)) hh) (sim_public_cap_h_overflow_latched B); smt().
 + conseq(sim_public_count_cap_raw_step B hr); smt().
 + move=> &2 h; conseq(sim_public_count_raw_ll (FOHashView(B)) hr) (sim_public_count_raw_overflow_latched B); smt().
 + move=> &1; conseq(sim_public_cap_raw_ll (FOHashView(B)) hr) (sim_public_cap_raw_overflow_latched B); smt().
 + conseq(sim_public_count_cap_d_step B hd); smt().
 + move=> &2 h; conseq(sim_public_d_ll (FODecapView(B)) hd) (sim_public_count_d_overflow_latched B); smt().
 + move=> &1; conseq(sim_public_d_ll (FODecapView(B)) hd) (sim_public_cap_d_overflow_latched B); smt().
 auto; smt().
qed.

lemma sim_public_count_cap_phase_equiv
 (A<:CCAExtendedAdversary {-SimPublicBudget}) (B<:FOBackend {-A,-SimPublicBudget}) q0 :
 islossless B.e=>islossless B.f=>islossless B.g=>islossless B.h=>islossless B.raw=>islossless B.decap=>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess) =>
 hoare[SimPublicCountedA(A,FOHashView(B),FODecapView(B)).guess:
 sim_public_budget_initial q0 SimPublicBudget.nh SimPublicBudget.limit SimPublicBudget.overflow ==>
 SimPublicBudget.nh<=q0] =>
 equiv[SimPublicCountedA(A,FOHashView(B),FODecapView(B)).guess ~
       SimPublicCappedA(A,FOHashView(B),FODecapView(B)).guess:
 ={arg,glob A,glob B,glob SimPublicBudget} /\
 sim_public_budget_initial q0 SimPublicBudget.nh{1} SimPublicBudget.limit{1} SimPublicBudget.overflow{1} ==>
 ={res,glob A,glob B,glob SimPublicBudget}].
proof.
 move=>he hf hg hh hr hd all bounded.
 conseq(sim_public_count_cap_phase_upto A B he hf hg hh hr hd all)
  (sim_public_counted_no_overflow A B q0 bounded) _; rewrite /sim_public_budget_initial; smt().
qed.

lemma sim_public_capped_phase_plain
 (A<:CCAExtendedAdversary {-SimPublicBudget}) (B<:FOBackend {-A,-SimPublicBudget}) q0 :
 islossless B.e=>islossless B.f=>islossless B.g=>islossless B.h=>islossless B.raw=>islossless B.decap=>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess) =>
 hoare[SimPublicCountedA(A,FOHashView(B),FODecapView(B)).guess:
 sim_public_budget_initial q0 SimPublicBudget.nh SimPublicBudget.limit SimPublicBudget.overflow ==>
 SimPublicBudget.nh<=q0] =>
 equiv[SimPublicCappedA(A,FOHashView(B),FODecapView(B)).guess ~ A(FOHashView(B),FODecapView(B)).guess:
 ={arg,glob A,glob B} /\
 sim_public_budget_initial q0 SimPublicBudget.nh{1} SimPublicBudget.limit{1} SimPublicBudget.overflow{1} ==>
 ={res,glob A,glob B}].
proof.
 move=>he hf hg hh hr hd all bounded.
 transitivity SimPublicCountedA(A,FOHashView(B),FODecapView(B)).guess
  (={arg,glob A,glob B,glob SimPublicBudget} /\
   sim_public_budget_initial q0 SimPublicBudget.nh{1} SimPublicBudget.limit{1} SimPublicBudget.overflow{1} ==>
   ={res,glob A,glob B})
  (={arg,glob A,glob B} ==> ={res,glob A,glob B})=> //.
 + smt().
 + symmetry; conseq(sim_public_count_cap_phase_equiv A B q0 he hf hg hh hr hd all bounded); smt().
 exact(sim_public_counted_adversary_projection A B).
qed.

lemma sim_public_configured_phase_plain
 (A<:CCAExtendedAdversary {-SimPublicBudget}) (B<:FOBackend {-A,-SimPublicBudget}) q0 :
 0<=q0 =>
 islossless B.e=>islossless B.f=>islossless B.g=>islossless B.h=>islossless B.raw=>islossless B.decap=>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess) =>
 hoare[SimPublicCountedA(A,FOHashView(B),FODecapView(B)).guess:
 sim_public_budget_initial q0 SimPublicBudget.nh SimPublicBudget.limit SimPublicBudget.overflow ==>
 SimPublicBudget.nh<=q0] =>
 equiv[SimPublicConfiguredA(A,FOHashView(B),FODecapView(B)).guess ~ A(FOHashView(B),FODecapView(B)).guess:
 ={arg,glob A,glob B} /\ SimPublicBudget.limit{1}=q0 ==> ={res,glob A,glob B}].
proof.
 move=>hq he hf hg hh hr hd all bounded.
 proc*; inline{1} SimPublicConfiguredA(A,FOHashView(B),FODecapView(B)).guess.
 wp.
 call(sim_public_capped_phase_plain A B q0 he hf hg hh hr hd all bounded).
 inline SimPublicBudget.init; auto; rewrite /sim_public_budget_initial; smt().
qed.

(* Same private initialization as the bounded analysis phase, followed by
   the original unlimited public ports. q initializes ghost accounting only. *)
module SimPublicPlainPhase(A:CCAExtendedAdversary,B:FOBackend) = {
 proc run(q:int,pk:W8.t Array1152.t,ct:W8.t Array1152.t,key:W8.t Array32.t) : bool = {
  var answer;var fixed_context;
  fixed_context<-(FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m);
  SimBad.corr<-false;SimPublicBudget.init(q);
  answer <@ A(FOHashView(B),FODecapView(B)).guess(pk,ct,key);
  return answer;
 }
}.
