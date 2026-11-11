require import AllCore List Distr FMap.
from Jasmin require import JWord.
require import Array32 Array1152.
require import NTRUPlus768CCAGame NTRUPlus768RawXOF NTRUPlus768CCADecapOracle.
require import NTRUPlus768FOModel NTRUPlus768FOQueryBudget.

op fo_budget_initial (q nh nd lim:int) (over:bool) =
 0<=q /\ nh=0 /\ nd=0 /\ lim=q /\ !over.

module FOConfiguredA(A:CCAExtendedAdversary,H:CCAExtendedOraclePort,D:CCADecapPort) = {
 proc guess(pk:W8.t Array1152.t,ct:W8.t Array1152.t,key:W8.t Array32.t) : bool = {
  var q:int; var answer:bool;
  q<-FOBudgetState.limit;
  FOBudgetState.configure(q);
  answer <@ FOCappedA(A,H,D).guess(pk,ct,key);
  return answer;
 }
}.

lemma fo_budget_initialize q0 :0<=q0=>
 hoare[FOBudgetState.configure:q=q0 ==>
 fo_budget_initial q0 FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit FOBudgetState.overflow].
proof. move=>hq; proc; auto; rewrite /fo_budget_initial; smt(). qed.

lemma fo_count_h_overflow_latched (B<:FOBackend {-FOBudgetState}) :
 hoare[FOCountHPort(FOHashView(B)).h:FOBudgetState.overflow ==>FOBudgetState.overflow].
proof.
 proc; inline FOQueryRequest.h FOQueryRequest.d.
 call(_:true ==>true); first by trivial. auto; smt().
qed.

lemma fo_cap_h_overflow_latched (B<:FOBackend {-FOBudgetState}) :
 hoare[FOCapHPort(FOHashView(B)).h:FOBudgetState.overflow ==>FOBudgetState.overflow].
proof.
 proc; inline FOQueryRequest.h FOQueryRequest.d.
 sp; if; last by auto; smt().
 wp; call(_:true ==>true); first by trivial. auto; smt().
qed.

lemma fo_count_h_overflow_exact (B<:FOBackend {-FOBudgetState}) q0 :
 hoare[FOCountHPort(FOHashView(B)).h:FOBudgetState.limit=q0 /\ FOBudgetState.overflow=(q0<fo_query_count FOBudgetState.nH FOBudgetState.nD) ==>FOBudgetState.limit=q0 /\ FOBudgetState.overflow=(q0<fo_query_count FOBudgetState.nH FOBudgetState.nD)].
proof.
 proc; call(_:true ==>true); first by trivial.
 inline FOQueryRequest.h FOQueryRequest.d; auto; rewrite /fo_query_count; smt().
qed.

lemma fo_count_cap_h_step (B<:FOBackend {-FOBudgetState}) :
 islossless B.h =>
 equiv[FOCountHPort(FOHashView(B)).h ~ FOCapHPort(FOHashView(B)).h:
 ={arg,glob B,glob FOBudgetState} /\ !FOBudgetState.overflow{2} ==>
 ={FOBudgetState.overflow} /\ (!FOBudgetState.overflow{2} => ={res,glob B,glob FOBudgetState})].
proof.
 move=>hll; proc; inline FOQueryRequest.h FOQueryRequest.d; sp; if{2}.
 + wp; call(_: ={arg,glob B} ==> ={res,glob B}); first by proc true; auto.
   auto; smt().
 wp; call{1} hll; auto; smt().
qed.

lemma fo_count_raw_overflow_latched (B<:FOBackend {-FOBudgetState}) :
 hoare[FOCountHPort(FOHashView(B)).raw:FOBudgetState.overflow ==>FOBudgetState.overflow].
proof.
 proc; inline FOQueryRequest.h FOQueryRequest.d.
 call(_:true ==>true); first by trivial. auto; smt().
qed.

lemma fo_cap_raw_overflow_latched (B<:FOBackend {-FOBudgetState}) :
 hoare[FOCapHPort(FOHashView(B)).raw:FOBudgetState.overflow ==>FOBudgetState.overflow].
proof.
 proc; inline FOQueryRequest.h FOQueryRequest.d.
 sp; if; last by auto; smt().
 wp; call(_:true ==>true); first by trivial. auto; smt().
qed.

lemma fo_count_raw_overflow_exact (B<:FOBackend {-FOBudgetState}) q0 :
 hoare[FOCountHPort(FOHashView(B)).raw:FOBudgetState.limit=q0 /\ FOBudgetState.overflow=(q0<fo_query_count FOBudgetState.nH FOBudgetState.nD) ==>FOBudgetState.limit=q0 /\ FOBudgetState.overflow=(q0<fo_query_count FOBudgetState.nH FOBudgetState.nD)].
proof.
 proc; call(_:true ==>true); first by trivial.
 inline FOQueryRequest.h FOQueryRequest.d; auto; rewrite /fo_query_count; smt().
qed.

lemma fo_count_cap_raw_step (B<:FOBackend {-FOBudgetState}) :
 islossless B.raw =>
 equiv[FOCountHPort(FOHashView(B)).raw ~ FOCapHPort(FOHashView(B)).raw:
 ={arg,glob B,glob FOBudgetState} /\ !FOBudgetState.overflow{2} ==>
 ={FOBudgetState.overflow} /\ (!FOBudgetState.overflow{2} => ={res,glob B,glob FOBudgetState})].
proof.
 move=>hll; proc; inline FOQueryRequest.h FOQueryRequest.d; sp; if{2}.
 + wp; call(_: ={arg,glob B} ==> ={res,glob B}); first by proc true; auto.
   auto; smt().
 wp; call{1} hll; auto; smt().
qed.

lemma fo_count_d_overflow_latched (B<:FOBackend {-FOBudgetState}) :
 hoare[FOCountDPort(FODecapView(B)).decap:FOBudgetState.overflow ==>FOBudgetState.overflow].
proof.
 proc; inline FOQueryRequest.h FOQueryRequest.d.
 call(_:true ==>true); first by trivial. auto; smt().
qed.

lemma fo_cap_d_overflow_latched (B<:FOBackend {-FOBudgetState}) :
 hoare[FOCapDPort(FODecapView(B)).decap:FOBudgetState.overflow ==>FOBudgetState.overflow].
proof.
 proc; inline FOQueryRequest.h FOQueryRequest.d.
 sp; if; last by auto; smt().
 wp; call(_:true ==>true); first by trivial. auto; smt().
qed.

lemma fo_count_d_overflow_exact (B<:FOBackend {-FOBudgetState}) q0 :
 hoare[FOCountDPort(FODecapView(B)).decap:FOBudgetState.limit=q0 /\ FOBudgetState.overflow=(q0<fo_query_count FOBudgetState.nH FOBudgetState.nD) ==>FOBudgetState.limit=q0 /\ FOBudgetState.overflow=(q0<fo_query_count FOBudgetState.nH FOBudgetState.nD)].
proof.
 proc; call(_:true ==>true); first by trivial.
 inline FOQueryRequest.h FOQueryRequest.d; auto; rewrite /fo_query_count; smt().
qed.

lemma fo_count_cap_d_step (B<:FOBackend {-FOBudgetState}) :
 islossless B.decap =>
 equiv[FOCountDPort(FODecapView(B)).decap ~ FOCapDPort(FODecapView(B)).decap:
 ={arg,glob B,glob FOBudgetState} /\ !FOBudgetState.overflow{2} ==>
 ={FOBudgetState.overflow} /\ (!FOBudgetState.overflow{2} => ={res,glob B,glob FOBudgetState})].
proof.
 move=>hll; proc; inline FOQueryRequest.h FOQueryRequest.d; sp; if{2}.
 + wp; call(_: ={arg,glob B} ==> ={res,glob B}); first by proc true; auto.
   auto; smt().
 wp; call{1} hll; auto; smt().
qed.

lemma fo_counted_overflow_exact
 (A<:CCAExtendedAdversary {-FOBudgetState}) (B<:FOBackend {-A,-FOBudgetState}) q0 :
 hoare[FOCountedA(A,FOHashView(B),FODecapView(B)).guess:
 FOBudgetState.limit=q0 /\ FOBudgetState.overflow=(q0<fo_query_count FOBudgetState.nH FOBudgetState.nD) ==>
 FOBudgetState.limit=q0 /\ FOBudgetState.overflow=(q0<fo_query_count FOBudgetState.nH FOBudgetState.nD)].
proof.
 proc(FOBudgetState.limit=q0 /\ FOBudgetState.overflow=(q0<fo_query_count FOBudgetState.nH FOBudgetState.nD)); 1,2:by auto.
 + proc*; call(_:true ==>true); first by trivial. auto.
 + proc*; call(_:true ==>true); first by trivial. auto.
 + proc*; call(_:true ==>true); first by trivial. auto.
 + exact(fo_count_h_overflow_exact B q0).
 + exact(fo_count_raw_overflow_exact B q0).
 exact(fo_count_d_overflow_exact B q0).
qed.

lemma fo_counted_adversary_projection
 (A<:CCAExtendedAdversary {-FOBudgetState}) (B<:FOBackend {-A,-FOBudgetState}) :
 equiv[FOCountedA(A,FOHashView(B),FODecapView(B)).guess ~ A(FOHashView(B),FODecapView(B)).guess:
 ={arg,glob A,glob B} ==> ={res,glob A,glob B}].
proof.
 proc(={glob B}); 1,2:by auto.
 + proc true; auto.
 + proc true; auto.
 + proc true; auto.
 + conseq(fo_count_h_projection (FOHashView(B))); smt().
 + conseq(fo_count_raw_projection (FOHashView(B))); smt().
 conseq(fo_count_d_projection (FODecapView(B))); smt().
qed.

lemma fo_counted_no_overflow
 (A<:CCAExtendedAdversary {-FOBudgetState}) (B<:FOBackend {-A,-FOBudgetState}) q0 :
 hoare[FOCountedA(A,FOHashView(B),FODecapView(B)).guess:
 fo_budget_initial q0 FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit FOBudgetState.overflow ==>
 fo_query_count FOBudgetState.nH FOBudgetState.nD<=q0] =>
 hoare[FOCountedA(A,FOHashView(B),FODecapView(B)).guess:
 fo_budget_initial q0 FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit FOBudgetState.overflow ==>
 !FOBudgetState.overflow].
proof.
 move=>hb; conseq hb (fo_counted_overflow_exact A B q0); rewrite /fo_budget_initial /fo_query_count; smt().
qed.

lemma fo_backend_e_same (B<:FOBackend {-FOBudgetState}) :
 equiv[B.e ~ B.e: ={arg,glob B} ==> ={res,glob B}].
proof. proc true; auto. qed.

lemma fo_backend_f_same (B<:FOBackend {-FOBudgetState}) :
 equiv[B.f ~ B.f: ={arg,glob B} ==> ={res,glob B}].
proof. proc true; auto. qed.

lemma fo_backend_g_same (B<:FOBackend {-FOBudgetState}) :
 equiv[B.g ~ B.g: ={arg,glob B} ==> ={res,glob B}].
proof. proc true; auto. qed.

lemma fo_counted_phase_ll
 (A<:CCAExtendedAdversary {-FOBudgetState}) (B<:FOBackend {-A,-FOBudgetState}) :
 islossless B.e=>islossless B.f=>islossless B.g=>islossless B.h=>islossless B.raw=>islossless B.decap=>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess) =>
 islossless FOCountedA(A,FOHashView(B),FODecapView(B)).guess.
proof.
 move=>he hf hg hh hr hd all.
 exact(all (FOCountHPort(FOHashView(B))) (FOCountDPort(FODecapView(B)))
   he hf hg (fo_count_h_ll (FOHashView(B)) hh)
   (fo_count_raw_ll (FOHashView(B)) hr) (fo_count_d_ll (FODecapView(B)) hd)).
qed.

lemma fo_capped_phase_ll
 (A<:CCAExtendedAdversary {-FOBudgetState}) (B<:FOBackend {-A,-FOBudgetState}) :
 islossless B.e=>islossless B.f=>islossless B.g=>islossless B.h=>islossless B.raw=>islossless B.decap=>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess) =>
 islossless FOCappedA(A,FOHashView(B),FODecapView(B)).guess.
proof.
 move=>he hf hg hh hr hd all.
 exact(all (FOCapHPort(FOHashView(B))) (FOCapDPort(FODecapView(B)))
   (fo_cap_e_ll (FOHashView(B)) he) (fo_cap_f_ll (FOHashView(B)) hf)
   (fo_cap_g_ll (FOHashView(B)) hg) (fo_cap_h_ll (FOHashView(B)) hh)
   (fo_cap_raw_ll (FOHashView(B)) hr) (fo_cap_d_ll (FODecapView(B)) hd)).
qed.

lemma fo_count_cap_phase_upto
 (A<:CCAExtendedAdversary {-FOBudgetState}) (B<:FOBackend {-A,-FOBudgetState}) :
 islossless B.e=>islossless B.f=>islossless B.g=>islossless B.h=>islossless B.raw=>islossless B.decap=>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess) =>
 equiv[FOCountedA(A,FOHashView(B),FODecapView(B)).guess ~
       FOCappedA(A,FOHashView(B),FODecapView(B)).guess:
 ={arg,glob A,glob B,glob FOBudgetState} /\ !FOBudgetState.overflow{2} ==>
 ={FOBudgetState.overflow} /\ (!FOBudgetState.overflow{2} => ={res,glob A,glob B,glob FOBudgetState})].
proof.
 move=>he hf hg hh hr hd all.
 have al:=fo_counted_phase_ll A B he hf hg hh hr hd all.
 have ar:=fo_capped_phase_ll A B he hf hg hh hr hd all.
 proc*; call(_:FOBudgetState.overflow, ={glob B,glob FOBudgetState}, ={FOBudgetState.overflow}).
 + symmetry; conseq(fo_cap_e_projection (FOHashView(B))); smt().
 + move=> &2 h; proc*; call he; auto; smt().
 + move=> &1; proc; wp; call he; auto; smt().
 + symmetry; conseq(fo_cap_f_projection (FOHashView(B))); smt().
 + move=> &2 h; proc*; call hf; auto; smt().
 + move=> &1; proc; wp; call hf; auto; smt().
 + symmetry; conseq(fo_cap_g_projection (FOHashView(B))); smt().
 + move=> &2 h; proc*; call hg; auto; smt().
 + move=> &1; proc; wp; call hg; auto; smt().
 + conseq(fo_count_cap_h_step B hh); smt().
 + move=> &2 h; conseq(fo_count_h_ll (FOHashView(B)) hh) (fo_count_h_overflow_latched B); smt().
 + move=> &1; conseq(fo_cap_h_ll (FOHashView(B)) hh) (fo_cap_h_overflow_latched B); smt().
 + conseq(fo_count_cap_raw_step B hr); smt().
 + move=> &2 h; conseq(fo_count_raw_ll (FOHashView(B)) hr) (fo_count_raw_overflow_latched B); smt().
 + move=> &1; conseq(fo_cap_raw_ll (FOHashView(B)) hr) (fo_cap_raw_overflow_latched B); smt().
 + conseq(fo_count_cap_d_step B hd); smt().
 + move=> &2 h; conseq(fo_count_d_ll (FODecapView(B)) hd) (fo_count_d_overflow_latched B); smt().
 + move=> &1; conseq(fo_cap_d_ll (FODecapView(B)) hd) (fo_cap_d_overflow_latched B); smt().
 auto; smt().
qed.

lemma fo_count_cap_phase_equiv
 (A<:CCAExtendedAdversary {-FOBudgetState}) (B<:FOBackend {-A,-FOBudgetState}) q0 :
 islossless B.e=>islossless B.f=>islossless B.g=>islossless B.h=>islossless B.raw=>islossless B.decap=>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess) =>
 hoare[FOCountedA(A,FOHashView(B),FODecapView(B)).guess:
 fo_budget_initial q0 FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit FOBudgetState.overflow ==>
 fo_query_count FOBudgetState.nH FOBudgetState.nD<=q0] =>
 equiv[FOCountedA(A,FOHashView(B),FODecapView(B)).guess ~
       FOCappedA(A,FOHashView(B),FODecapView(B)).guess:
 ={arg,glob A,glob B,glob FOBudgetState} /\
 fo_budget_initial q0 FOBudgetState.nH{1} FOBudgetState.nD{1} FOBudgetState.limit{1} FOBudgetState.overflow{1} ==>
 ={res,glob A,glob B,glob FOBudgetState}].
proof.
 move=>he hf hg hh hr hd all bounded.
 conseq(fo_count_cap_phase_upto A B he hf hg hh hr hd all)
  (fo_counted_no_overflow A B q0 bounded) _; rewrite /fo_budget_initial; smt().
qed.

lemma fo_capped_phase_plain
 (A<:CCAExtendedAdversary {-FOBudgetState}) (B<:FOBackend {-A,-FOBudgetState}) q0 :
 islossless B.e=>islossless B.f=>islossless B.g=>islossless B.h=>islossless B.raw=>islossless B.decap=>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess) =>
 hoare[FOCountedA(A,FOHashView(B),FODecapView(B)).guess:
 fo_budget_initial q0 FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit FOBudgetState.overflow ==>
 fo_query_count FOBudgetState.nH FOBudgetState.nD<=q0] =>
 equiv[FOCappedA(A,FOHashView(B),FODecapView(B)).guess ~ A(FOHashView(B),FODecapView(B)).guess:
 ={arg,glob A,glob B} /\
 fo_budget_initial q0 FOBudgetState.nH{1} FOBudgetState.nD{1} FOBudgetState.limit{1} FOBudgetState.overflow{1} ==>
 ={res,glob A,glob B}].
proof.
 move=>he hf hg hh hr hd all bounded.
 transitivity FOCountedA(A,FOHashView(B),FODecapView(B)).guess
  (={arg,glob A,glob B,glob FOBudgetState} /\
   fo_budget_initial q0 FOBudgetState.nH{1} FOBudgetState.nD{1} FOBudgetState.limit{1} FOBudgetState.overflow{1} ==>
   ={res,glob A,glob B})
  (={arg,glob A,glob B} ==> ={res,glob A,glob B})=> //.
 + smt().
 + symmetry; conseq(fo_count_cap_phase_equiv A B q0 he hf hg hh hr hd all bounded); smt().
 exact(fo_counted_adversary_projection A B).
qed.

lemma fo_configured_phase_plain
 (A<:CCAExtendedAdversary {-FOBudgetState}) (B<:FOBackend {-A,-FOBudgetState}) q0 :
 0<=q0 =>
 islossless B.e=>islossless B.f=>islossless B.g=>islossless B.h=>islossless B.raw=>islossless B.decap=>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess) =>
 hoare[FOCountedA(A,FOHashView(B),FODecapView(B)).guess:
 fo_budget_initial q0 FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit FOBudgetState.overflow ==>
 fo_query_count FOBudgetState.nH FOBudgetState.nD<=q0] =>
 equiv[FOConfiguredA(A,FOHashView(B),FODecapView(B)).guess ~ A(FOHashView(B),FODecapView(B)).guess:
 ={arg,glob A,glob B} /\ FOBudgetState.limit{1}=q0 ==> ={res,glob A,glob B}].
proof.
 move=>hq he hf hg hh hr hd all bounded.
 proc*; inline{1} FOConfiguredA(A,FOHashView(B),FODecapView(B)).guess.
 wp.
 call(fo_capped_phase_plain A B q0 he hf hg hh hr hd all bounded).
 inline FOBudgetState.configure; auto; rewrite /fo_budget_initial; smt().
qed.
