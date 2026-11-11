require import AllCore List Distr StdOrder StdBigop.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152.
require import NTRUPlus768FOModel NTRUPlus768FOError NTRUPlus768FOQueryBudget.
require import NTRUPlus768CCAGame.
require import NTRUPlus768RawXOF NTRUPlus768CCADecapOracle NTRUPlus768CCAStatusAdapter.
import RealOrder StdBigop.Bigreal.BRA.

lemma fo_fel_cost_sum q eps : 0<=q =>
 bigi predT (fun (_:int)=>eps) 0 q=q%r*eps.
proof.
 move=>hq; have hmax:max 0 q=q by smt().
 rewrite sumr_const RField.intmulr count_predT size_range subz0 hmax; ring.
qed.

module FOBadPhase(A:CCAExtendedAdversary,B:FOBackend) = {
 proc run(q:int,pk:W8.t Array1152.t,ct:W8.t Array1152.t,key:W8.t Array32.t) : bool = {
  var answer:bool; var fixed_context;
  (* Read-only snapshot anchors the generic invariant to the ambient state. *)
  fixed_context <- (FOContext.w,FOContext.g);
  FOBadState.init(); FOBudgetState.configure(q);
  answer <@ FOCappedA(A,FOHashView(B),FODecapView(B)).guess(pk,ct,key);
  return answer;
 }
}.

(* These hypotheses are per concrete backend, including its shared H/D
   state. Native and reencrypting Decaps must each discharge them. A budget
   cap alone is not a losslessness assertion about the adversary. *)
lemma fo_bounded_phase_bad
 (A<:CCAExtendedAdversary {-FOContext,-FOBadState,-FOBudgetState})
 (B<:FOBackend {-A,-FOBudgetState})
 w0 g0 q0 pk0 ct0 key0 &m :
 0<=q0 =>FOContext.w{m}=w0 =>FOContext.g{m}=g0 =>
 (forall b,hoare[B.e:FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b ==>
   FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b]) =>
 (forall b,hoare[B.f:FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b ==>
   FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b]) =>
 (forall b,hoare[B.g:FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b ==>
   FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b]) =>
 (forall b,hoare[B.h:FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b ==>
   FOContext.w=w0 /\ FOContext.g=g0 /\ (b=>FOBadState.bad)]) =>
 (forall b,hoare[B.raw:FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b ==>
   FOContext.w=w0 /\ FOContext.g=g0 /\ (b=>FOBadState.bad)]) =>
 (forall b,hoare[B.raw:FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b /\ !fo_raw_h input outlen ==>
   FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b]) =>
 (forall b,hoare[B.decap:FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b ==>
   FOContext.w=w0 /\ FOContext.g=g0 /\ (b=>FOBadState.bad)]) =>
 (phoare[B.h:FOContext.w=w0 /\ FOContext.g=g0 /\ !FOBadState.bad ==>FOBadState.bad]
   <=(fo_error w0 g0)) =>
 (phoare[B.raw:FOContext.w=w0 /\ FOContext.g=g0 /\ !FOBadState.bad /\ fo_raw_h input outlen ==>FOBadState.bad]
   <=(fo_error w0 g0)) =>
 (phoare[B.decap:FOContext.w=w0 /\ FOContext.g=g0 /\ !FOBadState.bad ==>FOBadState.bad]
   <=(fo_error w0 g0)) =>
 Pr[FOBadPhase(A,B).run(q0,pk0,ct0,key0) @ &m:FOBadState.bad] <=q0%r*fo_error w0 g0.
proof.
 move=>hq hw hg he hf hgg hh hr hr0 hd ph pr pd.
 (* Split context preservation from disjoint budget arithmetic. This keeps
    concrete backends free to access the monitored context and bad flag. *)
 have hdctx:forall b,hoare[B.decap:FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b ==>
   FOContext.w=w0 /\ FOContext.g=g0].
 + move=>b; conseq [-frame](hd b); smt().
 have hhctx:forall b,hoare[B.h:FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b ==>
   FOContext.w=w0 /\ FOContext.g=g0].
 + move=>b; conseq [-frame](hh b); smt().
 have hrctx:forall b,hoare[B.raw:FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b ==>
   FOContext.w=w0 /\ FOContext.g=g0].
 + move=>b; conseq [-frame](hr b); smt().
 fel 3 (fo_query_charge FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit)
  (fun _,fo_error w0 g0) q0 FOBadState.bad
  [FOCapHPort(FOHashView(B)).e : false; FOCapHPort(FOHashView(B)).f : false; FOCapHPort(FOHashView(B)).g : false;
   FOCapHPort(FOHashView(B)).h : (FOBudgetState.nH+FOBudgetState.nD<FOBudgetState.limit);
   FOCapHPort(FOHashView(B)).raw : (fo_raw_h input outlen /\ FOBudgetState.nH+FOBudgetState.nD<FOBudgetState.limit);
   FOCapDPort(FODecapView(B)).decap : (FOBudgetState.nH+FOBudgetState.nD<FOBudgetState.limit)]
  (FOContext.w=w0 /\ FOContext.g=g0 /\ FOBudgetState.limit=q0 /\
   fo_budget_range FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit) => //.
 + by rewrite(fo_fel_cost_sum q0 (fo_error w0 g0) hq).
 + rewrite /fo_query_charge; smt().
 + inline FOBadState.init FOBudgetState.configure; auto=> />;
   rewrite /fo_query_charge; smt().
 + proc; wp; rcondt 3; first by inline FOQueryRequest.d; auto; smt().
   call pd; inline FOQueryRequest.d; auto; smt().
 + move=>c.
   conseq [-frame] (_: _ ==> c<fo_query_charge FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit /\
     FOBudgetState.limit=q0 /\ fo_budget_range FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit)
    (_: _ ==> FOContext.w=w0 /\ FOContext.g=g0); 1,2:smt().
   + proc; exists* FOBadState.bad; elim*=>b0; wp; rcondt 3; first by inline FOQueryRequest.d; auto; smt().
     call(hdctx b0); inline FOQueryRequest.d; auto; smt().
   proc; wp; rcondt 3; first by inline FOQueryRequest.d; auto; smt().
   call(_:true ==>true); first by trivial.
   inline FOQueryRequest.d; auto=> />; rewrite /fo_query_charge; smt().
 + move=>b c; proc; wp; rcondf 3; first by inline FOQueryRequest.d; auto; smt().
   inline FOQueryRequest.d; auto=> />; rewrite /fo_query_charge; smt().
 + move=>b c.
   conseq [-frame] (_: _ ==> c<=fo_query_charge FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit /\
     FOBudgetState.limit=q0 /\ fo_budget_range FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit)
    (_: _ ==> FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b); 1,2:smt().
   + proc; wp; call(he b); auto; smt().
   proc; wp; call(_:true ==>true); first by trivial. auto; smt().
 + move=>b c.
   conseq [-frame] (_: _ ==> c<=fo_query_charge FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit /\
     FOBudgetState.limit=q0 /\ fo_budget_range FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit)
    (_: _ ==> FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b); 1,2:smt().
   + proc; wp; call(hf b); auto; smt().
   proc; wp; call(_:true ==>true); first by trivial. auto; smt().
 + move=>b c.
   conseq [-frame] (_: _ ==> c<=fo_query_charge FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit /\
     FOBudgetState.limit=q0 /\ fo_budget_range FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit)
    (_: _ ==> FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b); 1,2:smt().
   + proc; wp; call(hgg b); auto; smt().
   proc; wp; call(_:true ==>true); first by trivial. auto; smt().
 + proc; wp; rcondt 3; first by inline FOQueryRequest.h; auto; smt().
   call ph; inline FOQueryRequest.h; auto; smt().
 + move=>c.
   conseq [-frame] (_: _ ==> c<fo_query_charge FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit /\
     FOBudgetState.limit=q0 /\ fo_budget_range FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit)
    (_: _ ==> FOContext.w=w0 /\ FOContext.g=g0); 1,2:smt().
   + proc; exists* FOBadState.bad; elim*=>b0; wp; rcondt 3; first by inline FOQueryRequest.h; auto; smt().
     call(hhctx b0); inline FOQueryRequest.h; auto; smt().
   proc; wp; rcondt 3; first by inline FOQueryRequest.h; auto; smt().
   call(_:true ==>true); first by trivial.
   inline FOQueryRequest.h; auto=> />; rewrite /fo_query_charge; smt().
 + move=>b c; proc; wp; rcondf 3; first by inline FOQueryRequest.h; auto; smt().
   inline FOQueryRequest.h; auto=> />; rewrite /fo_query_charge; smt().
 + proc; wp; rcondt 2; first by auto; smt().
   rcondt 4; first by inline FOQueryRequest.h; auto; smt().
   call pr; inline FOQueryRequest.h; auto; smt().
 + move=>c.
   conseq [-frame] (_: _ ==> c<fo_query_charge FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit /\
     FOBudgetState.limit=q0 /\ fo_budget_range FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit)
    (_: _ ==> FOContext.w=w0 /\ FOContext.g=g0); 1,2:smt().
   + proc; exists* FOBadState.bad; elim*=>b0; wp; rcondt 2; first by auto; smt().
     rcondt 4; first by inline FOQueryRequest.h; auto; smt().
     call(hrctx b0); inline FOQueryRequest.h; auto; smt().
   proc; wp; rcondt 2; first by auto; smt().
   rcondt 4; first by inline FOQueryRequest.h; auto; smt().
   call(_:true ==>true); first by trivial.
   inline FOQueryRequest.h; auto=> />; rewrite /fo_query_charge; smt().
 move=>b c.
 conseq [-frame] (_: _ ==> c<=fo_query_charge FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit /\
   FOBudgetState.limit=q0 /\ fo_budget_range FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit)
  (_: _ ==> FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b); 1,2:smt().
 + proc; wp; sp 1; if.
   + rcondf 3; first by inline FOQueryRequest.h; auto; smt().
     inline FOQueryRequest.h; auto; smt().
   rcondt 2; first by auto. call(hr0 b); auto; smt().
 proc; wp; sp 1; if.
 + rcondf 3; first by inline FOQueryRequest.h; auto; smt().
   inline FOQueryRequest.h; auto=> />; rewrite /fo_query_charge; smt().
 rcondt 2; first by auto.
 call(_:true ==>true); first by trivial. auto; smt().
qed.
