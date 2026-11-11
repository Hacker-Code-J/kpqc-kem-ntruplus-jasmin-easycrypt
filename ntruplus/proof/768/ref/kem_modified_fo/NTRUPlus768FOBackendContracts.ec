require import AllCore List Distr FMap StdOrder.
from Jasmin require import JWord.
require import Array32 Array96 Array1152.
require import NTRUPlus768FOModel NTRUPlus768FOError NTRUPlus768FOHMonitor.
require import NTRUPlus768FOProcedures NTRUPlus768FOKEMGame NTRUPlus768FOQueryBudget.
require import NTRUPlus768ROMOracles NTRUPlus768RawXOF NTRUPlus768CCAGame.
require import NTRUPlus768CCADecapOracle NTRUPlus768RawXOFStreams.
require import NTRUPlus768DecapCompleteHash NTRUPlus768DecapCompleteTailProof NTRUPlus768DecapCompleteProof.
require import NTRUPlus768DecapMessageProof NTRUPlus768DecapR2CompCaller.
require import NTRUPlus768DecapHashHPrepareProof NTRUPlus768DecapFinishCorrectness.
require import NTRUPlus768PolyCBD1CheckedProof NTRUPlus768NTTProof NTRUPlus768PolyToBytesProof.
require import NTRUPlus768DecapClearProof.
import RealOrder.

module FONativeBackend = FOBackendPair(FOSharedOracles,FONativeDecap(SHAKEGROM,FOSHAKEH)).
module FOFullBackend = FOBackendPair(FOSharedOracles,FOReencryptDecap(SHAKEGROM,FOSHAKEH)).

lemma fo_shared_e_frame w0 g0 b0 : hoare[FOSharedOracles.e:
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b0 ==>
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b0].
proof. proc*; call(_:true ==>true); first by trivial. auto. qed.
lemma fo_shared_f_frame w0 g0 b0 : hoare[FOSharedOracles.f:
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b0 ==>
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b0].
proof. proc*; call(_:true ==>true); first by trivial. auto. qed.
lemma fo_shared_g_frame w0 g0 b0 : hoare[FOSharedOracles.g:
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b0 ==>
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b0].
proof. proc*; call(_:true ==>true); first by trivial. auto. qed.

lemma fo_shakeh_frame w0 g0 b0 : hoare[FOSHAKEH.shake:
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b0 ==>
 FOContext.w=w0 /\ FOContext.g=g0 /\ (b0=>FOBadState.bad)].
proof.
 proc; call(_:FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b0 ==>
   FOContext.w=w0 /\ FOContext.g=g0 /\ (b0=>FOBadState.bad)).
 + proc; seq 2:(FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b0).
   - call(_:true ==>true); first by trivial. auto.
   if; auto; smt().
 auto.
qed.

(* All arithmetic and clearing calls remain in the actual procedures.
   Only the one H call can change the hidden bad flag. No key validity or
   successful decoding assumption is needed for these callback bounds. *)
lemma fo_native_tail_frame w0 g0 b0 : hoare[CompleteTail(FOSHAKEH).run:
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b0 ==>
 FOContext.w=w0 /\ FOContext.g=g0 /\ (b0=>FOBadState.bad)].
proof.
 proc; do 4!(call(_:true ==>true); first by trivial).
 call(fo_shakeh_frame w0 g0 b0).
 call(_:true ==>true); first by trivial. auto.
qed.
lemma fo_native_core_frame w0 g0 b0 : hoare[CompleteCore(SHAKEGROM,FOSHAKEH).run:
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b0 ==>
 FOContext.w=w0 /\ FOContext.g=g0 /\ (b0=>FOBadState.bad)].
proof.
 proc; seq 1:(FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b0).
 + call(_:true ==>true); first by trivial. auto.
 if; last by auto.
 call(fo_native_tail_frame w0 g0 b0).
 call(_:true ==>true); first by trivial. auto.
qed.
lemma fo_native_decaps_frame w0 g0 b0 : hoare[CompleteDecaps(SHAKEGROM,FOSHAKEH).run:
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b0 ==>
 FOContext.w=w0 /\ FOContext.g=g0 /\ (b0=>FOBadState.bad)].
proof.
 proc; call(_:true ==>true); first by trivial.
 call(fo_native_core_frame w0 g0 b0); auto.
qed.
lemma fo_native_decap_frame w0 g0 b0 : hoare[FONativeBackend.decap:
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b0 ==>
 FOContext.w=w0 /\ FOContext.g=g0 /\ (b0=>FOBadState.bad)].
proof.
 proc; sp; if; first by auto.
 wp; call(fo_native_decaps_frame w0 g0 b0); auto.
qed.

lemma fo_full_tail_frame w0 g0 b0 : hoare[FOTail(SHAKEGROM,FOSHAKEH).run:
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b0 ==>
 FOContext.w=w0 /\ FOContext.g=g0 /\ (b0=>FOBadState.bad)].
proof.
 proc; call(_:true ==>true); first by trivial.
 call(fo_shakeh_frame w0 g0 b0).
 call(_:true ==>true); first by trivial. auto.
qed.
lemma fo_full_core_frame w0 g0 b0 : hoare[FOCore(SHAKEGROM,FOSHAKEH).run:
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b0 ==>
 FOContext.w=w0 /\ FOContext.g=g0 /\ (b0=>FOBadState.bad)].
proof.
 proc; seq 1:(FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b0).
 + call(_:true ==>true); first by trivial. auto.
 if; last by auto.
 call(fo_full_tail_frame w0 g0 b0).
 call(_:true ==>true); first by trivial. auto.
qed.
lemma fo_full_decaps_frame w0 g0 b0 : hoare[FODecaps(SHAKEGROM,FOSHAKEH).run:
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b0 ==>
 FOContext.w=w0 /\ FOContext.g=g0 /\ (b0=>FOBadState.bad)].
proof.
 proc; call(_:true ==>true); first by trivial.
 call(fo_full_core_frame w0 g0 b0); auto.
qed.
lemma fo_full_decap_frame w0 g0 b0 : hoare[FOFullBackend.decap:
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b0 ==>
 FOContext.w=w0 /\ FOContext.g=g0 /\ (b0=>FOBadState.bad)].
proof.
 proc; sp; if; first by auto.
 wp; call(fo_full_decaps_frame w0 g0 b0); auto.
qed.

lemma fo_native_tail_bad_bound w0 g0 : phoare[CompleteTail(FOSHAKEH).run:
 FOContext.w=w0 /\ FOContext.g=g0 /\ !FOBadState.bad ==>FOBadState.bad] <=(fo_error w0 g0).
proof.
 proc; seq 2:FOBadState.bad (fo_error w0 g0) 1%r 1%r 0%r true=> //.
 + call(fo_shakeh_bad_bound w0 g0).
   call(_:true ==>true); first by trivial. auto.
 hoare; do 4!(call(_:true ==>true); first by trivial). auto.
qed.
lemma fo_native_core_bad_bound w0 g0 : phoare[CompleteCore(SHAKEGROM,FOSHAKEH).run:
 FOContext.w=w0 /\ FOContext.g=g0 /\ !FOBadState.bad ==>FOBadState.bad] <=(fo_error w0 g0).
proof.
 have [hn _]:=fo_error_range w0 g0.
 proc; seq 1:(FOContext.w=w0 /\ FOContext.g=g0 /\ !FOBadState.bad)
   1%r (fo_error w0 g0) 0%r 1%r true=> //.
 + if; last by hoare; auto; smt().
   call(fo_native_tail_bad_bound w0 g0).
   call(_:true ==>true); first by trivial. auto.
 hoare; call(_:true ==>true); first by trivial. auto.
qed.
lemma fo_native_decaps_bad_bound w0 g0 : phoare[CompleteDecaps(SHAKEGROM,FOSHAKEH).run:
 FOContext.w=w0 /\ FOContext.g=g0 /\ !FOBadState.bad ==>FOBadState.bad] <=(fo_error w0 g0).
proof.
 proc; seq 1:FOBadState.bad (fo_error w0 g0) 1%r 1%r 0%r true=> //.
 + call(fo_native_core_bad_bound w0 g0); auto.
 hoare; call(_:true ==>true); first by trivial. auto.
qed.
lemma fo_native_decap_bad_bound w0 g0 : phoare[FONativeBackend.decap:
 FOContext.w=w0 /\ FOContext.g=g0 /\ !FOBadState.bad ==>FOBadState.bad] <=(fo_error w0 g0).
proof.
 have [hn _]:=fo_error_range w0 g0.
 proc; sp; if; first by hoare; auto; smt().
 wp; call(fo_native_decaps_bad_bound w0 g0); auto.
qed.

lemma fo_full_tail_bad_bound w0 g0 : phoare[FOTail(SHAKEGROM,FOSHAKEH).run:
 FOContext.w=w0 /\ FOContext.g=g0 /\ !FOBadState.bad ==>FOBadState.bad] <=(fo_error w0 g0).
proof.
 proc; seq 2:FOBadState.bad (fo_error w0 g0) 1%r 1%r 0%r true=> //.
 + call(fo_shakeh_bad_bound w0 g0).
   call(_:true ==>true); first by trivial. auto.
 hoare; call(_:true ==>true); first by trivial. auto.
qed.
lemma fo_full_core_bad_bound w0 g0 : phoare[FOCore(SHAKEGROM,FOSHAKEH).run:
 FOContext.w=w0 /\ FOContext.g=g0 /\ !FOBadState.bad ==>FOBadState.bad] <=(fo_error w0 g0).
proof.
 have [hn _]:=fo_error_range w0 g0.
 proc; seq 1:(FOContext.w=w0 /\ FOContext.g=g0 /\ !FOBadState.bad)
   1%r (fo_error w0 g0) 0%r 1%r true=> //.
 + if; last by hoare; auto; smt().
   call(fo_full_tail_bad_bound w0 g0).
   call(_:true ==>true); first by trivial. auto.
 hoare; call(_:true ==>true); first by trivial. auto.
qed.
lemma fo_full_decaps_bad_bound w0 g0 : phoare[FODecaps(SHAKEGROM,FOSHAKEH).run:
 FOContext.w=w0 /\ FOContext.g=g0 /\ !FOBadState.bad ==>FOBadState.bad] <=(fo_error w0 g0).
proof.
 proc; seq 1:FOBadState.bad (fo_error w0 g0) 1%r 1%r 0%r true=> //.
 + call(fo_full_core_bad_bound w0 g0); auto.
 hoare; call(_:true ==>true); first by trivial. auto.
qed.
lemma fo_full_decap_bad_bound w0 g0 : phoare[FOFullBackend.decap:
 FOContext.w=w0 /\ FOContext.g=g0 /\ !FOBadState.bad ==>FOBadState.bad] <=(fo_error w0 g0).
proof.
 have [hn _]:=fo_error_range w0 g0.
 proc; sp; if; first by hoare; auto; smt().
 wp; call(fo_full_decaps_bad_bound w0 g0); auto.
qed.

