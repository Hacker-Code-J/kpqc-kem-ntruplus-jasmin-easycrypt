require import AllCore List Distr FMap.
from Jasmin require import JWord.
require import Array32 Array192 Array768 Array14466.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteAttempt.
require import NTRUPlus768KeygenCompleteRetry NTRUPlus768KeygenCompleteProof.
require import NTRUPlus768KeygenCompleteFinish NTRUPlus768KeygenClearProof.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions.
require import NTRUPlus768StoppedKeygenModel NTRUPlus768StoppedKeygenPrefix.
require import NTRUPlus768FreshRetryLaw NTRUPlus768CCASetupState.
require import NTRUPlus768ErasureModel.

lemma erasure_programmed_expand_projection :
 equiv[LoggedProgrammedExpand.shake ~ ProgrammedFreshExpand.shake :
   ={seed,glob ROE} ==> ={res,glob ROE}].
proof. proc; inline ProgrammedFreshExpand.shake; auto. qed.
lemma erasure_erased_expand_projection :
 equiv[LoggedErasedExpand.shake ~ FreshExpand.shake : true ==> ={res}].
proof. proc; inline FreshExpand.shake; auto. qed.
lemma erasure_expand_coupling :
 equiv[LoggedProgrammedExpand.shake ~ LoggedErasedExpand.shake :
   ={seed,ErasureSeedLog.used} /\
   erasure_tables_agree ErasureSeedLog.used{1} ROE.m{1} ROE.m{2} ==>
   ={res,ErasureSeedLog.used} /\
   erasure_tables_agree ErasureSeedLog.used{1} ROE.m{1} ROE.m{2}].
proof.
 proc; inline ProgrammedFreshExpand.shake FreshExpand.shake.
 auto=> />; rewrite /erasure_tables_agree.
 move=> &1 &2 h y _ x; rewrite List.in_cons negb_or; move=>[hn hx].
 rewrite get_setE (negbTE _ hn); exact(h x hx).
qed.

lemma erasure_expand_coupling_fixed (m0:cca_e_table) :
 equiv[LoggedProgrammedExpand.shake ~ LoggedErasedExpand.shake :
   ={seed,ErasureSeedLog.used} /\
   erasure_tables_agree ErasureSeedLog.used{1} ROE.m{1} m0 ==>
   ={res,ErasureSeedLog.used} /\
   erasure_tables_agree ErasureSeedLog.used{1} ROE.m{1} m0].
proof.
 proc; inline ProgrammedFreshExpand.shake FreshExpand.shake.
 auto=> />; rewrite /erasure_tables_agree.
 move=> &1 &2 h y _ x; rewrite List.in_cons negb_or; move=>[hn hx].
 rewrite get_setE (negbTE _ hn); exact(h x hx).
qed.

(* Lift an expansion relation through the unchanged arithmetic calls. *)
lemma erasure_attempt_f_lift (E1<:KeygenExpand) (E2<:KeygenExpand)
 (I:(glob E1)->(glob E2)->bool) :
 equiv[E1.shake ~ E2.shake : ={seed} /\ I (glob E1){1} (glob E2){2} ==>
   ={res} /\ I (glob E1){1} (glob E2){2}] =>
 equiv[KeygenAttempt(E1).f ~ KeygenAttempt(E2).f :
   ={seed} /\ I (glob E1){1} (glob E2){2} ==> ={res} /\ I (glob E1){1} (glob E2){2}].
proof.
 move=>he; proc.
 do 4!(call (_:true); first by sim).
 call he; auto.
qed.
lemma erasure_retry_f_lift (E1<:KeygenExpand) (E2<:KeygenExpand)
 (I:(glob E1)->(glob E2)->bool) :
 equiv[E1.shake ~ E2.shake : ={seed} /\ I (glob E1){1} (glob E2){2} ==>
   ={res} /\ I (glob E1){1} (glob E2){2}] =>
 equiv[KeygenRetry(UniformSeedRNG,E1).f ~ KeygenRetry(UniformSeedRNG,E2).f :
   I (glob E1){1} (glob E2){2} ==> ={res} /\ I (glob E1){1} (glob E2){2}].
proof.
 move=>he; proc; while(={buf,ntt,inverse,status} /\ I (glob E1){1} (glob E2){2}).
 + call(erasure_attempt_f_lift E1 E2 I he).
   call (_:true); first by sim.
   auto.
 auto.
qed.
lemma erasure_counted_f_lift (E1<:KeygenExpand) (E2<:KeygenExpand)
 (I:(glob E1)->(glob E2)->bool) :
 equiv[E1.shake ~ E2.shake : ={seed} /\ I (glob E1){1} (glob E2){2} ==>
   ={res} /\ I (glob E1){1} (glob E2){2}] =>
 equiv[CountedRetry(UniformSeedRNG,E1).f ~ CountedRetry(UniformSeedRNG,E2).f :
   I (glob E1){1} (glob E2){2} ==> ={res} /\ I (glob E1){1} (glob E2){2}].
proof.
 move=>he; proc; inline CountedRetry(UniformSeedRNG,E1).f_from
   CountedRetry(UniformSeedRNG,E2).f_from; wp.
 while(={buf,ntt,inverse,status,count} /\ I (glob E1){1} (glob E2){2}).
 + wp; call(erasure_attempt_f_lift E1 E2 I he).
   call (_:true); first by sim.
   auto.
 auto.
qed.
lemma erasure_bounded_f_lift (E1<:KeygenExpand) (E2<:KeygenExpand)
 (I:(glob E1)->(glob E2)->bool) :
 equiv[E1.shake ~ E2.shake : ={seed} /\ I (glob E1){1} (glob E2){2} ==>
   ={res} /\ I (glob E1){1} (glob E2){2}] =>
 equiv[BoundedRetry(UniformSeedRNG,E1).f ~ BoundedRetry(UniformSeedRNG,E2).f :
   ={limit} /\ I (glob E1){1} (glob E2){2} ==> ={res} /\ I (glob E1){1} (glob E2){2}].
proof.
 move=>he; proc; inline BoundedRetry(UniformSeedRNG,E1).f_from
   BoundedRetry(UniformSeedRNG,E2).f_from; wp.
 while(={limit0,buf,ntt,inverse,status,count} /\ I (glob E1){1} (glob E2){2}).
 + wp; call(erasure_attempt_f_lift E1 E2 I he).
   call (_:true); first by sim.
   auto.
 auto.
qed.
lemma erasure_attempt_g_lift (E1<:KeygenExpand) (E2<:KeygenExpand)
 (I:(glob E1)->(glob E2)->bool) :
 equiv[E1.shake ~ E2.shake : ={seed} /\ I (glob E1){1} (glob E2){2} ==>
   ={res} /\ I (glob E1){1} (glob E2){2}] =>
 equiv[KeygenAttempt(E1).g ~ KeygenAttempt(E2).g :
   ={seed} /\ I (glob E1){1} (glob E2){2} ==> ={res} /\ I (glob E1){1} (glob E2){2}].
proof.
 move=>he; proc.
 do 4!(call (_:true); first by sim).
 call he; auto.
qed.
lemma erasure_retry_g_lift (E1<:KeygenExpand) (E2<:KeygenExpand)
 (I:(glob E1)->(glob E2)->bool) :
 equiv[E1.shake ~ E2.shake : ={seed} /\ I (glob E1){1} (glob E2){2} ==>
   ={res} /\ I (glob E1){1} (glob E2){2}] =>
 equiv[KeygenRetry(UniformSeedRNG,E1).g ~ KeygenRetry(UniformSeedRNG,E2).g :
   I (glob E1){1} (glob E2){2} ==> ={res} /\ I (glob E1){1} (glob E2){2}].
proof.
 move=>he; proc; while(={buf,ntt,inverse,status} /\ I (glob E1){1} (glob E2){2}).
 + call(erasure_attempt_g_lift E1 E2 I he).
   call (_:true); first by sim.
   auto.
 auto.
qed.
lemma erasure_counted_g_lift (E1<:KeygenExpand) (E2<:KeygenExpand)
 (I:(glob E1)->(glob E2)->bool) :
 equiv[E1.shake ~ E2.shake : ={seed} /\ I (glob E1){1} (glob E2){2} ==>
   ={res} /\ I (glob E1){1} (glob E2){2}] =>
 equiv[CountedRetry(UniformSeedRNG,E1).g ~ CountedRetry(UniformSeedRNG,E2).g :
   I (glob E1){1} (glob E2){2} ==> ={res} /\ I (glob E1){1} (glob E2){2}].
proof.
 move=>he; proc; inline CountedRetry(UniformSeedRNG,E1).g_from
   CountedRetry(UniformSeedRNG,E2).g_from; wp.
 while(={buf,ntt,inverse,status,count} /\ I (glob E1){1} (glob E2){2}).
 + wp; call(erasure_attempt_g_lift E1 E2 I he).
   call (_:true); first by sim.
   auto.
 auto.
qed.
lemma erasure_bounded_g_lift (E1<:KeygenExpand) (E2<:KeygenExpand)
 (I:(glob E1)->(glob E2)->bool) :
 equiv[E1.shake ~ E2.shake : ={seed} /\ I (glob E1){1} (glob E2){2} ==>
   ={res} /\ I (glob E1){1} (glob E2){2}] =>
 equiv[BoundedRetry(UniformSeedRNG,E1).g ~ BoundedRetry(UniformSeedRNG,E2).g :
   ={limit} /\ I (glob E1){1} (glob E2){2} ==> ={res} /\ I (glob E1){1} (glob E2){2}].
proof.
 move=>he; proc; inline BoundedRetry(UniformSeedRNG,E1).g_from
   BoundedRetry(UniformSeedRNG,E2).g_from; wp.
 while(={limit0,buf,ntt,inverse,status,count} /\ I (glob E1){1} (glob E2){2}).
 + wp; call(erasure_attempt_g_lift E1 E2 I he).
   call (_:true); first by sim.
   auto.
 auto.
qed.

lemma erasure_keygen_lift (E1<:KeygenExpand {-ROF}) (E2<:KeygenExpand {-ROF})
 (I:(glob E1)->(glob E2)->bool) :
 equiv[E1.shake ~ E2.shake : ={seed} /\ I (glob E1){1} (glob E2){2} ==>
   ={res} /\ I (glob E1){1} (glob E2){2}] =>
 equiv[KeygenInstrumented(UniformSeedRNG,E1,SHAKEFROM).run ~
       KeygenInstrumented(UniformSeedRNG,E2,SHAKEFROM).run :
   ={workspace,glob ROF} /\ I (glob E1){1} (glob E2){2} ==>
   ={res,glob ROF} /\ I (glob E1){1} (glob E2){2}].
proof.
 move=>he; proc.
 call (_:true); first by sim.
 call (_: ={glob ROF}); first by sim.
 call(erasure_retry_g_lift E1 E2 I he); call(erasure_retry_f_lift E1 E2 I he); auto.
qed.
lemma erasure_counted_lift (E1<:KeygenExpand {-ROF}) (E2<:KeygenExpand {-ROF})
 (I:(glob E1)->(glob E2)->bool) :
 equiv[E1.shake ~ E2.shake : ={seed} /\ I (glob E1){1} (glob E2){2} ==>
   ={res} /\ I (glob E1){1} (glob E2){2}] =>
 equiv[CountedKeygen(UniformSeedRNG,E1).run ~ CountedKeygen(UniformSeedRNG,E2).run :
   ={workspace,glob ROF} /\ I (glob E1){1} (glob E2){2} ==>
   ={res,glob ROF} /\ I (glob E1){1} (glob E2){2}].
proof.
 move=>he; proc; call (_: ={glob ROF}); first by sim.
 call(erasure_counted_g_lift E1 E2 I he); call(erasure_counted_f_lift E1 E2 I he); auto.
qed.
lemma erasure_stopped_lift (E1<:KeygenExpand {-ROF}) (E2<:KeygenExpand {-ROF})
 (I:(glob E1)->(glob E2)->bool) :
 equiv[E1.shake ~ E2.shake : ={seed} /\ I (glob E1){1} (glob E2){2} ==>
   ={res} /\ I (glob E1){1} (glob E2){2}] =>
 equiv[StoppedKeygen(UniformSeedRNG,E1).run ~ StoppedKeygen(UniformSeedRNG,E2).run :
   ={qf,qg,workspace,glob ROF} /\ I (glob E1){1} (glob E2){2} ==>
   ={res,glob ROF} /\ I (glob E1){1} (glob E2){2}].
proof.
 move=>he; proc; seq 3 3:(={fv,gv,result,qg,workspace,glob ROF} /\ I (glob E1){1} (glob E2){2}).
 + call(erasure_bounded_f_lift E1 E2 I he); auto.
 if; 1,3:by auto.
 seq 1 1:(={fv,gv,result,workspace,glob ROF} /\ I (glob E1){1} (glob E2){2}).
 + call(erasure_bounded_g_lift E1 E2 I he); auto.
 if; 1,3:by auto.
 wp; call (_: ={glob ROF}); first by sim.
 auto.
qed.

lemma erasure_programmed_instrumented_projection :
 equiv[KeygenInstrumented(UniformSeedRNG,LoggedProgrammedExpand,SHAKEFROM).run ~ KeygenInstrumented(UniformSeedRNG,ProgrammedFreshExpand,SHAKEFROM).run :
   ={workspace,glob ROE,glob ROF} ==> ={res,glob ROE,glob ROF}].
proof.
 conseq(erasure_keygen_lift LoggedProgrammedExpand ProgrammedFreshExpand (fun (lp:(glob LoggedProgrammedExpand)) (ep:(glob ProgrammedFreshExpand))=>lp.`2=ep) _) => //.
 conseq erasure_programmed_expand_projection=> />.
qed.

lemma erasure_programmed_counted_projection :
 equiv[CountedKeygen(UniformSeedRNG,LoggedProgrammedExpand).run ~ CountedKeygen(UniformSeedRNG,ProgrammedFreshExpand).run :
   ={workspace,glob ROE,glob ROF} ==> ={res,glob ROE,glob ROF}].
proof.
 conseq(erasure_counted_lift LoggedProgrammedExpand ProgrammedFreshExpand (fun (lp:(glob LoggedProgrammedExpand)) (ep:(glob ProgrammedFreshExpand))=>lp.`2=ep) _) => //.
 conseq erasure_programmed_expand_projection=> />.
qed.

lemma erasure_programmed_stopped_projection :
 equiv[StoppedKeygen(UniformSeedRNG,LoggedProgrammedExpand).run ~ StoppedKeygen(UniformSeedRNG,ProgrammedFreshExpand).run :
   ={qf,qg,workspace,glob ROE,glob ROF} ==> ={res,glob ROE,glob ROF}].
proof.
 conseq(erasure_stopped_lift LoggedProgrammedExpand ProgrammedFreshExpand (fun (lp:(glob LoggedProgrammedExpand)) (ep:(glob ProgrammedFreshExpand))=>lp.`2=ep) _) => //.
 conseq erasure_programmed_expand_projection=> />.
qed.

lemma erasure_programmed_keygen_projection :
 equiv[Keygen(UniformSeedRNG,LoggedProgrammedExpand,SHAKEFROM).run ~
       Keygen(UniformSeedRNG,ProgrammedFreshExpand,SHAKEFROM).run :
   ={glob ROE,glob ROF} ==> ={res,glob ROE,glob ROF}].
proof. proc; call erasure_programmed_instrumented_projection; auto. qed.

lemma erasure_erased_instrumented_projection :
 equiv[KeygenInstrumented(UniformSeedRNG,LoggedErasedExpand,SHAKEFROM).run ~ KeygenInstrumented(UniformSeedRNG,FreshExpand,SHAKEFROM).run :
   ={workspace,glob ROF} ==> ={res,glob ROF}].
proof.
 conseq(erasure_keygen_lift LoggedErasedExpand FreshExpand (fun (le:(glob LoggedErasedExpand)) (fe:(glob FreshExpand))=>true) _) => //.
 conseq erasure_erased_expand_projection=> />.
qed.

lemma erasure_erased_counted_projection :
 equiv[CountedKeygen(UniformSeedRNG,LoggedErasedExpand).run ~ CountedKeygen(UniformSeedRNG,FreshExpand).run :
   ={workspace,glob ROF} ==> ={res,glob ROF}].
proof.
 conseq(erasure_counted_lift LoggedErasedExpand FreshExpand (fun (le:(glob LoggedErasedExpand)) (fe:(glob FreshExpand))=>true) _) => //.
 conseq erasure_erased_expand_projection=> />.
qed.

lemma erasure_erased_stopped_projection :
 equiv[StoppedKeygen(UniformSeedRNG,LoggedErasedExpand).run ~ StoppedKeygen(UniformSeedRNG,FreshExpand).run :
   ={qf,qg,workspace,glob ROF} ==> ={res,glob ROF}].
proof.
 conseq(erasure_stopped_lift LoggedErasedExpand FreshExpand (fun (le:(glob LoggedErasedExpand)) (fe:(glob FreshExpand))=>true) _) => //.
 conseq erasure_erased_expand_projection=> />.
qed.

lemma erasure_erased_keygen_projection :
 equiv[Keygen(UniformSeedRNG,LoggedErasedExpand,SHAKEFROM).run ~
       Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run :
   ={glob ROF} ==> ={res,glob ROF}].
proof. proc; call erasure_erased_instrumented_projection; auto. qed.

lemma erasure_instrumented_coupling :
 equiv[KeygenInstrumented(UniformSeedRNG,LoggedProgrammedExpand,SHAKEFROM).run ~ KeygenInstrumented(UniformSeedRNG,LoggedErasedExpand,SHAKEFROM).run :
   ={workspace,glob ROF,ErasureSeedLog.used} /\
   erasure_tables_agree ErasureSeedLog.used{1} ROE.m{1} ROE.m{2} ==>
   ={res,glob ROF,ErasureSeedLog.used} /\
   erasure_tables_agree ErasureSeedLog.used{1} ROE.m{1} ROE.m{2}].
proof.
 proc*; exists* ROE.m{2}; elim*=>m0.
 call(erasure_keygen_lift LoggedProgrammedExpand LoggedErasedExpand
   (fun (lp:(glob LoggedProgrammedExpand)) (le:(glob LoggedErasedExpand))=>lp.`1=le /\ erasure_tables_agree lp.`1 lp.`2 m0) _).
 + conseq(erasure_expand_coupling_fixed m0)=> />.
 auto.
qed.

lemma erasure_counted_coupling :
 equiv[CountedKeygen(UniformSeedRNG,LoggedProgrammedExpand).run ~ CountedKeygen(UniformSeedRNG,LoggedErasedExpand).run :
   ={workspace,glob ROF,ErasureSeedLog.used} /\
   erasure_tables_agree ErasureSeedLog.used{1} ROE.m{1} ROE.m{2} ==>
   ={res,glob ROF,ErasureSeedLog.used} /\
   erasure_tables_agree ErasureSeedLog.used{1} ROE.m{1} ROE.m{2}].
proof.
 proc*; exists* ROE.m{2}; elim*=>m0.
 call(erasure_counted_lift LoggedProgrammedExpand LoggedErasedExpand
   (fun (lp:(glob LoggedProgrammedExpand)) (le:(glob LoggedErasedExpand))=>lp.`1=le /\ erasure_tables_agree lp.`1 lp.`2 m0) _).
 + conseq(erasure_expand_coupling_fixed m0)=> />.
 auto.
qed.

lemma erasure_stopped_coupling :
 equiv[StoppedKeygen(UniformSeedRNG,LoggedProgrammedExpand).run ~ StoppedKeygen(UniformSeedRNG,LoggedErasedExpand).run :
   ={qf,qg,workspace,glob ROF,ErasureSeedLog.used} /\
   erasure_tables_agree ErasureSeedLog.used{1} ROE.m{1} ROE.m{2} ==>
   ={res,glob ROF,ErasureSeedLog.used} /\
   erasure_tables_agree ErasureSeedLog.used{1} ROE.m{1} ROE.m{2}].
proof.
 proc*; exists* ROE.m{2}; elim*=>m0.
 call(erasure_stopped_lift LoggedProgrammedExpand LoggedErasedExpand
   (fun (lp:(glob LoggedProgrammedExpand)) (le:(glob LoggedErasedExpand))=>lp.`1=le /\ erasure_tables_agree lp.`1 lp.`2 m0) _).
 + conseq(erasure_expand_coupling_fixed m0)=> />.
 auto.
qed.

lemma erasure_keygen_coupling :
 equiv[Keygen(UniformSeedRNG,LoggedProgrammedExpand,SHAKEFROM).run ~
       Keygen(UniformSeedRNG,LoggedErasedExpand,SHAKEFROM).run :
   ={glob ROF,ErasureSeedLog.used} /\
   erasure_tables_agree ErasureSeedLog.used{1} ROE.m{1} ROE.m{2} ==>
   ={res,glob ROF,ErasureSeedLog.used} /\
   erasure_tables_agree ErasureSeedLog.used{1} ROE.m{1} ROE.m{2}].
proof. proc; call erasure_instrumented_coupling; auto. qed.
