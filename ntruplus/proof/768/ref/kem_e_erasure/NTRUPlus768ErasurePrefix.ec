require import AllCore List Distr FMap.
from Jasmin require import JWord.
require import Array32 Array192 Array768 Array14466.
require import NTRUPlus768ROMOracles NTRUPlus768KeygenCompleteSpec.
require import NTRUPlus768KeygenCompleteAttempt NTRUPlus768KeygenCompleteProof.
require import NTRUPlus768StoppedKeygenModel NTRUPlus768StoppedKeygenPrefix.
require import NTRUPlus768FreshRetryLaw NTRUPlus768FreshBoundedLaw.
require import NTRUPlus768AcceptanceProbability NTRUPlus768AcceptanceROMBound.
require import NTRUPlus768CCASetupState NTRUPlus768CCASetupProgrammed NTRUPlus768CCASetupPrefix.
require import NTRUPlus768ErasureModel NTRUPlus768ErasureSetup.

(* Every E call records one seed before the actual acceptance test. *)
lemma erasure_programmed_expand_length n0 :
 hoare[LoggedProgrammedExpand.shake : size ErasureSeedLog.used=n0 ==>
   size ErasureSeedLog.used=n0+1].
proof. proc; call (_:true ==> true); first by trivial.
 auto=> />; smt(). qed.
lemma erasure_programmed_attempt_f_length n0 :
 hoare[KeygenAttempt(LoggedProgrammedExpand).f : size ErasureSeedLog.used=n0 ==>
   size ErasureSeedLog.used=n0+1].
proof.
 proc; do 4!(call (_:true ==> true); first by trivial).
 call(erasure_programmed_expand_length n0); auto.
qed.
lemma erasure_programmed_counted_f_length n0 :
 hoare[CountedRetry(UniformSeedRNG,LoggedProgrammedExpand).f : size ErasureSeedLog.used=n0 ==>
   size ErasureSeedLog.used=n0+res.`rs_count].
proof.
 proc; inline CountedRetry(UniformSeedRNG,LoggedProgrammedExpand).f_from; wp.
 while(size ErasureSeedLog.used=n0+count).
 + wp; ecall(erasure_programmed_attempt_f_length (n0+count)).
   call (_:true ==> true); first by trivial.
   auto=> />; smt().
 auto=> />; rewrite /retry_initial /=; smt().
qed.
lemma erasure_programmed_bounded_f_length n0 :
 hoare[BoundedRetry(UniformSeedRNG,LoggedProgrammedExpand).f : size ErasureSeedLog.used=n0 ==>
   size ErasureSeedLog.used=n0+res.`rs_count].
proof.
 proc; inline BoundedRetry(UniformSeedRNG,LoggedProgrammedExpand).f_from; wp.
 while(size ErasureSeedLog.used=n0+count).
 + wp; ecall(erasure_programmed_attempt_f_length (n0+count)).
   call (_:true ==> true); first by trivial.
   auto=> />; smt().
 auto=> />; rewrite /retry_initial /=; smt().
qed.
lemma erasure_programmed_attempt_g_length n0 :
 hoare[KeygenAttempt(LoggedProgrammedExpand).g : size ErasureSeedLog.used=n0 ==>
   size ErasureSeedLog.used=n0+1].
proof.
 proc; do 4!(call (_:true ==> true); first by trivial).
 call(erasure_programmed_expand_length n0); auto.
qed.
lemma erasure_programmed_counted_g_length n0 :
 hoare[CountedRetry(UniformSeedRNG,LoggedProgrammedExpand).g : size ErasureSeedLog.used=n0 ==>
   size ErasureSeedLog.used=n0+res.`rs_count].
proof.
 proc; inline CountedRetry(UniformSeedRNG,LoggedProgrammedExpand).g_from; wp.
 while(size ErasureSeedLog.used=n0+count).
 + wp; ecall(erasure_programmed_attempt_g_length (n0+count)).
   call (_:true ==> true); first by trivial.
   auto=> />; smt().
 auto=> />; rewrite /retry_initial /=; smt().
qed.
lemma erasure_programmed_bounded_g_length n0 :
 hoare[BoundedRetry(UniformSeedRNG,LoggedProgrammedExpand).g : size ErasureSeedLog.used=n0 ==>
   size ErasureSeedLog.used=n0+res.`rs_count].
proof.
 proc; inline BoundedRetry(UniformSeedRNG,LoggedProgrammedExpand).g_from; wp.
 while(size ErasureSeedLog.used=n0+count).
 + wp; ecall(erasure_programmed_attempt_g_length (n0+count)).
   call (_:true ==> true); first by trivial.
   auto=> />; smt().
 auto=> />; rewrite /retry_initial /=; smt().
qed.
lemma erasure_programmed_counted_length n0 :
 hoare[CountedKeygen(UniformSeedRNG,LoggedProgrammedExpand).run : size ErasureSeedLog.used=n0 ==>
   size ErasureSeedLog.used=n0+res.`2+res.`3].
proof.
 proc; call (_:true ==> true); first by trivial.
 ecall(erasure_programmed_counted_g_length (n0+fv.`rs_count)).
 call(erasure_programmed_counted_f_length n0); auto=> />; smt().
qed.
lemma erasure_programmed_stopped_length n0 :
 hoare[StoppedKeygen(UniformSeedRNG,LoggedProgrammedExpand).run : size ErasureSeedLog.used=n0 ==>
   size ErasureSeedLog.used=n0+res.`2+res.`3].
proof.
 proc; seq 3:(size ErasureSeedLog.used=n0+fv.`rs_count /\ gv=retry_initial).
 + call(erasure_programmed_bounded_f_length n0); auto.
 if.
 + seq 1:(size ErasureSeedLog.used=n0+fv.`rs_count+gv.`rs_count).
   - ecall(erasure_programmed_bounded_g_length (n0+fv.`rs_count)); auto=> />; smt().
   if; last by auto.
   wp; call (_:true ==> true); first by trivial.
   auto.
 auto=> />; rewrite /retry_initial /=; smt().
qed.
lemma erasure_programmed_stopped_ll :
 islossless StoppedKeygen(UniformSeedRNG,LoggedProgrammedExpand).run.
proof. exact(stopped_keygen_lossless UniformSeedRNG LoggedProgrammedExpand uniform_seed_rng_ll logged_programmed_expand_ll). qed.
lemma erasure_programmed_instrumented_ll :
 islossless KeygenInstrumented(UniformSeedRNG,LoggedProgrammedExpand,SHAKEFROM).run.
proof. conseq erasure_programmed_instrumented_projection programmed_keygen_ll; smt(). qed.
lemma erasure_programmed_keygen_ll :
 islossless Keygen(UniformSeedRNG,LoggedProgrammedExpand,SHAKEFROM).run.
proof. proc; call erasure_programmed_instrumented_ll; auto. qed.
lemma erasure_programmed_counted_ll :
 islossless CountedKeygen(UniformSeedRNG,LoggedProgrammedExpand).run.
proof. conseq erasure_programmed_counted_projection programmed_counted_ll; smt(). qed.
lemma erasure_programmed_counted_tail &m qf qg workspace :
 0<=qf =>0<=qg =>
 Pr[CountedKeygen(UniformSeedRNG,LoggedProgrammedExpand).run(workspace) @ &m:
   !counted_within qf qg res] <=fresh_retry_tail qf qg.
proof.
 move=>hf hg.
 have he:Pr[CountedKeygen(UniformSeedRNG,LoggedProgrammedExpand).run(workspace) @ &m:
   !counted_within qf qg res]=
   Pr[CountedKeygen(UniformSeedRNG,ProgrammedFreshExpand).run(workspace) @ &m:
   !counted_within qf qg res] by byequiv erasure_programmed_counted_projection=> //.
 rewrite he.
 exact(programmed_counted_tail &m qf qg workspace hf hg).
qed.
lemma erasure_programmed_counted_tail_certified &m qf qg workspace :
 0<=qf =>0<=qg =>
 Pr[CountedKeygen(UniformSeedRNG,LoggedProgrammedExpand).run(workspace) @ &m:
   !counted_within qf qg res] <=(3%r/8%r)^qf+(3%r/8%r)^qg.
proof.
 move=>hf hg; have ht:=erasure_programmed_counted_tail &m qf qg workspace hf hg.
 have hc:=certified_fresh_retry_tail qf qg hf hg; smt().
qed.
lemma erasure_erased_expand_length n0 :
 hoare[LoggedErasedExpand.shake : size ErasureSeedLog.used=n0 ==>
   size ErasureSeedLog.used=n0+1].
proof. proc; call (_:true ==> true); first by trivial.
 auto=> />; smt(). qed.
lemma erasure_erased_attempt_f_length n0 :
 hoare[KeygenAttempt(LoggedErasedExpand).f : size ErasureSeedLog.used=n0 ==>
   size ErasureSeedLog.used=n0+1].
proof.
 proc; do 4!(call (_:true ==> true); first by trivial).
 call(erasure_erased_expand_length n0); auto.
qed.
lemma erasure_erased_counted_f_length n0 :
 hoare[CountedRetry(UniformSeedRNG,LoggedErasedExpand).f : size ErasureSeedLog.used=n0 ==>
   size ErasureSeedLog.used=n0+res.`rs_count].
proof.
 proc; inline CountedRetry(UniformSeedRNG,LoggedErasedExpand).f_from; wp.
 while(size ErasureSeedLog.used=n0+count).
 + wp; ecall(erasure_erased_attempt_f_length (n0+count)).
   call (_:true ==> true); first by trivial.
   auto=> />; smt().
 auto=> />; rewrite /retry_initial /=; smt().
qed.
lemma erasure_erased_bounded_f_length n0 :
 hoare[BoundedRetry(UniformSeedRNG,LoggedErasedExpand).f : size ErasureSeedLog.used=n0 ==>
   size ErasureSeedLog.used=n0+res.`rs_count].
proof.
 proc; inline BoundedRetry(UniformSeedRNG,LoggedErasedExpand).f_from; wp.
 while(size ErasureSeedLog.used=n0+count).
 + wp; ecall(erasure_erased_attempt_f_length (n0+count)).
   call (_:true ==> true); first by trivial.
   auto=> />; smt().
 auto=> />; rewrite /retry_initial /=; smt().
qed.
lemma erasure_erased_attempt_g_length n0 :
 hoare[KeygenAttempt(LoggedErasedExpand).g : size ErasureSeedLog.used=n0 ==>
   size ErasureSeedLog.used=n0+1].
proof.
 proc; do 4!(call (_:true ==> true); first by trivial).
 call(erasure_erased_expand_length n0); auto.
qed.
lemma erasure_erased_counted_g_length n0 :
 hoare[CountedRetry(UniformSeedRNG,LoggedErasedExpand).g : size ErasureSeedLog.used=n0 ==>
   size ErasureSeedLog.used=n0+res.`rs_count].
proof.
 proc; inline CountedRetry(UniformSeedRNG,LoggedErasedExpand).g_from; wp.
 while(size ErasureSeedLog.used=n0+count).
 + wp; ecall(erasure_erased_attempt_g_length (n0+count)).
   call (_:true ==> true); first by trivial.
   auto=> />; smt().
 auto=> />; rewrite /retry_initial /=; smt().
qed.
lemma erasure_erased_bounded_g_length n0 :
 hoare[BoundedRetry(UniformSeedRNG,LoggedErasedExpand).g : size ErasureSeedLog.used=n0 ==>
   size ErasureSeedLog.used=n0+res.`rs_count].
proof.
 proc; inline BoundedRetry(UniformSeedRNG,LoggedErasedExpand).g_from; wp.
 while(size ErasureSeedLog.used=n0+count).
 + wp; ecall(erasure_erased_attempt_g_length (n0+count)).
   call (_:true ==> true); first by trivial.
   auto=> />; smt().
 auto=> />; rewrite /retry_initial /=; smt().
qed.
lemma erasure_erased_counted_length n0 :
 hoare[CountedKeygen(UniformSeedRNG,LoggedErasedExpand).run : size ErasureSeedLog.used=n0 ==>
   size ErasureSeedLog.used=n0+res.`2+res.`3].
proof.
 proc; call (_:true ==> true); first by trivial.
 ecall(erasure_erased_counted_g_length (n0+fv.`rs_count)).
 call(erasure_erased_counted_f_length n0); auto=> />; smt().
qed.
lemma erasure_erased_stopped_length n0 :
 hoare[StoppedKeygen(UniformSeedRNG,LoggedErasedExpand).run : size ErasureSeedLog.used=n0 ==>
   size ErasureSeedLog.used=n0+res.`2+res.`3].
proof.
 proc; seq 3:(size ErasureSeedLog.used=n0+fv.`rs_count /\ gv=retry_initial).
 + call(erasure_erased_bounded_f_length n0); auto.
 if.
 + seq 1:(size ErasureSeedLog.used=n0+fv.`rs_count+gv.`rs_count).
   - ecall(erasure_erased_bounded_g_length (n0+fv.`rs_count)); auto=> />; smt().
   if; last by auto.
   wp; call (_:true ==> true); first by trivial.
   auto.
 auto=> />; rewrite /retry_initial /=; smt().
qed.
lemma erasure_erased_stopped_ll :
 islossless StoppedKeygen(UniformSeedRNG,LoggedErasedExpand).run.
proof. exact(stopped_keygen_lossless UniformSeedRNG LoggedErasedExpand uniform_seed_rng_ll logged_erased_expand_ll). qed.
lemma erasure_erased_instrumented_ll :
 islossless KeygenInstrumented(UniformSeedRNG,LoggedErasedExpand,SHAKEFROM).run.
proof. conseq erasure_erased_instrumented_projection (fresh_keygen_instrumented_ll fresh_f_accept_positive fresh_g_accept_positive); smt(). qed.
lemma erasure_erased_keygen_ll :
 islossless Keygen(UniformSeedRNG,LoggedErasedExpand,SHAKEFROM).run.
proof. proc; call erasure_erased_instrumented_ll; auto. qed.
lemma erasure_erased_counted_ll :
 islossless CountedKeygen(UniformSeedRNG,LoggedErasedExpand).run.
proof. conseq erasure_erased_counted_projection (fresh_counted_keygen_ll fresh_f_accept_positive fresh_g_accept_positive); smt(). qed.
lemma erasure_erased_counted_tail &m qf qg workspace :
 0<=qf =>0<=qg =>
 Pr[CountedKeygen(UniformSeedRNG,LoggedErasedExpand).run(workspace) @ &m:
   !counted_within qf qg res] <=fresh_retry_tail qf qg.
proof.
 move=>hf hg.
 have he:Pr[CountedKeygen(UniformSeedRNG,LoggedErasedExpand).run(workspace) @ &m:
   !counted_within qf qg res]=
   Pr[CountedKeygen(UniformSeedRNG,FreshExpand).run(workspace) @ &m:
   !counted_within qf qg res] by byequiv erasure_erased_counted_projection=> //.
 rewrite he.
 have hp:Pr[CountedKeygen(UniformSeedRNG,ProgrammedFreshExpand).run(workspace) @ &m:
   !counted_within qf qg res]=
   Pr[CountedKeygen(UniformSeedRNG,FreshExpand).run(workspace) @ &m:
   !counted_within qf qg res] by byequiv programmed_counted_projection=> //.
 rewrite -hp.
 exact(programmed_counted_tail &m qf qg workspace hf hg).
qed.
lemma erasure_erased_counted_tail_certified &m qf qg workspace :
 0<=qf =>0<=qg =>
 Pr[CountedKeygen(UniformSeedRNG,LoggedErasedExpand).run(workspace) @ &m:
   !counted_within qf qg res] <=(3%r/8%r)^qf+(3%r/8%r)^qg.
proof.
 move=>hf hg; have ht:=erasure_erased_counted_tail &m qf qg workspace hf hg.
 have hc:=certified_fresh_retry_tail qf qg hf hg; smt().
qed.

(* Exact joint-state prefix equality. No acceptance lower bound or
   unrestricted-loop losslessness is needed for this equality itself. *)
lemma erasure_programmed_state_prefix &m qf qg workspace
 (event:keygen_output->erasure_seed list->cca_e_table->cca_f_table->bool) :
 Pr[CountedKeygen(UniformSeedRNG,LoggedProgrammedExpand).run(workspace) @ &m:
   counted_within qf qg res /\ event res.`1 ErasureSeedLog.used ROE.m ROF.m]=
 Pr[StoppedKeygen(UniformSeedRNG,LoggedProgrammedExpand).run(qf,qg,workspace) @ &m:
   stopped_success res /\ event (oget res.`1) ErasureSeedLog.used ROE.m ROF.m].
proof.
 exact(cca_counted_stopped_state_prefix UniformSeedRNG LoggedProgrammedExpand qf qg workspace
   (fun out (ge:(glob LoggedProgrammedExpand)) fm=>event out ge.`1 ge.`2 fm) &m
   uniform_seed_rng_ll logged_programmed_expand_ll).
qed.

lemma erasure_erased_state_prefix &m qf qg workspace
 (event:keygen_output->erasure_seed list->cca_f_table->bool) :
 Pr[CountedKeygen(UniformSeedRNG,LoggedErasedExpand).run(workspace) @ &m:
   counted_within qf qg res /\ event res.`1 ErasureSeedLog.used ROF.m]=
 Pr[StoppedKeygen(UniformSeedRNG,LoggedErasedExpand).run(qf,qg,workspace) @ &m:
   stopped_success res /\ event (oget res.`1) ErasureSeedLog.used ROF.m].
proof.
 exact(cca_counted_stopped_state_prefix UniformSeedRNG LoggedErasedExpand qf qg workspace event &m
   uniform_seed_rng_ll logged_erased_expand_ll).
qed.

lemma erasure_programmed_stopped_abort qf0 qg0 :
 0<=qf0 =>0<=qg0 =>
 phoare[StoppedKeygen(UniformSeedRNG,LoggedProgrammedExpand).run:
   qf=qf0 /\ qg=qg0 ==> !stopped_success res] <= (fresh_retry_tail qf0 qg0).
proof.
 move=>hf hg; conseq erasure_programmed_stopped_projection
   (programmed_stopped_abort qf0 qg0 hf hg); smt().
qed.
lemma erasure_erased_stopped_abort qf0 qg0 :
 0<=qf0 =>0<=qg0 =>
 phoare[StoppedKeygen(UniformSeedRNG,LoggedErasedExpand).run:
   qf=qf0 /\ qg=qg0 ==> !stopped_success res] <= (fresh_retry_tail qf0 qg0).
proof.
 move=>hf hg; conseq erasure_erased_stopped_projection
   (fresh_stopped_keygen_abort qf0 qg0 hf hg); smt().
qed.
