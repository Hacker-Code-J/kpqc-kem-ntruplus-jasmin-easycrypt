require import AllCore Distr FMap.
from Jasmin require import JWord.
require import Array32 Array192 Array768 Array14466.
require import NTRUPlus768CCASetupState.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteAttempt.
require import NTRUPlus768KeygenCompleteRetry NTRUPlus768KeygenCompleteProof.
require import NTRUPlus768KeygenCompleteFinish NTRUPlus768KeygenClearProof.
require import NTRUPlus768StoppedKeygenModel NTRUPlus768StoppedKeygenPrefix.
require import NTRUPlus768AttemptRealized NTRUPlus768FreshRetryLaw NTRUPlus768FreshBoundedLaw.
require import NTRUPlus768AcceptanceProbability.

(* These projections preserve the actual output and F state. They do not
   identify the joint E table with an independent or empty table. *)

lemma programmed_attempt_f_projection :
 equiv[KeygenAttempt(ProgrammedFreshExpand).f ~ KeygenAttempt(FreshExpand).f :
 ={seed} ==> ={res}].
proof.
 transitivity AttemptResult(ProgrammedFreshExpand).f
  (={seed,glob ROE} ==> ={res,glob ROE})
  (={seed} ==> ={res}) => //.
 + smt().
 + exact(keygen_attempt_f_realized_equiv ProgrammedFreshExpand).
 transitivity AttemptResult(FreshExpand).f
  (={seed} ==> ={res}) (={seed} ==> ={res}) => //.
 + smt().
 + proc; call programmed_fresh_expand_projection; auto.
 symmetry; conseq(keygen_attempt_f_realized_equiv FreshExpand); smt().
qed.

lemma programmed_retry_f_projection :
 equiv[KeygenRetry(UniformSeedRNG,ProgrammedFreshExpand).f ~
       KeygenRetry(UniformSeedRNG,FreshExpand).f : true ==> ={res}].
proof.
 proc; while(={buf,ntt,inverse,status}).
 + call programmed_attempt_f_projection.
   call (_:true ==> ={res}); first by sim.
   auto.
 auto.
qed.

lemma programmed_bounded_f_projection :
 equiv[BoundedRetry(UniformSeedRNG,ProgrammedFreshExpand).f ~
       BoundedRetry(UniformSeedRNG,FreshExpand).f : ={limit} ==> ={res}].
proof.
 proc; inline BoundedRetry(UniformSeedRNG,ProgrammedFreshExpand).f_from
   BoundedRetry(UniformSeedRNG,FreshExpand).f_from; wp.
 while(={limit0,buf,ntt,inverse,status,count}).
 + wp; call programmed_attempt_f_projection.
   call (_:true ==> ={res}); first by sim.
   auto.
 auto.
qed.

lemma programmed_counted_f_projection :
 equiv[CountedRetry(UniformSeedRNG,ProgrammedFreshExpand).f ~
       CountedRetry(UniformSeedRNG,FreshExpand).f : true ==> ={res}].
proof.
 proc; inline CountedRetry(UniformSeedRNG,ProgrammedFreshExpand).f_from
   CountedRetry(UniformSeedRNG,FreshExpand).f_from; wp.
 while(={buf,ntt,inverse,status,count}).
 + wp; call programmed_attempt_f_projection.
   call (_:true ==> ={res}); first by sim.
   auto.
 auto.
qed.

lemma programmed_attempt_g_projection :
 equiv[KeygenAttempt(ProgrammedFreshExpand).g ~ KeygenAttempt(FreshExpand).g :
 ={seed} ==> ={res}].
proof.
 transitivity AttemptResult(ProgrammedFreshExpand).g
  (={seed,glob ROE} ==> ={res,glob ROE})
  (={seed} ==> ={res}) => //.
 + smt().
 + exact(keygen_attempt_g_realized_equiv ProgrammedFreshExpand).
 transitivity AttemptResult(FreshExpand).g
  (={seed} ==> ={res}) (={seed} ==> ={res}) => //.
 + smt().
 + proc; call programmed_fresh_expand_projection; auto.
 symmetry; conseq(keygen_attempt_g_realized_equiv FreshExpand); smt().
qed.

lemma programmed_retry_g_projection :
 equiv[KeygenRetry(UniformSeedRNG,ProgrammedFreshExpand).g ~
       KeygenRetry(UniformSeedRNG,FreshExpand).g : true ==> ={res}].
proof.
 proc; while(={buf,ntt,inverse,status}).
 + call programmed_attempt_g_projection.
   call (_:true ==> ={res}); first by sim.
   auto.
 auto.
qed.

lemma programmed_bounded_g_projection :
 equiv[BoundedRetry(UniformSeedRNG,ProgrammedFreshExpand).g ~
       BoundedRetry(UniformSeedRNG,FreshExpand).g : ={limit} ==> ={res}].
proof.
 proc; inline BoundedRetry(UniformSeedRNG,ProgrammedFreshExpand).g_from
   BoundedRetry(UniformSeedRNG,FreshExpand).g_from; wp.
 while(={limit0,buf,ntt,inverse,status,count}).
 + wp; call programmed_attempt_g_projection.
   call (_:true ==> ={res}); first by sim.
   auto.
 auto.
qed.

lemma programmed_counted_g_projection :
 equiv[CountedRetry(UniformSeedRNG,ProgrammedFreshExpand).g ~
       CountedRetry(UniformSeedRNG,FreshExpand).g : true ==> ={res}].
proof.
 proc; inline CountedRetry(UniformSeedRNG,ProgrammedFreshExpand).g_from
   CountedRetry(UniformSeedRNG,FreshExpand).g_from; wp.
 while(={buf,ntt,inverse,status,count}).
 + wp; call programmed_attempt_g_projection.
   call (_:true ==> ={res}); first by sim.
   auto.
 auto.
qed.

lemma programmed_keygen_projection :
 equiv[KeygenInstrumented(UniformSeedRNG,ProgrammedFreshExpand,SHAKEFROM).run ~
       KeygenInstrumented(UniformSeedRNG,FreshExpand,SHAKEFROM).run :
 ={workspace,glob ROF} ==> ={res,glob ROF}].
proof.
 proc.
 call (_:true); first by sim.
 call (_: ={glob ROF}); first by sim.
 call programmed_retry_g_projection; call programmed_retry_f_projection; auto.
qed.

lemma programmed_counted_projection :
 equiv[CountedKeygen(UniformSeedRNG,ProgrammedFreshExpand).run ~
       CountedKeygen(UniformSeedRNG,FreshExpand).run :
 ={workspace,glob ROF} ==> ={res,glob ROF}].
proof.
 proc; call (_: ={glob ROF}); first by sim.
 call programmed_counted_g_projection; call programmed_counted_f_projection; auto.
qed.

lemma programmed_stopped_projection :
 equiv[StoppedKeygen(UniformSeedRNG,ProgrammedFreshExpand).run ~
       StoppedKeygen(UniformSeedRNG,FreshExpand).run :
 ={qf,qg,workspace,glob ROF} ==> ={res,glob ROF}].
proof.
 proc; seq 3 3:(={fv,gv,result,qg,workspace,glob ROF}).
 + call programmed_bounded_f_projection; auto.
 if; 1,3:by auto.
 seq 1 1:(={fv,gv,result,workspace,glob ROF}).
 + call programmed_bounded_g_projection; auto.
 if; 1,3:by auto.
 wp; call (_: ={glob ROF}); first by sim.
 auto.
qed.

lemma programmed_keygen_ll :
 islossless KeygenInstrumented(UniformSeedRNG,ProgrammedFreshExpand,SHAKEFROM).run.
proof.
 conseq programmed_keygen_projection
   (fresh_keygen_instrumented_ll fresh_f_accept_positive fresh_g_accept_positive); smt().
qed.
lemma programmed_counted_ll : islossless CountedKeygen(UniformSeedRNG,ProgrammedFreshExpand).run.
proof.
 conseq programmed_counted_projection
   (fresh_counted_keygen_ll fresh_f_accept_positive fresh_g_accept_positive); smt().
qed.
lemma programmed_stopped_ll : islossless StoppedKeygen(UniformSeedRNG,ProgrammedFreshExpand).run.
proof.
 exact(stopped_keygen_lossless UniformSeedRNG ProgrammedFreshExpand
   uniform_seed_rng_ll programmed_fresh_expand_ll).
qed.
lemma programmed_joint_setup_ll : islossless JointSetup(ProgrammedFreshExpand).run.
proof. proc; call programmed_keygen_ll; auto. qed.
lemma programmed_joint_source_ll : islossless JointSetupSource(ProgrammedFreshExpand).guess.
proof. proc; call programmed_joint_setup_ll; call rof_init_ll; call roe_init_ll; auto. qed.

lemma programmed_stopped_abort qf0 qg0 :
 0<=qf0 => 0<=qg0 =>
 phoare[StoppedKeygen(UniformSeedRNG,ProgrammedFreshExpand).run :
 qf=qf0 /\ qg=qg0 ==> !stopped_success res] <= (fresh_retry_tail qf0 qg0).
proof.
 move=>hf hg; conseq programmed_stopped_projection
   (fresh_stopped_keygen_abort qf0 qg0 hf hg); smt().
qed.
lemma programmed_stopped_abort_probability &m qf0 qg0 workspace0 :
 0<=qf0 => 0<=qg0 =>
 Pr[StoppedKeygen(UniformSeedRNG,ProgrammedFreshExpand).run(qf0,qg0,workspace0) @ &m:
 !stopped_success res] <= fresh_retry_tail qf0 qg0.
proof. move=>hf hg; by byphoare(programmed_stopped_abort qf0 qg0 hf hg). qed.

lemma programmed_counted_tail &m qf0 qg0 workspace0 :
 0<=qf0 => 0<=qg0 =>
 Pr[CountedKeygen(UniformSeedRNG,ProgrammedFreshExpand).run(workspace0) @ &m:
 !counted_within qf0 qg0 res] <= fresh_retry_tail qf0 qg0.
proof.
 move=>hf hg.
 have hp:=counted_stopped_prefix UniformSeedRNG ProgrammedFreshExpand qf0 qg0
   workspace0 predT &m uniform_seed_rng_ll programmed_fresh_expand_ll.
 rewrite /stopped_event /predT /= in hp.
 have hc:Pr[CountedKeygen(UniformSeedRNG,ProgrammedFreshExpand).run(workspace0) @ &m:true]=1%r
   by byphoare programmed_counted_ll.
 have hs:Pr[StoppedKeygen(UniformSeedRNG,ProgrammedFreshExpand).run(qf0,qg0,workspace0) @ &m:true]=1%r
   by byphoare programmed_stopped_ll.
 have hb:=programmed_stopped_abort_probability &m qf0 qg0 workspace0 hf hg.
 rewrite /stopped_success in hb.
 rewrite Pr[mu_not] hc.
 move:hb; rewrite Pr[mu_not] hs.
 rewrite hp.
 done.
qed.

