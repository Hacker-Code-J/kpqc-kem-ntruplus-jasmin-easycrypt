require import AllCore Distr.
from Jasmin require import JWord.
require import Array192 Array14466.
require import NTRUPlus768ROMDistributions NTRUPlus768ROMOracles.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteAttempt.
require import NTRUPlus768KeygenCompleteRetry NTRUPlus768KeygenCompleteProof.
require import NTRUPlus768StoppedKeygenModel NTRUPlus768StoppedKeygenPrefix.
require import NTRUPlus768AttemptRealized NTRUPlus768FreshRetryLaw.
require import NTRUPlus768BoundedBufferRejection.

lemma fresh_bounded_f_equiv :
 equiv[BoundedRetry(UniformSeedRNG,FreshExpand).f ~ BoundedBufferRejection.run :
  limit{1}=q{2} /\ d{2}=uniform192 /\ accept{2}=keygen_f_accept ==>
  (!res{1}.`rs_ok <=> res{2}=None) /\
  (res{1}.`rs_ok => res{2}=Some res{1}.`rs_buf)].
proof.
 proc; inline BoundedRetry(UniformSeedRNG,FreshExpand).f_from; wp.
 while (limit0{1}=q{2} /\ d{2}=uniform192 /\ accept{2}=keygen_f_accept /\
   ={count} /\ 0<=count{1} /\
   (status{1}=W64.zero <=> success{2}) /\
   (success{2} => buf{1}=buffer{2})).
 + transitivity{1} {
     (buf,ntt,inverse,status) <@ AttemptResult(FreshExpand).f(seed);
     count <- count+1;
   }
   (={count,limit0} ==> ={buf,ntt,inverse,status,count,limit0})
   (limit0{1}=q{2} /\ d{2}=uniform192 /\ accept{2}=keygen_f_accept /\
     ={count} /\ 0<=count{1} ==>
    limit0{1}=q{2} /\ d{2}=uniform192 /\ accept{2}=keygen_f_accept /\
     ={count} /\ 0<=count{1} /\
     (status{1}=W64.zero <=> success{2}) /\
     (success{2} => buf{1}=buffer{2})) => //.
   - smt().
   - auto=> />; rewrite /max; smt().
   - wp; call fresh_attempt_f_equiv; call{1} uniform_seed_rng_ll; auto.
   inline AttemptResult(FreshExpand).f FreshExpand.shake; auto=> />.
   move=> &1 &2 *; rewrite keygen_f_attempt_accept /=;
     smt().
 auto=> />; rewrite /retry_initial /max /=; smt(W64.to_uint0 W64.to_uint1).
qed.

lemma fresh_bounded_g_equiv :
 equiv[BoundedRetry(UniformSeedRNG,FreshExpand).g ~ BoundedBufferRejection.run :
  limit{1}=q{2} /\ d{2}=uniform192 /\ accept{2}=keygen_g_accept ==>
  (!res{1}.`rs_ok <=> res{2}=None) /\
  (res{1}.`rs_ok => res{2}=Some res{1}.`rs_buf)].
proof.
 proc; inline BoundedRetry(UniformSeedRNG,FreshExpand).g_from; wp.
 while (limit0{1}=q{2} /\ d{2}=uniform192 /\ accept{2}=keygen_g_accept /\
   ={count} /\ 0<=count{1} /\
   (status{1}=W64.zero <=> success{2}) /\
   (success{2} => buf{1}=buffer{2})).
 + transitivity{1} {
     (buf,ntt,inverse,status) <@ AttemptResult(FreshExpand).g(seed);
     count <- count+1;
   }
   (={count,limit0} ==> ={buf,ntt,inverse,status,count,limit0})
   (limit0{1}=q{2} /\ d{2}=uniform192 /\ accept{2}=keygen_g_accept /\
     ={count} /\ 0<=count{1} ==>
    limit0{1}=q{2} /\ d{2}=uniform192 /\ accept{2}=keygen_g_accept /\
     ={count} /\ 0<=count{1} /\
     (status{1}=W64.zero <=> success{2}) /\
     (success{2} => buf{1}=buffer{2})) => //.
   - smt().
   - auto=> />; rewrite /max; smt().
   - wp; call fresh_attempt_g_equiv; call{1} uniform_seed_rng_ll; auto.
   inline AttemptResult(FreshExpand).g FreshExpand.shake; auto=> />.
   move=> &1 &2 *; rewrite keygen_g_attempt_accept /=;
     smt().
 auto=> />; rewrite /retry_initial /max /=; smt(W64.to_uint0 W64.to_uint1).
qed.

lemma fresh_bounded_f_tail q0 :
 0<=q0 =>
 phoare[BoundedRetry(UniformSeedRNG,FreshExpand).f : limit=q0 ==>
   !res.`rs_ok] = ((1%r-fresh_f_accept_mass)^q0).
proof.
 move=> hq; bypr=> &m ->; rewrite /fresh_f_accept_mass.
 rewrite -(bounded_buffer_rejection_tail &m uniform192 keygen_f_accept q0 uniform192_ll hq).
 by byequiv fresh_bounded_f_equiv; auto; smt().
qed.
lemma fresh_bounded_g_tail q0 :
 0<=q0 =>
 phoare[BoundedRetry(UniformSeedRNG,FreshExpand).g : limit=q0 ==>
   !res.`rs_ok] = ((1%r-fresh_g_accept_mass)^q0).
proof.
 move=> hq; bypr=> &m ->; rewrite /fresh_g_accept_mass.
 rewrite -(bounded_buffer_rejection_tail &m uniform192 keygen_g_accept q0 uniform192_ll hq).
 by byequiv fresh_bounded_g_equiv; auto; smt().
qed.

lemma fresh_stopped_keygen_lossless :
 islossless StoppedKeygen(UniformSeedRNG,FreshExpand).run.
proof.
 exact (stopped_keygen_lossless UniformSeedRNG FreshExpand
   uniform_seed_rng_ll fresh_expand_ll).
qed.

lemma fresh_stopped_keygen_abort qf0 qg0 :
 0<=qf0 => 0<=qg0 =>
 phoare[StoppedKeygen(UniformSeedRNG,FreshExpand).run :
   qf=qf0 /\ qg=qg0 ==> !stopped_success res] <= (fresh_retry_tail qf0 qg0).
proof.
 move=> hf hg.
 have hfb: phoare[BoundedRetry(UniformSeedRNG,FreshExpand).f : limit=qf0 ==>
   !res.`rs_ok] <= ((1%r-fresh_f_accept_mass)^qf0)
   by conseq (fresh_bounded_f_tail qf0 hf).
 have hgb: phoare[BoundedRetry(UniformSeedRNG,FreshExpand).g : limit=qg0 ==>
   !res.`rs_ok] <= ((1%r-fresh_g_accept_mass)^qg0)
   by conseq (fresh_bounded_g_tail qg0 hg).
 proc; rewrite /stopped_success /fresh_retry_tail.
 seq 3 : (!fv.`rs_ok) ((1%r-fresh_f_accept_mass)^qf0) 1%r
   1%r ((1%r-fresh_g_accept_mass)^qg0) (qg=qg0) => //.
 + by call (_:true ==> true); auto.
 + call hfb; auto.
 + rcondt 1; first by auto.
   seq 1 : (!gv.`rs_ok) ((1%r-fresh_g_accept_mass)^qg0) 1%r 1%r 0%r
     true => //.
   - call hgb; auto.
   - hoare; rcondt 1; first by auto.
     wp; call (_:true ==> true); auto.
qed.

lemma fresh_stopped_keygen_abort_probability &m qf0 qg0 workspace0 :
 0<=qf0 => 0<=qg0 =>
 Pr[StoppedKeygen(UniformSeedRNG,FreshExpand).run(qf0,qg0,workspace0) @ &m :
   !stopped_success res] <= fresh_retry_tail qf0 qg0.
proof.
 move=> hf hg; by byphoare (fresh_stopped_keygen_abort qf0 qg0 hf hg).
qed.

lemma fresh_counted_keygen_ll :
 0%r<fresh_f_accept_mass => 0%r<fresh_g_accept_mass =>
 islossless CountedKeygen(UniformSeedRNG,FreshExpand).run.
proof.
 move=> pf pg.
 conseq (counted_keygen_erasure UniformSeedRNG FreshExpand)
  (fresh_keygen_instrumented_ll pf pg); smt().
qed.
