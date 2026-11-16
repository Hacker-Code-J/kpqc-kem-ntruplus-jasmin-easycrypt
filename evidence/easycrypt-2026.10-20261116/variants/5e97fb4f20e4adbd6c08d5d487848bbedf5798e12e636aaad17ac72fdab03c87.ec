require import AllCore Distr.
from Jasmin require import JWord.
require import Array32 Array192 Array768 Array14466.
require import NTRUPlus768ROMDistributions NTRUPlus768ROMOracles.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteAttempt.
require import NTRUPlus768KeygenCompleteRetry NTRUPlus768KeygenCompleteProof.
require import NTRUPlus768KeygenCompleteFinish NTRUPlus768KeygenClearProof.
require import NTRUPlus768StoppedKeygenModel NTRUPlus768AttemptRealized.
require import NTRUPlus768BufferRejection.

module UniformSeedRNG = {
 proc sample() : W8.t Array32.t = { var seed; seed <$ uniform32; return seed; }
}.
module FreshExpand = {
 proc shake(seed:W8.t Array32.t) : W8.t Array192.t = {
  var buf; buf <$ uniform192; return buf;
 }
}.

op fresh_f_accept_mass = mu uniform192 keygen_f_accept.
op fresh_g_accept_mass = mu uniform192 keygen_g_accept.
op fresh_retry_tail (qf qg:int) =
 (1%r-fresh_f_accept_mass)^qf + (1%r-fresh_g_accept_mass)^qg.

lemma uniform_seed_rng_ll : islossless UniformSeedRNG.sample.
proof. proc; rnd; auto=> />; exact uniform32_ll. qed.
lemma fresh_expand_ll : islossless FreshExpand.shake.
proof. proc; rnd; auto=> />; exact uniform192_ll. qed.
lemma fresh_f_mass_range : 0%r <= fresh_f_accept_mass <= 1%r.
proof. exact (mu_bounded uniform192 keygen_f_accept). qed.
lemma fresh_g_mass_range : 0%r <= fresh_g_accept_mass <= 1%r.
proof. exact (mu_bounded uniform192 keygen_g_accept). qed.

lemma fresh_attempt_f_probability
 (event:(W8.t Array192.t * W16.t Array768.t * W16.t Array768.t * W64.t) -> bool) :
 phoare[KeygenAttempt(FreshExpand).f : true ==> event res] =
 (mu uniform192 (fun buf=>event(keygen_f_attempt_result buf))).
proof.
 have hs: phoare[AttemptResult(FreshExpand).f:true ==> event res] =
   (mu uniform192 (fun buf=>event(keygen_f_attempt_result buf))).
 + proc; inline FreshExpand.shake; wp; by rnd; auto.
 conseq (keygen_attempt_f_realized_equiv FreshExpand) hs; smt().
qed.
lemma fresh_attempt_g_probability
 (event:(W8.t Array192.t * W16.t Array768.t * W16.t Array768.t * W64.t) -> bool) :
 phoare[KeygenAttempt(FreshExpand).g : true ==> event res] =
 (mu uniform192 (fun buf=>event(keygen_g_attempt_result buf))).
proof.
 have hs: phoare[AttemptResult(FreshExpand).g:true ==> event res] =
   (mu uniform192 (fun buf=>event(keygen_g_attempt_result buf))).
 + proc; inline FreshExpand.shake; wp; by rnd; auto.
 conseq (keygen_attempt_g_realized_equiv FreshExpand) hs; smt().
qed.
lemma fresh_attempt_f_acceptance :
 phoare[KeygenAttempt(FreshExpand).f:true ==> res.`4=W64.zero]=fresh_f_accept_mass.
proof.
 have he: (fun buf=> (keygen_f_attempt_result buf).`4=W64.zero)=keygen_f_accept.
 + apply fun_ext=>buf; by rewrite keygen_f_attempt_accept.
 have hh:=fresh_attempt_f_probability (fun (v:W8.t Array192.t * W16.t Array768.t * W16.t Array768.t * W64.t)=>v.`4=W64.zero).
 by rewrite he in hh.
qed.
lemma fresh_attempt_g_acceptance :
 phoare[KeygenAttempt(FreshExpand).g:true ==> res.`4=W64.zero]=fresh_g_accept_mass.
proof.
 have he: (fun buf=> (keygen_g_attempt_result buf).`4=W64.zero)=keygen_g_accept.
 + apply fun_ext=>buf; by rewrite keygen_g_attempt_accept.
 have hh:=fresh_attempt_g_probability (fun (v:W8.t Array192.t * W16.t Array768.t * W16.t Array768.t * W64.t)=>v.`4=W64.zero).
 by rewrite he in hh.
qed.

lemma fresh_attempt_f_equiv :
 equiv[KeygenAttempt(FreshExpand).f ~ AttemptResult(FreshExpand).f : true ==> ={res}].
proof.
 transitivity AttemptResult(FreshExpand).f
  (={seed} ==> ={res}) (true ==> ={res}) => //.
 + smt().
 + exact (keygen_attempt_f_realized_equiv FreshExpand).
 proc; inline FreshExpand.shake; wp; rnd; auto.
qed.
lemma fresh_attempt_g_equiv :
 equiv[KeygenAttempt(FreshExpand).g ~ AttemptResult(FreshExpand).g : true ==> ={res}].
proof.
 transitivity AttemptResult(FreshExpand).g
  (={seed} ==> ={res}) (true ==> ={res}) => //.
 + smt().
 + exact (keygen_attempt_g_realized_equiv FreshExpand).
 proc; inline FreshExpand.shake; wp; rnd; auto.
qed.

module FreshRetrySpec = {
 proc f() : W8.t Array192.t * W16.t Array768.t * W16.t Array768.t = {
  var buf; var result:W8.t Array192.t * W16.t Array768.t * W16.t Array768.t * W64.t;
  buf <@ BufferRejection.flagged(uniform192,keygen_f_accept);
  result <- keygen_f_attempt_result buf; return (result.`1,result.`2,result.`3);
 }
 proc g() : W8.t Array192.t * W16.t Array768.t * W16.t Array768.t = {
  var buf; var result:W8.t Array192.t * W16.t Array768.t * W16.t Array768.t * W64.t;
  buf <@ BufferRejection.flagged(uniform192,keygen_g_accept);
  result <- keygen_g_attempt_result buf; return (result.`1,result.`2,result.`3);
 }
}.

lemma fresh_retry_f_equiv :
 equiv[KeygenRetry(UniformSeedRNG,FreshExpand).f ~ FreshRetrySpec.f : true ==> ={res}].
proof.
 proc; inline BufferRejection.flagged; wp.
 while (d{2}=uniform192 /\ accept{2}=keygen_f_accept /\
  (status{1}=W64.zero <=> success{2}) /\
  (success{2} => (buf{1},ntt{1},inverse{1})=
   ((keygen_f_attempt_result buffer{2}).`1,(keygen_f_attempt_result buffer{2}).`2,
    (keygen_f_attempt_result buffer{2}).`3))).
 + transitivity{1} { (buf,ntt,inverse,status) <@ AttemptResult(FreshExpand).f(seed); }
    (true ==> ={buf,ntt,inverse,status})
    (d{2}=uniform192 /\ accept{2}=keygen_f_accept ==>
     d{2}=uniform192 /\ accept{2}=keygen_f_accept /\
     (status{1}=W64.zero <=> success{2}) /\
     (success{2} => (buf{1},ntt{1},inverse{1})=
      ((keygen_f_attempt_result buffer{2}).`1,(keygen_f_attempt_result buffer{2}).`2,
       (keygen_f_attempt_result buffer{2}).`3))) => //.
   - call fresh_attempt_f_equiv.
     call{1} uniform_seed_rng_ll; auto.
   inline AttemptResult(FreshExpand).f FreshExpand.shake; auto=> />.
   by move=> buf _; rewrite keygen_f_attempt_accept.
 auto=> />; smt(W64.to_uint0 W64.to_uint1).
qed.

lemma fresh_retry_g_equiv :
 equiv[KeygenRetry(UniformSeedRNG,FreshExpand).g ~ FreshRetrySpec.g : true ==> ={res}].
proof.
 proc; inline BufferRejection.flagged; wp.
 while (d{2}=uniform192 /\ accept{2}=keygen_g_accept /\
  (status{1}=W64.zero <=> success{2}) /\
  (success{2} => (buf{1},ntt{1},inverse{1})=
   ((keygen_g_attempt_result buffer{2}).`1,(keygen_g_attempt_result buffer{2}).`2,
    (keygen_g_attempt_result buffer{2}).`3))).
 + transitivity{1} { (buf,ntt,inverse,status) <@ AttemptResult(FreshExpand).g(seed); }
    (true ==> ={buf,ntt,inverse,status})
    (d{2}=uniform192 /\ accept{2}=keygen_g_accept ==>
     d{2}=uniform192 /\ accept{2}=keygen_g_accept /\
     (status{1}=W64.zero <=> success{2}) /\
     (success{2} => (buf{1},ntt{1},inverse{1})=
      ((keygen_g_attempt_result buffer{2}).`1,(keygen_g_attempt_result buffer{2}).`2,
       (keygen_g_attempt_result buffer{2}).`3))) => //.
   - call fresh_attempt_g_equiv.
     call{1} uniform_seed_rng_ll; auto.
   inline AttemptResult(FreshExpand).g FreshExpand.shake; auto=> />.
   by move=> buf _; rewrite keygen_g_attempt_accept.
 auto=> />; smt(W64.to_uint0 W64.to_uint1).
qed.

lemma fresh_retry_f_probability
 (event:(W8.t Array192.t * W16.t Array768.t * W16.t Array768.t) -> bool) :
 phoare[KeygenRetry(UniformSeedRNG,FreshExpand).f : true ==> event res] =
 (mu (dcond uniform192 keygen_f_accept)
   (fun buf=>event((keygen_f_attempt_result buf).`1,
     (keygen_f_attempt_result buf).`2,(keygen_f_attempt_result buf).`3))).
proof.
 have hs: phoare[FreshRetrySpec.f:true ==> event res] =
 (mu (dcond uniform192 keygen_f_accept)
   (fun buf=>event((keygen_f_attempt_result buf).`1,
     (keygen_f_attempt_result buf).`2,(keygen_f_attempt_result buf).`3))).
 + proc; wp; call (buffer_rejection_flagged_probability uniform192 keygen_f_accept
   (fun buf=>event((keygen_f_attempt_result buf).`1,
     (keygen_f_attempt_result buf).`2,(keygen_f_attempt_result buf).`3)) uniform192_ll).
   auto.
 by conseq fresh_retry_f_equiv hs.
qed.
lemma fresh_retry_g_probability
 (event:(W8.t Array192.t * W16.t Array768.t * W16.t Array768.t) -> bool) :
 phoare[KeygenRetry(UniformSeedRNG,FreshExpand).g : true ==> event res] =
 (mu (dcond uniform192 keygen_g_accept)
   (fun buf=>event((keygen_g_attempt_result buf).`1,
     (keygen_g_attempt_result buf).`2,(keygen_g_attempt_result buf).`3))).
proof.
 have hs: phoare[FreshRetrySpec.g:true ==> event res] =
 (mu (dcond uniform192 keygen_g_accept)
   (fun buf=>event((keygen_g_attempt_result buf).`1,
     (keygen_g_attempt_result buf).`2,(keygen_g_attempt_result buf).`3))).
 + proc; wp; call (buffer_rejection_flagged_probability uniform192 keygen_g_accept
   (fun buf=>event((keygen_g_attempt_result buf).`1,
     (keygen_g_attempt_result buf).`2,(keygen_g_attempt_result buf).`3)) uniform192_ll).
   auto.
 by conseq fresh_retry_g_equiv hs.
qed.
lemma fresh_retry_f_ll :
 0%r < fresh_f_accept_mass => islossless KeygenRetry(UniformSeedRNG,FreshExpand).f.
proof.
 move=> hp; have hll:=dcond_ll uniform192 keygen_f_accept hp.
 conseq (fresh_retry_f_probability predT) => />; exact hll.
qed.
lemma fresh_retry_g_ll :
 0%r < fresh_g_accept_mass => islossless KeygenRetry(UniformSeedRNG,FreshExpand).g.
proof.
 move=> hp; have hll:=dcond_ll uniform192 keygen_g_accept hp.
 conseq (fresh_retry_g_probability predT) => />; exact hll.
qed.
lemma fresh_keygen_instrumented_ll :
 0%r < fresh_f_accept_mass => 0%r < fresh_g_accept_mass =>
 islossless KeygenInstrumented(UniformSeedRNG,FreshExpand,SHAKEFROM).run.
proof.
 move=> pf pg; proc.
 call keygen_clear_lossless; call(keygen_finish_lossless SHAKEFROM ro_f_shake_ll).
 call(fresh_retry_g_ll pg); call(fresh_retry_f_ll pf); auto.
qed.
lemma fresh_keygen_ll :
 0%r < fresh_f_accept_mass => 0%r < fresh_g_accept_mass =>
 islossless Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run.
proof.
 move=> pf pg; proc; call(fresh_keygen_instrumented_ll pf pg); auto.
qed.

(* Acceptance conditions the whole buffer.  No coefficient independence
   after that conditioning is asserted. *)
lemma fresh_retry_f_buffer_law (event:W8.t Array192.t -> bool) :
 phoare[KeygenRetry(UniformSeedRNG,FreshExpand).f : true ==> event res.`1] =
 (mu (dcond uniform192 keygen_f_accept) event).
proof.
 conseq (fresh_retry_f_probability
  (fun (v:W8.t Array192.t * W16.t Array768.t * W16.t Array768.t)=>event v.`1)) => />.
qed.
lemma fresh_retry_g_buffer_law (event:W8.t Array192.t -> bool) :
 phoare[KeygenRetry(UniformSeedRNG,FreshExpand).g : true ==> event res.`1] =
 (mu (dcond uniform192 keygen_g_accept) event).
proof.
 conseq (fresh_retry_g_probability
  (fun (v:W8.t Array192.t * W16.t Array768.t * W16.t Array768.t)=>event v.`1)) => />.
qed.
