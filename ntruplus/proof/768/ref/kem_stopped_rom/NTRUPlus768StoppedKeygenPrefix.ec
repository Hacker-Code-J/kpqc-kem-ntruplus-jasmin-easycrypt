require import AllCore Distr.
from Jasmin require import JWord.
require import Array32 Array192 Array768 Array1152 Array2336 Array14466.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteAttempt.
require import NTRUPlus768KeygenCompleteRetry NTRUPlus768KeygenCompleteFinish NTRUPlus768KeygenCompleteProof.
require import NTRUPlus768KeygenClear NTRUPlus768KeygenClearProof.
require import NTRUPlus768EncapCompleteHash NTRUPlus768ROMOracles.
require import NTRUPlus768StoppedKeygenModel.

lemma bounded_f_from_count (R<:KeygenSeedRNG) (E<:KeygenExpand) c q :
 hoare[BoundedRetry(R,E).f_from : start.`rs_count=c /\ limit=q ==>
 c <= res.`rs_count <= max c (max 0 q) /\
 (!res.`rs_ok => max 0 q <= res.`rs_count)].
proof.
 proc; while(c <= count <= max c (max 0 q) /\ limit=q).
 + wp; call(keygen_attempt_f_accepted E); call (_:true ==> true); auto => />; smt().
 auto => />; smt().
qed.
lemma bounded_g_from_count (R<:KeygenSeedRNG) (E<:KeygenExpand) c q :
 hoare[BoundedRetry(R,E).g_from : start.`rs_count=c /\ limit=q ==>
 c <= res.`rs_count <= max c (max 0 q) /\
 (!res.`rs_ok => max 0 q <= res.`rs_count)].
proof.
 proc; while(c <= count <= max c (max 0 q) /\ limit=q).
 + wp; call(keygen_attempt_g_accepted E); call (_:true ==> true); auto => />; smt().
 auto => />; smt().
qed.
lemma bounded_f_count (R<:KeygenSeedRNG) (E<:KeygenExpand) q :
 hoare[BoundedRetry(R,E).f : limit=q ==>
 0 <= res.`rs_count <= max 0 q /\ (!res.`rs_ok => res.`rs_count=max 0 q)].
proof.
 proc; call(bounded_f_from_count R E 0 q); auto => />;
 rewrite /retry_initial /=; smt().
qed.
lemma bounded_g_count (R<:KeygenSeedRNG) (E<:KeygenExpand) q :
 hoare[BoundedRetry(R,E).g : limit=q ==>
 0 <= res.`rs_count <= max 0 q /\ (!res.`rs_ok => res.`rs_count=max 0 q)].
proof.
 proc; call(bounded_g_from_count R E 0 q); auto => />;
 rewrite /retry_initial /=; smt().
qed.
lemma counted_f_from_count (R<:KeygenSeedRNG) (E<:KeygenExpand) c :
 hoare[CountedRetry(R,E).f_from : start.`rs_count=c ==>
 c <= res.`rs_count /\ res.`rs_ok].
proof.
 proc; while(c <= count).
 + wp; call(keygen_attempt_f_accepted E); call (_:true ==> true); auto => />; smt().
 auto => />; smt().
qed.
lemma counted_g_from_count (R<:KeygenSeedRNG) (E<:KeygenExpand) c :
 hoare[CountedRetry(R,E).g_from : start.`rs_count=c ==>
 c <= res.`rs_count /\ res.`rs_ok].
proof.
 proc; while(c <= count).
 + wp; call(keygen_attempt_g_accepted E); call (_:true ==> true); auto => />; smt().
 auto => />; smt().
qed.

lemma bounded_f_from_lossless (R<:KeygenSeedRNG) (E<:KeygenExpand) :
 islossless R.sample => islossless E.shake =>
 islossless BoundedRetry(R,E).f_from.
proof.
 move=> hR hE; proc.
 while true (max 0 limit-count).
 + move=> z; wp; call(keygen_attempt_f_lossless E hE); call hR; auto => />; smt().
 auto => />; smt().
qed.
lemma bounded_g_from_lossless (R<:KeygenSeedRNG) (E<:KeygenExpand) :
 islossless R.sample => islossless E.shake =>
 islossless BoundedRetry(R,E).g_from.
proof.
 move=> hR hE; proc.
 while true (max 0 limit-count).
 + move=> z; wp; call(keygen_attempt_g_lossless E hE); call hR; auto => />; smt().
 auto => />; smt().
qed.
lemma bounded_f_lossless (R<:KeygenSeedRNG) (E<:KeygenExpand) :
 islossless R.sample => islossless E.shake => islossless BoundedRetry(R,E).f.
proof. move=> hR hE; proc; call(bounded_f_from_lossless R E hR hE); auto. qed.
lemma bounded_g_lossless (R<:KeygenSeedRNG) (E<:KeygenExpand) :
 islossless R.sample => islossless E.shake => islossless BoundedRetry(R,E).g.
proof. move=> hR hE; proc; call(bounded_g_from_lossless R E hR hE); auto. qed.

lemma counted_f_erasure (R<:KeygenSeedRNG) (E<:KeygenExpand {-R}) :
 equiv[CountedRetry(R,E).f ~ KeygenRetry(R,E).f : ={glob R,glob E} ==>
 (res.`rs_buf,res.`rs_ntt,res.`rs_inv){1}=res{2} /\ ={glob R,glob E}].
proof.
 proc; inline CountedRetry(R,E).f_from; wp.
 while(={buf,ntt,inverse,status,glob R,glob E}).
 + wp; sim.
 by auto => />; rewrite /retry_initial /=.
qed.
lemma counted_g_erasure (R<:KeygenSeedRNG) (E<:KeygenExpand {-R}) :
 equiv[CountedRetry(R,E).g ~ KeygenRetry(R,E).g : ={glob R,glob E} ==>
 (res.`rs_buf,res.`rs_ntt,res.`rs_inv){1}=res{2} /\ ={glob R,glob E}].
proof.
 proc; inline CountedRetry(R,E).g_from; wp.
 while(={buf,ntt,inverse,status,glob R,glob E}).
 + wp; sim.
 by auto => />; rewrite /retry_initial /=.
qed.
lemma counted_keygen_erasure (R<:KeygenSeedRNG {-ROF}) (E<:KeygenExpand {-ROF,-R}) :
 equiv[CountedKeygen(R,E).run ~ KeygenInstrumented(R,E,SHAKEFROM).run :
 ={workspace,glob R,glob E,glob ROF} ==>
 res.`1{1}=res{2} /\ ={glob R,glob E,glob ROF}].
proof.
 proc; inline ObservedFinish.run; wp.
 call (_:true); first by sim.
 call (_: ={glob ROF}); first by sim.
 wp; call(counted_g_erasure R E); call(counted_f_erasure R E); auto => />.
qed.

lemma observed_finish_lossless : islossless ObservedFinish.run.
proof.
 proc; call keygen_clear_lossless;
 call(keygen_finish_lossless SHAKEFROM ro_f_shake_ll); auto.
qed.
lemma stopped_keygen_lossless (R<:KeygenSeedRNG) (E<:KeygenExpand) :
 islossless R.sample => islossless E.shake => islossless StoppedKeygen(R,E).run.
proof.
 move=> hR hE; proc.
 seq 3 : true; 1,4,5: by auto.
 + call(bounded_f_lossless R E hR hE); auto.
 if; last by auto.
 seq 1 : true; 1,4,5: by auto.
 + call(bounded_g_lossless R E hR hE); auto.
 if; last by auto.
 wp; call observed_finish_lossless; auto.
qed.

lemma counted_f_split (R<:KeygenSeedRNG) (E<:KeygenExpand {-R}) q :
 equiv[CountedRetry(R,E).f ~ SplitRetry(R,E).f :
 ={glob R,glob E} /\ limit{2}=q ==> ={res,glob R,glob E}].
proof.
 proc; inline CountedRetry(R,E).f_from BoundedRetry(R,E).f BoundedRetry(R,E).f_from.
 splitwhile{1} 7 : (count < max 0 q).
 seq 7 9 : (buf{1}=buf0{2} /\ ntt{1}=ntt0{2} /\ inverse{1}=inverse0{2} /\ count{1}=count0{2} /\
   ={glob R,glob E} /\ status{1}=status0{2}).
 + while(buf{1}=buf0{2} /\ ntt{1}=ntt0{2} /\ inverse{1}=inverse0{2} /\ count{1}=count0{2} /\
     ={glob R,glob E} /\ status{1}=status0{2} /\ limit1{2}=q).
   - wp; call (_: ={glob E}); first by sim.
     call (_:true); auto => />; smt().
   by auto => />; rewrite /retry_initial /=.
 wp; while(={buf,ntt,inverse,count,glob R,glob E} /\
   (status{1}=W64.zero)=(status{2}=W64.zero)).
 + wp; call (_: ={glob E}); first by sim.
     call (_:true); auto => />; smt().
 auto => />; smt(W64.to_uint0 W64.to_uint1).
qed.
lemma counted_g_split (R<:KeygenSeedRNG) (E<:KeygenExpand {-R}) q :
 equiv[CountedRetry(R,E).g ~ SplitRetry(R,E).g :
 ={glob R,glob E} /\ limit{2}=q ==> ={res,glob R,glob E}].
proof.
 proc; inline CountedRetry(R,E).g_from BoundedRetry(R,E).g BoundedRetry(R,E).g_from.
 splitwhile{1} 7 : (count < max 0 q).
 seq 7 9 : (buf{1}=buf0{2} /\ ntt{1}=ntt0{2} /\ inverse{1}=inverse0{2} /\ count{1}=count0{2} /\
   ={glob R,glob E} /\ status{1}=status0{2}).
 + while(buf{1}=buf0{2} /\ ntt{1}=ntt0{2} /\ inverse{1}=inverse0{2} /\ count{1}=count0{2} /\
     ={glob R,glob E} /\ status{1}=status0{2} /\ limit1{2}=q).
   - wp; call (_: ={glob E}); first by sim.
     call (_:true); auto => />; smt().
   by auto => />; rewrite /retry_initial /=.
 wp; while(={buf,ntt,inverse,count,glob R,glob E} /\
   (status{1}=W64.zero)=(status{2}=W64.zero)).
 + wp; call (_: ={glob E}); first by sim.
     call (_:true); auto => />; smt().
 auto => />; smt(W64.to_uint0 W64.to_uint1).
qed.

lemma counted_f_from_failed (R<:KeygenSeedRNG) (E<:KeygenExpand) c :
 hoare[CountedRetry(R,E).f_from : !start.`rs_ok /\ start.`rs_count=c ==>
 c < res.`rs_count /\ res.`rs_ok].
proof.
 proc; while(c <= count /\ (count=c => status<>W64.zero)).
 + wp; call(keygen_attempt_f_accepted E); call (_:true ==> true); auto => />; smt().
 auto => />; smt(W64.to_uint0 W64.to_uint1).
qed.
lemma counted_g_from_failed (R<:KeygenSeedRNG) (E<:KeygenExpand) c :
 hoare[CountedRetry(R,E).g_from : !start.`rs_ok /\ start.`rs_count=c ==>
 c < res.`rs_count /\ res.`rs_ok].
proof.
 proc; while(c <= count /\ (count=c => status<>W64.zero)).
 + wp; call(keygen_attempt_g_accepted E); call (_:true ==> true); auto => />; smt().
 auto => />; smt(W64.to_uint0 W64.to_uint1).
qed.
lemma counted_f_from_done (R<:KeygenSeedRNG) (E<:KeygenExpand) s :
 hoare[CountedRetry(R,E).f_from : start=s /\ s.`rs_ok ==> res=s].
proof. proc; rcondf 6; auto => />; smt(). qed.
lemma counted_g_from_done (R<:KeygenSeedRNG) (E<:KeygenExpand) s :
 hoare[CountedRetry(R,E).g_from : start=s /\ s.`rs_ok ==> res=s].
proof. proc; rcondf 6; auto => />; smt(). qed.

lemma resumed_prefix_upto (R<:KeygenSeedRNG {-PrefixBad})
 (E<:KeygenExpand {-PrefixBad,-R}) (qf qg:int) (w:W8.t Array14466.t)
 (event:keygen_output -> bool) &m :
 Pr[ResumedKeygen(R,E).run(qf,qg,w) @ &m : event res.`1 /\ !PrefixBad.bad] =
 Pr[PrefixOnlyKeygen(R,E).run(qf,qg,w) @ &m : event res.`1 /\ !PrefixBad.bad].
proof. byupto. qed.

lemma resumed_counted_within (R<:KeygenSeedRNG {-PrefixBad})
 (E<:KeygenExpand {-PrefixBad}) qf0 qg0 :
 hoare[ResumedKeygen(R,E).run : qf=qf0 /\ qg=qg0 ==>
 counted_within qf0 qg0 res = !PrefixBad.bad].
proof.
 proc; call (_:true ==> true); first by trivial.
 seq 3 : (qf=qf0 /\ qg=qg0 /\
   (PrefixBad.bad <=> max 0 qf0 < fv.`rs_count)).
 + seq 2 : (qf=qf0 /\ qg=qg0 /\ !PrefixBad.bad /\
     0<=fv.`rs_count<=max 0 qf0 /\ (!fv.`rs_ok => fv.`rs_count=max 0 qf0)).
   - call(bounded_f_count R E qf0); auto => />.
   if.
   - ecall(counted_f_from_failed R E fv.`rs_count); auto => />; smt().
   auto => />; smt().
 seq 1 : (qg=qg0 /\ (PrefixBad.bad <=> max 0 qf0 < fv.`rs_count) /\
   0<=gv.`rs_count<=max 0 qg0 /\ (!gv.`rs_ok => gv.`rs_count=max 0 qg0)).
 + call(bounded_g_count R E qg0); auto => />.
 if.
 + ecall(counted_g_from_failed R E gv.`rs_count); auto => />;
   rewrite /counted_within /=; smt().
 auto => />; rewrite /counted_within /=; smt().
qed.

lemma counted_keygen_split (R<:KeygenSeedRNG {-ROF}) (E<:KeygenExpand {-ROF,-R}) qf0 qg0 :
 equiv[CountedKeygen(R,E).run ~ SplitKeygen(R,E).run :
 ={workspace,glob R,glob E,glob ROF} /\ qf{2}=qf0 /\ qg{2}=qg0 ==>
 ={res,glob R,glob E,glob ROF}].
proof.
 proc; call (_: ={glob ROF}); first by sim.
 call(counted_g_split R E qg0); call(counted_f_split R E qf0); auto => />.
qed.
lemma split_keygen_resumed (R<:KeygenSeedRNG {-ROF,-PrefixBad})
 (E<:KeygenExpand {-ROF,-PrefixBad,-R}) :
 equiv[SplitKeygen(R,E).run ~ ResumedKeygen(R,E).run :
 ={qf,qg,workspace,glob R,glob E,glob ROF} ==>
 ={res,glob R,glob E,glob ROF}].
proof.
 proc; call (_: ={glob ROF}); first by sim.
 seq 1 3 : (={fv,qg,workspace,glob R,glob E,glob ROF}).
 + inline SplitRetry(R,E).f; sp.
   seq 1 1 : (v{1}=fv{2} /\ ={qg,workspace,glob R,glob E,glob ROF}).
   - call (_: ={glob R,glob E}); first by sim.
     auto => />.
   if{2}.
   - wp; call (_: ={glob R,glob E}); first by sim.
     auto => />.
   inline CountedRetry(R,E).f_from.
   rcondf{1} 7; first by auto => />.
   auto => />; smt().
 inline SplitRetry(R,E).g; sp.
 seq 1 1 : (v{1}=gv{2} /\ ={fv,workspace,glob R,glob E,glob ROF}).
 + call (_: ={glob R,glob E}); first by sim.
   auto => />.
 if{2}.
 + wp; call (_: ={glob R,glob E}); first by sim.
   auto => />.
 inline CountedRetry(R,E).g_from.
 rcondf{1} 7; first by auto => />.
 auto => />; smt().
qed.

lemma prefix_only_stopped_event (R<:KeygenSeedRNG {-ROF,-PrefixBad})
 (E<:KeygenExpand {-ROF,-PrefixBad,-R}) (event:keygen_output -> bool) :
 islossless R.sample => islossless E.shake =>
 equiv[PrefixOnlyKeygen(R,E).run ~ StoppedKeygen(R,E).run :
 ={qf,qg,workspace,glob R,glob E,glob ROF} ==>
 (event res.`1{1} /\ !PrefixBad.bad{1}) = stopped_event event res{2}].
proof.
 move=> hR hE; proc.
 seq 2 3 : (={fv,qg,workspace,glob R,glob E,glob ROF} /\
   !PrefixBad.bad{1} /\ result{2}=None).
 + call (_: ={glob R,glob E}); first by sim.
   auto => />.
 if{2}.
 + rcondf{1} 1; first by auto => />.
   seq 1 1 : (={fv,gv,workspace,glob R,glob E,glob ROF} /\
     !PrefixBad.bad{1} /\ result{2}=None).
   - call (_: ={glob R,glob E}); first by sim.
     auto => />.
   if{2}.
   - rcondf{1} 1; first by auto => />.
     wp; call (_: ={glob ROF}); first by sim.
     by auto => />; rewrite /stopped_event /=.
   rcondt{1} 1; first by auto => />.
   call{1} observed_finish_lossless; by auto => />; rewrite /stopped_event /=.
 rcondt{1} 1; first by auto => />.
 seq 2 0 : (PrefixBad.bad{1} /\ result{2}=None).
 + call{1}(bounded_g_lossless R E hR hE); auto => />.
 call{1} observed_finish_lossless; if{1}; by auto => />; rewrite /stopped_event /=.
qed.

(* Exact subdistribution equality: the unrestricted loops may diverge after
   the bad latch has been set. Only bounded attempts and finish need be LL. *)
lemma counted_stopped_prefix (R<:KeygenSeedRNG {-ROF,-PrefixBad})
 (E<:KeygenExpand {-ROF,-PrefixBad,-R}) (qf0 qg0:int)
 (w:W8.t Array14466.t) (event:keygen_output -> bool) &m :
 islossless R.sample => islossless E.shake =>
 Pr[CountedKeygen(R,E).run(w) @ &m : counted_within qf0 qg0 res /\ event res.`1] =
 Pr[StoppedKeygen(R,E).run(qf0,qg0,w) @ &m : stopped_event event res].
proof.
 move=> hR hE.
 have h1 : Pr[CountedKeygen(R,E).run(w) @ &m : counted_within qf0 qg0 res /\ event res.`1] =
   Pr[SplitKeygen(R,E).run(qf0,qg0,w) @ &m : counted_within qf0 qg0 res /\ event res.`1].
 + by byequiv (counted_keygen_split R E qf0 qg0) => //.
 have h2 : Pr[SplitKeygen(R,E).run(qf0,qg0,w) @ &m : counted_within qf0 qg0 res /\ event res.`1] =
   Pr[ResumedKeygen(R,E).run(qf0,qg0,w) @ &m : counted_within qf0 qg0 res /\ event res.`1].
 + by byequiv (split_keygen_resumed R E) => //.
 have h3 : Pr[ResumedKeygen(R,E).run(qf0,qg0,w) @ &m : counted_within qf0 qg0 res /\ event res.`1] =
   Pr[ResumedKeygen(R,E).run(qf0,qg0,w) @ &m : event res.`1 /\ !PrefixBad.bad].
 + byequiv (_: ={qf,qg,workspace,glob R,glob E,glob ROF} /\ qf{2}=qf0 /\ qg{2}=qg0 ==>
     ={res,PrefixBad.bad} /\ counted_within qf0 qg0 res{2}=!PrefixBad.bad{2}) => //; last by smt().
   conseq (_: ={qf,qg,workspace,glob R,glob E,glob ROF} ==> ={res,PrefixBad.bad})
     _ (resumed_counted_within R E qf0 qg0) => //.
   proc; sim.
 have h4 := resumed_prefix_upto R E qf0 qg0 w event &m.
 have h5 : Pr[PrefixOnlyKeygen(R,E).run(qf0,qg0,w) @ &m : event res.`1 /\ !PrefixBad.bad] =
   Pr[StoppedKeygen(R,E).run(qf0,qg0,w) @ &m : stopped_event event res].
 + by byequiv (prefix_only_stopped_event R E event hR hE) => //; smt().
 by rewrite h1 h2 h3 h4 h5.
qed.

lemma counted_stopped_prefix_nonnegative (R<:KeygenSeedRNG {-ROF,-PrefixBad})
 (E<:KeygenExpand {-ROF,-PrefixBad,-R}) (qf0 qg0:int)
 (w:W8.t Array14466.t) (event:keygen_output -> bool) &m :
 0<=qf0 => 0<=qg0 => islossless R.sample => islossless E.shake =>
 Pr[CountedKeygen(R,E).run(w) @ &m : (res.`2<=qf0 /\ res.`3<=qg0) /\ event res.`1] =
 Pr[StoppedKeygen(R,E).run(qf0,qg0,w) @ &m : res.`1<>None /\ event (oget res.`1)].
proof.
 move=> hqf hqg hR hE.
 have h := counted_stopped_prefix R E qf0 qg0 w event &m hR hE.
 rewrite /counted_within /stopped_event in h.
 rewrite -h.
 by rewrite Pr[mu_eq] => />; smt().
qed.
