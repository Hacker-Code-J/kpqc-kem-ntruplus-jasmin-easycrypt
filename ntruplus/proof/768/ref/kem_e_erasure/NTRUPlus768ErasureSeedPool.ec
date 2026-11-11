require import AllCore List Distr DList FMap.
from Jasmin require import JWord.
require import Array32 Array192 Array14466.
require import NTRUPlus768ErasureModel NTRUPlus768ROMDistributions NTRUPlus768ROMOracles.
require import NTRUPlus768FreshRetryLaw NTRUPlus768StoppedKeygenModel NTRUPlus768StoppedKeygenPrefix.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768AttemptRealized.
require import NTRUPlus768ProposalKeygenBridge.
require import NTRUPlus768CCASetupState.

lemma erasure_take_step (xs:erasure_seed list) i : 0<=i<size xs =>
 rev(take(i+1)xs)=nth witness xs i::rev(take i xs).
proof. move=>hi; by rewrite(take_nth witness i xs hi) rev_rcons. qed.

lemma erasure_fixed_result_f xs c q0 :
 equiv[ResultRetry(ErasureSeedPool,LoggedErasedExpand).f ~
       ResultRetry(UniformSeedRNG,FreshExpand).f :
 ={limit} /\ limit{1}=q0 /\ 0<=c /\ 0<=q0 /\ c+q0<=size xs /\
 ErasureSeedPool.seeds{1}=xs /\ ErasureSeedPool.cursor{1}=c /\
 ErasureSeedLog.used{1}=rev(take c xs) ==>
 ={res} /\ ErasureSeedPool.seeds{1}=xs /\
 ErasureSeedPool.cursor{1}=c+res.`rs_count{1} /\
 ErasureSeedLog.used{1}=rev(take(c+res.`rs_count{1})xs) /\
 0<=res.`rs_count{1}<=q0].
proof.
 proc.
 while(={limit,buf,ntt,inverse,status,count} /\ limit{1}=q0 /\
  0<=c /\ 0<=q0 /\ c+q0<=size xs /\ 0<=count{1}<=q0 /\
  ErasureSeedPool.seeds{1}=xs /\ ErasureSeedPool.cursor{1}=c+count{1} /\
  ErasureSeedLog.used{1}=rev(take(c+count{1})xs)).
 + inline AttemptResult(LoggedErasedExpand).f AttemptResult(FreshExpand).f.
   inline ErasureSeedPool.sample LoggedErasedExpand.shake UniformSeedRNG.sample FreshExpand.shake.
   wp; rnd; wp; rnd{2}; auto=> />.
   move=> &2 hc hq hsz hcount0 hcount1 hstatus hbound.
   have hcq:count{2}<q0 by move:hbound; rewrite /max; smt().
   have hi:0<=c+count{2}<size xs by smt().
   have ht:=erasure_take_step xs (c+count{2}) hi.
   rewrite uniform32_ll /=.
   smt().
 auto=> />; smt().
qed.

lemma erasure_fixed_result_g xs c q0 :
 equiv[ResultRetry(ErasureSeedPool,LoggedErasedExpand).g ~
       ResultRetry(UniformSeedRNG,FreshExpand).g :
 ={limit} /\ limit{1}=q0 /\ 0<=c /\ 0<=q0 /\ c+q0<=size xs /\
 ErasureSeedPool.seeds{1}=xs /\ ErasureSeedPool.cursor{1}=c /\
 ErasureSeedLog.used{1}=rev(take c xs) ==>
 ={res} /\ ErasureSeedPool.seeds{1}=xs /\
 ErasureSeedPool.cursor{1}=c+res.`rs_count{1} /\
 ErasureSeedLog.used{1}=rev(take(c+res.`rs_count{1})xs) /\
 0<=res.`rs_count{1}<=q0].
proof.
 proc.
 while(={limit,buf,ntt,inverse,status,count} /\ limit{1}=q0 /\
  0<=c /\ 0<=q0 /\ c+q0<=size xs /\ 0<=count{1}<=q0 /\
  ErasureSeedPool.seeds{1}=xs /\ ErasureSeedPool.cursor{1}=c+count{1} /\
  ErasureSeedLog.used{1}=rev(take(c+count{1})xs)).
 + inline AttemptResult(LoggedErasedExpand).g AttemptResult(FreshExpand).g.
   inline ErasureSeedPool.sample LoggedErasedExpand.shake UniformSeedRNG.sample FreshExpand.shake.
   wp; rnd; wp; rnd{2}; auto=> />.
   move=> &2 hc hq hsz hcount0 hcount1 hstatus hbound.
   have hcq:count{2}<q0 by move:hbound; rewrite /max; smt().
   have hi:0<=c+count{2}<size xs by smt().
   have ht:=erasure_take_step xs (c+count{2}) hi.
   rewrite uniform32_ll /=.
   smt().
 auto=> />; smt().
qed.

lemma erasure_fixed_result_stopped xs qf0 qg0 :
 equiv[ResultStoppedKeygen(ErasureSeedPool,LoggedErasedExpand).run ~
       ResultStoppedKeygen(UniformSeedRNG,FreshExpand).run :
 ={qf,qg,workspace,glob ROF} /\ qf{1}=qf0 /\ qg{1}=qg0 /\ 0<=qf{1} /\ 0<=qg{1} /\ qf{1}+qg{1}<=size xs /\
 ErasureSeedPool.seeds{1}=xs /\ ErasureSeedPool.cursor{1}=0 /\ ErasureSeedLog.used{1}=[] ==>
 ={res,glob ROF} /\ ErasureSeedPool.seeds{1}=xs /\
 ErasureSeedPool.cursor{1}=res.`2{1}+res.`3{1} /\
 ErasureSeedLog.used{1}=rev(take(res.`2{1}+res.`3{1})xs) /\
 0<=res.`2{1}+res.`3{1}<=qf0+qg0].
proof.
 proc.
 seq 3 3:(={qf,qg,workspace,fv,gv,result,glob ROF} /\ gv{1}=retry_initial /\
  qf{1}=qf0 /\ qg{1}=qg0 /\ 0<=qf{1} /\ 0<=qg{1} /\ qf{1}+qg{1}<=size xs /\
  ErasureSeedPool.seeds{1}=xs /\ ErasureSeedPool.cursor{1}=fv.`rs_count{1} /\
  ErasureSeedLog.used{1}=rev(take fv.`rs_count{1} xs) /\ 0<=fv.`rs_count{1}<=qf{1}).
 + ecall(erasure_fixed_result_f xs 0 qf{1}); auto=> />; rewrite take0 /=; smt().
 if; first by auto.
 + seq 1 1:(={qf,qg,workspace,fv,gv,result,glob ROF} /\
    ErasureSeedPool.seeds{1}=xs /\ ErasureSeedPool.cursor{1}=fv.`rs_count{1}+gv.`rs_count{1} /\
    ErasureSeedLog.used{1}=rev(take(fv.`rs_count{1}+gv.`rs_count{1})xs) /\
    0<=fv.`rs_count{1}+gv.`rs_count{1}<=qf0+qg0).
   - ecall(erasure_fixed_result_g xs fv.`rs_count{1} qg{1}); auto=> />; smt().
   if; 1,3:by auto.
   wp; call (_: ={fv,gv,workspace,glob ROF} ==> ={res,glob ROF}); first by sim.
   auto.
 auto=> />; rewrite /retry_initial /=; smt().
qed.

lemma erasure_fixed_stopped xs qf0 qg0 :
 equiv[StoppedKeygen(ErasureSeedPool,LoggedErasedExpand).run ~
       StoppedKeygen(UniformSeedRNG,FreshExpand).run :
 ={qf,qg,workspace,glob ROF} /\ qf{1}=qf0 /\ qg{1}=qg0 /\ 0<=qf{1} /\ 0<=qg{1} /\ qf{1}+qg{1}<=size xs /\
 ErasureSeedPool.seeds{1}=xs /\ ErasureSeedPool.cursor{1}=0 /\ ErasureSeedLog.used{1}=[] ==>
 ={res,glob ROF} /\ ErasureSeedPool.seeds{1}=xs /\
 ErasureSeedPool.cursor{1}=res.`2{1}+res.`3{1} /\
 ErasureSeedLog.used{1}=rev(take(res.`2{1}+res.`3{1})xs) /\
 0<=res.`2{1}+res.`3{1}<=qf0+qg0].
proof.
 transitivity ResultStoppedKeygen(ErasureSeedPool,LoggedErasedExpand).run
  (={qf,qg,workspace,glob ROF,glob ErasureSeedPool,glob ErasureSeedLog} ==>
   ={res,glob ROF,glob ErasureSeedPool,glob ErasureSeedLog})
  (={qf,qg,workspace,glob ROF} /\ qf{1}=qf0 /\ qg{1}=qg0 /\ 0<=qf{1} /\ 0<=qg{1} /\ qf{1}+qg{1}<=size xs /\
   ErasureSeedPool.seeds{1}=xs /\ ErasureSeedPool.cursor{1}=0 /\ ErasureSeedLog.used{1}=[] ==>
   ={res,glob ROF} /\ ErasureSeedPool.seeds{1}=xs /\
   ErasureSeedPool.cursor{1}=res.`2{1}+res.`3{1} /\
   ErasureSeedLog.used{1}=rev(take(res.`2{1}+res.`3{1})xs) /\
   0<=res.`2{1}+res.`3{1}<=qf0+qg0)=> //.
 + smt().
 + conseq(stopped_result_equiv ErasureSeedPool LoggedErasedExpand); smt().
 transitivity ResultStoppedKeygen(UniformSeedRNG,FreshExpand).run
  (={qf,qg,workspace,glob ROF} /\ qf{1}=qf0 /\ qg{1}=qg0 /\ 0<=qf{1} /\ 0<=qg{1} /\ qf{1}+qg{1}<=size xs /\
   ErasureSeedPool.seeds{1}=xs /\ ErasureSeedPool.cursor{1}=0 /\ ErasureSeedLog.used{1}=[] ==>
   ={res,glob ROF} /\ ErasureSeedPool.seeds{1}=xs /\
   ErasureSeedPool.cursor{1}=res.`2{1}+res.`3{1} /\
   ErasureSeedLog.used{1}=rev(take(res.`2{1}+res.`3{1})xs) /\
   0<=res.`2{1}+res.`3{1}<=qf0+qg0)
  (={qf,qg,workspace,glob ROF} ==> ={res,glob ROF})=> //.
 + smt().
 + exact(erasure_fixed_result_stopped xs qf0 qg0).
 symmetry; conseq(stopped_result_equiv UniformSeedRNG FreshExpand); smt().
qed.

type erasure_pool_observation = stopped_output * cca_f_table * erasure_seed list * erasure_seed list.
module ErasurePoolExperiment = {
 proc before(qf:int,qg:int,workspace:W8.t Array14466.t) : erasure_pool_observation = {
  var pool:erasure_seed list; var out:stopped_output;
  pool <$ dlist uniform32 (qf+qg);
  ErasureSeedPool.init(pool); ErasureSeedLog.init();
  out <@ StoppedKeygen(ErasureSeedPool,LoggedErasedExpand).run(qf,qg,workspace);
  return(out,ROF.m,pool,ErasureSeedLog.used);
 }
 proc independent(qf:int,qg:int,workspace:W8.t Array14466.t) : erasure_pool_observation = {
  var pool:erasure_seed list; var out:stopped_output;
  pool <$ dlist uniform32 (qf+qg);
  out <@ StoppedKeygen(UniformSeedRNG,FreshExpand).run(qf,qg,workspace);
  ErasureSeedPool.init(pool);
  ErasureSeedPool.cursor <- out.`2+out.`3;
  ErasureSeedLog.used <- rev(take(out.`2+out.`3)pool);
  return(out,ROF.m,pool,ErasureSeedLog.used);
 }
 proc after(qf:int,qg:int,workspace:W8.t Array14466.t) : erasure_pool_observation = {
  var pool:erasure_seed list; var out:stopped_output;
  out <@ StoppedKeygen(UniformSeedRNG,FreshExpand).run(qf,qg,workspace);
  pool <$ dlist uniform32 (qf+qg);
  ErasureSeedPool.init(pool);
  ErasureSeedPool.cursor <- out.`2+out.`3;
  ErasureSeedLog.used <- rev(take(out.`2+out.`3)pool);
  return(out,ROF.m,pool,ErasureSeedLog.used);
 }
}.

lemma erasure_pool_fixed_projection qf0 qg0 :
 equiv[ErasurePoolExperiment.before ~ ErasurePoolExperiment.independent :
 ={qf,qg,workspace,glob ROF} /\ qf{1}=qf0 /\ qg{1}=qg0 /\ 0<=qf0 /\ 0<=qg0 ==>
 ={res,glob ROF,glob ErasureSeedPool,glob ErasureSeedLog}].
proof.
 proc.
 seq 1 1:(={qf,qg,workspace,pool,glob ROF} /\ qf{1}=qf0 /\ qg{1}=qg0 /\
  0<=qf0 /\ 0<=qg0 /\ size pool{1}=qf0+qg0).
 + rnd; auto=> />; smt(supp_dlist_size).
 inline ErasureSeedPool.init ErasureSeedLog.init.
 wp; ecall(erasure_fixed_stopped pool{1} qf0 qg0); auto=> />; smt().
qed.

lemma erasure_pool_postsample :
 equiv[ErasurePoolExperiment.independent ~ ErasurePoolExperiment.after :
 ={qf,qg,workspace,glob ROF} ==> ={res,glob ROF,glob ErasureSeedPool,glob ErasureSeedLog}].
proof. proc; swap{1} 1 1; sim. qed.

(* The entire Q-sample pool is independent of the visible stopped output,
   F table and counts. The actual used trace is its reversed used prefix. *)
lemma erasure_pool_before_after qf0 qg0 :
 equiv[ErasurePoolExperiment.before ~ ErasurePoolExperiment.after :
 ={qf,qg,workspace,glob ROF} /\ qf{1}=qf0 /\ qg{1}=qg0 /\ 0<=qf0 /\ 0<=qg0 ==>
 ={res,glob ROF,glob ErasureSeedPool,glob ErasureSeedLog}].
proof.
 transitivity ErasurePoolExperiment.independent
  (={qf,qg,workspace,glob ROF} /\ qf{1}=qf0 /\ qg{1}=qg0 /\ 0<=qf0 /\ 0<=qg0 ==>
   ={res,glob ROF,glob ErasureSeedPool,glob ErasureSeedLog})
  (={qf,qg,workspace,glob ROF} ==> ={res,glob ROF,glob ErasureSeedPool,glob ErasureSeedLog})=> //.
 + smt().
 + exact(erasure_pool_fixed_projection qf0 qg0).
 exact erasure_pool_postsample.
qed.

require import NTRUPlus768ErasureSeedTape.

(* The online sampler records every draw in its tape prefix, and is the
   actual uniform-seed RNG on every call that the bounded caller makes. *)

lemma erasure_online_result_f c q0 Q :
 equiv[ResultRetry(ErasureOnlinePool,LoggedErasedExpand).f ~
       ResultRetry(UniformSeedRNG,LoggedErasedExpand).f :
 ={limit,glob ErasureSeedLog} /\ limit{1}=q0 /\ 0<=c /\ 0<=q0 /\ c+q0<=Q /\
 ErasureTape.q{1}=Q /\ size ErasureSeedPool.seeds{1}=Q /\ ErasureSeedPool.cursor{1}=c /\
 take c ErasureSeedPool.seeds{1}=rev ErasureSeedLog.used{1} ==>
 ={res,glob ErasureSeedLog} /\ ErasureTape.q{1}=Q /\ size ErasureSeedPool.seeds{1}=Q /\
 ErasureSeedPool.cursor{1}=c+res.`rs_count{1} /\
 take(c+res.`rs_count{1})ErasureSeedPool.seeds{1}=rev ErasureSeedLog.used{1} /\
 0<=res.`rs_count{1}<=q0].
proof.
 proc.
 while(={limit,buf,ntt,inverse,status,count,glob ErasureSeedLog} /\ limit{1}=q0 /\
  0<=c /\ 0<=q0 /\ c+q0<=Q /\ 0<=count{1}<=q0 /\ ErasureTape.q{1}=Q /\
  size ErasureSeedPool.seeds{1}=Q /\ ErasureSeedPool.cursor{1}=c+count{1} /\
  take(c+count{1})ErasureSeedPool.seeds{1}=rev ErasureSeedLog.used{1}).
 + rewrite equiv[{1} 1 erasure_online_normalized_equiv]; first by auto=> />; smt().
   inline AttemptResult(LoggedErasedExpand).f.
   inline ErasureOnlinePool.sample_raw LoggedErasedExpand.shake UniformSeedRNG.sample FreshExpand.shake.
   rcondt{1} 4; first by auto=> />; rewrite /max; smt().
   auto=> />.
   move=> &1 &2 hc hq hsz hn0 hn1 hp hs hb.
   have hn:count{2}<q0 by move:hb; rewrite(lez_maxr 0 q0 hq).
   have hi:0<=c+count{2}<size ErasureSeedPool.seeds{1} by smt().
   move=>x hx buf hbuf; clear hx hbuf buf.
   have ht:=erasure_take_put ErasureSeedPool.seeds{1} (c+count{2}) x hi.
   rewrite size_put rev_cons -hp; smt().
 auto=> />; smt().
qed.

lemma erasure_online_result_g c q0 Q :
 equiv[ResultRetry(ErasureOnlinePool,LoggedErasedExpand).g ~
       ResultRetry(UniformSeedRNG,LoggedErasedExpand).g :
 ={limit,glob ErasureSeedLog} /\ limit{1}=q0 /\ 0<=c /\ 0<=q0 /\ c+q0<=Q /\
 ErasureTape.q{1}=Q /\ size ErasureSeedPool.seeds{1}=Q /\ ErasureSeedPool.cursor{1}=c /\
 take c ErasureSeedPool.seeds{1}=rev ErasureSeedLog.used{1} ==>
 ={res,glob ErasureSeedLog} /\ ErasureTape.q{1}=Q /\ size ErasureSeedPool.seeds{1}=Q /\
 ErasureSeedPool.cursor{1}=c+res.`rs_count{1} /\
 take(c+res.`rs_count{1})ErasureSeedPool.seeds{1}=rev ErasureSeedLog.used{1} /\
 0<=res.`rs_count{1}<=q0].
proof.
 proc.
 while(={limit,buf,ntt,inverse,status,count,glob ErasureSeedLog} /\ limit{1}=q0 /\
  0<=c /\ 0<=q0 /\ c+q0<=Q /\ 0<=count{1}<=q0 /\ ErasureTape.q{1}=Q /\
  size ErasureSeedPool.seeds{1}=Q /\ ErasureSeedPool.cursor{1}=c+count{1} /\
  take(c+count{1})ErasureSeedPool.seeds{1}=rev ErasureSeedLog.used{1}).
 + rewrite equiv[{1} 1 erasure_online_normalized_equiv]; first by auto=> />; smt().
   inline AttemptResult(LoggedErasedExpand).g.
   inline ErasureOnlinePool.sample_raw LoggedErasedExpand.shake UniformSeedRNG.sample FreshExpand.shake.
   rcondt{1} 4; first by auto=> />; rewrite /max; smt().
   auto=> />.
   move=> &1 &2 hc hq hsz hn0 hn1 hp hs hb.
   have hn:count{2}<q0 by move:hb; rewrite(lez_maxr 0 q0 hq).
   have hi:0<=c+count{2}<size ErasureSeedPool.seeds{1} by smt().
   move=>x hx buf hbuf; clear hx hbuf buf.
   have ht:=erasure_take_put ErasureSeedPool.seeds{1} (c+count{2}) x hi.
   rewrite size_put rev_cons -hp; smt().
 auto=> />; smt().
qed.

lemma erasure_online_result_stopped qf0 qg0 :
 equiv[ResultStoppedKeygen(ErasureOnlinePool,LoggedErasedExpand).run ~
       ResultStoppedKeygen(UniformSeedRNG,LoggedErasedExpand).run :
 ={qf,qg,workspace,glob ROF,glob ErasureSeedLog} /\
 qf{1}=qf0 /\ qg{1}=qg0 /\ 0<=qf0 /\ 0<=qg0 /\
 ErasureTape.q{1}=qf0+qg0 /\ size ErasureSeedPool.seeds{1}=qf0+qg0 /\
 ErasureSeedPool.cursor{1}=0 /\ ErasureSeedLog.used{1}=[] ==>
 ={res,glob ROF,glob ErasureSeedLog} /\ ErasureTape.q{1}=qf0+qg0 /\
 size ErasureSeedPool.seeds{1}=qf0+qg0 /\ ErasureSeedPool.cursor{1}=res.`2{1}+res.`3{1} /\
 take(res.`2{1}+res.`3{1})ErasureSeedPool.seeds{1}=rev ErasureSeedLog.used{1} /\
 0<=res.`2{1}+res.`3{1}<=qf0+qg0].
proof.
 proc.
 seq 3 3:(={qf,qg,workspace,fv,gv,result,glob ROF,glob ErasureSeedLog} /\ gv{1}=retry_initial /\
  qf{1}=qf0 /\ qg{1}=qg0 /\ 0<=qf0 /\ 0<=qg0 /\ ErasureTape.q{1}=qf0+qg0 /\
  size ErasureSeedPool.seeds{1}=qf0+qg0 /\ ErasureSeedPool.cursor{1}=fv.`rs_count{1} /\
  take fv.`rs_count{1} ErasureSeedPool.seeds{1}=rev ErasureSeedLog.used{1} /\ 0<=fv.`rs_count{1}<=qf0).
 + ecall(erasure_online_result_f 0 qf0 (qf0+qg0)); auto=> />; smt(take0).
 if; first by auto.
 + seq 1 1:(={qf,qg,workspace,fv,gv,result,glob ROF,glob ErasureSeedLog} /\
    ErasureTape.q{1}=qf0+qg0 /\ size ErasureSeedPool.seeds{1}=qf0+qg0 /\
    ErasureSeedPool.cursor{1}=fv.`rs_count{1}+gv.`rs_count{1} /\
    take(fv.`rs_count{1}+gv.`rs_count{1})ErasureSeedPool.seeds{1}=rev ErasureSeedLog.used{1} /\
    0<=fv.`rs_count{1}+gv.`rs_count{1}<=qf0+qg0).
   - ecall(erasure_online_result_g fv.`rs_count{1} qg0 (qf0+qg0)); auto=> />; smt().
   if; 1,3:by auto.
   wp; call (_: ={fv,gv,workspace,glob ROF} ==> ={res,glob ROF}); first by sim.
   auto.
 auto=> />; rewrite /retry_initial /=; smt().
qed.

lemma erasure_online_stopped qf0 qg0 :
 equiv[StoppedKeygen(ErasureOnlinePool,LoggedErasedExpand).run ~
       StoppedKeygen(UniformSeedRNG,LoggedErasedExpand).run :
 ={qf,qg,workspace,glob ROF,glob ErasureSeedLog} /\
 qf{1}=qf0 /\ qg{1}=qg0 /\ 0<=qf0 /\ 0<=qg0 /\
 ErasureTape.q{1}=qf0+qg0 /\ size ErasureSeedPool.seeds{1}=qf0+qg0 /\
 ErasureSeedPool.cursor{1}=0 /\ ErasureSeedLog.used{1}=[] ==> ={res,glob ROF,glob ErasureSeedLog} /\ ErasureTape.q{1}=qf0+qg0 /\
 size ErasureSeedPool.seeds{1}=qf0+qg0 /\ ErasureSeedPool.cursor{1}=res.`2{1}+res.`3{1} /\
 take(res.`2{1}+res.`3{1})ErasureSeedPool.seeds{1}=rev ErasureSeedLog.used{1} /\
 0<=res.`2{1}+res.`3{1}<=qf0+qg0].
proof.
 transitivity ResultStoppedKeygen(ErasureOnlinePool,LoggedErasedExpand).run
  (={qf,qg,workspace,glob ROF,glob ErasureSeedPool,glob ErasureSeedLog,ErasureTape.q} ==>
   ={res,glob ROF,glob ErasureSeedPool,glob ErasureSeedLog,ErasureTape.q})
  (={qf,qg,workspace,glob ROF,glob ErasureSeedLog} /\
 qf{1}=qf0 /\ qg{1}=qg0 /\ 0<=qf0 /\ 0<=qg0 /\
 ErasureTape.q{1}=qf0+qg0 /\ size ErasureSeedPool.seeds{1}=qf0+qg0 /\
 ErasureSeedPool.cursor{1}=0 /\ ErasureSeedLog.used{1}=[] ==> ={res,glob ROF,glob ErasureSeedLog} /\ ErasureTape.q{1}=qf0+qg0 /\
 size ErasureSeedPool.seeds{1}=qf0+qg0 /\ ErasureSeedPool.cursor{1}=res.`2{1}+res.`3{1} /\
 take(res.`2{1}+res.`3{1})ErasureSeedPool.seeds{1}=rev ErasureSeedLog.used{1} /\
 0<=res.`2{1}+res.`3{1}<=qf0+qg0)=> //.
 + smt().
 + conseq(stopped_result_equiv ErasureOnlinePool LoggedErasedExpand); smt().
 transitivity ResultStoppedKeygen(UniformSeedRNG,LoggedErasedExpand).run
  (={qf,qg,workspace,glob ROF,glob ErasureSeedLog} /\
 qf{1}=qf0 /\ qg{1}=qg0 /\ 0<=qf0 /\ 0<=qg0 /\
 ErasureTape.q{1}=qf0+qg0 /\ size ErasureSeedPool.seeds{1}=qf0+qg0 /\
 ErasureSeedPool.cursor{1}=0 /\ ErasureSeedLog.used{1}=[] ==> ={res,glob ROF,glob ErasureSeedLog} /\ ErasureTape.q{1}=qf0+qg0 /\
 size ErasureSeedPool.seeds{1}=qf0+qg0 /\ ErasureSeedPool.cursor{1}=res.`2{1}+res.`3{1} /\
 take(res.`2{1}+res.`3{1})ErasureSeedPool.seeds{1}=rev ErasureSeedLog.used{1} /\
 0<=res.`2{1}+res.`3{1}<=qf0+qg0)
  (={qf,qg,workspace,glob ROF,glob ErasureSeedLog} ==> ={res,glob ROF,glob ErasureSeedLog})=> //.
 + smt().
 + exact(erasure_online_result_stopped qf0 qg0).
 symmetry; conseq(stopped_result_equiv UniformSeedRNG LoggedErasedExpand); smt().
qed.

module ErasureOnlineExperiment = {
 proc online(qf:int,qg:int,workspace:W8.t Array14466.t) : erasure_pool_observation = {
  var out:stopped_output;
  ErasureSeedLog.init();
  ErasureTape.q <- qf+qg;
  ErasureSeedPool.init(nseq(qf+qg)witness);
  out <@ StoppedKeygen(ErasureOnlinePool,LoggedErasedExpand).run(qf,qg,workspace);
  ErasureTape.refresh();
  return(out,ROF.m,ErasureSeedPool.seeds,ErasureSeedLog.used);
 }
 proc padded(qf:int,qg:int,workspace:W8.t Array14466.t) : erasure_pool_observation = {
  var out:stopped_output; var suffix:erasure_seed list;
  ErasureSeedLog.init();
  out <@ StoppedKeygen(UniformSeedRNG,LoggedErasedExpand).run(qf,qg,workspace);
  suffix <$ dlist uniform32 (qf+qg-(out.`2+out.`3));
  ErasureSeedPool.seeds <- rev ErasureSeedLog.used ++ suffix;
  ErasureSeedPool.cursor <- out.`2+out.`3;
  ErasureTape.q <- qf+qg;
  return(out,ROF.m,ErasureSeedPool.seeds,ErasureSeedLog.used);
 }
 proc presampled(qf:int,qg:int,workspace:W8.t Array14466.t) : erasure_pool_observation = {
  var out:stopped_output;
  ErasureSeedLog.init();
  ErasureTape.q <- qf+qg;
  ErasureSeedPool.init(nseq(qf+qg)witness);
  ErasureTape.refresh();
  out <@ StoppedKeygen(ErasureSeedPool,LoggedErasedExpand).run(qf,qg,workspace);
  return(out,ROF.m,ErasureSeedPool.seeds,ErasureSeedLog.used);
 }
}.

lemma erasure_online_padded qf0 qg0 :
 equiv[ErasureOnlineExperiment.online ~ ErasureOnlineExperiment.padded :
 ={qf,qg,workspace,glob ROF} /\ qf{1}=qf0 /\ qg{1}=qg0 /\ 0<=qf0 /\ 0<=qg0 ==>
 ={res,glob ROF,glob ErasureSeedPool,glob ErasureSeedLog,ErasureTape.q}].
proof.
 proc.
 seq 4 2:(={qf,qg,out,glob ROF,glob ErasureSeedLog} /\
  ErasureTape.q{1}=qf{1}+qg{1} /\ ErasureSeedPool.cursor{1}=out.`2{1}+out.`3{1} /\
  size ErasureSeedPool.seeds{1}=qf{1}+qg{1} /\ 0<=out.`2{1}+out.`3{1} /\
  take(out.`2{1}+out.`3{1})ErasureSeedPool.seeds{1}=rev ErasureSeedLog.used{1}).
 + ecall(erasure_online_stopped qf0 qg0).
   inline ErasureSeedLog.init ErasureSeedPool.init; auto=> />.
   rewrite size_nseq /max; smt().
 inline ErasureTape.refresh ErasureTape.normalize.
 rcondf{1} 1; first by auto=> />; smt().
 inline ErasureTape.refresh_raw; auto=> />; smt().
qed.

lemma erasure_pool_eager qf0 qg0 :
 equiv[ErasurePoolExperiment.before ~ ErasureOnlineExperiment.presampled :
 ={qf,qg,workspace,glob ROF} /\ qf{1}=qf0 /\ qg{1}=qg0 /\ 0<=qf0 /\ 0<=qg0 ==>
 ={res,glob ROF,glob ErasureSeedPool,glob ErasureSeedLog}].
proof.
 proc.
 call (_: ={qf,qg,workspace,glob ROF,glob ErasureSeedPool,glob ErasureSeedLog} ==>
   ={res,glob ROF,glob ErasureSeedPool,glob ErasureSeedLog}); first by sim.
 inline ErasureSeedPool.init ErasureSeedLog.init ErasureTape.refresh
   ErasureTape.normalize ErasureTape.refresh_raw.
 rcondf{2} ^if; first by auto=> />; rewrite size_nseq /max; smt().
 auto=> />; smt(take0).
qed.

module ErasureTapeStopped(R:KeygenSeedRNG) = {
 proc run=StoppedKeygen(R,LoggedErasedExpand).run
}.

lemma erasure_eager_online qf0 qg0 :
 equiv[ErasureOnlineExperiment.presampled ~ ErasureOnlineExperiment.online :
 ={qf,qg,workspace,glob ROF} /\ qf{1}=qf0 /\ qg{1}=qg0 /\ 0<=qf0 /\ 0<=qg0 ==> ={res,glob ROF,glob ErasureSeedPool,glob ErasureSeedLog} /\ ={ErasureTape.q}].
proof.
 proc.
 seq 3 3:(={qf,qg,workspace,glob ROF,glob ErasureSeedPool,glob ErasureSeedLog,ErasureTape.q}).
 + inline ErasureSeedLog.init ErasureSeedPool.init; auto.
 eager call(erasure_tape_context ErasureTapeStopped); auto.
qed.

lemma erasure_pool_online qf0 qg0 :
 equiv[ErasurePoolExperiment.before ~ ErasureOnlineExperiment.online :
 ={qf,qg,workspace,glob ROF} /\ qf{1}=qf0 /\ qg{1}=qg0 /\ 0<=qf0 /\ 0<=qg0 ==> ={res,glob ROF,glob ErasureSeedPool,glob ErasureSeedLog}].
proof.
 transitivity ErasureOnlineExperiment.presampled
  (={qf,qg,workspace,glob ROF} /\ qf{1}=qf0 /\ qg{1}=qg0 /\ 0<=qf0 /\ 0<=qg0 ==> ={res,glob ROF,glob ErasureSeedPool,glob ErasureSeedLog})
  (={qf,qg,workspace,glob ROF} /\ qf{1}=qf0 /\ qg{1}=qg0 /\ 0<=qf0 /\ 0<=qg0 ==> ={res,glob ROF,glob ErasureSeedPool,glob ErasureSeedLog})=> //.
 + smt().
 + exact(erasure_pool_eager qf0 qg0).
 conseq(erasure_eager_online qf0 qg0); smt().
qed.

lemma erasure_online_postsample qf0 qg0 :
 equiv[ErasureOnlineExperiment.online ~ ErasurePoolExperiment.after :
 ={qf,qg,workspace,glob ROF} /\ qf{1}=qf0 /\ qg{1}=qg0 /\ 0<=qf0 /\ 0<=qg0 ==> ={res,glob ROF,glob ErasureSeedPool,glob ErasureSeedLog}].
proof.
 transitivity ErasurePoolExperiment.before
  (={qf,qg,workspace,glob ROF} /\ qf{1}=qf0 /\ qg{1}=qg0 /\ 0<=qf0 /\ 0<=qg0 ==> ={res,glob ROF,glob ErasureSeedPool,glob ErasureSeedLog})
  (={qf,qg,workspace,glob ROF} /\ qf{1}=qf0 /\ qg{1}=qg0 /\ 0<=qf0 /\ 0<=qg0 ==> ={res,glob ROF,glob ErasureSeedPool,glob ErasureSeedLog})=> //.
 + smt().
 + symmetry; conseq(erasure_pool_online qf0 qg0); smt().
 exact(erasure_pool_before_after qf0 qg0).
qed.

(* Actual online uniform seeds, including rejected attempts, followed by
   unused independent padding have exactly the visible-setup-first law.
   The post-sampled full pool is independent; used remains its N-prefix. *)
lemma erasure_padded_postsample qf0 qg0 :
 equiv[ErasureOnlineExperiment.padded ~ ErasurePoolExperiment.after :
 ={qf,qg,workspace,glob ROF} /\ qf{1}=qf0 /\ qg{1}=qg0 /\ 0<=qf0 /\ 0<=qg0 ==> ={res,glob ROF,glob ErasureSeedPool,glob ErasureSeedLog}].
proof.
 transitivity ErasureOnlineExperiment.online
  (={qf,qg,workspace,glob ROF} /\ qf{1}=qf0 /\ qg{1}=qg0 /\ 0<=qf0 /\ 0<=qg0 ==> ={res,glob ROF,glob ErasureSeedPool,glob ErasureSeedLog})
  (={qf,qg,workspace,glob ROF} /\ qf{1}=qf0 /\ qg{1}=qg0 /\ 0<=qf0 /\ 0<=qg0 ==> ={res,glob ROF,glob ErasureSeedPool,glob ErasureSeedLog})=> //.
 + smt().
 + symmetry; conseq(erasure_online_padded qf0 qg0); smt().
 exact(erasure_online_postsample qf0 qg0).
qed.




