require import AllCore List Distr DList FMap.
from Jasmin require import JWord.
require import Array32 Array1152 Array2336 Array14466.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768StoppedKeygenModel.
require import NTRUPlus768FreshRetryLaw NTRUPlus768ROMDistributions NTRUPlus768ROMOracles.
require import NTRUPlus768CCAGame NTRUPlus768CCADecapOracle NTRUPlus768RawXOFStreams.
require import NTRUPlus768ErasureModel NTRUPlus768ErasureBudget NTRUPlus768ErasureGames.
require import NTRUPlus768ErasureHitBound NTRUPlus768ErasureQueryKernel.
require import NTRUPlus768ErasureSeedTape NTRUPlus768ErasureSeedPool.

module ErasureHitContinuation(A:CCAExtendedAdversary) = {
 proc run(setup:stopped_output) : bool = {
  var out:keygen_output; var win:bool;
  if(setup.`1<>None){
   out <- oget setup.`1;
   win <@ CCAChallengeOriginal(CappedA(A)).run(out.`1.`kg_pk,out.`1.`kg_sk);
  }
  return ErasureHit.bad;
 }
}.
module ErasureQueryContinuation(A:CCAExtendedAdversary) = {
 proc run(setup:stopped_output) : erasure_seed list = {
  var out:keygen_output; var win:bool;
  if(setup.`1<>None){
   out <- oget setup.`1;
   win <@ CCAChallengeOriginal(CappedA(A)).run(out.`1.`kg_pk,out.`1.`kg_sk);
  }
  return EBudgetState.queries;
 }
}.
module ErasurePaddedHitGame(A:CCAExtendedAdversary) = {
 proc run(qf:int,qg:int) : bool = {
  var observation:erasure_pool_observation; var bad:bool;
  ROMInit.init(); RawXOFStreams.init(); CCADecapOracle.reset(); ErasureHit.init();
  observation <@ ErasureOnlineExperiment.padded(qf,qg,witness);
  bad <@ ErasureHitContinuation(A).run(observation.`1);
  return bad;
 }
}.
module ErasureSetupPoolHitGame(A:CCAExtendedAdversary) = {
 proc run(qf:int,qg:int) : bool = {
  var observation:erasure_pool_observation; var bad:bool;
  ROMInit.init(); RawXOFStreams.init(); CCADecapOracle.reset(); ErasureHit.init();
  observation <@ ErasurePoolExperiment.after(qf,qg,witness);
  bad <@ ErasureHitContinuation(A).run(observation.`1);
  return bad;
 }
}.
module ErasureBeforeQueryPool(A:CCAExtendedAdversary) = {
 proc run(qf:int,qg:int) : bool = {
  var setup:stopped_output; var pool,queries:erasure_seed list;
  ROMInit.init(); RawXOFStreams.init(); CCADecapOracle.reset();
  ErasureSeedLog.init(); ErasureHit.init();
  setup <@ StoppedKeygen(UniformSeedRNG,FreshExpand).run(qf,qg,witness);
  pool <$ dlist uniform32(qf+qg);
  queries <@ ErasureQueryContinuation(A).run(setup);
  return erasure_pool_hits (rev(take(setup.`2+setup.`3)pool))queries;
 }
}.

lemma erasure_hit_trace_pool used queries :
 erasure_trace_hit used queries=erasure_pool_hits used queries.
proof. rewrite /erasure_trace_hit /erasure_pool_hits !hasP; smt(). qed.

lemma erasure_challenge_ghost_observation
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState,-ErasureTape}) used0 :
 equiv[CCAChallengeOriginal(CappedA(A)).run ~ CCAChallengeOriginal(CappedA(A)).run:
 ={pk,sk,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,
   glob CCADecapOracle,glob EBudgetState} /\ ErasureSeedLog.used{1}=used0 /\
 ErasureHit.bad{1}=erasure_trace_hit used0 EBudgetState.queries{1} ==>
 ={res,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,
   glob CCADecapOracle,glob EBudgetState} /\
 ErasureHit.bad{1}=erasure_trace_hit used0 EBudgetState.queries{2}].
proof.
 conseq(erasure_capped_challenge_ghost_independent A)
  (erasure_capped_challenge_hit A) _ => />; smt().
qed.

lemma erasure_continuation_observation
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState,-ErasureTape}) used0 :
 equiv[ErasureHitContinuation(A).run ~ ErasureQueryContinuation(A).run:
 ={setup,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,
   glob CCADecapOracle,glob EBudgetState} /\ ErasureSeedLog.used{1}=used0 /\
 ErasureHit.bad{1}=erasure_trace_hit used0 EBudgetState.queries{1} ==>
 res{1}=erasure_pool_hits used0 res{2}].
proof.
 proc; if; first by auto.
 + call(erasure_challenge_ghost_observation A used0); auto=> />;
   smt(erasure_hit_trace_pool).
 auto=> />; smt(erasure_hit_trace_pool).
qed.

lemma erasure_pool_move_after_queries
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState,-ErasureTape}) :
 equiv[ErasureBeforeQueryPool(A).run ~ ErasurePostQueryPool(A).run:
 ={qf,qg,glob A,glob EBudgetState} ==> ={res}].
proof.
 proc; inline ErasureQueryKernel(A).guess ErasureQueryContinuation(A).run.
 swap{1} 7 3.
 rnd; wp.
 conseq (_: _ ==> ={qf,qg,setup,EBudgetState.queries})=> //.
 sim.
 call(_: ={qf,qg,workspace,glob ROF} ==> ={res,glob ROF}); first by sim.
 inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init
   CCADecapOracle.reset ErasureSeedLog.init ErasureHit.init; auto.
qed.

(* Padding samples only private unused suffix values. It does not change
   the stopped output, the F table, or the actual used-seed trace. *)
lemma erasure_stopped_padding :
 equiv[StoppedKeygen(UniformSeedRNG,LoggedErasedExpand).run ~ ErasureOnlineExperiment.padded:
 ={qf,qg,workspace,glob ROF} /\ ErasureSeedLog.used{1}=[] ==>
 res{1}=res.`1{2} /\ ={glob ROF,glob ErasureSeedLog}].
proof.
 proc*; inline{2} ErasureOnlineExperiment.padded.
 wp; rnd{2}.
 call(_: ={qf,qg,workspace,glob ROF,glob ErasureSeedLog} ==>
   ={res,glob ROF,glob ErasureSeedLog}); first by sim.
 inline ErasureSeedLog.init; auto=> />; smt(dlist_ll uniform32_ll).
qed.

lemma erasure_stopped_padded_hit
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState,-ErasureTape}) :
 equiv[ErasureStoppedIndependentGame(A).run ~ ErasurePaddedHitGame(A).run:
 ={qf,qg,glob A,glob EBudgetState} ==> ErasureHit.bad{1}=res{2}].
proof.
 proc; inline{2} ErasureHitContinuation(A).run.
 seq 6 5:(setup{1}=observation.`1{2} /\
  ={glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,
    glob CCADecapOracle,glob EBudgetState,glob ErasureSeedLog,glob ErasureHit}).
 + call erasure_stopped_padding.
   inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init
    CCADecapOracle.reset ErasureSeedLog.init ErasureHit.init; auto.
 wp; sp; if; 1,3:by auto.
 wp; call(_: ={glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,
   glob CCADecapOracle,glob EBudgetState,glob ErasureSeedLog,glob ErasureHit}); first by sim.
 auto.
qed.

lemma erasure_setup_pool_observation
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState,-ErasureTape}) :
 equiv[ErasureSetupPoolHitGame(A).run ~ ErasureBeforeQueryPool(A).run:
 ={qf,qg,glob A,glob EBudgetState} /\ EBudgetState.queries{1}=[] ==> ={res}].
proof.
 proc; inline{1} ErasurePoolExperiment.after.
 wp; ecall(erasure_continuation_observation A (rev(take(setup.`2{2}+setup.`3{2})pool{2}))).
 inline ErasureSeedPool.init; wp; rnd.
 call(_: ={qf,qg,workspace,glob ROF} ==> ={res,glob ROF}); first by sim.
 inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init
   CCADecapOracle.reset ErasureSeedLog.init ErasureHit.init.
 auto=> />; rewrite /erasure_trace_hit; smt().
qed.

lemma erasure_padded_setup_hit
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState,-ErasureTape}) qf0 qg0 :
 equiv[ErasurePaddedHitGame(A).run ~ ErasureSetupPoolHitGame(A).run:
 ={qf,qg,glob A,glob EBudgetState} /\ qf{1}=qf0 /\ qg{1}=qg0 /\
 0<=qf0 /\ 0<=qg0 ==> ={res}].
proof.
 proc; call(_: ={setup,glob ErasureHitContinuation(A)} ==>
   ={res,glob ErasureHitContinuation(A)}); first by sim.
 call(erasure_padded_postsample qf0 qg0).
 inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init
   CCADecapOracle.reset ErasureHit.init; auto.
qed.

(* The observer can diverge: every step preserves its subdistribution.
   The fresh full pool is moved after the actual challenge and all queries,
   and only its used prefix appears in the exact hit event. *)
lemma erasure_actual_stopped_hit_probability
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState,-ErasureTape}) &m qf0 qg0 :
 0<=qf0 =>0<=qg0 => EBudgetState.queries{m}=[] =>
 Pr[ErasureStoppedIndependentGame(A).run(qf0,qg0) @ &m:ErasureHit.bad]=
 Pr[ErasurePostQueryPool(A).run(qf0,qg0) @ &m:res].
proof.
 move=>hf hg hx.
 have h1:Pr[ErasureStoppedIndependentGame(A).run(qf0,qg0) @ &m:ErasureHit.bad]=
   Pr[ErasurePaddedHitGame(A).run(qf0,qg0) @ &m:res].
 + byequiv(erasure_stopped_padded_hit A)=> //.
 have h2:Pr[ErasurePaddedHitGame(A).run(qf0,qg0) @ &m:res]=
   Pr[ErasureSetupPoolHitGame(A).run(qf0,qg0) @ &m:res].
 + byequiv(erasure_padded_setup_hit A qf0 qg0)=> //; smt().
 have h3:Pr[ErasureSetupPoolHitGame(A).run(qf0,qg0) @ &m:res]=
   Pr[ErasureBeforeQueryPool(A).run(qf0,qg0) @ &m:res].
 + byequiv(erasure_setup_pool_observation A)=> //.
 have h4:Pr[ErasureBeforeQueryPool(A).run(qf0,qg0) @ &m:res]=
   Pr[ErasurePostQueryPool(A).run(qf0,qg0) @ &m:res].
 + byequiv(erasure_pool_move_after_queries A)=> //.
 by rewrite h1 h2 h3 h4.
qed.

lemma erasure_actual_stopped_hit_bound
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState,-ErasureTape}) &m qf0 qg0 q0 :
 0<=qf0 =>0<=qg0 =>
 erasure_budget_initial q0 EBudgetState.requests{m} EBudgetState.forwarded{m}
   EBudgetState.limit{m} EBudgetState.overflow{m} EBudgetState.queries{m} =>
 Pr[ErasureStoppedIndependentGame(A).run(qf0,qg0) @ &m:ErasureHit.bad]
 <=erasure_hit_bound(qf0+qg0)q0.
proof.
 move=>hf hg hi.
 have hx:EBudgetState.queries{m}=[] by move:hi; rewrite /erasure_budget_initial; smt().
 rewrite(erasure_actual_stopped_hit_probability A &m qf0 qg0 hf hg hx).
 exact(erasure_postquery_hit_bound A &m qf0 qg0 q0 hf hg hi).
qed.
