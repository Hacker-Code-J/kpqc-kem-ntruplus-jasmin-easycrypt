require import AllCore List Distr DList FMap SDist RealSeries.
from Jasmin require import JWord.
require import Array32 Array1152 Array2336 Array14466.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768StoppedKeygenModel.
require import NTRUPlus768FreshRetryLaw NTRUPlus768ROMDistributions NTRUPlus768ROMOracles.
require import NTRUPlus768CCAGame NTRUPlus768CCADecapOracle NTRUPlus768RawXOFStreams.
require import NTRUPlus768ErasureModel NTRUPlus768ErasureBudget NTRUPlus768ErasureGames.
require import NTRUPlus768ErasureHitBound.

type erasure_query_observation = int * erasure_seed list.

(* Only the returned count and the actual forwarded query log are needed
   for the hit bound. No seed pool, used-seed trace, or hit flag is exposed
   in this kernel's output. The adversary may adapt to the whole public
   transcript, including the real challenge and decapsulation answers. *)
module ErasureQueryKernel(A:CCAExtendedAdversary) = {
 proc guess(budgets:int*int) : erasure_query_observation = {
  var setup:stopped_output; var out:keygen_output; var win:bool;
  ROMInit.init(); RawXOFStreams.init(); CCADecapOracle.reset();
  ErasureSeedLog.init(); ErasureHit.init();
  setup <@ StoppedKeygen(UniformSeedRNG,FreshExpand).run(budgets.`1,budgets.`2,witness);
  if(setup.`1<>None){
   out <- oget setup.`1;
   win <@ CCAChallengeOriginal(CappedA(A)).run(out.`1.`kg_pk,out.`1.`kg_sk);
  }
  return(setup.`2+setup.`3,EBudgetState.queries);
 }
}.

module ErasurePostQueryPool(A:CCAExtendedAdversary) = {
 proc run(qf:int,qg:int) : bool = {
  var query:erasure_query_observation; var pool:erasure_seed list;
  query <@ ErasureQueryKernel(A).guess(qf,qg);
  pool <$ dlist uniform32 (qf+qg);
  return erasure_pool_hits (rev(take query.`1 pool)) query.`2;
 }
}.

clone SDist.GenDist as ErasureQueryDist with
 type in_t <- int*int,
 type out_t <- erasure_query_observation
 proof *.

lemma erasure_query_kernel_bound
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState}) q0 :
 hoare[ErasureQueryKernel(A).guess:
 erasure_budget_initial q0 EBudgetState.requests EBudgetState.forwarded
  EBudgetState.limit EBudgetState.overflow EBudgetState.queries ==>
 size res.`2<=q0].
proof.
 proc; seq 6:(erasure_budget_initial q0 EBudgetState.requests EBudgetState.forwarded
  EBudgetState.limit EBudgetState.overflow EBudgetState.queries).
 + call(_:true ==>true); first by trivial.
   inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init
    CCADecapOracle.reset ErasureSeedLog.init ErasureHit.init; auto.
 if.
 + call(erasure_capped_challenge_query_bound A q0).
   auto; rewrite /erasure_budget_initial /erasure_cap_invariant; smt().
 auto; rewrite /erasure_budget_initial; smt().
qed.

lemma erasure_query_source_sample (S<:ErasureQueryDist.Distinguisher) &m b :
 equiv[S.guess ~ ErasureQueryDist.S.sample:
 x{1}=b /\ (glob S){1}=(glob S){m} /\
 d{2}=mk(fun z=>Pr[S.guess(b) @ &m:res=z]) ==> ={res}].
proof.
 bypr(res{1})(res{2})=> // &1 &2 z [hx [hg hd]].
 rewrite hx hd ErasureQueryDist.sampleE -(ErasureQueryDist.adv_mu1 S &m z b).
 byequiv (_: ={x,glob S} ==> ={res})=> //.
 proc true; auto.
qed.

lemma erasure_query_support_bound
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState}) &m qf qg q0 :
 erasure_budget_initial q0 EBudgetState.requests{m} EBudgetState.forwarded{m}
  EBudgetState.limit{m} EBudgetState.overflow{m} EBudgetState.queries{m} =>
 forall z,z \in mk(fun z=>Pr[ErasureQueryKernel(A).guess(qf,qg) @ &m:res=z]) =>size z.`2<=q0.
proof.
 move=>hi z hz; rewrite supportP -(ErasureQueryDist.adv_mu1 (ErasureQueryKernel(A)) &m z (qf,qg)) in hz.
 case(size z.`2<=q0)=> // hn.
 have hzero:Pr[ErasureQueryKernel(A).guess(qf,qg) @ &m:res=z]=0%r.
 + byphoare (_: erasure_budget_initial q0 EBudgetState.requests EBudgetState.forwarded
     EBudgetState.limit EBudgetState.overflow EBudgetState.queries ==> res=z)=> //.
   hoare; conseq(erasure_query_kernel_bound A q0); smt().
 smt().
qed.

module ErasureQueryPostSample = {
 proc run(d:erasure_query_observation distr,Q:int) : bool = {
  var query:erasure_query_observation; var pool:erasure_seed list;
  query <$ d;
  pool <$ dlist uniform32 Q;
  return erasure_pool_hits (rev(take query.`1 pool)) query.`2;
 }
}.

lemma erasure_query_postsample_mu &m (K:erasure_query_observation distr) Q0 :
 Pr[ErasureQueryPostSample.run(K,Q0) @ &m:res]=
 mu(erasure_joint_after K Q0)
  (fun (zpool:erasure_query_observation*erasure_seed list)=>
   erasure_pool_hits (rev(take zpool.`1.`1 zpool.`2))zpool.`1.`2).
proof.
 byphoare (_:d=K /\ Q=Q0 ==> res) => //.
 proc; rndsem 0.
 rnd (fun (z:erasure_query_observation*erasure_seed list)=>erasure_pool_hits (rev(take z.`1.`1 z.`2))z.`1.`2).
 skip=> />.
qed.

lemma erasure_postquery_hit_bound
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState}) &m qf0 qg0 q0 :
 0<=qf0=>0<=qg0=>
 erasure_budget_initial q0 EBudgetState.requests{m} EBudgetState.forwarded{m}
  EBudgetState.limit{m} EBudgetState.overflow{m} EBudgetState.queries{m} =>
 Pr[ErasurePostQueryPool(A).run(qf0,qg0) @ &m:res]<=erasure_hit_bound (qf0+qg0)q0.
proof.
 move=>hf hg hi.
 have he:Pr[ErasurePostQueryPool(A).run(qf0,qg0) @ &m:res]=
 Pr[ErasureQueryPostSample.run(
  mk(fun z=>Pr[ErasureQueryKernel(A).guess(qf0,qg0) @ &m:res=z]),qf0+qg0) @ &m:res].
 + byequiv (_: qf{1}=qf0 /\ qg{1}=qg0 /\
    (glob ErasureQueryKernel(A)){1}=(glob ErasureQueryKernel(A)){m} /\ Q{2}=qf0+qg0 /\
    d{2}=mk(fun z=>Pr[ErasureQueryKernel(A).guess(qf0,qg0) @ &m:res=z]) ==> ={res})=> //.
   proc; rnd; outline{2} 1 ~ ErasureQueryDist.S.sample.
   call(erasure_query_source_sample (ErasureQueryKernel(A)) &m (qf0,qg0)); auto.
 rewrite he erasure_query_postsample_mu.
 apply(erasure_used_prefix_hit_bound _ (fun (z:erasure_query_observation)=>z.`2)
   (fun (z:erasure_query_observation)=>z.`1) (qf0+qg0)q0).
 + smt().
 + move:hi; rewrite /erasure_budget_initial; smt().
 exact(erasure_query_support_bound A &m qf0 qg0 q0 hi).
qed.
