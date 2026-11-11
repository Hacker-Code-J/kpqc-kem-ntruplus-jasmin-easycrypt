require import AllCore List Distr FMap StdOrder.
from Jasmin require import JWord.
require import NTRUPlus768ROMOracles NTRUPlus768CCAGame NTRUPlus768CCAOraclePorts.
require import NTRUPlus768CCADecapOracle NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
require import NTRUPlus768ErasureModel NTRUPlus768ErasureBudget NTRUPlus768ErasureSetup.
require import NTRUPlus768ErasureGames NTRUPlus768ErasureAdversaryCoupling.
require import NTRUPlus768ErasureHitBound NTRUPlus768ProposalSwitch.
require import NTRUPlus768ErasureCapRemoval NTRUPlus768CCASetupGame.
require import NTRUPlus768ErasureSeedTape NTRUPlus768ErasureActualHit NTRUPlus768ErasureGameTail.
require import NTRUPlus768FreshRetryLaw NTRUPlus768AcceptanceROMBound NTRUPlus768AcceptanceBudget.
import RealOrder RField.

op erasure_total_error qf qg qE =
 proposal_delta 0 (qf+qg)+2%r*fresh_retry_tail qf qg+erasure_hit_bound(qf+qg)qE.

lemma erasure_retry_tail_256 : fresh_retry_tail 256 256<=2%r/(2%r^256).
proof.
 have hb:=certified_keygen_error_256 0.
 rewrite (_:256+256=512) 1:// keygen_budget_collision_512 /= in hb.
 smt().
qed.

lemma erasure_error_256 qE :
 erasure_total_error 256 256 qE<=(130820%r+512%r*qE%r)/(2%r^256).
proof.
 have ht:=erasure_retry_tail_256.
 rewrite /erasure_total_error /erasure_hit_bound (_:256+256=512) 1://
   keygen_budget_collision_512 fromintM /=.
 smt().
qed.

lemma erasure_error_256_queries_238 :
 erasure_total_error 256 256 256<1%r/(2%r^238).
proof.
 apply(ler_lt_trans _ _ _ (erasure_error_256 256) _); rewrite /=.
 have hp:0%r<2%r^238 by apply expr_gt0; smt().
 have he:2%r^256=(2%r^238)*262144%r by ring.
 rewrite he; smt().
qed.

(* Unlike the earlier actual-ROM setup comparison, this E-erasure hop
   explicitly assumes a terminating adversary phase against lossless
   ports. A query cap by itself would not justify return-time bad events. *)
lemma erasure_stopped_games_upto
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState}) :
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>
  islossless H.raw=>islossless D.decap=>islossless A(H,D).guess) =>
 equiv[ErasureStoppedProgrammedGame(A).run ~ ErasureStoppedIndependentGame(A).run:
 ={qf,qg,glob A,glob EBudgetState} ==>
 ={ErasureHit.bad} /\ (!ErasureHit.bad{2} => ={res})].
proof.
 move=>all; proc.
 seq 7 7:(={setup,result,glob A,glob EBudgetState,ROF.m,ROG.m,ROH.m,
   RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,
   ErasureSeedLog.used} /\ !ErasureHit.bad{1} /\ !ErasureHit.bad{2} /\
   erasure_tables_agree ErasureSeedLog.used{1} ROE.m{1} ROE.m{2}).
 + wp; call erasure_stopped_coupling.
   inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init
    CCADecapOracle.reset ErasureSeedLog.init ErasureHit.init.
   auto=> />; rewrite /erasure_tables_agree; smt().
 if; first by auto.
 + wp; ecall(erasure_challenge_upto A ErasureSeedLog.used{1} all); auto=> />; smt().
 auto=> />; smt().
qed.

lemma erasure_stopped_games_good
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState}) &m qf qg :
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>
  islossless H.raw=>islossless D.decap=>islossless A(H,D).guess) =>
 Pr[ErasureStoppedProgrammedGame(A).run(qf,qg) @ &m:res=Some true /\ !ErasureHit.bad]=
 Pr[ErasureStoppedIndependentGame(A).run(qf,qg) @ &m:res=Some true /\ !ErasureHit.bad].
proof. move=>all; byequiv(erasure_stopped_games_upto A all)=> //; smt(). qed.

lemma erasure_stopped_games_bad
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState}) &m qf qg :
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>
  islossless H.raw=>islossless D.decap=>islossless A(H,D).guess) =>
 Pr[ErasureStoppedProgrammedGame(A).run(qf,qg) @ &m:ErasureHit.bad]=
 Pr[ErasureStoppedIndependentGame(A).run(qf,qg) @ &m:ErasureHit.bad].
proof. move=>all; byequiv(erasure_stopped_games_upto A all)=> //; smt(). qed.

lemma erasure_stopped_distance_bad
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState}) &m qf qg :
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>
  islossless H.raw=>islossless D.decap=>islossless A(H,D).guess) =>
 `|Pr[ErasureStoppedProgrammedGame(A).run(qf,qg) @ &m:res=Some true]-
   Pr[ErasureStoppedIndependentGame(A).run(qf,qg) @ &m:res=Some true]|<=
 Pr[ErasureStoppedIndependentGame(A).run(qf,qg) @ &m:ErasureHit.bad].
proof.
 move=>all.
 have good:=erasure_stopped_games_good A &m qf qg all.
 have bad:=erasure_stopped_games_bad A &m qf qg all.
 have hp:Pr[ErasureStoppedProgrammedGame(A).run(qf,qg) @ &m:res=Some true /\ ErasureHit.bad]<=
   Pr[ErasureStoppedProgrammedGame(A).run(qf,qg) @ &m:ErasureHit.bad] by rewrite Pr[mu_sub].
 have hi:Pr[ErasureStoppedIndependentGame(A).run(qf,qg) @ &m:res=Some true /\ ErasureHit.bad]<=
   Pr[ErasureStoppedIndependentGame(A).run(qf,qg) @ &m:ErasureHit.bad] by rewrite Pr[mu_sub].
 rewrite Pr[mu_split ErasureHit.bad].
 have ->:Pr[ErasureStoppedIndependentGame(A).run(qf,qg) @ &m:res=Some true]=
   Pr[ErasureStoppedIndependentGame(A).run(qf,qg) @ &m:res=Some true /\ ErasureHit.bad]+
   Pr[ErasureStoppedIndependentGame(A).run(qf,qg) @ &m:res=Some true /\ !ErasureHit.bad]
   by rewrite Pr[mu_split ErasureHit.bad].
 smt(mu_bounded).
qed.

lemma erasure_independent_counted_projection
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState}) :
 equiv[CCASharedSetupGame(FreshExpand,CountedA(A)).run ~ CCASharedSetupGame(FreshExpand,A).run:
 ={glob A} ==> ={res,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,
  glob CCADecapOracle}].
proof.
 proc; call(counted_challenge_erasure A).
 call(_: ={glob ROF} ==> ={res,glob ROF}); first by sim.
 inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init CCADecapOracle.reset.
 auto.
qed.

lemma erasure_count_cap_independent_equiv
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState}) q0 :
 0<=q0 =>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>
  islossless H.raw=>islossless D.decap=>islossless A(H,D).guess) =>
 hoare[CountedA(A,SharedCCAExtendedOracles,CCADecapOracle).guess:
 EBudgetState.requests=0 /\ EBudgetState.forwarded=0 /\ EBudgetState.limit=q0 /\
 !EBudgetState.overflow /\ EBudgetState.queries=[] ==> EBudgetState.requests<=q0] =>
 equiv[CCASharedSetupGame(FreshExpand,CountedA(A)).run ~ ErasureIndependentGame(A).run:
 ={glob A,glob EBudgetState} /\
 erasure_budget_initial q0 EBudgetState.requests{1} EBudgetState.forwarded{1}
  EBudgetState.limit{1} EBudgetState.overflow{1} EBudgetState.queries{1} ==>
 ={res,glob A,glob EBudgetState,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,
   glob CCADecapOracle}].
proof.
 move=>hq all bounded; proc.
 call(count_cap_challenge_equiv A q0 hq all bounded).
 call(_: ={glob ROF} ==> ={res,glob ROF}); first by sim.
 inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init CCADecapOracle.reset.
 auto; rewrite /erasure_budget_initial; smt().
qed.

lemma erasure_capped_independent_event
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState}) &m q0 (event:bool->bool) :
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>
  islossless H.raw=>islossless D.decap=>islossless A(H,D).guess) =>
 hoare[CountedA(A,SharedCCAExtendedOracles,CCADecapOracle).guess:
 EBudgetState.requests=0 /\ EBudgetState.forwarded=0 /\ EBudgetState.limit=q0 /\
 !EBudgetState.overflow /\ EBudgetState.queries=[] ==> EBudgetState.requests<=q0] =>
 erasure_budget_initial q0 EBudgetState.requests{m} EBudgetState.forwarded{m}
  EBudgetState.limit{m} EBudgetState.overflow{m} EBudgetState.queries{m} =>
 Pr[ErasureIndependentGame(A).run() @ &m:event res]=
 Pr[CCASharedSetupGame(FreshExpand,A).run() @ &m:event res].
proof.
 move=>all bounded hi.
 have hq:0<=q0 by move:hi; rewrite /erasure_budget_initial; smt().
 have he:Pr[CCASharedSetupGame(FreshExpand,CountedA(A)).run() @ &m:event res]=
   Pr[ErasureIndependentGame(A).run() @ &m:event res].
 + byequiv(erasure_count_cap_independent_equiv A q0 hq all bounded)=> //.
 rewrite -he.
 byequiv(erasure_independent_counted_projection A)=> //.
qed.

lemma erasure_triangle_bound (p0 p1 p2 a b:real) :
 `|p0-p1|<=a=>`|p1-p2|<=b=>`|p0-p2|<=a+b.
proof. rewrite !ler_norml; smt(). qed.

lemma erasure_stopped_distance
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState,-ErasureTape}) &m qf qg qE :
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>
  islossless H.raw=>islossless D.decap=>islossless A(H,D).guess) =>
 0<=qf=>0<=qg=>
 erasure_budget_initial qE EBudgetState.requests{m} EBudgetState.forwarded{m}
  EBudgetState.limit{m} EBudgetState.overflow{m} EBudgetState.queries{m} =>
 `|Pr[ErasureStoppedProgrammedGame(A).run(qf,qg) @ &m:res=Some true]-
   Pr[ErasureStoppedIndependentGame(A).run(qf,qg) @ &m:res=Some true]|<=erasure_hit_bound(qf+qg)qE.
proof.
 move=>all hf hg hi.
 exact(ler_trans _ _ _ (erasure_stopped_distance_bad A &m qf qg all)
   (erasure_actual_stopped_hit_bound A &m qf qg qE hf hg hi)).
qed.

lemma erasure_programmed_independent_distance
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState,-ErasureTape}) &m qf qg qE :
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>
  islossless H.raw=>islossless D.decap=>islossless A(H,D).guess) =>
 0<=qf=>0<=qg=>
 erasure_budget_initial qE EBudgetState.requests{m} EBudgetState.forwarded{m}
  EBudgetState.limit{m} EBudgetState.overflow{m} EBudgetState.queries{m} =>
 `|Pr[ErasureProgrammedGame(A).run() @ &m:res]-
   Pr[ErasureIndependentGame(A).run() @ &m:res]|<=
 erasure_hit_bound(qf+qg)qE+fresh_retry_tail qf qg.
proof.
 move=>all hf hg hi.
 have hc:=erasure_games_common_tail A &m qf qg (erasure_challenge_ll A all) hf hg.
 have hs:=erasure_stopped_distance A &m qf qg qE all hf hg hi.
 apply(ler_trans _ _ _ hc).
 apply ler_add; first exact hs.
 smt().
qed.

lemma erasure_original_independent_capped_distance
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState,-ErasureTape}) &m qf qg qE :
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>
  islossless H.raw=>islossless D.decap=>islossless A(H,D).guess) =>
 0<=qf=>0<=qg=>
 erasure_budget_initial qE EBudgetState.requests{m} EBudgetState.forwarded{m}
  EBudgetState.limit{m} EBudgetState.overflow{m} EBudgetState.queries{m} =>
 `|Pr[ErasureOriginalGame(A).run() @ &m:res]-
   Pr[ErasureIndependentGame(A).run() @ &m:res]|<=erasure_total_error qf qg qE.
proof.
 move=>all hf hg hi.
 have h1:=erasure_original_programmed_distance A &m qf qg hf hg.
 have h2:=erasure_programmed_independent_distance A &m qf qg qE all hf hg hi.
 have ht:=erasure_triangle_bound _ _ _ _ _ h1 h2.
 have he:(proposal_delta 0(qf+qg)+fresh_retry_tail qf qg)+
  (erasure_hit_bound(qf+qg)qE+fresh_retry_tail qf qg)=erasure_total_error qf qg qE
  by rewrite /erasure_total_error; ring.
 by move:ht; rewrite he.
qed.

(* Both endpoints below have the original, uncapped adversary interface.
   The separate universal counted-query contract discharges both caps.
   Nothing in this theorem assumes that actual ROM KeyGen terminates. *)
lemma erasure_original_independent_distance
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState,-ErasureTape}) &m qf qg qE :
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>
  islossless H.raw=>islossless D.decap=>islossless A(H,D).guess) =>
 hoare[CountedA(A,SharedCCAExtendedOracles,CCADecapOracle).guess:
 EBudgetState.requests=0 /\ EBudgetState.forwarded=0 /\ EBudgetState.limit=qE /\
 !EBudgetState.overflow /\ EBudgetState.queries=[] ==> EBudgetState.requests<=qE] =>
 0<=qf=>0<=qg=>
 erasure_budget_initial qE EBudgetState.requests{m} EBudgetState.forwarded{m}
  EBudgetState.limit{m} EBudgetState.overflow{m} EBudgetState.queries{m} =>
 `|Pr[CCAOriginalGame(A).run() @ &m:res]-
   Pr[CCASharedSetupGame(FreshExpand,A).run() @ &m:res]|<=erasure_total_error qf qg qE.
proof.
 move=>all bounded hf hg hi.
 have [hq [hn [hnf [hl [ho hx]]]]]:=hi.
 have ho':Pr[ErasureOriginalGame(A).run() @ &m:res]=Pr[CCAOriginalGame(A).run() @ &m:res].
 + exact(capped_original_event A &m qE (fun b=>b) hq all bounded hn hnf hl ho hx).
 have hi':Pr[ErasureIndependentGame(A).run() @ &m:res]=
   Pr[CCASharedSetupGame(FreshExpand,A).run() @ &m:res].
 + exact(erasure_capped_independent_event A &m qE (fun b=>b) all bounded hi).
 rewrite -ho' -hi'.
 exact(erasure_original_independent_capped_distance A &m qf qg qE all hf hg hi).
qed.

lemma erasure_original_independent_256
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState,-ErasureTape}) &m qE :
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>
  islossless H.raw=>islossless D.decap=>islossless A(H,D).guess) =>
 hoare[CountedA(A,SharedCCAExtendedOracles,CCADecapOracle).guess:
 EBudgetState.requests=0 /\ EBudgetState.forwarded=0 /\ EBudgetState.limit=qE /\
 !EBudgetState.overflow /\ EBudgetState.queries=[] ==> EBudgetState.requests<=qE] =>
 erasure_budget_initial qE EBudgetState.requests{m} EBudgetState.forwarded{m}
  EBudgetState.limit{m} EBudgetState.overflow{m} EBudgetState.queries{m} =>
 `|Pr[CCAOriginalGame(A).run() @ &m:res]-
   Pr[CCASharedSetupGame(FreshExpand,A).run() @ &m:res]|<=
 (130820%r+512%r*qE%r)/(2%r^256).
proof.
 move=>all bounded hi.
 have h:=erasure_original_independent_distance A &m 256 256 qE all bounded _ _ hi; first 2 smt().
 exact(ler_trans _ _ _ h (erasure_error_256 qE)).
qed.
