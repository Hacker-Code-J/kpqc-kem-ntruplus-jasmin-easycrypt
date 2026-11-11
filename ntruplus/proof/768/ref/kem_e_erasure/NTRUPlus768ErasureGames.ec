require import AllCore List Distr FMap.
from Jasmin require import JWord.
require import Array32 Array1152 Array2336 Array14466.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteProof.
require import NTRUPlus768StoppedKeygenModel NTRUPlus768StoppedKeygenPrefix.
require import NTRUPlus768FreshRetryLaw NTRUPlus768ROMOracles.
require import NTRUPlus768ROMCorrectness NTRUPlus768CCAGame.
require import NTRUPlus768CCADecapOracle NTRUPlus768RawXOFStreams.
require import NTRUPlus768RawXOF NTRUPlus768CCAOraclePorts.
require import NTRUPlus768CCASetupGame NTRUPlus768CCASetupSecurity.
require import NTRUPlus768ProposalSwitch NTRUPlus768AcceptanceROMBound.
require import NTRUPlus768ErasureModel NTRUPlus768ErasureBudget.
require import NTRUPlus768ErasureSetup NTRUPlus768ErasurePrefix.

(* The analysis counter is configured before the game. This explicit
   initial-state predicate states the query budget without changing the
   existing CCA game body or its unbounded real-ROM setup. *)
op erasure_budget_initial (q n f lim:int) (over:bool) (queries:erasure_seed list) =
 0<=q /\ n=0 /\ f=0 /\ lim=q /\ !over /\ queries=[].

module ErasureOriginalGame(A:CCAExtendedAdversary) = CCAOriginalGame(CappedA(A)).
module ErasureProgrammedGame(A:CCAExtendedAdversary) = CCAProgrammedFreshGame(CappedA(A)).
module ErasureIndependentGame(A:CCAExtendedAdversary) = CCASharedSetupGame(FreshExpand,CappedA(A)).

(* Logging is private and includes every attempted seed. The challenge
   and oracle interfaces are the existing concrete ones. *)
module ErasureLoggedGame(E:KeygenExpand,A:CCAExtendedAdversary) = {
 proc run() : bool = {
  var pk:W8.t Array1152.t; var sk:W8.t Array2336.t; var win:bool;
  ROMInit.init(); RawXOFStreams.init(); CCADecapOracle.reset();
  ErasureSeedLog.init(); ErasureHit.init();
  (pk,sk) <@ Keygen(UniformSeedRNG,E,SHAKEFROM).run();
  win <@ CCAChallengeOriginal(CappedA(A)).run(pk,sk);
  return win;
 }
}.
module ErasureLoggedProgrammedGame(A:CCAExtendedAdversary) = ErasureLoggedGame(LoggedProgrammedExpand,A).
module ErasureLoggedIndependentGame(A:CCAExtendedAdversary) = ErasureLoggedGame(LoggedErasedExpand,A).

module ErasureStoppedGame(E:KeygenExpand,A:CCAExtendedAdversary) = {
 proc run(qf:int,qg:int) : bool option = {
  var setup:stopped_output; var out:keygen_output;
  var result:bool option; var win:bool;
  ROMInit.init(); RawXOFStreams.init(); CCADecapOracle.reset();
  ErasureSeedLog.init(); ErasureHit.init();
  setup <@ StoppedKeygen(UniformSeedRNG,E).run(qf,qg,witness);
  result <- None;
  if(setup.`1<>None){
   out <- oget setup.`1;
   win <@ CCAChallengeOriginal(CappedA(A)).run(out.`1.`kg_pk,out.`1.`kg_sk);
   result <- Some win;
  }
  return result;
 }
}.
module ErasureStoppedProgrammedGame(A:CCAExtendedAdversary) = ErasureStoppedGame(LoggedProgrammedExpand,A).
module ErasureStoppedIndependentGame(A:CCAExtendedAdversary) = ErasureStoppedGame(LoggedErasedExpand,A).

module ErasureCountedGame(E:KeygenExpand,A:CCAExtendedAdversary) = {
 proc run() : bool*int*int = {
  var setup:counted_output; var win:bool;
  ROMInit.init(); RawXOFStreams.init(); CCADecapOracle.reset();
  ErasureSeedLog.init(); ErasureHit.init();
  setup <@ CountedKeygen(UniformSeedRNG,E).run(witness);
  win <@ CCAChallengeOriginal(CappedA(A)).run(setup.`1.`1.`kg_pk,setup.`1.`1.`kg_sk);
  return (win,setup.`2,setup.`3);
 }
}.

lemma erasure_configure_initial q0 : 0<=q0 =>
 hoare[EBudgetState.configure:q=q0 ==>
 erasure_budget_initial q0 EBudgetState.requests EBudgetState.forwarded
  EBudgetState.limit EBudgetState.overflow EBudgetState.queries].
proof. move=>hq; proc; auto; rewrite /erasure_budget_initial; smt(). qed.

lemma erasure_capped_challenge_ghost_independent
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState}) :
 equiv[CCAChallengeOriginal(CappedA(A)).run ~ CCAChallengeOriginal(CappedA(A)).run:
 ={pk,sk,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,
   glob CCADecapOracle,glob EBudgetState} ==>
 ={res,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,
   glob CCADecapOracle,glob EBudgetState}].
proof.
 proc; call (_: ={glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,
   glob CCADecapOracle,glob EBudgetState}).
 + conseq(cap_e_ghost_independent SharedCCAExtendedOracles); smt().
 + by sim.
 + by sim.
 + by sim.
 + conseq(cap_raw_ghost_independent SharedCCAExtendedOracles); smt().
 + by sim.
 inline CCADecapOracle.init; wp.
 rnd; rnd; call (_: ={glob ROF,glob ROG,glob ROH}); first by sim.
 auto.
qed.

lemma erasure_programmed_game_projection
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState}) :
 equiv[ErasureLoggedProgrammedGame(A).run ~ ErasureProgrammedGame(A).run:
 ={glob A,glob EBudgetState} ==>
 ={res,glob A,glob EBudgetState,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,
   glob CCADecapOracle}].
proof.
 proc; call(erasure_capped_challenge_ghost_independent A).
 call erasure_programmed_keygen_projection.
 inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init
  CCADecapOracle.reset ErasureSeedLog.init ErasureHit.init.
 auto.
qed.

lemma erasure_independent_game_projection
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState}) :
 equiv[ErasureLoggedIndependentGame(A).run ~ ErasureIndependentGame(A).run:
 ={glob A,glob EBudgetState} ==>
 ={res,glob A,glob EBudgetState,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,
   glob CCADecapOracle}].
proof.
 proc; call(erasure_capped_challenge_ghost_independent A).
 call erasure_erased_keygen_projection.
 inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init
  CCADecapOracle.reset ErasureSeedLog.init ErasureHit.init.
 auto.
qed.

(* This preceding hop still allows a partial adversary and partial ROM
   setup. Only the later E-erasure hop needs the explicit A_LL contract. *)
lemma erasure_original_programmed_distance
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState}) &m qf qg :
 0<=qf=>0<=qg=>
 `|Pr[ErasureOriginalGame(A).run() @ &m:res]-
   Pr[ErasureProgrammedGame(A).run() @ &m:res]|<=
 proposal_delta 0 (qf+qg)+fresh_retry_tail qf qg.
proof. exact(cca_original_programmed_setup_distance (CappedA(A)) &m qf qg). qed.

lemma erasure_capped_challenge_hit
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState}) :
 hoare[CCAChallengeOriginal(CappedA(A)).run:
 ErasureHit.bad=erasure_trace_hit ErasureSeedLog.used EBudgetState.queries ==>
 ErasureHit.bad=erasure_trace_hit ErasureSeedLog.used EBudgetState.queries].
proof.
 proc; call(cap_adversary_hit_invariant A SharedCCAExtendedOracles CCADecapOracle).
 call(_:true ==>true); first by trivial.
 rnd; rnd; call(_:true ==>true); first by trivial.
 auto.
qed.

lemma erasure_capped_challenge_query_bound
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState}) q0 :
 hoare[CCAChallengeOriginal(CappedA(A)).run:
 erasure_cap_invariant EBudgetState.requests EBudgetState.forwarded EBudgetState.limit EBudgetState.queries /\
 EBudgetState.limit=q0 ==> size EBudgetState.queries<=q0].
proof.
 proc; call(cap_adversary_queries_bound A SharedCCAExtendedOracles CCADecapOracle q0).
 call(_:true ==>true); first by trivial.
 rnd; rnd; call(_:true ==>true); first by trivial.
 auto.
qed.
