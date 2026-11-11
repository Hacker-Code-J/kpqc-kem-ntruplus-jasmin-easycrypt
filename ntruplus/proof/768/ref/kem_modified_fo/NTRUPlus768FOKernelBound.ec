require import AllCore List Distr FMap StdOrder.
from Jasmin require import JWord.
require import Array32 Array1152 Array2336.
require import NTRUPlus768ROMOracles NTRUPlus768RawXOFStreams NTRUPlus768CCADecapOracle.
require import NTRUPlus768CCAGame NTRUPlus768ACWC2Oracle.
require import NTRUPlus768FOModel NTRUPlus768FOError NTRUPlus768FOKEMGame.
require import NTRUPlus768FOQueryBudget NTRUPlus768FOBadBound NTRUPlus768FOFixedGames.
require import NTRUPlus768FOBackendContracts NTRUPlus768FOBackendBounds.
require import NTRUPlus768FOSetupDistribution NTRUPlus768FOSetupExpectation.
import RealOrder.

lemma fo_full_phase_bad_ph
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
   -FOPublicKey,-FOContext,-FOBadState,-FOBudgetState}) w0 g0 Q :
 0<=Q =>phoare[FOBadPhase(A,FOFullBackend).run:
 q=Q /\ FOContext.w=w0 /\ FOContext.g=g0 ==>FOBadState.bad] <=(Q%r*fo_error w0 g0).
proof.
 move=>hQ; bypr=> &m [hq [hw hg]]; rewrite hq.
 exact(fo_full_bounded_bad A w0 g0 Q pk{m} ct{m} key{m} &m hQ hw hg).
qed.

(* Plain challenge Encaps may update F/G/H and the challenge snapshot.
   It preserves the fixed w/g and the configured limit. The following
   bounded phase resets bad itself, so no challenge-bad precondition is used. *)
lemma fo_observed_full_challenge_bad_ph
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
   -FOPublicKey,-FOContext,-FOBadState,-FOBudgetState}) w0 g0 Q :
 0<=Q =>phoare[FOObservedChallenge(A,FOFullBackend).run:
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOBudgetState.limit=Q ==>FOBadState.bad]
 <=(Q%r*fo_error w0 g0).
proof.
 move=>hQ; proc; call(fo_full_phase_bad_ph A w0 g0 Q hQ).
 wp; call(_:true ==>true); first by trivial.
 call(_:true ==>true); first by trivial.
 rnd; rnd; call(_:true ==>true); first by trivial.
 auto.
qed.

lemma fo_observed_full_kernel_bad_ph
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
   -FOPublicKey,-FOContext,-FOBadState,-FOBudgetState}) s0 Q :
 0<=Q =>phoare[FOObservedFullKernel(A).guess:
 s=s0 /\ FOBudgetState.limit=Q ==>FOBadState.bad] <=(Q%r*fo_setup_error s0).
proof.
 move=>hQ; rewrite /fo_setup_error; proc.
 call(fo_observed_full_challenge_bad_ph A s0.`1.`1 (acwc2_gfun s0.`3) Q hQ).
 inline FOContext.init CCADecapOracle.reset RawXOFStreams.init
   ROE.init ROG.init ROH.init.
 auto.
qed.

(* This bounds the returned bad mass even for a partial adversary. No
   validity/support premise on s, or adversary losslessness, is required. *)
lemma fo_observed_full_kernel_bad
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
   -FOPublicKey,-FOContext,-FOBadState,-FOBudgetState}) s Q &m :
 0<=Q =>FOBudgetState.limit{m}=Q =>
 Pr[FOObservedFullKernel(A).guess(s) @ &m:FOBadState.bad]<=Q%r*fo_setup_error s.
proof.
 move=>hQ hlim; byphoare(fo_observed_full_kernel_bad_ph A s Q hQ)=> //.
qed.
