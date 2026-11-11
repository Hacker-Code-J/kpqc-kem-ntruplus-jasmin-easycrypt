require import AllCore List Distr DBool FMap.
from Jasmin require import JWord.
require import Array32 Array1152 Array2336.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768StoppedKeygenModel.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions.
require import NTRUPlus768RawXOFStreams NTRUPlus768RawXOF NTRUPlus768CCADecapOracle NTRUPlus768CCAGame.
require import NTRUPlus768KEMFailureModel NTRUPlus768DecapCompleteSpec NTRUPlus768ACWC2Oracle.
require import NTRUPlus768FOModel NTRUPlus768FOKEMGame NTRUPlus768FOChallengeBridge.
require import NTRUPlus768FOHMonitor NTRUPlus768FOQueryBudget NTRUPlus768FOCapRemoval.
require import NTRUPlus768FOBadBound NTRUPlus768FOSetupDistribution.

(* The actual challenge is issued before the adversary's budget starts.
   Its H entry is registered privately before the bad monitor is reset;
   the separate challenge-exclusion lemmas justify this exception. *)
module FOObservedChallenge(A:CCAExtendedAdversary,B:FOBackend) = {
 proc run(pk:W8.t Array1152.t,sk:W8.t Array2336.t) : bool = {
  var real:encap_result; var random:W8.t Array32.t;
  var bit,guess:bool; var q:int;
  real <@ FOChallengeEncap.run(pk,witness);
  random <$ uniform32;bit <$ dbool;
  FOPublicKey.init(pk);CCADecapOracle.init(sk,real.`1);
  q<-FOBudgetState.limit;
  guess <@ FOBadPhase(A,B).run(q,pk,real.`1,if bit then random else real.`2);
  return guess=bit;
 }
}.

(* This is a private setup observation. Only pk/ciphertext/key and the
   original query ports are passed to the adversary. The F table is kept
   with the key, and only the canonical G-input image is prepopulated. *)
module FOObservedKernel(A:CCAExtendedAdversary,B:FOBackend) = {
 proc guess(s:fo_setup_observation) : bool = {
  var win:bool;
  ROE.init();ROG.init();ROH.init();RawXOFStreams.init();CCADecapOracle.reset();
  ROF.m<-s.`2;ROG.m<-acwc2_g_cache s.`3;
  FOContext.init(s.`1.`1,acwc2_gfun s.`3);
  win <@ FOObservedChallenge(A,B).run(s.`1.`1.`kg_pk,s.`1.`1.`kg_sk);
  return win;
 }
}.
module FOObservedNativeKernel(A:CCAExtendedAdversary) =
 FOObservedKernel(A,FOBackendPair(FOSharedOracles,FONativeDecap(SHAKEGROM,FOSHAKEH))).
module FOObservedFullKernel(A:CCAExtendedAdversary) =
 FOObservedKernel(A,FOBackendPair(FOSharedOracles,FOReencryptDecap(SHAKEGROM,FOSHAKEH))).

lemma fo_bad_phase_ll
 (A<:CCAExtendedAdversary {-FOBudgetState}) (B<:FOBackend {-A,-FOBudgetState}) :
 islossless B.e=>islossless B.f=>islossless B.g=>islossless B.h=>islossless B.raw=>islossless B.decap=>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess) =>
 islossless FOBadPhase(A,B).run.
proof.
 move=>he hf hg hh hr hd all; proc.
 call(fo_capped_phase_ll A B he hf hg hh hr hd all).
 call fo_budget_configure_ll;call fo_bad_init_ll;auto.
qed.

lemma fo_observed_challenge_ll
 (A<:CCAExtendedAdversary {-FOBudgetState}) (B<:FOBackend {-A,-FOBudgetState}) :
 islossless B.e=>islossless B.f=>islossless B.g=>islossless B.h=>islossless B.raw=>islossless B.decap=>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess) =>
 islossless FOObservedChallenge(A,B).run.
proof.
 move=>he hf hg hh hr hd all; proc.
 call(fo_bad_phase_ll A B he hf hg hh hr hd all).
 wp;call cca_decap_init_lossless;call fo_public_key_init_ll.
 rnd;rnd;call fo_challenge_encap_ll;auto; smt(dbool_ll uniform32_ll).
qed.

lemma fo_observed_kernel_ll
 (A<:CCAExtendedAdversary {-FOBudgetState}) (B<:FOBackend {-A,-FOBudgetState}) :
 islossless B.e=>islossless B.f=>islossless B.g=>islossless B.h=>islossless B.raw=>islossless B.decap=>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess) =>
 islossless FOObservedKernel(A,B).guess.
proof.
 move=>he hf hg hh hr hd all; proc.
 call(fo_observed_challenge_ll A B he hf hg hh hr hd all).
 call fo_context_init_ll;wp;call cca_decap_reset_lossless;call raw_stream_init_ll;
 call roh_init_ll;call rog_init_ll;call roe_init_ll;auto.
qed.
