require import AllCore Distr DBool FMap.
from Jasmin require import JWord.
require import Array32 Array1152 Array2336.
require import NTRUPlus768SimModel NTRUPlus768SimSampling NTRUPlus768SimAnswer NTRUPlus768SimOracles NTRUPlus768SimLookup NTRUPlus768SimPorts.
require import NTRUPlus768FOModel NTRUPlus768FOSetupDistribution NTRUPlus768FOGAdapters NTRUPlus768FOEagerG NTRUPlus768FOChallengeBridge.
require import NTRUPlus768FOProcedures NTRUPlus768FOKEMGame NTRUPlus768FOJointGames.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
require import NTRUPlus768CCAGame NTRUPlus768CCADecapOracle NTRUPlus768CCAOraclePorts.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768FreshRetryLaw NTRUPlus768EncapCompleteRNG.
require import NTRUPlus768DecapCompleteSpec NTRUPlus768KEMFailureModel NTRUPlus768ACWC2Oracle.
require import NTRUPlus768StoppedKeygenModel NTRUPlus768NumericalDFRModel.

(* This endpoint never installs the secret key in an adversary oracle.
   The F(pk) suffix is obtained through the public oracle. *)
module SimPublicChallenge(A:CCAExtendedAdversary,G:FOGPort,H:SimHPort) = {
 proc run(pk:W8.t Array1152.t) : bool = {
  var real:encap_result;var random,suffix:W8.t Array32.t;var bit,guess:bool;
  real<@EncapRandom(SHAKEFROM,FOGHash(G),SimHShake(H),UniformCoins).run(pk,witness);
  random<$uniform32;bit<$dbool;
  suffix<@ROF.get(pk);
  SimPublic.init(pk,suffix,real.`1);SimHistory.init();
  guess<@A(SimOracles(G,H),SimLookup(G)).guess(pk,real.`1,if bit then random else real.`2);
  return guess=bit;
 }
}.
module SimPublicFreshGame(A:CCAExtendedAdversary) = {
 proc run() : bool = {
  var pk:W8.t Array1152.t;var sk:W8.t Array2336.t;var win:bool;
  ROMInit.init();RawXOFStreams.init();
  (pk,sk)<@Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run();
  win<@SimPublicChallenge(A,FOGActual,SimHActual).run(pk);
  return win;
 }
}.
module SimPublicGContext(A:CCAExtendedAdversary,G:FOGPort) = {
 proc run(out:keygen_output) : bool = {
  var win;win<@SimPublicChallenge(A,G,SimHActual).run(out.`1.`kg_pk);return win;
 }
}.
module SimPublicEagerGame(A:CCAExtendedAdversary)=FOGEagerGame(SimPublicGContext(A)).
module SimPublicKernel(A:CCAExtendedAdversary) = {
 proc guess(s:fo_setup_observation) : bool = {
  var win;
  ROE.init();ROG.init();ROH.init();RawXOFStreams.init();
  ROF.m<-s.`2;ROG.m<-acwc2_g_cache s.`3;
  win<@SimPublicChallenge(A,FOGActual,SimHActual).run(s.`1.`1.`kg_pk);
  return win;
 }
}.
module SimPublicJointGame(A:CCAExtendedAdversary) = {
 proc run() : bool = {
  var s:fo_setup_observation;var win;
  s<@FOSetupSource.guess(witness);win<@SimPublicKernel(A).guess(s);return win;
 }
}.

(* Diagnostic setup records the challenge privately before the adaptive
   phase. Neither hidden H/G erasure nor the final simulator reads this
   record through an adversary callback. *)
module SimObservedSetup = {
 proc run(s:fo_setup_observation) : unit = {
  var real:encap_result;var random:W8.t Array32.t;var bit:bool;
  ROE.init();ROG.init();ROH.init();RawXOFStreams.init();CCADecapOracle.reset();
  ROF.m<-s.`2;ROG.m<-acwc2_g_cache s.`3;
  FOContext.init(s.`1.`1,acwc2_gfun s.`3);
  real<@FOChallengeEncap.run(s.`1.`1.`kg_pk,witness);
  random<$uniform32;bit<$dbool;
  CCADecapOracle.init(s.`1.`1.`kg_sk,real.`1);
  FOPublicKey.init(s.`1.`1.`kg_pk);
  SimPublic.init(s.`1.`1.`kg_pk,complete_sk_suffix s.`1.`1.`kg_sk,real.`1);
  SimHistory.init();SimBad.init();
  SimPhaseInput.init(s.`1.`1.`kg_pk,real.`1,if bit then random else real.`2,bit);
 }
}.
module SimObservedPortKernel(A:CCAExtendedAdversary,U:SimAnswer) = {
 proc guess(s:fo_setup_observation) : bool = {
  var win;
  SimObservedSetup.run(s);
  win<@SimAdaptive(A,SimLeaksBackend(FOGActual,SimHActual),U).distinguish(s);
  return win;
 }
}.
module SimObservedRealKernel(A:CCAExtendedAdversary)=SimObservedPortKernel(A,SimAnswerReal(FOGActual,SimHActual)).
module SimObservedKnownKernel(A:CCAExtendedAdversary)=SimObservedPortKernel(A,SimAnswerNever).
module SimDirectPhase(A:CCAExtendedAdversary,O:CCAExtendedOraclePort,D:CCADecapPort) = {
 proc distinguish(s:fo_setup_observation) : bool = {
  var guess;guess<@A(O,D).guess(SimPhaseInput.pk,SimPhaseInput.ct,SimPhaseInput.key);
  return guess=SimPhaseInput.bit;
 }
}.
module SimObservedLookupKernel(A:CCAExtendedAdversary) = {
 proc guess(s:fo_setup_observation) : bool = {
  var win;
  SimObservedSetup.run(s);
  win<@SimDirectPhase(A,SimOracles(FOGActual,SimHActual),SimLookup(FOGActual)).distinguish(s);
  return win;
 }
}.

lemma sim_observed_setup_ll : islossless SimObservedSetup.run.
proof.
 proc;call sim_phase_input_ll;call sim_bad_init_ll;call sim_history_init_ll;call sim_public_init_ll;
 call fo_public_key_init_ll;call cca_decap_init_lossless;rnd;rnd;call fo_challenge_encap_ll;
 call fo_context_init_ll;wp;call cca_decap_reset_lossless;call raw_stream_init_ll;
 call roh_init_ll;call rog_init_ll;call roe_init_ll;auto;smt(dbool_ll uniform32_ll).
qed.
