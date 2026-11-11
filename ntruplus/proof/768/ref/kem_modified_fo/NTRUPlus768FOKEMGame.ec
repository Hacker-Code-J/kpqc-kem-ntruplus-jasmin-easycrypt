require import AllCore Distr DBool FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array1152 Array2336 Array13506 Array13634.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768FreshRetryLaw.
require import NTRUPlus768DecapMessageSpec NTRUPlus768DecapCompleteHash.
require import NTRUPlus768DecapCompleteProof NTRUPlus768DecapCompleteSpec.
require import NTRUPlus768EncapCompleteRNG NTRUPlus768EncapCompleteSpec.
require import NTRUPlus768KEMFailureModel.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions NTRUPlus768NumericalDFRModel.
require import NTRUPlus768CCAStatusAdapter NTRUPlus768CCADecapOracle.
require import NTRUPlus768CCAOraclePorts NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
require import NTRUPlus768CCAGame NTRUPlus768CCASetupGame.
require import NTRUPlus768FOModel NTRUPlus768FOProcedures.

module FOPublicKey = {
 var pk:W8.t Array1152.t
 proc init(pk0:W8.t Array1152.t) = {pk<-pk0;}
}.

(* Both ports use the existing exact challenge exclusion and count every
   Decaps request, including blocked and malformed ciphertexts. *)
module FONativeDecap(G:MessageSHAKE,H:CompleteSHAKEH) : CCADecapPort = {
 proc decap(ct:W8.t Array1152.t) : cca_reply = {
  var answer:cca_reply;
  var result:W8.t Array32.t*W32.t*W8.t Array13506.t;
  CCADecapOracle.count<-CCADecapOracle.count+1;
  if(CCADecapOracle.cstar=Some ct){answer<-None;}
  else{
   result <@ CompleteDecaps(G,H).run(ct,CCADecapOracle.sk,witness);
   answer<-cca_status_result result.`1 result.`2;
  }
  return answer;
 }
}.
module FOReencryptDecap(G:MessageSHAKE,H:CompleteSHAKEH) : CCADecapPort = {
 proc decap(ct:W8.t Array1152.t) : cca_reply = {
  var answer:cca_reply;
  var result:W8.t Array32.t*W32.t*W8.t Array13506.t;
  CCADecapOracle.count<-CCADecapOracle.count+1;
  if(CCADecapOracle.cstar=Some ct){answer<-None;}
  else{
   result <@ FODecaps(G,H).run(FOPublicKey.pk,ct,CCADecapOracle.sk,witness);
   answer<-cca_status_result result.`1 result.`2;
  }
  return answer;
 }
}.

(* G/H and the query ports are parameters only for exact simulation
   lemmas. Concrete endpoints below instantiate the actual shared ROM. *)
module FOCCAChallenge(G:MessageSHAKE,H:CompleteSHAKEH,
 O:CCAExtendedOraclePort,D:CCADecapPort,A:CCAExtendedAdversary) = {
 proc run(pk:W8.t Array1152.t,sk:W8.t Array2336.t) : bool = {
  var real:encap_result; var random:W8.t Array32.t; var bit,guess:bool;
  real <@ EncapRandom(SHAKEFROM,G,H,UniformCoins).run(pk,witness);
  random <$ uniform32;bit <$ dbool;
  FOPublicKey.init(pk);
  CCADecapOracle.init(sk,real.`1);
  guess <@ A(O,D).guess(pk,real.`1,if bit then random else real.`2);
  return guess=bit;
 }
}.
module FOFreshGame(A:CCAExtendedAdversary,D:CCADecapPort) = {
 proc run() : bool = {
  var pk:W8.t Array1152.t; var sk:W8.t Array2336.t; var win:bool;
  ROMInit.init();RawXOFStreams.init();CCADecapOracle.reset();
  (pk,sk) <@ Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run();
  win <@ FOCCAChallenge(SHAKEGROM,SHAKEHROM,SharedCCAExtendedOracles,D,A).run(pk,sk);
  return win;
 }
}.
module FOFreshNativeGame(A:CCAExtendedAdversary) =
 FOFreshGame(A,FONativeDecap(SHAKEGROM,SHAKEHROM)).
module FOFreshReencryptGame(A:CCAExtendedAdversary) =
 FOFreshGame(A,FOReencryptDecap(SHAKEGROM,SHAKEHROM)).

lemma fo_public_key_init_ll : islossless FOPublicKey.init.
proof. proc; auto. qed.
lemma fo_native_decap_ll (G<:MessageSHAKE) (H<:CompleteSHAKEH) :
 islossless G.shake=>islossless H.shake=>islossless FONativeDecap(G,H).decap.
proof.
 move=>hG hH; proc; sp; if; first by auto.
 wp; call(complete_lossless G H hG hH); auto.
qed.
lemma fo_reencrypt_decap_ll (G<:MessageSHAKE) (H<:CompleteSHAKEH) :
 islossless G.shake=>islossless H.shake=>islossless FOReencryptDecap(G,H).decap.
proof.
 move=>hG hH; proc; sp; if; first by auto.
 wp; call(fo_decaps_lossless G H hG hH); auto.
qed.

lemma fo_native_decap_projection :
 equiv[FONativeDecap(SHAKEGROM,SHAKEHROM).decap ~ CCADecapOracle.decap:
 ={ct,glob CCADecapOracle} ==> ={res,glob CCADecapOracle}].
proof. proc; inline CCAStatusAdapter.run; sim. qed.

lemma fo_native_challenge_projection
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey}) :
 equiv[FOCCAChallenge(SHAKEGROM,SHAKEHROM,SharedCCAExtendedOracles,
   FONativeDecap(SHAKEGROM,SHAKEHROM),A).run ~ CCAChallengeOriginal(A).run:
 ={pk,sk,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle} ==>
 ={res,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle}].
proof.
 proc; call(_: ={glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle});
  1..5:by sim.
 + conseq fo_native_decap_projection; smt().
 inline CCADecapOracle.init FOPublicKey.init; wp; rnd; rnd.
 call(_: ={pk,workspace,glob ROF,glob ROG,glob ROH} ==> ={res,glob ROF,glob ROG,glob ROH}); first by sim.
 auto.
qed.

lemma fo_fresh_native_game_projection
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey}) :
 equiv[FOFreshNativeGame(A).run ~ CCASharedSetupGame(FreshExpand,A).run:
 ={glob A} ==> ={res,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle}].
proof.
 proc; call(fo_native_challenge_projection A).
 call(_: ={glob ROF} ==> ={res,glob ROF}); first by sim.
 inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init CCADecapOracle.reset.
 auto.
qed.

lemma fo_fresh_native_game_event
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey})
 &m (event:bool->bool) :
 Pr[FOFreshNativeGame(A).run() @ &m:event res]=
 Pr[CCASharedSetupGame(FreshExpand,A).run() @ &m:event res].
proof. by byequiv(fo_fresh_native_game_projection A)=> //. qed.
