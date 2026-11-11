require import AllCore Distr DBool FMap FSet List.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152 Array2336.
require import NTRUPlus768SimGames NTRUPlus768SimLookup NTRUPlus768SimOracles NTRUPlus768SimSampling NTRUPlus768SimModel.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions NTRUPlus768FOModel NTRUPlus768FOGAdapters NTRUPlus768FOEagerG.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768FreshRetryLaw NTRUPlus768RawXOFStreams NTRUPlus768KEMPayloadSpec.
require import NTRUPlus768CCAGame NTRUPlus768CCAOraclePorts NTRUPlus768CCADecapOracle.

(* ACWC2 encryption uses the actual CBD/SOTP/PKE calls and the same public
   G oracle as the adversary. The first 32 bytes of the independent seed
   are unused by encryption; the remaining 192 bytes supply CBD1. *)
module CPACipher = {
 proc run(pk:W8.t Array1152.t,msg:W8.t Array96.t) : W8.t Array1152.t = {
  var hout:W8.t Array224.t;var ct:W8.t Array1152.t option;
  hout<$uniform224;ct<@SimEncrypt(FOGActual).run(pk,msg,hout);
  return oget ct;
 }
}.
(* The transcript is generated without access to either challenge message.
   The suffix, raw/typed H history, and public decapsulation are unchanged. *)
module CPAPhase(A:CCAExtendedAdversary) = {
 proc run(pk ct:W8.t Array1152.t,key:W8.t Array32.t) : bool = {
  var suffix:W8.t Array32.t;var answer:bool;
  suffix<@ROF.get(pk);SimPublic.init(pk,suffix,ct);SimHistory.init();
  answer<@A(SimOracles(FOGActual,SimHActual),SimLookup(FOGActual)).guess(pk,ct,key);
  return answer;
 }
}.
module type CPAAdversary = {
 proc choose(pk:W8.t Array1152.t):W8.t Array96.t * W8.t Array96.t
 proc guess(ct:W8.t Array1152.t):bool
}.
module CPAReduction(A:CCAExtendedAdversary) : CPAAdversary = {
 var pk:W8.t Array1152.t
 var target:W8.t Array96.t
 proc choose(pk0:W8.t Array1152.t) : W8.t Array96.t * W8.t Array96.t = {
  var other:W8.t Array96.t;
  pk<-pk0;target<$uniform96;other<$uniform96;
  return(target,other);
 }
 proc guess(ct:W8.t Array1152.t) : bool = {
  var key:W8.t Array32.t;var ignored:bool;
  key<$uniform32;ignored<@CPAPhase(A).run(pk,ct,key);
  return !((target,SimPublic.suffix) \in SimHistory.h);
 }
}.
(* Shared G and auxiliary E/F/raw interfaces remain explicit ROM state.
   The reduction has no access to sk or the challenger's challenge bit. *)
module CPAGame(B:CPAAdversary) = {
 proc run() : bool = {
  var pk:W8.t Array1152.t;var sk:W8.t Array2336.t;
  var m0,m1:W8.t Array96.t;var ct:W8.t Array1152.t;var bit,guess:bool;
  ROMInit.init();RawXOFStreams.init();
  (pk,sk)<@Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run();
  (m0,m1)<@B.choose(pk);bit<$dbool;
  ct<@CPACipher.run(pk,if bit then m1 else m0);
  guess<@B.guess(ct);return guess=bit;
 }
}.
module CPAHybrid(A:CCAExtendedAdversary) = {
 proc run(branch:bool) : bool = {
  var pk:W8.t Array1152.t;var sk:W8.t Array2336.t;
  var m0,m1:W8.t Array96.t;var ct:W8.t Array1152.t;var key:W8.t Array32.t;var ignored:bool;
  ROMInit.init();RawXOFStreams.init();
  (pk,sk)<@Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run();
  m0<$uniform96;m1<$uniform96;
  ct<@CPACipher.run(pk,if branch then m1 else m0);
  key<$uniform32;ignored<@CPAPhase(A).run(pk,ct,key);
  return (m0,SimPublic.suffix) \in SimHistory.h;
 }
}.
module CPAUnprogrammed(A:CCAExtendedAdversary) = {
 proc run() : bool = {
  var pk:W8.t Array1152.t;var sk:W8.t Array2336.t;
  var msg:W8.t Array96.t;var ct:W8.t Array1152.t;var key:W8.t Array32.t;var ignored:bool;
  ROMInit.init();RawXOFStreams.init();
  (pk,sk)<@Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run();
  msg<$uniform96;ct<@CPACipher.run(pk,msg);
  key<$uniform32;ignored<@CPAPhase(A).run(pk,ct,key);
  return (msg,SimPublic.suffix) \in SimHistory.h;
 }
}.

lemma cpa_cipher_ll : islossless CPACipher.run.
proof. proc;call(sim_encrypt_lossless FOGActual rog_get_ll);rnd;auto;smt(uniform224_ll). qed.
