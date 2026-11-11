require import AllCore Distr DProd DBool FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152 Array2336.
require import NTRUPlus768CPAModel NTRUPlus768HashPayloadSampling.
require import NTRUPlus768CCAGame NTRUPlus768ROMOracles NTRUPlus768ROMDistributions.
require import NTRUPlus768RawXOFStreams NTRUPlus768KeygenCompleteProof NTRUPlus768FreshRetryLaw.
require import NTRUPlus768SimLookup NTRUPlus768FOEagerG NTRUPlus768KEMPayloadSpec.

(* The single programmed entry is the actual fresh challenge H answer.
   Programming occurs before the adversary starts and preserves every
   auxiliary oracle and the exact native KeyGen law. *)
module CPAProgrammed(A:CCAExtendedAdversary) = {
 proc run() : bool = {
  var pk:W8.t Array1152.t;var sk:W8.t Array2336.t;
  var msg:W8.t Array96.t;var hout:W8.t Array224.t;
  var suffix,random:W8.t Array32.t;var ct:W8.t Array1152.t option;
  var bit,guess:bool;
  ROMInit.init();RawXOFStreams.init();
  (pk,sk)<@Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run();
  msg<$uniform96;hout<$uniform224;suffix<@ROF.get(pk);
  ct<@SimEncrypt(FOGActual).run(pk,msg,hout);
  ROH.m<-empty.[(msg,suffix)<-hout];
  random<$uniform32;bit<$dbool;
  guess<@CPAPhase(A).run(pk,oget ct,if bit then random else payload_shared_key hout);
  return guess=bit;
 }
}.

lemma cpa_hash_headE hout : hash_head hout=payload_shared_key hout.
proof. by rewrite /hash_head /payload_shared_key. qed.
lemma cpa_hash_split_law : dmap (uniform32 `*` uniform192) hash_join=uniform224.
proof. exact uniform224_join_law. qed.
