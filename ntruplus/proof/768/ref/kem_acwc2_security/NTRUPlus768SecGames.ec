require import AllCore Distr DBool FMap List.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array768 Array1152 Array2336.
require import NTRUPlus768SecModel NTRUPlus768SecGOracles.
require import NTRUPlus768PKEModel NTRUPlus768PKEKeyDistribution NTRUPlus768RRecCodec.
require import NTRUPlus768PolySOTPEncodeAlgebra NTRUPlus768SOTPContracts.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768FreshRetryLaw.
require import NTRUPlus768FOGAdapters NTRUPlus768FOEagerG NTRUPlus768CCAGame.

(* Only the challenge entry changes between these two experiments. The
   honest challenge query is never placed in the adaptive query log. *)
module SecGame(A:CCAExtendedAdversary) = {
 proc run(program:bool):sec_observation = {
  var pk,ct:W8.t Array1152.t;var sk:W8.t Array2336.t;
  var target,other:W8.t Array96.t;var bit,guess:bool;
  var r,code:pke_poly;var pad:W8.t Array192.t;
  ROMInit.init();RawXOFStreams.init();
  (pk,sk)<@Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run();
  target<$uniform96;other<$uniform96;bit<$dbool;
  r<$pke_psi1;pad<$uniform192;
  code<-poly_sotp_encode_spec (if bit then other else target) pad;
  ct<-pke_ciphertext pk code r;
  ROG.m<-if program then empty.[rr_G_input r<-pad] else empty;
  SecGHistory.init();
  guess<@SecRun(A,SecGLogged(FOGActual)).run(pk,ct,target);
  return {|so_win=guess=bit;so_pk=pk;so_ct=ct;so_code=code;so_r=r;so_queries=SecGHistory.queries|};
 }
}.
module SecRandomGame(A:CCAExtendedAdversary) = {
 proc run():sec_observation = {
  var pk,ct:W8.t Array1152.t;var sk:W8.t Array2336.t;
  var target,other:W8.t Array96.t;var bit,guess:bool;var r,code:pke_poly;
  ROMInit.init();RawXOFStreams.init();
  (pk,sk)<@Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run();
  target<$uniform96;other<$uniform96;bit<$dbool;
  r<$pke_psi1;code<$pke_psi1;ct<-pke_ciphertext pk code r;
  SecGHistory.init();
  guess<@SecRun(A,SecGLogged(FOGActual)).run(pk,ct,target);
  return {|so_win=guess=bit;so_pk=pk;so_ct=ct;so_code=code;so_r=r;so_queries=SecGHistory.queries|};
 }
}.
(* The same finite transcript without the reduction's discarded final
   membership test. It does not initialize or inspect any physical ROM. *)
module SecTranscript(A:CCAExtendedAdversary) = {
 proc run(pk ct:W8.t Array1152.t) : W8.t Array1152.t list = {
  var key:W8.t Array32.t;var ignored:bool;
  SecGHistory.init();key<$uniform32;
  ignored<@SecPhase(A,SecGLogged(FOGActual)).run(pk,ct,key);
  return SecGHistory.queries;
 }
}.

lemma sec_hit_record w pk ct code r queries :
 sec_hit {|so_win=w;so_pk=pk;so_ct=ct;so_code=code;so_r=r;so_queries=queries|}=
 (rr_G_input r \in queries).
proof. by rewrite /sec_hit. qed.
