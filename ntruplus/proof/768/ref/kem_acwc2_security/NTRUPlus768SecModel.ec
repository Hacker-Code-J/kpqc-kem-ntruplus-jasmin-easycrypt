require import AllCore Distr DBool FMap List.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array768 Array1152 Array2336.
require import NTRUPlus768CPAModel NTRUPlus768CPAReduction.
require import NTRUPlus768SimModel NTRUPlus768SimSampling NTRUPlus768SimOracles NTRUPlus768SimLookup.
require import NTRUPlus768FOGAdapters NTRUPlus768FOEagerG.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
require import NTRUPlus768CCAOraclePorts NTRUPlus768CCAGame NTRUPlus768CCADecapOracle.
require import NTRUPlus768PKEModel NTRUPlus768PKEKeyDistribution NTRUPlus768RRecCodec.
require import NTRUPlus768SOTPContracts NTRUPlus768PolySOTPEncodeAlgebra.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768FreshRetryLaw.

(* One G parameter serves direct queries, raw queries, and every internal
   public-lookup encryption. The challenge's own G evaluation is separate. *)
module SecPhase(A:CCAExtendedAdversary,G:FOGPort) = {
 proc run(pk ct:W8.t Array1152.t,key:W8.t Array32.t) : bool = {
  var suffix:W8.t Array32.t;var answer:bool;
  suffix<@ROF.get(pk);SimPublic.init(pk,suffix,ct);SimHistory.init();
  answer<@A(SimOracles(G,SimHActual),SimLookup(G)).guess(pk,ct,key);
  return answer;
 }
}.
module SecRun(A:CCAExtendedAdversary,G:FOGPort) = {
 proc run(pk ct:W8.t Array1152.t,target:W8.t Array96.t) : bool = {
  var key:W8.t Array32.t;var ignored:bool;
  key<$uniform32;ignored<@SecPhase(A,G).run(pk,ct,key);
  return !((target,SimPublic.suffix) \in SimHistory.h);
 }
}.
module type SecGContext(G:FOGPort) = {
 proc run(pk ct:W8.t Array1152.t,target:W8.t Array96.t) : bool {G.get}
}.

type sec_observation = {
 so_win:bool;
 so_pk:W8.t Array1152.t;
 so_ct:W8.t Array1152.t;
 so_code:pke_poly;
 so_r:pke_poly;
 so_queries:W8.t Array1152.t list;
}.
op sec_hit (s:sec_observation) = rr_G_input s.`so_r \in s.`so_queries.
(* Computational injectivity is a collision-finding experiment, not an
   assertion that the complete encryption map is mathematically injective. *)
type sec_collision = pke_poly*pke_poly*pke_poly*pke_poly.
op sec_inj_win (pk:W8.t Array1152.t) (w:sec_collision) =
 pke_domain w.`1 /\ pke_domain w.`2 /\ pke_domain w.`3 /\ pke_domain w.`4 /\
 (w.`1,w.`3)<>(w.`2,w.`4) /\
 pke_enc_spec pk w.`1 w.`3=pke_enc_spec pk w.`2 w.`4 /\
 pke_enc_spec pk w.`1 w.`3<>None.
module type SecINJAdversary = {proc run(pk:W8.t Array1152.t):sec_collision}.
module type SecOWAdversary = {proc run(pk ct:W8.t Array1152.t):pke_poly}.
module SecINJGame(B:SecINJAdversary) = {
 proc run():bool = {
  var pk:W8.t Array1152.t;var sk:W8.t Array2336.t;var out:sec_collision;
  ROMInit.init();RawXOFStreams.init();
  (pk,sk)<@Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run();
  out<@B.run(pk);return sec_inj_win pk out;
 }
}.
module SecOWGame(B:SecOWAdversary) = {
 proc run():bool = {
  var pk,ct:W8.t Array1152.t;var sk:W8.t Array2336.t;
  var code,r,answer:pke_poly;
  ROMInit.init();RawXOFStreams.init();
  (pk,sk)<@Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run();
  code<$pke_psi1;r<$pke_psi1;ct<-pke_ciphertext pk code r;
  answer<@B.run(pk,ct);return answer=code;
 }
}.

lemma sec_inj_witness pk m m' r r' ct :
 pke_domain m=>pke_domain m'=>pke_domain r=>pke_domain r'=>r<>r'=>
 pke_enc_spec pk m r=Some ct=>pke_enc_spec pk m' r'=Some ct=>
 sec_inj_win pk (m,m',r,r').
proof. rewrite /sec_inj_win;smt(). qed.
