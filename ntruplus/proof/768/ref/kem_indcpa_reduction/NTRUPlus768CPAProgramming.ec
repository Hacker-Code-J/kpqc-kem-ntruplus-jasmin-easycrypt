require import AllCore Distr DBool FMap StdOrder.
from Jasmin require import JWord.
require import Array32 Array96 Array224 Array1152 Array2336.
require import NTRUPlus768CPAModel NTRUPlus768CPAReduction NTRUPlus768CPAHitOracles.
require import NTRUPlus768SimModel NTRUPlus768SimOracles NTRUPlus768SimSampling NTRUPlus768SimLookup.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions NTRUPlus768FOGAdapters NTRUPlus768FOEagerG.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768FreshRetryLaw NTRUPlus768RawXOFStreams NTRUPlus768KEMPayloadSpec.
require import NTRUPlus768CCAGame NTRUPlus768CCAOraclePorts NTRUPlus768CCADecapOracle.
import RealOrder.

module CPAPhaseH(A:CCAExtendedAdversary,H:SimHPort) = {
 proc run(pk ct:W8.t Array1152.t,key:W8.t Array32.t) : bool = {
  var suffix:W8.t Array32.t;var answer:bool;
  suffix<@ROF.get(pk);SimPublic.init(pk,suffix,ct);SimHistory.init();
  answer<@A(SimOracles(FOGActual,H),SimLookup(FOGActual)).guess(pk,ct,key);
  return answer;
 }
}.
module CPAProgrammingKernel(A:CCAExtendedAdversary) = {
 proc run(program:bool,pk:W8.t Array1152.t,msg:W8.t Array96.t,
  hout:W8.t Array224.t,suffix:W8.t Array32.t,ct:W8.t Array1152.t) : bool*bool = {
  var random:W8.t Array32.t;var bit,guess:bool;
  ROH.m<-if program then empty.[(msg,suffix)<-hout] else empty;
  random<$uniform32;bit<$dbool;CPAHitState.init((msg,suffix));
  guess<@CPAPhaseH(A,CPAHitH).run(pk,ct,if bit then random else payload_shared_key hout);
  return(guess=bit,CPAHitState.hit);
 }
}.
module CPAProgrammingGame(A:CCAExtendedAdversary) = {
 proc run(program:bool) : bool*bool = {
  var pk:W8.t Array1152.t;var sk:W8.t Array2336.t;
  var msg:W8.t Array96.t;var hout:W8.t Array224.t;
  var suffix:W8.t Array32.t;var ct:W8.t Array1152.t option;var result:bool*bool;
  ROMInit.init();RawXOFStreams.init();
  (pk,sk)<@Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run();
  msg<$uniform96;hout<$uniform224;suffix<@ROF.get(pk);
  ct<@SimEncrypt(FOGActual).run(pk,msg,hout);
  result<@CPAProgrammingKernel(A).run(program,pk,msg,hout,suffix,oget ct);
  return result;
 }
}.
lemma cpa_phase_actual (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-CPAHitState}) :
 equiv[CPAPhaseH(A,SimHActual).run ~ CPAPhase(A).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams} ==>
 ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h}].
proof.
 proc;call(_: ={ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h});first 6 by sim.
 inline SimHistory.init SimPublic.init;wp;call(_: ={arg,ROF.m} ==> ={res,ROF.m});first by sim. auto.
qed.

lemma cpa_h_outside_program x y p1 p2 :
 cpa_h_outside x (if p1 then empty.[x<-y] else empty) (if p2 then empty.[x<-y] else empty).
proof. rewrite /cpa_h_outside=>z hz;case p1;case p2;rewrite /= ?get_setE;smt(). qed.

lemma cpa_programming_kernel_coupling
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-CPAHitState}) :
 (forall(H<:SimHPort {-A}),islossless H.get=>
 islossless A(SimOracles(FOGActual,H),SimLookup(FOGActual)).guess)=>
 equiv[CPAProgrammingKernel(A).run ~ CPAProgrammingKernel(A).run:
 ={pk,msg,hout,suffix,ct,glob A,ROE.m,ROF.m,ROG.m,glob RawXOFStreams,glob SimPublic,SimHistory.h} ==>
 res{1}.`2=res{2}.`2 /\ (!res{2}.`2=>res{1}.`1=res{2}.`1)].
proof.
 move=>all.
 have cl:forall(H<:SimHPort {-CPAPhaseH(A)}),islossless H.get=>islossless CPAPhaseH(A,H).run.
 + move=>H hl;proc;call(all H hl);call sim_history_init_ll;call sim_public_init_ll;call rof_get_ll;auto.
 proc;wp;call(cpa_hit_context_coupling (CPAPhaseH(A)) cl).
 inline CPAHitState.init;auto=> /> &1 &2 random hr bit hb.
 split;first exact(cpa_h_outside_program _ _ _ _).
 progress;smt().
qed.

module type CPASameEncryptPort = {proc run(pk:W8.t Array1152.t,msg:W8.t Array96.t,hout:W8.t Array224.t):W8.t Array1152.t option}.
lemma cpa_same_encrypt (M<:CPASameEncryptPort) :
 equiv[M.run ~ M.run: ={arg,glob M} ==> ={res,glob M}].
proof. proc true;auto. qed.

lemma cpa_programming_game_coupling
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-CPAHitState}) :
 (forall(H<:SimHPort {-A}),islossless H.get=>
 islossless A(SimOracles(FOGActual,H),SimLookup(FOGActual)).guess)=>
 equiv[CPAProgrammingGame(A).run ~ CPAProgrammingGame(A).run:
 ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h} ==>
 res{1}.`2=res{2}.`2 /\ (!res{2}.`2=>res{1}.`1=res{2}.`1)].
proof.
 move=>all;proc;call(cpa_programming_kernel_coupling A all).
 call(cpa_same_encrypt (SimEncrypt(FOGActual))).
 call(_: ={arg,ROF.m} ==> ={res,ROF.m});first by sim.
 rnd;rnd.
 call(cpa_gen_same (Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM))).
 call(cpa_init_same RawXOFStreams).
 call(cpa_init_same ROMInit).
 auto.
qed.

lemma cpa_programming_game_distance
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-CPAHitState}) &m :
 (forall(H<:SimHPort {-A}),islossless H.get=>
 islossless A(SimOracles(FOGActual,H),SimLookup(FOGActual)).guess)=>
 `|Pr[CPAProgrammingGame(A).run(true)@&m:res.`1]-Pr[CPAProgrammingGame(A).run(false)@&m:res.`1]|
 <=Pr[CPAProgrammingGame(A).run(false)@&m:res.`2].
proof.
 move=>all.
 have good:Pr[CPAProgrammingGame(A).run(true)@&m:res.`1 /\ !res.`2]=
 Pr[CPAProgrammingGame(A).run(false)@&m:res.`1 /\ !res.`2]
 by byequiv(cpa_programming_game_coupling A all)=> //;smt().
 have bad:Pr[CPAProgrammingGame(A).run(true)@&m:res.`2]=
 Pr[CPAProgrammingGame(A).run(false)@&m:res.`2]
 by byequiv(cpa_programming_game_coupling A all)=> //;smt().
 have b0:Pr[CPAProgrammingGame(A).run(true)@&m:res.`1 /\ res.`2]<=
 Pr[CPAProgrammingGame(A).run(true)@&m:res.`2] by rewrite Pr[mu_sub].
 have b1:Pr[CPAProgrammingGame(A).run(false)@&m:res.`1 /\ res.`2]<=
 Pr[CPAProgrammingGame(A).run(false)@&m:res.`2] by rewrite Pr[mu_sub].
 rewrite Pr[mu_split res.`2].
 have ->:Pr[CPAProgrammingGame(A).run(false)@&m:res.`1]=
 Pr[CPAProgrammingGame(A).run(false)@&m:res.`1 /\ res.`2]+
 Pr[CPAProgrammingGame(A).run(false)@&m:res.`1 /\ !res.`2] by rewrite Pr[mu_split res.`2].
 clear all;smt(mu_bounded).
qed.
