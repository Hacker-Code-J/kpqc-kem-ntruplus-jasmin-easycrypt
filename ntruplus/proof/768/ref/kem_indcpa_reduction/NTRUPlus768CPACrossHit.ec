require import AllCore Distr FMap FSet List StdOrder.
from Jasmin require import JWord.
require import Array32 Array96 Array224 Array1152 Array2336.
require import NTRUPlus768CPAModel NTRUPlus768CPAReduction NTRUPlus768FOModel.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions NTRUPlus768FreshRetryLaw NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
require import NTRUPlus768SimModel NTRUPlus768SimOracles NTRUPlus768SimLookup NTRUPlus768FOGAdapters.
require import NTRUPlus768FOEagerG NTRUPlus768SimSampling NTRUPlus768KeygenCompleteProof.
require import NTRUPlus768CCAGame NTRUPlus768CCAOraclePorts NTRUPlus768CCADecapOracle.
import RField RealOrder.

lemma cpa_message_point x : mu1 uniform96 x=1%r/(2%r^768).
proof.
 rewrite uniform96_point !div1r exprVn //.
 have heq:256%r=2%r^8 by ring.
 by rewrite heq -exprM /=.
qed.
lemma cpa_history_hit_bound (history:(fo_h_input,W8.t Array224.t)fmap) suffix :
 mu uniform96(fun m=>(m,suffix) \in history)<=(fsize history)%r/(2%r^768).
proof.
 have he:mu uniform96(fun m=>(m,suffix) \in history)=
  mu uniform96(fun m=>has(fun x=>x=(m,suffix))(elems(fdom history))).
 + apply mu_eq=>m;rewrite hasP -mem_fdom FSet.memE;smt().
 rewrite he /fsize FSet.cardE.
 apply mu_has_leM=>x hx.
 have hb:mu uniform96(fun m=>x=(m,suffix))<=mu1 uniform96 x.`1.
 + apply mu_le=>m hm;rewrite /pred1;smt().
 by rewrite cpa_message_point in hb.
qed.

module CPALateTarget(A:CCAExtendedAdversary) = {
 proc run():bool = {
  var pk:W8.t Array1152.t;var sk:W8.t Array2336.t;
  var m0,m1:W8.t Array96.t;var ct:W8.t Array1152.t;var key:W8.t Array32.t;var ignored:bool;
  ROMInit.init();RawXOFStreams.init();
  (pk,sk)<@Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run();
  m1<$uniform96;ct<@CPACipher.run(pk,m1);
  key<$uniform32;ignored<@CPAPhase(A).run(pk,ct,key);
  m0<$uniform96;
  return (m0,SimPublic.suffix) \in SimHistory.h;
 }
}.
module CPACrossEarly(A:CCAExtendedAdversary) = {
 proc run():bool = {
  var pk:W8.t Array1152.t;var sk:W8.t Array2336.t;
  var m0,m1:W8.t Array96.t;var ct:W8.t Array1152.t;var key:W8.t Array32.t;var ignored:bool;
  ROMInit.init();RawXOFStreams.init();
  (pk,sk)<@Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run();
  m0<$uniform96;m1<$uniform96;ct<@CPACipher.run(pk,m1);
  key<$uniform32;ignored<@CPAPhase(A).run(pk,ct,key);
  return (m0,SimPublic.suffix) \in SimHistory.h;
 }
}.
lemma cpa_cross_early (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory}) &m :
 Pr[CPAHybrid(A).run(true)@&m:res]=Pr[CPACrossEarly(A).run()@&m:res].
proof.
 byequiv(_:branch{1}=true /\ ={glob CPAHybrid(A)} ==> ={res})=> //.
 proc;wp;call(cpa_phase_same (CPAPhase(A))).
 wp;rnd;call(cpa_cipher_same CPACipher).
 rnd;rnd;call(cpa_gen_same (Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM))).
 call(cpa_init_same RawXOFStreams).
 call(cpa_init_same ROMInit).
 auto;smt().
qed.
lemma cpa_cross_late (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory}) &m :
 Pr[CPAHybrid(A).run(true)@&m:res]=Pr[CPALateTarget(A).run()@&m:res].
proof.
 rewrite(cpa_cross_early A &m).
 byequiv(_: ={glob CPAHybrid(A)} ==> ={res})=> //.
 proc;swap{1} 4 4.
 wp;rnd;call(cpa_phase_same (CPAPhase(A))).
 wp;rnd;call(cpa_cipher_same CPACipher).
 rnd;call(cpa_gen_same (Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM))).
 call(cpa_init_same RawXOFStreams).
 call(cpa_init_same ROMInit).
 auto;smt().
qed.

(* This is a separate count contract for the concrete CPA transcript.
   No H-count bound for the prior Known simulator is reused. *)
lemma cpa_cross_hit (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory}) qHC &m : 0<=qHC=>
 hoare[CPAPhase(A).run:true ==>fsize SimHistory.h<=qHC]=>
 Pr[CPAHybrid(A).run(true)@&m:res]<=qHC%r/(2%r^768).
proof.
 move=>hq hc;rewrite(cpa_cross_late A &m).
 byphoare(_:true ==>res)=> //.
 proc;seq 7:(fsize SimHistory.h<=qHC) 1%r (qHC%r/(2%r^768)) 0%r 1%r true=> //.
 + wp;rnd;skip=> &n hn.
   have hb:=cpa_history_hit_bound SimHistory.h{n} SimPublic.suffix{n}.
   have hp:0%r<2%r^768 by apply expr_gt0;auto.
   split;last by auto.
   apply(ler_trans _ _ _ hb).
   rewrite ler_pmul2r 1:invr_gt0 1:hp le_fromint;smt().
 hoare;call hc.
 rnd;call(_:true ==>true);first by trivial.
 rnd;call(_:true ==>true);first by trivial.
 call(_:true ==>true);first by trivial.
 call(_:true ==>true);first by trivial.
 auto.
qed.
