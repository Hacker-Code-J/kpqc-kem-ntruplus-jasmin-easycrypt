require import AllCore Distr DBool FMap List StdOrder.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array768 Array1152 Array2336.
require import NTRUPlus768SecModel NTRUPlus768SecGOracles NTRUPlus768SecGames NTRUPlus768SecChallengeBridge.
require import NTRUPlus768CPAReduction NTRUPlus768PKEModel NTRUPlus768PKEKeyDistribution NTRUPlus768RRecCodec.
require import NTRUPlus768PolySOTPEncodeAlgebra NTRUPlus768SOTPContracts.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768FreshRetryLaw.
require import NTRUPlus768FOGAdapters NTRUPlus768FOEagerG NTRUPlus768CCAGame NTRUPlus768CCAOraclePorts NTRUPlus768CCADecapOracle.
require import NTRUPlus768SimModel NTRUPlus768SimSampling NTRUPlus768SimOracles NTRUPlus768SimLookup.
import RealOrder.

module SecMarkedGame(A:CCAExtendedAdversary) = {
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
  SecGHistory.init();SecGMark.init(rr_G_input r);
  guess<@SecRun(A,SecGMarked(FOGActual)).run(pk,ct,target);
  return {|so_win=guess=bit;so_pk=pk;so_ct=ct;so_code=code;so_r=r;so_queries=SecGHistory.queries|};
 }
}.
lemma sec_g_outside_program x y p1 p2 :
 sec_g_outside x (if p1 then empty.[x<-y] else empty) (if p2 then empty.[x<-y] else empty).
proof. rewrite /sec_g_outside=>z hz;case p1;case p2;rewrite /= ?get_setE;smt(). qed.

lemma sec_marked_projection
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[SecMarkedGame(A).run ~ SecGame(A).run:
 ={arg,glob SecRun(A,FOGActual)} ==> ={res}].
proof.
 proc;wp;call(sec_g_context_marked_logged FOGActual (SecRun(A))).
 inline SecGHistory.init SecGMark.init;wp.
 rnd;rnd;rnd;rnd;rnd;
 call(cpa_gen_same (Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM))).
 call(cpa_init_same RawXOFStreams);call(cpa_init_same ROMInit);auto.
qed.
lemma sec_marked_hit
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 hoare[SecMarkedGame(A).run:true ==>SecGMark.hit=sec_hit res].
proof.
 proc;wp;call(sec_g_context_history FOGActual (SecRun(A))).
 inline SecGHistory.init SecGMark.init;wp.
 rnd;rnd;rnd;rnd;rnd;
 call(_:true ==>true);first by trivial.
 call(_:true ==>true);first by trivial.
 call(_:true ==>true);first by trivial.
 auto;rewrite /sec_hit /=;smt().
qed.
lemma sec_marked_recorded
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[SecMarkedGame(A).run ~ SecGame(A).run:
 ={arg,glob SecRun(A,FOGActual)} ==> ={res} /\ SecGMark.hit{1}=sec_hit res{2}].
proof. conseq(sec_marked_projection A)(sec_marked_hit A) _=> //;smt(). qed.

lemma sec_marked_coupling
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 (forall(G<:FOGPort {-SecRun(A)}),islossless G.get=>islossless SecRun(A,G).run)=>
 equiv[SecMarkedGame(A).run ~ SecMarkedGame(A).run:
 ={glob SecRun(A,FOGActual)} ==>
 ={SecGMark.hit} /\ (!SecGMark.hit{2}=> ={res})].
proof.
 move=>all;proc;wp;call(sec_g_context_coupling (SecRun(A)) all).
 inline SecGHistory.init SecGMark.init;wp.
 rnd;rnd;rnd;rnd;rnd;
 call(cpa_gen_same (Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM))).
 call(cpa_init_same RawXOFStreams);call(cpa_init_same ROMInit);auto=> />.
 move=> &1 &2 target ht other ho bit hb r hr pad hp.
 split;first exact(sec_g_outside_program _ _ _ _).
 progress;smt().
qed.

lemma sec_programming_distance
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) &m :
 (forall(G<:FOGPort {-SecRun(A)}),islossless G.get=>islossless SecRun(A,G).run)=>
 `|Pr[SecGame(A).run(true)@&m:res.`so_win]-Pr[SecGame(A).run(false)@&m:res.`so_win]|
 <=Pr[SecGame(A).run(false)@&m:sec_hit res].
proof.
 move=>all.
 have h0:Pr[SecGame(A).run(true)@&m:res.`so_win]=Pr[SecMarkedGame(A).run(true)@&m:res.`so_win]
 by apply/eq_sym;byequiv(sec_marked_projection A)=> //.
 have h1:Pr[SecGame(A).run(false)@&m:res.`so_win]=Pr[SecMarkedGame(A).run(false)@&m:res.`so_win]
 by apply/eq_sym;byequiv(sec_marked_projection A)=> //.
 have hit:Pr[SecMarkedGame(A).run(false)@&m:SecGMark.hit]=Pr[SecGame(A).run(false)@&m:sec_hit res]
 by byequiv(sec_marked_recorded A)=> //;smt().
 have good:Pr[SecMarkedGame(A).run(true)@&m:res.`so_win /\ !SecGMark.hit]=
 Pr[SecMarkedGame(A).run(false)@&m:res.`so_win /\ !SecGMark.hit].
 + byequiv(sec_marked_coupling A all)=> //.
   clear all h0 h1 hit;smt().
 have bad:Pr[SecMarkedGame(A).run(true)@&m:SecGMark.hit]=
 Pr[SecMarkedGame(A).run(false)@&m:SecGMark.hit]
 by byequiv(sec_marked_coupling A all)=> //;smt().
 have b0:Pr[SecMarkedGame(A).run(true)@&m:res.`so_win /\ SecGMark.hit]<=Pr[SecMarkedGame(A).run(true)@&m:SecGMark.hit]
 by rewrite Pr[mu_sub].
 have b1:Pr[SecMarkedGame(A).run(false)@&m:res.`so_win /\ SecGMark.hit]<=Pr[SecMarkedGame(A).run(false)@&m:SecGMark.hit]
 by rewrite Pr[mu_sub].
 rewrite h0 h1 -hit Pr[mu_split SecGMark.hit].
 have ->:Pr[SecMarkedGame(A).run(false)@&m:res.`so_win]=
 Pr[SecMarkedGame(A).run(false)@&m:res.`so_win /\ SecGMark.hit]+
 Pr[SecMarkedGame(A).run(false)@&m:res.`so_win /\ !SecGMark.hit] by rewrite Pr[mu_split SecGMark.hit].
 clear all;smt(mu_bounded).
qed.
