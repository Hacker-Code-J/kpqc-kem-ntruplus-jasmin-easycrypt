require import AllCore Distr DBool FMap List.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array768 Array1152 Array2336.
require import NTRUPlus768SecModel NTRUPlus768SecGOracles NTRUPlus768SecGames NTRUPlus768SecChallengeBridge.
require import NTRUPlus768CPAReduction NTRUPlus768CCAGame NTRUPlus768CCAOraclePorts NTRUPlus768CCADecapOracle.
require import NTRUPlus768PKEModel NTRUPlus768PKEKeyDistribution NTRUPlus768RRecCodec.
require import NTRUPlus768PolySOTPEncodeAlgebra NTRUPlus768SOTPContracts.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768FreshRetryLaw NTRUPlus768AcceptanceProbability.
require import NTRUPlus768FOGAdapters NTRUPlus768FOEagerG NTRUPlus768SimModel.

(* The entire SOTP code distribution is independent of the fixed message;
   this statement includes its later ciphertext and query-history uses. *)
module type SecCodePort = {proc sample(msg:W8.t Array96.t):pke_poly}.
module SecCode = {
 proc sample(msg:W8.t Array96.t):pke_poly = {
  var pad:W8.t Array192.t;var code:pke_poly;
  pad<$uniform192;code<-poly_sotp_encode_spec msg pad;return code;
 }
}.
module SecRandomCode = {
 proc sample(msg:W8.t Array96.t):pke_poly = {
  var code:pke_poly;code<$pke_psi1;return code;
 }
}.
lemma sec_code_uniform : equiv[SecCode.sample ~ SecRandomCode.sample:true ==> ={res}].
proof. proc;rndsem*{1} 0;rnd;auto=> /> &1;by rewrite sotp_encode_psi1. qed.

module SecCodedGame(A:CCAExtendedAdversary,C:SecCodePort) = {
 proc run():sec_observation = {
  var pk,ct:W8.t Array1152.t;var sk:W8.t Array2336.t;
  var target,other:W8.t Array96.t;var bit,guess:bool;var r,code:pke_poly;
  ROMInit.init();RawXOFStreams.init();
  (pk,sk)<@Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run();
  target<$uniform96;other<$uniform96;bit<$dbool;
  r<$pke_psi1;code<@C.sample(if bit then other else target);
  ct<-pke_ciphertext pk code r;ROG.m<-empty;
  SecGHistory.init();guess<@SecRun(A,SecGLogged(FOGActual)).run(pk,ct,target);
  return {|so_win=guess=bit;so_pk=pk;so_ct=ct;so_code=code;so_r=r;so_queries=SecGHistory.queries|};
 }
}.
lemma sec_unprogrammed_coded
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[SecGame(A).run ~ SecCodedGame(A,SecCode).run:
 program{1}=false /\ ={glob SecRun(A,SecGLogged(FOGActual))} ==> ={res}].
proof.
 proc;inline{2} SecCode.sample;wp;call(sec_run_same (SecRun(A,SecGLogged(FOGActual))));
 call(cpa_init_same SecGHistory);wp;rnd;wp;rnd;rnd;rnd;rnd;
 call(cpa_gen_same (Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM)));
 call(cpa_init_same RawXOFStreams);call(cpa_init_same ROMInit);auto.
qed.
lemma sec_coded_random
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[SecCodedGame(A,SecCode).run ~ SecCodedGame(A,SecRandomCode).run:
 ={glob SecRun(A,SecGLogged(FOGActual))} ==> ={res}].
proof.
 proc;wp;call(sec_run_same (SecRun(A,SecGLogged(FOGActual))));
 call(cpa_init_same SecGHistory);wp;call sec_code_uniform;rnd;rnd;rnd;rnd;
 call(cpa_gen_same (Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM)));
 call(cpa_init_same RawXOFStreams);call(cpa_init_same ROMInit);auto.
qed.
lemma sec_coded_random_game
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[SecCodedGame(A,SecRandomCode).run ~ SecRandomGame(A).run:
 ={glob SecRun(A,SecGLogged(FOGActual))} ==> ={res}].
proof.
 proc;inline{1} SecRandomCode.sample;wp;call(sec_run_same (SecRun(A,SecGLogged(FOGActual))));
 call(cpa_init_same SecGHistory);wp;rnd;wp;rnd;rnd;rnd;rnd;
 call(cpa_gen_same (Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM)));
 inline ROMInit.init RawXOFStreams.init ROE.init ROF.init ROG.init ROH.init;auto.
qed.
lemma sec_unprogrammed_random_law
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) &m
 (event:sec_observation->bool) :
 Pr[SecGame(A).run(false)@&m:event res]=Pr[SecRandomGame(A).run()@&m:event res].
proof.
 have h1:Pr[SecGame(A).run(false)@&m:event res]=Pr[SecCodedGame(A,SecCode).run()@&m:event res]
  by byequiv(sec_unprogrammed_coded A)=> //.
 have h2:Pr[SecCodedGame(A,SecCode).run()@&m:event res]=Pr[SecCodedGame(A,SecRandomCode).run()@&m:event res]
  by byequiv(sec_coded_random A)=> //.
 rewrite h1 h2;byequiv(sec_coded_random_game A)=> //.
qed.
lemma sec_random_unbiased_ph
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
 islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
 islossless D.decap=>islossless A(H,D).guess)=>
 phoare[SecRandomGame(A).run:true ==> res.`so_win] = (1%r/2%r).
proof.
 move=>all;proc;swap 6 5.
 seq 10 : true 1%r (1%r/2%r) 0%r 0%r true=> //.
 + call(sec_run_ll A (SecGLogged(FOGActual)) all (sec_g_logged_ll FOGActual rog_get_ll));
   call sec_g_history_init_ll;wp;rnd;rnd;rnd;rnd;
   call fresh_keygen_lossless_unconditional;call raw_stream_init_ll;call rom_init_ll;
   auto;smt(uniform96_ll pke_psi1_lossless).
 rnd;auto=> /> &hr;rewrite dboolE /=;case(guess{hr});smt().
qed.
lemma sec_random_unbiased
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) &m :
 (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
 islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
 islossless D.decap=>islossless A(H,D).guess)=>
 Pr[SecRandomGame(A).run()@&m:res.`so_win]=(1%r/2%r).
proof. move=>all;byphoare(sec_random_unbiased_ph A all)=> //. qed.
