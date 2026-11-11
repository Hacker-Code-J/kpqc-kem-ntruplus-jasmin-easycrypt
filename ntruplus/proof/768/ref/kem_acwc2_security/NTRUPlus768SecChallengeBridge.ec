require import AllCore Distr DBool FMap List.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array768 Array1152 Array2336.
require import NTRUPlus768SecModel NTRUPlus768SecGOracles NTRUPlus768SecGames.
require import NTRUPlus768CPAModel NTRUPlus768CPAReduction NTRUPlus768CPAChallengeBridge.
require import NTRUPlus768CCAGame NTRUPlus768CCAOraclePorts NTRUPlus768CCADecapOracle.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
require import NTRUPlus768FOGAdapters NTRUPlus768FOEagerG NTRUPlus768FOModel NTRUPlus768FOAlgebra NTRUPlus768FOError NTRUPlus768FOChallenge.
require import NTRUPlus768SimModel NTRUPlus768SimSampling NTRUPlus768SimOracles NTRUPlus768SimLookup.
require import NTRUPlus768PKEModel NTRUPlus768PKEKeyDistribution NTRUPlus768PKEAlgebra NTRUPlus768RRecCodec.
require import NTRUPlus768SOTPContracts NTRUPlus768PolySOTPEncodeAlgebra.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768FreshRetryLaw NTRUPlus768AcceptanceProbability.
require import NTRUPlus768KEMPayloadSpec NTRUPlus768EncapGuardSpec.

module type SecRunPort = {proc run(pk ct:W8.t Array1152.t,target:W8.t Array96.t):bool}.
lemma sec_run_same (M<:SecRunPort):equiv[M.run ~ M.run: ={arg,glob M} ==> ={res,glob M}].
proof. proc true;auto. qed.
lemma sec_phase_ll
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory})
 (G<:FOGPort {-A}) :
 (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
 islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
 islossless D.decap=>islossless A(H,D).guess)=>
 islossless G.get=>islossless SecPhase(A,G).run.
proof.
 move=>all gl;proc;call(all (SimOracles(G,SimHActual)) (SimLookup(G)) _ _ _ _ _ _).
 + exact cca_e_ll.
 + exact cca_f_ll.
 + proc;call gl;auto.
 + exact(sim_logged_h_ll SimHActual roh_get_ll).
 + exact(sim_raw_get_ll G SimHActual gl roh_get_ll).
 + exact(sim_lookup_lossless G gl).
 call sim_history_init_ll;call sim_public_init_ll;call rof_get_ll;auto.
qed.
lemma sec_run_ll
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory})
 (G<:FOGPort {-A}) :
 (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
 islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
 islossless D.decap=>islossless A(H,D).guess)=>
 islossless G.get=>islossless SecRun(A,G).run.
proof. move=>all gl;proc;call(sec_phase_ll A G all gl);rnd;auto;smt(uniform32_ll). qed.
lemma sec_phase_plain
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory}) :
 equiv[CPAPhase(A).run ~ SecPhase(A,FOGActual).run:
 ={arg,glob CPAPhase(A)} ==> ={res,glob CPAPhase(A)}].
proof. proc;sim. qed.
lemma sec_reduction_run
 (A<:CCAExtendedAdversary {-CPAReduction,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory}) :
 equiv[CPAReduction(A).guess ~ SecRun(A,FOGActual).run:
 ={ct,glob CPAPhase(A)} /\ CPAReduction.pk{1}=pk{2} /\ CPAReduction.target{1}=target{2}
 ==> ={res,glob CPAPhase(A)}].
proof. proc;call(sec_phase_plain A);rnd;auto. qed.
lemma sec_run_logged_plain
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[SecRun(A,SecGLogged(FOGActual)).run ~ SecRun(A,FOGActual).run:
 ={arg,glob SecRun(A,FOGActual)} ==> ={res,glob SecRun(A,FOGActual)}].
proof. conseq(sec_g_context_logged_plain FOGActual (SecRun(A)))=> //. qed.

module SecCipherView = {
 proc run(pk:W8.t Array1152.t,msg:W8.t Array96.t):W8.t Array1152.t = {
  var hout:W8.t Array224.t;var er:W8.t Array1152.t * W8.t Array32.t;
  hout<$uniform224;er<@CPAEncryptSpec.run(pk,msg,hout);return er.`1;
 }
}.
(* This replacement is related to the actual query only from an empty G
   cache. Its singleton retains the exact challenge pad and randomness. *)
module SecCipherFresh = {
 proc run(pk:W8.t Array1152.t,msg:W8.t Array96.t):W8.t Array1152.t = {
  var hout:W8.t Array224.t;var pad:W8.t Array192.t;
  hout<$uniform224;pad<$uniform192;
  ROG.m<-empty.[rr_G_input(fo_randomness hout)<-pad];
  return pke_ciphertext pk (poly_sotp_encode_spec msg pad) (fo_randomness hout);
 }
}.
module type SecRPort = {proc sample():pke_poly}.
module SecRandomness = {
 proc seed():pke_poly = {
  var hout:W8.t Array224.t;var r:pke_poly;
  hout<$uniform224;r<-fo_randomness hout;return r;
 }
 proc psi():pke_poly = {var r:pke_poly;r<$pke_psi1;return r;}
}.
module SecRSeed = {proc sample=SecRandomness.seed}.
module SecRPsi = {proc sample=SecRandomness.psi}.
module SecCipherFromR(R:SecRPort) = {
 proc run(pk:W8.t Array1152.t,msg:W8.t Array96.t):W8.t Array1152.t = {
  var r:pke_poly;var pad:W8.t Array192.t;
  r<@R.sample();pad<$uniform192;ROG.m<-empty.[rr_G_input r<-pad];
  return pke_ciphertext pk (poly_sotp_encode_spec msg pad) r;
 }
}.
(* The existing whole-buffer law supplies the actual CBD1 distribution.
   The unused hash head is removed before any adversarial call. *)
lemma sec_randomness_law : equiv[SecRSeed.sample ~ SecRPsi.sample:true ==> ={res}].
proof. proc;rndsem*{1} 0;rnd;auto=> />;by rewrite fo_randomness_law. qed.
lemma sec_sim_encrypt_spec_valid :
 equiv[SimEncrypt(FOGActual).run ~ CPAEncryptSpec.run:
 ={pk,msg,hout,ROG.m} /\ encap_key_canonical pk{1} ==>
 res{1}=Some res.`1{2} /\ ={ROG.m}].
proof.
 exists* pk{1},msg{1},hout{1};elim*=>pk0 msg0 hout0.
 case(encap_key_canonical pk0)=>hk;last by conseq(_:false ==>_)=> //;smt().
 conseq(cpa_sim_encrypt_spec pk0 msg0 hout0 hk);smt().
qed.
lemma sec_cipher_view :
 equiv[CPACipher.run ~ SecCipherView.run:
 ={arg,ROG.m} /\ encap_key_canonical pk{1} ==> ={res,ROG.m}].
proof. proc;call sec_sim_encrypt_spec_valid;rnd;auto;smt(). qed.
lemma sec_cipher_view_fresh :
 equiv[SecCipherView.run ~ SecCipherFresh.run:
 ={arg} /\ ROG.m{1}=empty ==> ={res,ROG.m}].
proof.
 proc;inline{1} CPAEncryptSpec.run ROG.get.
 rcondt{1} 6;first by auto;smt(mem_empty).
 auto=> /> &2 hout hh pad hp.
 by rewrite get_set_sameE /= fo_payload_serialized.
qed.
lemma sec_cipher_fresh_seed :
 equiv[SecCipherFresh.run ~ SecCipherFromR(SecRSeed).run:
 ={arg} ==> ={res,ROG.m}].
proof. proc;inline{2} SecRSeed.sample;wp;rnd;wp;rnd;auto. qed.
lemma sec_cipher_seed_psi :
 equiv[SecCipherFromR(SecRSeed).run ~ SecCipherFromR(SecRPsi).run:
 ={arg} ==> ={res,ROG.m}].
proof. proc;wp;rnd;call sec_randomness_law;auto. qed.
lemma sec_cipher_fresh_psi :
 equiv[SecCipherFresh.run ~ SecCipherFromR(SecRPsi).run:
 ={arg} ==> ={res,ROG.m}].
proof.
 transitivity SecCipherFromR(SecRSeed).run
 (={arg} ==> ={res,ROG.m}) (={arg} ==> ={res,ROG.m});1,2:by smt().
 + exact sec_cipher_fresh_seed.
 exact sec_cipher_seed_psi.
qed.
lemma sec_cipher_view_psi :
 equiv[SecCipherView.run ~ SecCipherFromR(SecRPsi).run:
 ={arg} /\ ROG.m{1}=empty ==> ={res,ROG.m}].
proof.
 transitivity SecCipherFresh.run
 (={arg} /\ ROG.m{1}=empty ==> ={res,ROG.m}) (={arg} ==> ={res,ROG.m});1,2:by smt().
 + exact sec_cipher_view_fresh.
 exact sec_cipher_fresh_psi.
qed.
lemma sec_cipher_pure :
 equiv[CPACipher.run ~ SecCipherFromR(SecRPsi).run:
 ={arg} /\ ROG.m{1}=empty /\ encap_key_canonical pk{1} ==> ={res,ROG.m}].
proof.
 transitivity SecCipherView.run
 (={arg,ROG.m} /\ encap_key_canonical pk{1} ==> ={res,ROG.m})
 (={arg} /\ ROG.m{1}=empty ==> ={res,ROG.m});1,2:by smt().
 + exact sec_cipher_view.
 exact sec_cipher_view_psi.
qed.

module SecPureCPAGame(A:CCAExtendedAdversary) = {
 proc run():bool = {
  var pk,ct:W8.t Array1152.t;var sk:W8.t Array2336.t;
  var target,other:W8.t Array96.t;var bit,guess:bool;
  ROMInit.init();RawXOFStreams.init();
  (pk,sk)<@Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run();
  target<$uniform96;other<$uniform96;bit<$dbool;
  ct<@SecCipherFromR(SecRPsi).run(pk,if bit then other else target);
  guess<@SecRun(A,FOGActual).run(pk,ct,target);return guess=bit;
 }
}.
(* This concrete reduction performs no G query while selecting messages.
   ROM initialization and the actual fresh KeyGen therefore establish the
   empty G cache; KeyGen also establishes the public-key canonicality. *)
lemma sec_cpa_pure_game
 (A<:CCAExtendedAdversary {-CPAReduction,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory}) :
 equiv[CPAGame(CPAReduction(A)).run ~ SecPureCPAGame(A).run:
 ={glob SecRun(A,FOGActual)} ==> ={res}].
proof.
 proc;inline{1} CPAReduction(A).choose;wp;
 call(sec_reduction_run A);call sec_cipher_pure;
 rnd;wp;rnd;rnd;wp;
 call(_: ={ROF.m} ==> ={res,ROF.m} /\ encap_key_canonical res{1}.`1).
 + conseq(cpa_gen_same (Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM))) cpa_keygen_canonical _=> //.
 inline ROMInit.init RawXOFStreams.init ROE.init ROF.init ROG.init ROH.init;auto.
qed.
lemma sec_run_plain_logged
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[SecRun(A,FOGActual).run ~ SecRun(A,SecGLogged(FOGActual)).run:
 ={arg,glob SecRun(A,FOGActual)} ==> ={res,glob SecRun(A,FOGActual)}].
proof. symmetry;conseq(sec_run_logged_plain A);smt(). qed.
lemma sec_pure_programmed_game
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[SecPureCPAGame(A).run ~ SecGame(A).run:
 program{2}=true /\ ={glob SecRun(A,FOGActual)} ==> res{1}=res{2}.`so_win].
proof.
 proc;inline{1} SecCipherFromR(SecRPsi).run SecRPsi.sample;
 inline{2} SecGHistory.init;
 wp;call(sec_run_plain_logged A);wp;rnd;wp;rnd;wp;rnd;rnd;rnd;
 call(cpa_gen_same (Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM)));
 call(cpa_init_same RawXOFStreams);call(cpa_init_same ROMInit);auto.
qed.
lemma sec_cpa_programmed_probability
 (A<:CCAExtendedAdversary {-CPAReduction,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) &m :
 Pr[CPAGame(CPAReduction(A)).run()@&m:res]=Pr[SecGame(A).run(true)@&m:res.`so_win].
proof.
 have h:Pr[CPAGame(CPAReduction(A)).run()@&m:res]=Pr[SecPureCPAGame(A).run()@&m:res]
  by byequiv(sec_cpa_pure_game A)=> //.
 rewrite h;byequiv(sec_pure_programmed_game A)=> //.
qed.
