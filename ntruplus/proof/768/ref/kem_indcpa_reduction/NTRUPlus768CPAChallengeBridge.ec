require import AllCore Distr DBool FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array768 Array1152 Array2336 Array13634.
require import NTRUPlus768CPAChallenge NTRUPlus768CPAModel NTRUPlus768CPAReduction.
require import NTRUPlus768CCAGame NTRUPlus768ROMOracles NTRUPlus768ROMDistributions NTRUPlus768ROMDomains.
require import NTRUPlus768RawXOFStreams NTRUPlus768KeygenCompleteProof NTRUPlus768FreshRetryLaw.
require import NTRUPlus768FOEagerG NTRUPlus768KEMPayloadSpec NTRUPlus768FOModel NTRUPlus768FOProcedures.
require import NTRUPlus768PKEModel NTRUPlus768PKEProcedures NTRUPlus768EncapGuardSpec NTRUPlus768CanonicalDecoder.
require import NTRUPlus768DecapCompleteSpec NTRUPlus768DecapMessageSpec NTRUPlus768DecapCandidateSpec.
require import NTRUPlus768ROMPayloadHash NTRUPlus768PolySOTPEncodeAlgebra.
require import NTRUPlus768NumericalDFRModel NTRUPlus768FOAlgebra NTRUPlus768FONativeBridge NTRUPlus768ACWC2Model NTRUPlus768PKEAlgebra.
require import NTRUPlus768EncapHashFPrepareProof NTRUPlus768DecapHashHPrepareProof.
require import NTRUPlus768SimModel NTRUPlus768SimOracles NTRUPlus768PolySOTPEncodeCheckedRoundTrip.
require import NTRUPlus768EncapCompleteProof NTRUPlus768KEMFailureModel NTRUPlus768EncapCompleteBody NTRUPlus768EncapCompleteRNG NTRUPlus768EncapCompleteHash.
require import NTRUPlus768EncapGuardProof NTRUPlus768EncapClearProof NTRUPlus768EncapClearCoinsProof.
require import NTRUPlus768ROMEncap NTRUPlus768ROMKeygen NTRUPlus768EncapFreshBridge.
require import NTRUPlus768FOChallenge NTRUPlus768FOChallengeBridge NTRUPlus768FOGAdapters.
require import NTRUPlus768SimLookup NTRUPlus768SimSampling NTRUPlus768SimGames.
require import NTRUPlus768PKECallProof NTRUPlus768SOTPContracts NTRUPlus768ACWC2HashG.
require import NTRUPlus768PolyCBD1CheckedProof NTRUPlus768NTTProof NTRUPlus768DecapMessagePrepareProof.
require import NTRUPlus768PolySOTPEncodeCheckedProof NTRUPlus768PolyBasemulProof.
require import NTRUPlus768PolyCenteredAddCorrectness NTRUPlus768PolyToBytesProof NTRUPlus768EncapCopyKeyProof.

module CPAEncryptSpec = {
 proc run(pk:W8.t Array1152.t,msg:W8.t Array96.t,hout:W8.t Array224.t) : W8.t Array1152.t * W8.t Array32.t = {
  var pad:W8.t Array192.t;
  pad<@ROG.get(payload_serialized hout);
  return (pke_ciphertext pk (poly_sotp_encode_spec msg pad) (fo_randomness hout),payload_shared_key hout);
 }
}.

lemma cpa_product_correct rp0 ap0 bp0 :
 phoare[NTRUPlus768PolyBasemul.M.jade_ntruplus_ntruplus768_amd64_ref_poly_basemul:
 rp=rp0 /\ ap=ap0 /\ bp=bp0 ==>res=candidate_product_spec ap0 bp0]=1%r.
proof. by conseq poly_basemul_lossless (encap_product_functional rp0 ap0 bp0). qed.

lemma cpa_body_spec pk0 msg0 hout0 : encap_key_canonical pk0=>
 equiv[EncapBody(FOGHash(FOGActual)).run ~ CPAEncryptSpec.run:
 hp{1}=decoded_poly pk0 /\ coins{1}=msg0 /\ hashout{1}=hout0 /\
 pk{2}=pk0 /\ msg{2}=msg0 /\ hout{2}=hout0 /\ ={ROG.m} ==>
 ={res,ROG.m}].
proof.
 move=>hk;proc.
 seq 4 1:(hp{1}=decoded_poly pk0 /\ coins{1}=msg0 /\ hashout{1}=hout0 /\
 pk{2}=pk0 /\ msg{2}=msg0 /\ hout{2}=hout0 /\
 rhat{1}=payload_rhat hout0 /\ ={pad,ROG.m}).
 + inline{1} FOGHash(FOGActual).shake.
   wp;call(_: ={input,ROG.m} ==> ={res,ROG.m}); first by sim.
   wp;ecall{1}(message_prepare_correct witness witness(payload_rhat hout0)(payload_rhat_range hout0)).
   ecall{1}(ntt_correct witness(payload_r hout0)).
   wp;ecall{1}(poly_cbd1_correct witness(complete_hash_tail hout0)).
   auto=> />;rewrite payload_rE payload_rhatE NTRUPlus768PolyToBytesAlgebra.poly_tobytes_procedure_specE payload_serializedE.
   by rewrite payload_g_preparation peel_encode_g.
 ecall{1}(encap_copy_key_correct witness hout0).
 ecall{1}(poly_tobytes_correct witness(payload_cipher pk0 msg0 hout0 pad{1})
   (payload_cipher_serializer pk0 msg0 hout0 pad{1} hk)).
 ecall{1}(poly_centered_add_correct witness(payload_product pk0 hout0)(payload_mhat msg0 pad{1})
   (payload_product_range pk0 hout0 hk)(payload_mhat_centered msg0 pad{1})).
 ecall{1}(cpa_product_correct witness(decoded_poly pk0)(payload_rhat hout0)).
 ecall{1}(ntt_correct witness(payload_m msg0 pad{1})).
 ecall{1}(poly_sotp_encode_correct witness msg0 pad{1}).
 clear hk;auto=> /> &2.
 rewrite ?payload_mE ?payload_mhatE ?payload_productE ?payload_cipherE
 /encap_copy_key_spec ?payload_shared_keyE ?NTRUPlus768PolyToBytesAlgebra.poly_tobytes_procedure_specE ?fo_payload_cipher.
 by rewrite /payload_m.
qed.

lemma cpa_code_domain msg pad : pke_domain(poly_sotp_encode_spec msg pad).
proof. rewrite sotp_domainE;exact(poly_sotp_encode_spec_trit_input msg pad). qed.

lemma cpa_sim_encrypt_spec pk0 msg0 hout0 : encap_key_canonical pk0=>
 equiv[SimEncrypt(FOGActual).run ~ CPAEncryptSpec.run:
 pk{1}=pk0 /\ msg{1}=msg0 /\ hout{1}=hout0 /\
 pk{2}=pk0 /\ msg{2}=msg0 /\ hout{2}=hout0 /\ ={ROG.m} ==>
 res{1}=Some res.`1{2} /\ res.`2{2}=payload_shared_key hout0 /\ ={ROG.m}].
proof.
 move=>hk;proc.
 seq 2 1:(pk{1}=pk0 /\ msg{1}=msg0 /\ hout{1}=hout0 /\
 pk{2}=pk0 /\ msg{2}=msg0 /\ hout{2}=hout0 /\
 r{1}=fo_randomness hout0 /\ ={pad,ROG.m}).
 + inline{1} FOHashG(FOGHash(FOGActual)).run FOGHash(FOGActual).shake.
   wp;call(_: ={input,ROG.m} ==> ={res,ROG.m});first by sim.
   wp;ecall{1}(acwc2_g_prepare_correct (fo_randomness hout0)).
   wp;ecall{1}(poly_cbd1_correct witness(complete_hash_tail hout0)).
   auto=> />;rewrite fo_randomnessE;split;first exact(fo_randomness_domain hout0).
   by rewrite acwc2_g_query_payload -fo_payload_serialized.
 ecall{1}(pke_enc_correct pk0 (poly_sotp_encode_spec msg0 pad{1}) (fo_randomness hout0)
   (cpa_code_domain msg0 pad{1}) (fo_randomness_domain hout0)).
 ecall{1}(sotp_encode_correct msg0 pad{1}).
 auto=> /> &2;by rewrite (pke_enc_accept _ _ _ hk).
qed.

lemma cpa_native_encrypt pk0 msg0 hout0 : encap_key_canonical pk0=>
 equiv[EncapBody(FOGHash(FOGActual)).run ~ SimEncrypt(FOGActual).run:
 hp{1}=decoded_poly pk0 /\ coins{1}=msg0 /\ hashout{1}=hout0 /\
 pk{2}=pk0 /\ msg{2}=msg0 /\ hout{2}=hout0 /\ ={ROG.m} ==>
 res{2}=Some res.`1{1} /\ res.`2{1}=payload_shared_key hout0 /\ ={ROG.m}].
proof.
 move=>hk;transitivity CPAEncryptSpec.run
 (hp{1}=decoded_poly pk0 /\ coins{1}=msg0 /\ hashout{1}=hout0 /\
  pk{2}=pk0 /\ msg{2}=msg0 /\ hout{2}=hout0 /\ ={ROG.m} ==> ={res,ROG.m})
 (pk{1}=pk0 /\ msg{1}=msg0 /\ hout{1}=hout0 /\
  pk{2}=pk0 /\ msg{2}=msg0 /\ hout{2}=hout0 /\ ={ROG.m} ==>
  res{2}=Some res.`1{1} /\ res.`2{1}=payload_shared_key hout0 /\ ={ROG.m}).
 + smt().
 + smt().
 + exact(cpa_body_spec pk0 msg0 hout0 hk).
 symmetry;conseq(cpa_sim_encrypt_spec pk0 msg0 hout0 hk);smt().
qed.

module CPASeed = {
 proc run(pk:W8.t Array1152.t,coins:W8.t Array96.t) : W8.t Array224.t = {
  var suffix:W8.t Array32.t;var hout:W8.t Array224.t;
  suffix<@ROF.get(pk);hout<$uniform224;
  ROH.m<-empty.[(coins,suffix)<-hout];return hout;
 }
}.
module CPAEncap = {
 proc run(pk:W8.t Array1152.t,coins:W8.t Array96.t) : W8.t Array1152.t * W8.t Array32.t = {
  var hout:W8.t Array224.t;var ct:W8.t Array1152.t option;
  hout<@CPASeed.run(pk,coins);
  ct<@SimEncrypt(FOGActual).run(pk,coins,hout);
  return(oget ct,payload_shared_key hout);
 }
}.
module CPAEncapRandom = {
 proc run(pk:W8.t Array1152.t) : W8.t Array1152.t * W8.t Array32.t = {
  var msg:W8.t Array96.t;var result:W8.t Array1152.t * W8.t Array32.t;
  msg<$uniform96;result<@CPAEncap.run(pk,msg);return result;
 }
}.

lemma cpa_seed :
 equiv[EncapSeed(SHAKEFROM,SimHShake(SimHActual)).run ~ CPASeed.run:
 ={pk,coins,ROF.m} /\ ROH.m{1}=empty ==> ={res,ROF.m,ROH.m}].
proof.
 proc;seq 2 1:(={pk,coins,ROF.m} /\ suffix{1}=suffix{2} /\ ROH.m{1}=empty).
 + inline{1} SHAKEFROM.shake.
   wp;call(_: ={input,ROF.m} ==> ={res,ROF.m});first by sim.
   wp;ecall{1}(encap_hash_f_prepare_correct witness pk{1}).
   auto=> /> &2;by rewrite payload_f_preparation peel_encode_f.
 inline{1} SimHShake(SimHActual).shake.
 sp 0 0.
 seq 1 0:(peel_h inputh{1}=(coins{2},suffix{2}) /\ ={ROF.m} /\ ROH.m{1}=empty).
 + ecall{1}(hash_h_prepare_correct witness coins{1} suffix{1}).
   auto=> /> &2;by rewrite payload_h_preparation peel_encode_h.
 inline{1} ROH.get;sp;rcondt{1} 1;first by auto;smt(mem_empty).
 auto=> />;smt(get_set_sameE).
qed.

lemma cpa_guard_correct pk0 : encap_key_canonical pk0=>
 phoare[NTRUPlus768EncapGuard.M.jade_ntruplus_ntruplus768_amd64_ref_encap_guard:
 hp=witness /\ ct=encap_zero_ct /\ ss=encap_zero_ss /\ pk=pk0 ==>
 res=(decoded_poly pk0,encap_zero_ct,encap_zero_ss,W32.zero)]=1%r.
proof. move=>hk;by conseq encap_guard_lossless
 (encap_guard_canonical_functional witness encap_zero_ct encap_zero_ss pk0 hk). qed.

lemma cpa_core pk0 : encap_key_canonical pk0=>
 equiv[EncapCore(SHAKEFROM,FOGHash(FOGActual),SimHShake(SimHActual)).run ~ CPAEncap.run:
 pk{1}=pk0 /\ pk{2}=pk0 /\ ={coins,ROF.m,ROG.m} /\ ROH.m{1}=empty ==>
 (res.`1{1},res.`2{1})=res{2} /\ res.`3{1}=W32.zero /\ ={ROF.m,ROG.m,ROH.m}].
proof.
 move=>hk;proc;rcondt{1} 2.
 + move=> &ml;call(encap_guard_canonical_functional witness encap_zero_ct encap_zero_ss pk0 hk);auto.
 ecall(cpa_native_encrypt pk0 coins{1} hashout{1} hk).
 call cpa_seed.
 ecall{1}(cpa_guard_correct pk0 hk).
 auto=> />;smt().
qed.

lemma cpa_random pk0 : encap_key_canonical pk0=>
 equiv[EncapRandom(SHAKEFROM,FOGHash(FOGActual),SimHShake(SimHActual),UniformCoins).run ~ CPAEncapRandom.run:
 pk{1}=pk0 /\ pk{2}=pk0 /\ ={ROF.m,ROG.m} /\ ROH.m{1}=empty ==>
 (res.`1{1},res.`2{1})=res{2} /\ ={ROF.m,ROG.m,ROH.m}].
proof.
 move=>hk;proc;inline{1} EncapDerand(SHAKEFROM,FOGHash(FOGActual),SimHShake(SimHActual)).run.
 call{1} encap_clear_coins_lossless;wp;call{1} encap_clear_lossless;wp.
 call(cpa_core pk0 hk);inline UniformCoins.sample;auto.
qed.

module CPASequenceChallenge(A:CCAExtendedAdversary) = {
 proc run(pk:W8.t Array1152.t) : bool = {
  var er:W8.t Array1152.t*W8.t Array32.t;var random:W8.t Array32.t;var bit,guess:bool;
  er<@CPAEncapRandom.run(pk);random<$uniform32;bit<$dbool;
  guess<@CPAPhase(A).run(pk,er.`1,if bit then random else er.`2);
  return guess=bit;
 }
}.
module CPASequenceGame(A:CCAExtendedAdversary) = {
 proc run() : bool = {
  var pk:W8.t Array1152.t;var sk:W8.t Array2336.t;var win:bool;
  ROMInit.init();RawXOFStreams.init();
  (pk,sk)<@Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run();
  win<@CPASequenceChallenge(A).run(pk);return win;
 }
}.

lemma cpa_public_challenge
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory}) pk0 :
 encap_key_canonical pk0=>
 equiv[SimPublicChallenge(A,FOGActual,SimHActual).run ~ CPASequenceChallenge(A).run:
 pk{1}=pk0 /\ pk{2}=pk0 /\ ={glob A,ROE.m,ROF.m,ROG.m,glob RawXOFStreams} /\ ROH.m{1}=empty ==>
 ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams}].
proof.
 move=>hk;proc;inline{2} CPAPhase(A).run;wp.
 call(_: ={ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,glob SimHistory});1..6:by sim.
 inline SimPublic.init SimHistory.init;wp.
 call(_: ={input,ROF.m} ==> ={res,ROF.m});first by sim.
 wp;rnd;rnd;call(cpa_random pk0 hk);auto.
qed.

lemma cpa_public_challenge_valid
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory}) :
 equiv[SimPublicChallenge(A,FOGActual,SimHActual).run ~ CPASequenceChallenge(A).run:
 ={pk,glob A,ROE.m,ROF.m,ROG.m,glob RawXOFStreams} /\
 encap_key_canonical pk{1} /\ ROH.m{1}=empty ==>
 ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams}].
proof.
 exists* pk{1};elim*=>pk0.
 case(encap_key_canonical pk0)=>hk;last by conseq(_:false ==>_)=> //;smt().
 conseq(cpa_public_challenge A pk0 hk);smt().
qed.

lemma cpa_keygen_canonical :
 hoare[Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run:true ==>encap_key_canonical res.`1].
proof.
 conseq(rom_keygen_public UniformSeedRNG FreshExpand)=> />.
 move=>fm w hk;exact(pke_key_canonical w (pke_key_from_rom w fm hk)).
qed.

module type CPABridgeEncryptPort = {
 proc run(pk:W8.t Array1152.t,msg:W8.t Array96.t,hout:W8.t Array224.t):W8.t Array1152.t option
}.
lemma cpa_bridge_encrypt_same (M<:CPABridgeEncryptPort) :
 equiv[M.run ~ M.run: ={arg,glob M} ==> ={res,glob M}].
proof. proc true;auto. qed.

lemma cpa_actual_sequence
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory}) :
 equiv[SimPublicFreshGame(A).run ~ CPASequenceGame(A).run:
 ={glob A} ==> ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams}].
proof.
 proc;seq 3 3:(={pk,glob A,ROE.m,ROF.m,ROG.m,glob RawXOFStreams} /\
 encap_key_canonical pk{1} /\ ROH.m{1}=empty).
 + call(_: ={ROF.m} ==> ={res,ROF.m} /\ encap_key_canonical res.`1{1}).
   - conseq(_: ={ROF.m} ==> ={res,ROF.m}) cpa_keygen_canonical _=> //.
     exact(cpa_gen_same (Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM))).
   inline ROMInit.init RawXOFStreams.init ROE.init ROF.init ROG.init ROH.init;auto.
 call(cpa_public_challenge_valid A);auto.
qed.

lemma cpa_sequence_programmed
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory}) :
 equiv[CPASequenceGame(A).run ~ CPAProgrammed(A).run:
 ={glob A,glob SimPublic,SimHistory.h} ==> ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams}].
proof.
 proc;inline{1} CPASequenceChallenge(A).run CPAEncapRandom.run CPAEncap.run CPASeed.run.
 wp;call(cpa_phase_same (CPAPhase(A))).
 wp;rnd;rnd;wp.
 call(cpa_bridge_encrypt_same (SimEncrypt(FOGActual))).
 wp;swap{2} 5 1;rnd.
 call(_: ={input,ROF.m} ==> ={res,ROF.m});first by sim.
 wp;rnd;wp;call(cpa_gen_same (Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM))).
 inline ROMInit.init RawXOFStreams.init ROE.init ROF.init ROG.init ROH.init;auto.
qed.

lemma cpa_actual_programmed_probability
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory}) &m :
 Pr[SimPublicFreshGame(A).run() @ &m:res]=Pr[CPAProgrammed(A).run() @ &m:res].
proof.
 have he:Pr[SimPublicFreshGame(A).run() @ &m:res]=Pr[CPASequenceGame(A).run() @ &m:res]
 by byequiv(cpa_actual_sequence A)=> //.
 rewrite he;byequiv(cpa_sequence_programmed A)=> //.
qed.
