require import AllCore List Distr FMap DBool.
from Jasmin require import JWord.
require import Array32 Array96 Array129 Array192 Array224 Array768 Array1152 Array2336 Array13634.
require import NTRUPlus768FOModel NTRUPlus768FOChallenge.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768PKEModel NTRUPlus768PKEAlgebra.
require import NTRUPlus768DecapCompleteSpec NTRUPlus768RRecCodec.
require import NTRUPlus768ROMDomains NTRUPlus768ROMOracles NTRUPlus768ROMDistributions.
require import NTRUPlus768ROMPayloadHash NTRUPlus768ROMEncap NTRUPlus768ROMKeygen.
require import NTRUPlus768KEMPayloadSpec NTRUPlus768KEMFailureModel NTRUPlus768KEMFailureProof.
require import NTRUPlus768EncapCompleteRNG NTRUPlus768EncapCompleteBody NTRUPlus768EncapCompleteProof NTRUPlus768EncapCompleteHash.
require import NTRUPlus768EncapFreshBridge NTRUPlus768EncapGuardProof NTRUPlus768EncapGuardSpec.
require import NTRUPlus768EncapHashFPrepareProof NTRUPlus768DecapHashHPrepareProof.
require import NTRUPlus768PolyCBD1CheckedProof NTRUPlus768NTTProof NTRUPlus768DecapMessagePrepareProof.
require import NTRUPlus768PolyToBytesProof NTRUPlus768PolyToBytesAlgebra.
require import NTRUPlus768EncapClearProof NTRUPlus768EncapClearCoinsProof.
require import NTRUPlus768NumericalDFRModel NTRUPlus768ACWC2Oracle.
require import NTRUPlus768CCAOraclePorts NTRUPlus768RawXOF NTRUPlus768RawXOFStreams.
require import NTRUPlus768CCADecapOracle NTRUPlus768CCAGame.

lemma fo_roh_singleton input0 :
 hoare[ROH.get:input=input0 /\ ROH.m=empty ==> ROH.m=empty.[input0<-res]].
proof.
 proc; rcondt 1; first by auto; smt(mem_empty).
 auto=> &hr [hi hm] r hr; by rewrite hi hm /= get_set_sameE.
qed.
lemma fo_h_singleton msg0 suffix0 :
 hoare[SHAKEHROM.shake:input=hash_h_prepare_spec msg0 suffix0 /\ ROH.m=empty ==>
 ROH.m=empty.[(msg0,suffix0)<-res]].
proof.
 proc; call(fo_roh_singleton (msg0,suffix0)); auto=> />.
 by rewrite payload_h_preparation peel_encode_h.
qed.
lemma fo_encap_seed_singleton pk0 msg0 suffix0 fm0 : fm0.[pk0]=Some suffix0 =>
 hoare[EncapSeed(SHAKEFROM,SHAKEHROM).run:
 pk=pk0 /\ coins=msg0 /\ ROF.m=fm0 /\ ROH.m=empty ==>
 ROF.m=fm0 /\ ROH.m=empty.[(msg0,suffix0)<-res]].
proof.
 move=>hc; proc; call(fo_h_singleton msg0 suffix0).
 call(hash_h_prepare_functional witness msg0 suffix0).
 call(rom_f_cached pk0 suffix0 fm0 hc).
 call(encap_hash_f_prepare_functional witness pk0); auto.
qed.

lemma fo_encap_body_cached g gm0 hout0 : acwc2_cache_matches g gm0 =>
 hoare[EncapBody(SHAKEGROM).run:hashout=hout0 /\ ROG.m=gm0 ==>ROG.m=gm0].
proof.
 move=>hg.
 have hr:=pke_domain_cbd(complete_hash_tail hout0).
 have hc:=hg (fo_randomness hout0) hr.
 rewrite -fo_payload_serialized in hc.
 proc; do 6!(call(_:true ==>true); first by trivial).
 call(rom_g_cached (payload_serialized hout0) (g(fo_randomness hout0)) gm0 hc).
 call(message_prepare_functional witness witness (payload_rhat hout0) (payload_rhat_range hout0)).
 call(ntt_functional witness(payload_r hout0)).
 call(poly_cbd1_functional witness(complete_hash_tail hout0)).
 auto=> />; by rewrite payload_rE payload_rhatE poly_tobytes_procedure_specE payload_serializedE.
qed.

lemma fo_encap_core_state pk0 msg0 suffix0 fm0 gm0 g :
 encap_key_canonical pk0 =>fm0.[pk0]=Some suffix0 =>acwc2_cache_matches g gm0 =>
 hoare[EncapCore(SHAKEFROM,SHAKEGROM,SHAKEHROM).run:
 pk=pk0 /\ coins=msg0 /\ ROF.m=fm0 /\ ROG.m=gm0 /\ ROH.m=empty ==>
 ROF.m=fm0 /\ ROG.m=gm0 /\ exists hout,ROH.m=empty.[(msg0,suffix0)<-hout]].
proof.
 move=>hp hf hg; proc; rcondt 2.
 + call(encap_guard_canonical_functional witness encap_zero_ct encap_zero_ss pk0 hp); auto.
 ecall(fo_encap_body_cached g gm0 hashout hg).
 call(fo_encap_seed_singleton pk0 msg0 suffix0 fm0 hf).
 call(encap_guard_canonical_functional witness encap_zero_ct encap_zero_ss pk0 hp).
 auto=> /> hout; exists hout; done.
qed.
lemma fo_encap_derand_state pk0 msg0 suffix0 fm0 gm0 g :
 encap_key_canonical pk0 =>fm0.[pk0]=Some suffix0 =>acwc2_cache_matches g gm0 =>
 hoare[EncapDerand(SHAKEFROM,SHAKEGROM,SHAKEHROM).run:
 pk=pk0 /\ coins=msg0 /\ ROF.m=fm0 /\ ROG.m=gm0 /\ ROH.m=empty ==>
 ROF.m=fm0 /\ ROG.m=gm0 /\ exists hout,ROH.m=empty.[(msg0,suffix0)<-hout]].
proof.
 move=>hp hf hg; proc; call(_:true ==>true); first by trivial.
 call(fo_encap_core_state pk0 msg0 suffix0 fm0 gm0 g hp hf hg); auto.
qed.
lemma fo_encap_instrumented_state pk0 suffix0 fm0 gm0 g :
 encap_key_canonical pk0 =>fm0.[pk0]=Some suffix0 =>acwc2_cache_matches g gm0 =>
 hoare[EncapRandomInstrumented(SHAKEFROM,SHAKEGROM,SHAKEHROM,UniformCoins).run:
 pk=pk0 /\ ROF.m=fm0 /\ ROG.m=gm0 /\ ROH.m=empty ==>
 ROF.m=fm0 /\ ROG.m=gm0 /\ exists hout,ROH.m=empty.[(res.`2,suffix0)<-hout]].
proof.
 move=>hp hf hg; proc; call(_:true ==>true); first by trivial.
 ecall(fo_encap_derand_state pk0 coins suffix0 fm0 gm0 g hp hf hg).
 wp; call(_:true ==>true); first by trivial.
 auto.
qed.

(* The copied coins are private proof data. The return type and all public
   values are the unchanged actual Encaps result, including clearing. *)
module FOChallengeEncap = {
 proc run(pk:W8.t Array1152.t,workspace:W8.t Array13634.t) : encap_result = {
  var er:encap_result; var coins:W8.t Array96.t; var hout:W8.t Array224.t;
  (er,coins) <@ EncapRandomInstrumented(SHAKEFROM,SHAKEGROM,SHAKEHROM,UniformCoins).run(pk,workspace);
  hout <- oget ROH.m.[(coins,complete_sk_suffix FOContext.w.`kg_sk)];
  FOContext.challenge((coins,complete_sk_suffix FOContext.w.`kg_sk),hout,er.`1);
  return er;
 }
}.
lemma fo_challenge_encap_projection :
 equiv[EncapRandom(SHAKEFROM,SHAKEGROM,SHAKEHROM,UniformCoins).run ~ FOChallengeEncap.run:
 ={pk,workspace,ROF.m,ROG.m,ROH.m} ==> ={res,ROF.m,ROG.m,ROH.m}].
proof.
 proc*; inline{2} FOChallengeEncap.run FOContext.challenge; wp.
 call(encap_instrumented_projection UniformCoins SHAKEFROM SHAKEGROM SHAKEHROM); auto.
qed.
lemma fo_challenge_encap_ll : islossless FOChallengeEncap.run.
proof.
 proc; call fo_context_challenge_ll; wp; call encap_instrumented_uniform_lossless; auto.
qed.

lemma fo_encap_instrumented_witness w0 g fm0 gm0 :
 rom_key_relation w0 fm0 =>acwc2_cache_matches g gm0 =>
 hoare[EncapRandomInstrumented(SHAKEFROM,SHAKEGROM,SHAKEHROM,UniformCoins).run:
 pk=w0.`kg_pk /\ ROF.m=fm0 /\ ROG.m=gm0 /\ ROH.m=empty ==>
 let x=(res.`2,complete_sk_suffix w0.`kg_sk) in
 let hout=oget ROH.m.[x] in
 fo_challenge_relation w0 g x hout res.`1.`1 /\
 ROF.m=fm0 /\ ROG.m=gm0 /\ ROH.m=empty.[x<-hout] /\
 res.`1.`3=W32.zero /\ res.`1.`2=payload_shared_key hout /\ res.`1.`4=encap_clear_zero_spec /\
 res.`1.`5=encap_clear_coins_zero_spec].
proof.
 move=>hk hg.
 have hp:=pke_key_from_rom w0 fm0 hk.
 have hc:=pke_key_canonical w0 hp.
 have hf:fm0.[w0.`kg_pk]=Some(complete_sk_suffix w0.`kg_sk)
  by move:hk; rewrite /rom_key_relation; smt().
 conseq (rom_encap_instrumented UniformCoins w0.`kg_pk (complete_sk_suffix w0.`kg_sk) fm0 hc hf)
  (fo_encap_instrumented_state w0.`kg_pk (complete_sk_suffix w0.`kg_sk) fm0 gm0 g hc hf hg) _ => />.
 smt(fo_rom_encap_relation get_set_sameE).
qed.

lemma fo_challenge_encap_state w0 g fm0 gm0 :
 rom_key_relation w0 fm0 =>acwc2_cache_matches g gm0 =>
 hoare[FOChallengeEncap.run:
 pk=w0.`kg_pk /\ FOContext.w=w0 /\ FOContext.g=g /\
 ROF.m=fm0 /\ ROG.m=gm0 /\ ROH.m=empty ==>
 FOContext.w=w0 /\ FOContext.g=g /\ ROF.m=fm0 /\ ROG.m=gm0 /\
 fo_challenge_invariant w0 g FOContext.challenge_h FOContext.challenge_hash
  FOContext.challenge_ct ROH.m /\
 fo_hcache_good w0 g FOContext.challenge_h ROH.m /\
 FOContext.challenge_ct=res.`1 /\ res.`3=W32.zero /\
 res.`2=payload_shared_key FOContext.challenge_hash /\
 res.`4=encap_clear_zero_spec /\ res.`5=encap_clear_coins_zero_spec].
proof.
 move=>hk hg; proc; inline FOContext.challenge; wp.
 call(fo_encap_instrumented_witness w0 g fm0 gm0 hk hg).
 auto=> />; rewrite /fo_challenge_invariant; smt(fo_challenge_singleton_good get_set_sameE).
qed.

(* Same public inputs, public reply, challenge timing and adversary ports.
   The only additional state records the private Encaps witness. *)
module FOChallengeOriginal(A:CCAExtendedAdversary) = {
 module Adv=A(SharedCCAExtendedOracles,CCADecapOracle)
 proc run(pk:W8.t Array1152.t,sk:W8.t Array2336.t) : bool = {
  var real:encap_result; var random:W8.t Array32.t; var bit,guess:bool;
  real <@ FOChallengeEncap.run(pk,witness);
  random <$ uniform32; bit <$ dbool;
  CCADecapOracle.init(sk,real.`1);
  guess <@ Adv.guess(pk,real.`1,if bit then random else real.`2);
  return guess=bit;
 }
}.
lemma fo_challenge_original_projection
 (A<:CCAExtendedAdversary {-FOContext,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle}) :
 equiv[CCAChallengeOriginal(A).run ~ FOChallengeOriginal(A).run:
 ={pk,sk,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob CCADecapOracle} ==>
 ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob CCADecapOracle}].
proof.
 proc; call(_: ={glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle}); 1..6:by sim.
 inline CCADecapOracle.init; wp; rnd; rnd.
 call fo_challenge_encap_projection; auto.
qed.
lemma fo_challenge_original_ll
 (A<:CCAExtendedAdversary {-FOContext,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle}) :
 islossless A(SharedCCAExtendedOracles,CCADecapOracle).guess =>
 islossless FOChallengeOriginal(A).run.
proof.
 move=>hA; proc; call hA; call cca_decap_init_lossless; rnd; rnd;
 call fo_challenge_encap_ll; auto=> />; smt(uniform32_ll dbool_ll).
qed.
