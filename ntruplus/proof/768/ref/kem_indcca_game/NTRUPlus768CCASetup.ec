require import AllCore Distr FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array768 Array1152 Array2336 Array14466 Array13634.
require import NTRUPlus768StoppedKeygenModel NTRUPlus768KeygenCompleteRetry.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteAttempt.
require import NTRUPlus768KeygenCompleteFinish NTRUPlus768KeygenCompleteProof.
require import NTRUPlus768KeygenClearProof NTRUPlus768ROMKeygen NTRUPlus768ROMOracles.
require import NTRUPlus768KEMPayloadSpec NTRUPlus768ValidKeyM1Recovery.
require import NTRUPlus768EncapGuardSpec NTRUPlus768EncapGuardProof.
require import NTRUPlus768EncapCompleteProof NTRUPlus768EncapCompleteRNG.
require import NTRUPlus768EncapCompleteHash NTRUPlus768DecapMessageSpec NTRUPlus768DecapCompleteHash.
require import NTRUPlus768EncapClearProof NTRUPlus768EncapClearCoinsProof.
require import NTRUPlus768NumericalDFRModel.

lemma cca_bounded_f_accepted (R<:KeygenSeedRNG) (E<:KeygenExpand) :
 hoare[BoundedRetry(R,E).f : true ==>
 res.`rs_ok => keygen_f_accepted res.`rs_buf res.`rs_ntt res.`rs_inv].
proof.
 proc; inline BoundedRetry(R,E).f_from; wp.
 while(status=W64.zero => keygen_f_accepted buf ntt inverse).
 + wp; call(keygen_attempt_f_accepted E); call (_:true ==> true); auto.
 auto=> />; rewrite /retry_initial /=; smt(W64.to_uint0 W64.to_uint1).
qed.
lemma cca_bounded_g_accepted (R<:KeygenSeedRNG) (E<:KeygenExpand) :
 hoare[BoundedRetry(R,E).g : true ==>
 res.`rs_ok => keygen_g_accepted res.`rs_buf res.`rs_ntt res.`rs_inv].
proof.
 proc; inline BoundedRetry(R,E).g_from; wp.
 while(status=W64.zero => keygen_g_accepted buf ntt inverse).
 + wp; call(keygen_attempt_g_accepted E); call (_:true ==> true); auto.
 auto=> />; rewrite /retry_initial /=; smt(W64.to_uint0 W64.to_uint1).
qed.

lemma cca_observed_finish_valid : hoare[ObservedFinish.run :
 keygen_f_accepted fv.`rs_buf fv.`rs_ntt fv.`rs_inv /\
 keygen_g_accepted gv.`rs_buf gv.`rs_ntt gv.`rs_inv ==>
 rom_key_relation res.`1 ROF.m /\ res.`2=keygen_clear_zero_spec].
proof.
 proc; ecall(keygen_clear_functional workspace).
 ecall(rom_keygen_finish_from_accepted fv.`rs_buf gv.`rs_buf
  fv.`rs_ntt fv.`rs_inv gv.`rs_ntt gv.`rs_inv).
 auto=> /> &hr hf hg result fm hout.
 rewrite /rom_finish_valid /= in hout.
 by rewrite /rom_key_relation /=.
qed.

lemma cca_stopped_keygen_valid (R<:KeygenSeedRNG) (E<:KeygenExpand) :
 hoare[StoppedKeygen(R,E).run : true ==>
 res.`1<>None => rom_key_relation (oget res.`1).`1 ROF.m /\
  (oget res.`1).`2=keygen_clear_zero_spec].
proof.
 proc; seq 3 : (result=None /\
  (fv.`rs_ok => keygen_f_accepted fv.`rs_buf fv.`rs_ntt fv.`rs_inv)).
 + call(cca_bounded_f_accepted R E); auto=> />; smt().
 if; last by auto.
 seq 1 : (result=None /\ keygen_f_accepted fv.`rs_buf fv.`rs_ntt fv.`rs_inv /\
  (gv.`rs_ok => keygen_g_accepted gv.`rs_buf gv.`rs_ntt gv.`rs_inv)).
 + call(cca_bounded_g_accepted R E); auto=> />; smt().
 if; last by auto.
 wp; call cca_observed_finish_valid; auto=> />; smt().
qed.

lemma cca_rom_key_canonical w fm : rom_key_relation w fm => encap_key_canonical w.`kg_pk.
proof.
 move=>h; rewrite /rom_key_relation in h; move:h=>[hk hf].
 have h:=payload_key_canonical _ _ _ _ _ _ _ _ hk; smt().
qed.
lemma cca_keygen_public_canonical (R<:KeygenSeedRNG {-ROF}) (E<:KeygenExpand {-ROF}) :
 hoare[Keygen(R,E,SHAKEFROM).run : true ==> encap_key_canonical res.`1].
proof.
 proc; call(rom_keygen_instrumented R E).
 auto=> /> result fm hv hc.
 exact (cca_rom_key_canonical result.`1 fm hv).
qed.

lemma cca_encap_core_status (F<:EncapSHAKEF) (G<:MessageSHAKE) (H<:CompleteSHAKEH) pk0 :
 encap_key_canonical pk0 =>
 hoare[EncapCore(F,G,H).run : pk=pk0 ==> res.`3=W32.zero].
proof.
 move=>hk; proc; seq 1 : (status=W32.zero).
 + call(encap_guard_canonical_functional witness encap_zero_ct encap_zero_ss pk0 hk); auto.
 if; last by auto.
 call(_:true); first by trivial.
 call(_:true); first by trivial.
 auto.
qed.
lemma cca_encap_derand_status (F<:EncapSHAKEF) (G<:MessageSHAKE) (H<:CompleteSHAKEH) pk0 :
 encap_key_canonical pk0 =>
 hoare[EncapDerand(F,G,H).run : pk=pk0 ==> res.`3=W32.zero].
proof.
 move=>hk; proc; ecall(encap_clear_functional workspace); call(cca_encap_core_status F G H pk0 hk); auto.
qed.
lemma cca_encap_random_status (R<:EncapRNG) (F<:EncapSHAKEF) (G<:MessageSHAKE) (H<:CompleteSHAKEH) pk0 :
 encap_key_canonical pk0 =>
 hoare[EncapRandom(F,G,H,R).run : pk=pk0 ==> res.`3=W32.zero].
proof.
 move=>hk; proc; ecall(encap_clear_coins_functional coins); call(cca_encap_derand_status F G H pk0 hk);
 call(_:true ==> true); auto.
qed.

lemma cca_encap_random_status_any (R<:EncapRNG) (F<:EncapSHAKEF) (G<:MessageSHAKE) (H<:CompleteSHAKEH) :
 hoare[EncapRandom(F,G,H,R).run : encap_key_canonical pk ==> res.`3=W32.zero].
proof.
 exists* pk; elim*=>pk0.
 case (encap_key_canonical pk0)=>hk.
 + conseq (cca_encap_random_status R F G H pk0 hk)=> />; smt().
 conseq (_:false ==> _) => //; smt().
qed.
