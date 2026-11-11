require import AllCore List FMap Distr.
from Jasmin require import JWord.
require import NTRUPlus768ROMDomains NTRUPlus768ROMOracles.
require import NTRUPlus768DecapMessageProof NTRUPlus768DecapCompleteTailProof.
require import NTRUPlus768DecapCompleteProof.
require import NTRUPlus768CCAOraclePorts NTRUPlus768RawXOFStreams.
require import NTRUPlus768RawXOF NTRUPlus768RawXOFLaws.
require import NTRUPlus768CCAStatusAdapter NTRUPlus768CCADecapOracle NTRUPlus768CCAGame.

(* The actual Decaps hash adapters only extend G/H. All arithmetic and
   clearing calls keep their original procedure boundaries. *)
lemma cca_shake_g_preserves_raw_known x0 s0 : hoare[SHAKEGROM.shake :
 raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other ==>
 raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other].
proof.
 proc; ecall(rog_get_value ROG.m (peel1153 input)); auto=> />;
 smt(raw_stored_mono cache_extends_refl).
qed.
lemma cca_shake_h_preserves_raw_known x0 s0 : hoare[SHAKEHROM.shake :
 raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other ==>
 raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other].
proof.
 proc; ecall(roh_get_value ROH.m (peel_h input)); auto=> />;
 smt(raw_stored_mono cache_extends_refl).
qed.
lemma cca_decap_message_preserves_raw_known x0 s0 : hoare[DecapMessage(SHAKEGROM).run :
 raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other ==>
 raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other].
proof.
 proc; call(_:true ==> true); first by trivial.
 call(cca_shake_g_preserves_raw_known x0 s0).
 call(_:true ==> true); first by trivial.
 auto.
qed.
lemma cca_decap_tail_preserves_raw_known x0 s0 : hoare[CompleteTail(SHAKEHROM).run :
 raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other ==>
 raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other].
proof.
 proc; call(_:true ==> true); first by trivial.
 call(_:true ==> true); first by trivial.
 call(_:true ==> true); first by trivial.
 call(_:true ==> true); first by trivial.
 call(cca_shake_h_preserves_raw_known x0 s0).
 call(_:true ==> true); first by trivial.
 auto.
qed.
lemma cca_decap_core_preserves_raw_known x0 s0 : hoare[CompleteCore(SHAKEGROM,SHAKEHROM).run :
 raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other ==>
 raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other].
proof.
 proc; seq 1 : (raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
   RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other).
 + call(_:true ==> true); first by trivial. auto.
 if; last by auto.
 call(cca_decap_tail_preserves_raw_known x0 s0).
 call(cca_decap_message_preserves_raw_known x0 s0); auto.
qed.
lemma cca_actual_decaps_preserves_raw_known x0 s0 : hoare[CompleteDecaps(SHAKEGROM,SHAKEHROM).run :
 raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other ==>
 raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other].
proof.
 proc; call(_:true ==> true); first by trivial.
 call(cca_decap_core_preserves_raw_known x0 s0); auto.
qed.
lemma cca_status_adapter_preserves_raw_known x0 s0 : hoare[CCAStatusAdapter.run :
 raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other ==>
 raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other].
proof. proc; call(cca_actual_decaps_preserves_raw_known x0 s0); auto. qed.

(* This includes blocked, malformed, and ordinary ciphertexts. No accepted
   encoding, successful decryption, or termination premise is required. *)
lemma cca_decap_preserves_raw_known x0 s0 : hoare[CCADecapOracle.decap :
 raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other ==>
 raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other].
proof.
 proc; sp 1; if; first by auto.
 call(cca_status_adapter_preserves_raw_known x0 s0); auto.
qed.

(* The exact adversary interface used by both CCA games may interleave all
   five hash-query methods with Decaps adaptively. Every stored stream is
   preserved on every returning trace, even for a non-lossless adversary. *)
lemma cca_adversary_preserves_raw_known
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams}) x0 s0 :
 hoare[A(SharedCCAExtendedOracles,CCADecapOracle).guess :
 raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other ==>
 raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other].
proof.
 proc (raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
   RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other); 1,2:by auto.
 + exact(typed_e_preserves_raw_known x0 s0).
 + exact(typed_f_preserves_raw_known x0 s0).
 + exact(typed_g_preserves_raw_known x0 s0).
 + exact(typed_h_preserves_raw_known x0 s0).
 + exact(raw_get_preserves_known x0 s0).
 exact(cca_decap_preserves_raw_known x0 s0).
qed.
