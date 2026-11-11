require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.
require import Array2336 Array2304 Array1152 Array32 Array96 Array192 Array224 Array768 Array13506.
require import NTRUPlus768DecapCompleteSpec NTRUPlus768DecapCompleteHash NTRUPlus768DecapCompleteTailProof.
require import NTRUPlus768DecapMessageSpec NTRUPlus768DecapMessageProof NTRUPlus768DecapMessageAlgebra.
require import NTRUPlus768DecapR2CompCaller NTRUPlus768DecapGuardSpec NTRUPlus768EncapGuardSpec.
require import NTRUPlus768DecapClear NTRUPlus768DecapClearProof NTRUPlus768DecapHashHBridge.

require import FMap NTRUPlus768KEMPayloadSpec NTRUPlus768KEMPayloadAlgebra NTRUPlus768ROMPayloadHash NTRUPlus768ROMOracles.
require import NTRUPlus768DecapHashHPrepareProof NTRUPlus768NTTProof NTRUPlus768PolyCBD1CheckedProof NTRUPlus768PolyCBD1Algebra.
require import NTRUPlus768DecapMessagePrepareProof NTRUPlus768ValidKeyM1Recovery NTRUPlus768CanonicalDecoder NTRUPlus768PolyToBytesProof.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768ROMKeygen NTRUPlus768ROMEncap.
require import NTRUPlus768DecapCompleteProof NTRUPlus768DecapMessageProof NTRUPlus768DecapFinishCorrectness.
require import NTRUPlus768PolySOTPRoundTrip NTRUPlus768PolySOTPDecodeAlgebra NTRUPlus768PolySOTPDecodeCheckedProof.
require import NTRUPlus768PolyToBytesAlgebra NTRUPlus768NTTAlgebra.


lemma rom_decap_message r20 coins0 pad0 gm0 :
 NTRUPlus768PolyToBytesProof.poly_tobytes_input_qrange r20 =>
 poly_sotp_trit_input (payload_m coins0 pad0) =>
 gm0.[NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec r20]=Some pad0 =>
 hoare[DecapMessage(SHAKEGROM).run:
 serialized=witness /\ input=witness /\ msg=witness /\ r2=r20 /\
 m1=payload_m coins0 pad0 /\ ROG.m=gm0 ==>
 res=(NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec r20,coins0,W32.zero) /\ ROG.m=gm0].
proof.
 move=> hr hm hc; proc.
 call(poly_sotp_decode_functional witness (payload_m coins0 pad0) pad0).
 call(rom_g_cached (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec r20) pad0 gm0 hc).
 call(message_prepare_functional witness witness r20 hr).
 auto => />.
 rewrite /payload_m poly_tobytes_procedure_specE.
 have H := poly_sotp_encode_decode_roundtrip coins0 pad0.
 by move: H; rewrite /poly_sotp_decode_spec; move=> [-> ->].
qed.

lemma rom_decap_tail coins0 suffix0 hout0 hm0 : hm0.[(coins0,suffix0)]=Some hout0 =>
 hoare[CompleteTail(SHAKEHROM).run:
 recovered=payload_serialized hout0 /\ msg=coins0 /\ decode_fail=W32.zero /\ suffix=suffix0 /\ ROH.m=hm0 ==>
 res=(payload_shared_key hout0,W32.zero) /\ ROH.m=hm0].
proof.
 move=> hc; proc.
 call(finish_functional witness hout0 (payload_serialized hout0) (payload_serialized hout0) false).
 call(poly_tobytes_functional witness (payload_rhat hout0) (payload_rhat_range hout0)).
 call(ntt_functional witness (payload_r hout0)).
 call(poly_cbd1_functional witness (complete_hash_tail hout0)).
 call(rom_h_cached coins0 suffix0 hout0 hm0 hc).
 call(hash_h_prepare_functional witness coins0 suffix0).
 auto => />; by rewrite payload_rE payload_rhatE poly_tobytes_procedure_specE payload_serializedE
   /finish_ss_spec /finish_key_prefix payload_shared_keyE.
qed.

lemma rom_decap_success (w:keygen_witness) coins0 hout0 pad0 gm0 hm0 ws0 :
 payload_key_relation w.`kg_fbuf w.`kg_gbuf w.`kg_finv w.`kg_ginv w.`kg_h w.`kg_hinv w.`kg_pk w.`kg_sk =>
 gm0.[payload_serialized hout0]=Some pad0 =>
 hm0.[(coins0,complete_sk_suffix w.`kg_sk)]=Some hout0 =>
 sampled_m1_no_wrap w.`kg_fbuf w.`kg_gbuf (payload_r hout0) (payload_m coins0 pad0) =>
 hoare[CompleteDecaps(SHAKEGROM,SHAKEHROM).run:
 ct=NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec(payload_cipher w.`kg_pk coins0 hout0 pad0) /\
 sk=w.`kg_sk /\ workspace=ws0 /\ ROG.m=gm0 /\ ROH.m=hm0 ==>
 res=(payload_shared_key hout0,W32.zero,clear_zero_spec) /\ ROG.m=gm0 /\ ROH.m=hm0].
proof.
 move=> hk hg hh hn.
 have [hpk _] := payload_key_canonical _ _ _ _ _ _ _ _ hk.
 have henc := payload_cipher_qring w.`kg_pk coins0 hout0 pad0 hpk.
 rewrite /payload_rhat /payload_mhat !ntt_specE in henc.
 have [ha [hmsg hbytes]] := payload_actual_prefix_recovery w.`kg_fbuf w.`kg_gbuf w.`kg_finv w.`kg_ginv
   w.`kg_h w.`kg_hinv w.`kg_pk w.`kg_sk (payload_r hout0) (payload_m coins0 pad0)
   (payload_cipher w.`kg_pk coins0 hout0 pad0) hk (payload_r_range hout0)
   (payload_m_trit coins0 pad0) henc hn.
 have [hr hm] := message_caller_input_closure
   (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec(payload_cipher w.`kg_pk coins0 hout0 pad0))
   (complete_sk_poly w.`kg_sk) ha.
 rewrite hmsg in hm.
 rewrite -ntt_specE payload_rhatE payload_serializedE in hbytes.
 have hc : gm0.[NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec
   (message_r2 (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec(payload_cipher w.`kg_pk coins0 hout0 pad0))
     (complete_sk_poly w.`kg_sk))]=Some pad0.
 + by rewrite hbytes.
 proc; inline CompleteCore(SHAKEGROM,SHAKEHROM).run; rcondt 4.
 + call(guarded_r2_functional witness witness witness witness witness encap_zero_ss
     (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec(payload_cipher w.`kg_pk coins0 hout0 pad0)) (complete_sk_poly w.`kg_sk)).
   auto => />; by rewrite complete_guarded_prefix ha.
 wp; call(decap_clear_functional ws0).
 wp; call(rom_decap_tail coins0 (complete_sk_suffix w.`kg_sk) hout0 hm0 hh).
 call(rom_decap_message
   (message_r2 (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec(payload_cipher w.`kg_pk coins0 hout0 pad0))
     (complete_sk_poly w.`kg_sk)) coins0 pad0 gm0 hr hm hc).
 call(guarded_r2_functional witness witness witness witness witness encap_zero_ss
     (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec(payload_cipher w.`kg_pk coins0 hout0 pad0)) (complete_sk_poly w.`kg_sk)).
 by auto => />; rewrite complete_guarded_prefix ha /= hmsg.
qed.
