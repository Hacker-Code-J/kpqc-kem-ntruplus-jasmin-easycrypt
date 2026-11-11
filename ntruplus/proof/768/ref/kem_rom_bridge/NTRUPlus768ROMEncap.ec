require import AllCore Distr.
from Jasmin require import JWord JModel_x86.
require import Array768 Array1152 Array1153 Array32 Array96 Array192 Array224.
require import NTRUPlus768EncapCompleteSpec NTRUPlus768EncapCompleteAlgebra NTRUPlus768EncapGuardSpec NTRUPlus768CanonicalDecoder.
require import NTRUPlus768DecapCompleteSpec NTRUPlus768DecapCandidateSpec.
require import NTRUPlus768DecapMessageSpec NTRUPlus768DecapMessagePrepare NTRUPlus768DecapMessagePrepareProof NTRUPlus768DecapHashGBridge.
require import NTRUPlus768PolyCBD1Checked NTRUPlus768PolyCBD1CheckedProof NTRUPlus768PolyCBD1Algebra.
require import NTRUPlus768PolySOTPEncodeChecked NTRUPlus768PolySOTPEncodeCheckedProof NTRUPlus768PolySOTPEncodeAlgebra.
require import NTRUPlus768NTT NTRUPlus768NTTProof.
require import NTRUPlus768PolyBasemul NTRUPlus768PolyBasemulProof.
require import NTRUPlus768PolyCenteredAdd NTRUPlus768PolyCenteredAddCorrectness NTRUPlus768EncapPolyBasemulAddAlgebra.
require import NTRUPlus768PolyToBytes NTRUPlus768PolyToBytesProof NTRUPlus768EncapCopyKey NTRUPlus768EncapCopyKeyProof.

require import FMap NTRUPlus768KEMPayloadSpec NTRUPlus768ROMPayloadHash NTRUPlus768ROMOracles.
require import NTRUPlus768EncapHashFPrepareProof NTRUPlus768DecapHashHPrepareProof NTRUPlus768PolyToBytesAlgebra.
require import NTRUPlus768EncapCompleteBody NTRUPlus768EncapCompleteProof NTRUPlus768EncapCompleteRNG NTRUPlus768EncapCompleteHash NTRUPlus768EncapGuardProof.
require import NTRUPlus768KEMFailureModel NTRUPlus768EncapClearProof NTRUPlus768EncapClearCoinsProof.


lemma rom_encap_seed pk0 coins0 suffix0 fm0 : fm0.[pk0]=Some suffix0 =>
 hoare[EncapSeed(SHAKEFROM,SHAKEHROM).run:pk=pk0 /\ coins=coins0 /\ ROF.m=fm0 ==>
 ROH.m.[(coins0,suffix0)]=Some res /\ ROF.m=fm0].
proof.
 move=> hc; proc.
 call(rom_h_value coins0 suffix0).
 call(hash_h_prepare_functional witness coins0 suffix0).
 call(rom_f_cached pk0 suffix0 fm0 hc).
 call(encap_hash_f_prepare_functional witness pk0).
 by auto => />.
qed.

lemma rom_encap_body pk0 coins0 hout0 : encap_key_canonical pk0 =>
 hoare[EncapBody(SHAKEGROM).run: hp=decoded_poly pk0 /\ coins=coins0 /\ hashout=hout0 ==>
 let pad0=oget ROG.m.[payload_serialized hout0] in
 ROG.m.[payload_serialized hout0]=Some pad0 /\
 res=(NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec(payload_cipher pk0 coins0 hout0 pad0),payload_shared_key hout0)].
proof.
 move=> hk; proc.
 seq 4 : (hp=decoded_poly pk0 /\ coins=coins0 /\ hashout=hout0 /\
 r=payload_r hout0 /\ rhat=payload_rhat hout0 /\
 serialized=payload_serialized hout0 /\ ROG.m.[payload_serialized hout0]=Some pad).
 + call(rom_g_value (payload_serialized hout0)).
   call(message_prepare_functional witness witness (payload_rhat hout0) (payload_rhat_range hout0)).
   call(ntt_functional witness(payload_r hout0)).
   call(poly_cbd1_functional witness(complete_hash_tail hout0)).
   auto => />; by rewrite payload_rE payload_rhatE poly_tobytes_procedure_specE payload_serializedE.
 ecall(encap_copy_key_functional witness hout0).
 ecall(poly_tobytes_functional witness (payload_cipher pk0 coins0 hout0 pad)
   (payload_cipher_serializer pk0 coins0 hout0 pad hk)).
 ecall(poly_centered_add_functional witness (payload_product pk0 hout0) (payload_mhat coins0 pad)
   (payload_product_range pk0 hout0 hk) (payload_mhat_centered coins0 pad)).
 ecall(encap_product_functional witness (decoded_poly pk0) (payload_rhat hout0)).
 ecall(ntt_functional witness (payload_m coins0 pad)).
 ecall(poly_sotp_encode_functional witness coins0 pad).
 auto => /> &hr Hmap.
 rewrite payload_mE payload_mhatE payload_productE payload_cipherE
   /encap_copy_key_spec payload_shared_keyE poly_tobytes_procedure_specE Hmap /=.
 done.
qed.

op [opaque] rom_encap_relation pk coins suffix
 (fm:(W8.t Array1152.t,W8.t Array32.t) fmap)
 (gm:(W8.t Array1152.t,W8.t Array192.t) fmap)
 (hm:(W8.t Array96.t * W8.t Array32.t,W8.t Array224.t) fmap)
 (er:W8.t Array1152.t * W8.t Array32.t * W32.t) =
 let hout=oget hm.[(coins,suffix)] in
 let pad=oget gm.[payload_serialized hout] in
 fm.[pk]=Some suffix /\ hm.[(coins,suffix)]=Some hout /\
 gm.[payload_serialized hout]=Some pad /\
 er=(NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec(payload_cipher pk coins hout pad),
   payload_shared_key hout,W32.zero).

lemma rom_encap_core pk0 coins0 suffix0 fm0 : encap_key_canonical pk0 => fm0.[pk0]=Some suffix0 =>
 hoare[EncapCore(SHAKEFROM,SHAKEGROM,SHAKEHROM).run:
 pk=pk0 /\ coins=coins0 /\ ROF.m=fm0 ==>
 rom_encap_relation pk0 coins0 suffix0 ROF.m ROG.m ROH.m res /\ ROF.m=fm0].
proof.
 move=> hk hc; proc; rcondt 2.
 + call(encap_guard_canonical_functional witness encap_zero_ct encap_zero_ss pk0 hk); by auto.
 ecall(rom_encap_body pk0 coins0 hashout hk).
 call(rom_encap_seed pk0 coins0 suffix0 fm0 hc).
 call(encap_guard_canonical_functional witness encap_zero_ct encap_zero_ss pk0 hk).
 wp.
 skip => />.
 rewrite /rom_encap_relation.
 move=> hout hm Hcache gm Hpad.
 by rewrite Hcache /= hc Hpad.
qed.

lemma rom_encap_derand pk0 coins0 suffix0 fm0 ws0 : encap_key_canonical pk0 => fm0.[pk0]=Some suffix0 =>
 hoare[EncapDerand(SHAKEFROM,SHAKEGROM,SHAKEHROM).run:
 pk=pk0 /\ coins=coins0 /\ workspace=ws0 /\ ROF.m=fm0 ==>
 rom_encap_relation pk0 coins0 suffix0 ROF.m ROG.m ROH.m (res.`1,res.`2,res.`3) /\
 res.`4=encap_clear_zero_spec /\ ROF.m=fm0].
proof.
 move=> hk hc; proc; call(encap_clear_functional ws0).
 call(rom_encap_core pk0 coins0 suffix0 fm0 hk hc).
 wp.
 skip => />.
 move=> result gm hm Hrel.
 by rewrite encap_tuple3_eta.
qed.

lemma rom_encap_instrumented (Q<:EncapRNG {-ROF,-ROG,-ROH}) pk0 suffix0 fm0 :
 encap_key_canonical pk0 => fm0.[pk0]=Some suffix0 =>
 hoare[EncapRandomInstrumented(SHAKEFROM,SHAKEGROM,SHAKEHROM,Q).run:
 pk=pk0 /\ ROF.m=fm0 ==>
 rom_encap_relation pk0 res.`2 suffix0 ROF.m ROG.m ROH.m (res.`1.`1,res.`1.`2,res.`1.`3) /\
 res.`1.`4=encap_clear_zero_spec /\ res.`1.`5=encap_clear_coins_zero_spec /\ ROF.m=fm0].
proof.
 move=> hk hc; proc.
 ecall(encap_clear_coins_functional coins).
 ecall(rom_encap_derand pk0 coins suffix0 fm0 workspace hk hc).
 wp; call(_:true); auto => />; smt().
qed.
