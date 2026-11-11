require import AllCore FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152 Array1153 Array129.
require import NTRUPlus768ROMDomains NTRUPlus768ROMOracles.
require import NTRUPlus768EncapHashFPrepareProof NTRUPlus768DecapMessagePrepareProof NTRUPlus768DecapHashHPrepareProof.

lemma payload_f_preparation pk : encap_hash_f_input_spec pk=encode_f pk.
proof. by rewrite /encap_hash_f_input_spec /encode_f. qed.
lemma payload_g_preparation bs : message_hash_input bs=encode_g bs.
proof. by rewrite /message_hash_input /encode_g. qed.
lemma payload_h_preparation coins suffix : hash_h_prepare_spec coins suffix=encode_h coins suffix.
proof. by rewrite /hash_h_prepare_spec /encode_h. qed.

lemma rom_f_value pk0 :
 hoare[SHAKEFROM.shake:input=encap_hash_f_input_spec pk0 ==> ROF.m.[pk0]=Some res].
proof. proc; ecall(rof_get_value ROF.m pk0); auto => />; by rewrite payload_f_preparation peel_encode_f. qed.
lemma rom_f_cached pk0 suffix0 fm0 : fm0.[pk0]=Some suffix0 =>
 hoare[SHAKEFROM.shake:input=encap_hash_f_input_spec pk0 /\ ROF.m=fm0 ==>
 res=suffix0 /\ ROF.m=fm0].
proof. move=> hc; proc; call(rof_get_cached fm0 pk0 suffix0); auto => />; by rewrite payload_f_preparation peel_encode_f. qed.
lemma rom_g_value bs0 :
 hoare[SHAKEGROM.shake:input=message_hash_input bs0 ==> ROG.m.[bs0]=Some res].
proof. proc; ecall(rog_get_value ROG.m bs0); auto => />; by rewrite payload_g_preparation peel_encode_g. qed.
lemma rom_g_cached bs0 pad0 gm0 : gm0.[bs0]=Some pad0 =>
 hoare[SHAKEGROM.shake:input=message_hash_input bs0 /\ ROG.m=gm0 ==>
 res=pad0 /\ ROG.m=gm0].
proof. move=> hc; proc; call(rog_get_cached gm0 bs0 pad0); auto => />; by rewrite payload_g_preparation peel_encode_g. qed.
lemma rom_h_value coins0 suffix0 :
 hoare[SHAKEHROM.shake:input=hash_h_prepare_spec coins0 suffix0 ==>
 ROH.m.[(coins0,suffix0)]=Some res].
proof. proc; ecall(roh_get_value ROH.m (coins0,suffix0)); auto => />; by rewrite payload_h_preparation peel_encode_h. qed.
lemma rom_h_cached coins0 suffix0 hout0 hm0 : hm0.[(coins0,suffix0)]=Some hout0 =>
 hoare[SHAKEHROM.shake:input=hash_h_prepare_spec coins0 suffix0 /\ ROH.m=hm0 ==>
 res=hout0 /\ ROH.m=hm0].
proof. move=> hc; proc; call(roh_get_cached hm0 (coins0,suffix0) hout0); auto => />; by rewrite payload_h_preparation peel_encode_h. qed.
