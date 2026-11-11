require import AllCore Distr.
from Jasmin require import JWord JModel_x86.
require import Array32 Array96 Array129 Array192 Array224 Array768 Array1152 Array2336 Array13506.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768PKEModel NTRUPlus768PKEAlgebra NTRUPlus768PKECallProof.
require import NTRUPlus768RRecNativeProcedures NTRUPlus768RRecNativeComparison.
require import NTRUPlus768DecapCompleteSpec NTRUPlus768DecapCompleteHash NTRUPlus768DecapCompleteTailProof NTRUPlus768DecapCompleteProof.
require import NTRUPlus768DecapMessageSpec NTRUPlus768DecapMessageProof NTRUPlus768DecapMessagePrepareProof NTRUPlus768DecapMessageAlgebra.
require import NTRUPlus768DecapR2CompCaller NTRUPlus768DecapGuardSpec NTRUPlus768EncapGuardSpec.
require import NTRUPlus768DecapFinishCorrectness NTRUPlus768VerifyProof NTRUPlus768DecapClearProof.
require import NTRUPlus768PolyCBD1CheckedProof NTRUPlus768PolyCBD1Algebra NTRUPlus768NTTProof NTRUPlus768NTTAlgebra NTRUPlus768PolyToBytesProof.

lemma native_verify_correct a b :
 phoare[Finish.verify_bytes:arg=(a,b) ==>res=verify_spec a b]=1%r.
proof. by conseq finish_verify_ll (finish_verify_functional a b). qed.

(* Even an arbitrary incoming decode-failure WORD is preserved: equality
   of the byte-comparison decisions suffices for the actual finish kernel. *)
lemma native_finish_test_equiv :
 equiv[Finish.jade_ntruplus_ntruplus768_amd64_ref_decap_finish ~
       Finish.jade_ntruplus_ntruplus768_amd64_ref_decap_finish:
 ={ss,hashout,decode_fail} /\
 (recovered{1}=regenerated{1})=(recovered{2}=regenerated{2}) ==> ={res}].
proof.
 proc; seq 2 2:(={ss,hashout,decode_fail,comparison}).
 + ecall{1}(native_verify_correct recovered{1} regenerated{1}).
   ecall{2}(native_verify_correct recovered{2} regenerated{2}).
   auto=> />; rewrite /verify_spec; smt().
 by sim.
qed.

lemma native_tail_outline (G<:MessageSHAKE) (H<:CompleteSHAKEH {-G}) :
 equiv[CompleteTail(H).run ~ NativeTailOutlined(H).run:
 ={recovered,msg,decode_fail,suffix,glob G,glob H} ==> ={res,glob G,glob H}].
proof.
 proc; inline{2} NativeRegenerateFinish.run; wp.
 conseq (_:_ ==> ={ss,status,glob G,glob H})=> //; sim.
qed.

(* G is coupled as the same abstract call. Only the deterministic prepare
   prefix is interpreted; no functional or losslessness premise on G or H. *)
lemma native_message_equiv (G<:MessageSHAKE) (H<:CompleteSHAKEH {-G}) r20 m10 :
 poly_tobytes_input_qrange r20 =>
 equiv[DecapMessage(G).run ~ DecapMessage(G).run:
 serialized{1}=witness /\ serialized{2}=witness /\
 input{1}=witness /\ input{2}=witness /\ msg{1}=witness /\ msg{2}=witness /\
 r2{1}=r20 /\ r2{2}=r20 /\ m1{1}=m10 /\ m1{2}=m10 /\ ={glob G,glob H} ==>
 ={res,glob G,glob H} /\ res.`1{1}=NTRUPlus768PolyToBytesProof.poly_tobytes_spec r20].
proof.
 move=>hr; proc.
 call(_: ={msg,ap,buf} ==> ={res}); first by sim.
 call(_: ={input,glob G,glob H} ==> ={res,glob G,glob H}); first by sim.
 ecall{1}(message_prepare_correct witness witness r20 hr).
 ecall{2}(message_prepare_correct witness witness r20 hr).
 auto.
qed.
lemma native_guarded_correct ct0 sk0 :
 phoare[GuardedR2.run:
 rp=witness /\ mp=witness /\ cp=witness /\ fp=witness /\ hp=witness /\
 ss=encap_zero_ss /\ ct=ct0 /\ skpoly=complete_sk_poly sk0 ==>
 res=guarded_r2_spec witness witness encap_zero_ss ct0 (complete_sk_poly sk0)]=1%r.
proof.
 by conseq guarded_r2_lossless
 (guarded_r2_functional witness witness witness witness witness encap_zero_ss ct0 (complete_sk_poly sk0)).
qed.

lemma native_body_reencrypt_equiv pk0 ct0 m0 bs0 hout0 df0 :
 rrec_compare_relation pk0 ct0 m0 bs0 =>
 equiv[NativeRegenerateFinish.run ~ ReencryptFinish.run:
 recovered{1}=bs0 /\ hashout{1}=hout0 /\ decode_fail{1}=df0 /\
 pk{2}=pk0 /\ ct{2}=ct0 /\ m1{2}=m0 /\ hashout{2}=hout0 /\ decode_fail{2}=df0 ==>
 ={res}].
proof.
 move=>hrel.
 have hp:=rrec_compare_pk_canonical pk0 ct0 m0 bs0 hrel.
 have hm:=rrec_compare_message_domain pk0 ct0 m0 bs0 hrel.
 have hr:=pke_domain_cbd(complete_hash_tail hout0).
 have he:=pke_enc_accept pk0 m0 (poly_cbd1_spec(complete_hash_tail hout0)) hp.
 have hc:=rrec_compare_reencrypt pk0 ct0 m0 bs0 hout0 hrel.
 have ht:(bs0=complete_regenerated hout0)=
   (ct0=pke_ciphertext pk0 m0 (poly_cbd1_spec(complete_hash_tail hout0))).
 + by move:hc; rewrite he /=
     (eq_sym (pke_ciphertext pk0 m0 (poly_cbd1_spec(complete_hash_tail hout0))) ct0).
 proc; rcondt{2} 5.
 + move=> &ml; wp; call(pke_enc_functional pk0 m0 (poly_cbd1_spec(complete_hash_tail hout0)) hm hr).
   call(poly_cbd1_functional witness (complete_hash_tail hout0)).
   auto=> />.
   move=> _ ->; by rewrite he.
 call native_finish_test_equiv; wp.
 ecall{1}(poly_tobytes_correct witness (ntt_spec(poly_cbd1_spec(complete_hash_tail hout0)))
   (complete_regeneration_qrange hout0)).
 ecall{1}(ntt_correct witness (poly_cbd1_spec(complete_hash_tail hout0))).
 ecall{1}(poly_cbd1_correct witness (complete_hash_tail hout0)).
 ecall{2}(pke_enc_correct pk0 m0 (poly_cbd1_spec(complete_hash_tail hout0)) hm hr).
 ecall{2}(poly_cbd1_correct witness (complete_hash_tail hout0)).
 auto=> />; rewrite ?he /=; exact ht.
qed.

lemma native_outlined_reencrypt_tail (G<:MessageSHAKE) (H<:CompleteSHAKEH {-G}) pk0 ct0 m0 bs0 :
 rrec_compare_relation pk0 ct0 m0 bs0 =>
 equiv[NativeTailOutlined(H).run ~ ReencryptTail(H).run:
 recovered{1}=bs0 /\ pk{2}=pk0 /\ ct{2}=ct0 /\ m1{2}=m0 /\
 ={msg,decode_fail,suffix,glob G,glob H} ==> ={res,glob G,glob H}].
proof.
 move=>hrel; proc.
 ecall(native_body_reencrypt_equiv pk0 ct0 m0 bs0 hashout{1} decode_fail{1} hrel).
 call(_: ={input,glob G,glob H} ==> ={res,glob G,glob H}); first by sim.
 call(_: ={input,msg,suffix} ==> ={res}); first by sim.
 auto.
qed.

lemma native_reencrypt_tail (G<:MessageSHAKE) (H<:CompleteSHAKEH {-G}) pk0 ct0 m0 bs0 :
 rrec_compare_relation pk0 ct0 m0 bs0 =>
 equiv[CompleteTail(H).run ~ ReencryptTail(H).run:
 recovered{1}=bs0 /\ pk{2}=pk0 /\ ct{2}=ct0 /\ m1{2}=m0 /\
 ={msg,decode_fail,suffix,glob G,glob H} ==> ={res,glob G,glob H}].
proof.
 move=>hrel.
 transitivity NativeTailOutlined(H).run
   (={recovered,msg,decode_fail,suffix,glob G,glob H} ==> ={res,glob G,glob H})
   (recovered{1}=bs0 /\ pk{2}=pk0 /\ ct{2}=ct0 /\ m1{2}=m0 /\
    ={msg,decode_fail,suffix,glob G,glob H} ==> ={res,glob G,glob H})=> //.
 + clear hrel; smt().
 + exact(native_tail_outline G H).
 exact(native_outlined_reencrypt_tail G H pk0 ct0 m0 bs0 hrel).
qed.

lemma native_reencrypt_core (G<:MessageSHAKE) (H<:CompleteSHAKEH {-G}) w ct0 :
 pke_key_relation w =>
 equiv[CompleteCore(G,H).run ~ ReencryptCore(G,H).run:
 ct{1}=ct0 /\ ct{2}=ct0 /\ sk{1}=w.`kg_sk /\ sk{2}=w.`kg_sk /\ pk{2}=w.`kg_pk /\
 ={glob G,glob H} ==> ={res,glob G,glob H}].
proof.
 move=>hk; case(complete_entry_accepts ct0 w.`kg_sk)=>ha.
 + have [hr hm]:=message_caller_input_closure ct0 (complete_sk_poly w.`kg_sk) ha.
   have hrel:=rrec_native_compare_relation_procedure w ct0 hk ha.
   proc; rcondt{1} 2.
   - move=> &ml; conseq (_:ct=ct0 /\ sk=w.`kg_sk ==> status=W32.zero)=> //.
     call(guarded_r2_functional witness witness witness witness witness encap_zero_ss ct0 (complete_sk_poly w.`kg_sk)).
     auto=> />; by rewrite complete_guarded_prefix ha.
   rcondt{2} 2.
   - move=> &ml; conseq (_:ct=ct0 /\ sk=w.`kg_sk ==> status=W32.zero)=> //.
     call(guarded_r2_functional witness witness witness witness witness encap_zero_ss ct0 (complete_sk_poly w.`kg_sk)).
     auto=> />; by rewrite complete_guarded_prefix ha.
   call(native_reencrypt_tail G H w.`kg_pk ct0 (message_candidate ct0 (complete_sk_poly w.`kg_sk))
     (NTRUPlus768PolyToBytesProof.poly_tobytes_spec(message_r2 ct0 (complete_sk_poly w.`kg_sk))) hrel).
   call(native_message_equiv G H (message_r2 ct0 (complete_sk_poly w.`kg_sk))
     (message_candidate ct0 (complete_sk_poly w.`kg_sk)) hr).
   ecall{1}(native_guarded_correct ct0 w.`kg_sk).
   ecall{2}(native_guarded_correct ct0 w.`kg_sk).
   auto=> />; rewrite complete_guarded_prefix ha /=; smt().
 proc; rcondf{1} 2.
 + move=> &ml; conseq (_:ct=ct0 /\ sk=w.`kg_sk ==> status<>W32.zero)=> //.
   call(guarded_r2_functional witness witness witness witness witness encap_zero_ss ct0 (complete_sk_poly w.`kg_sk)).
   auto=> />; rewrite complete_guarded_prefix ha; smt(W32.to_uint0 W32.to_uint1).
 rcondf{2} 2.
 + move=> &ml; conseq (_:ct=ct0 /\ sk=w.`kg_sk ==> status<>W32.zero)=> //.
   call(guarded_r2_functional witness witness witness witness witness encap_zero_ss ct0 (complete_sk_poly w.`kg_sk)).
   auto=> />; rewrite complete_guarded_prefix ha; smt(W32.to_uint0 W32.to_uint1).
 ecall{1}(native_guarded_correct ct0 w.`kg_sk).
 ecall{2}(native_guarded_correct ct0 w.`kg_sk).
 auto=> />; by rewrite complete_guarded_prefix ha.
qed.

(* Stateful G and H calls are coupled in their original order. Their
   abstract state must be separated; neither a functional hash law nor a
   hash-call losslessness premise is needed for this partial equivalence. *)
lemma native_reencrypt_decaps (G<:MessageSHAKE) (H<:CompleteSHAKEH {-G}) w ct0 :
 pke_key_relation w =>
 equiv[CompleteDecaps(G,H).run ~ ReencryptDecaps(G,H).run:
 ct{1}=ct0 /\ ct{2}=ct0 /\ sk{1}=w.`kg_sk /\ sk{2}=w.`kg_sk /\ pk{2}=w.`kg_pk /\
 ={workspace,glob G,glob H} ==>
 ={res,glob G,glob H} /\ res.`3{1}=clear_zero_spec].
proof.
 move=>hk; proc.
 ecall{1}(decap_clear_correct workspace{1}).
 ecall{2}(decap_clear_correct workspace{2}).
 call(native_reencrypt_core G H w ct0 hk); auto=> />; smt().
qed.

require import NTRUPlus768ROMOracles.
(* The concrete ROM ports use the separate ROG and ROH tables. This does
   not assert an equivalence for an arbitrary shared raw-oracle backend. *)
lemma native_reencrypt_rom_decaps w ct0 : pke_key_relation w =>
 equiv[CompleteDecaps(SHAKEGROM,SHAKEHROM).run ~ ReencryptDecaps(SHAKEGROM,SHAKEHROM).run:
 ct{1}=ct0 /\ ct{2}=ct0 /\ sk{1}=w.`kg_sk /\ sk{2}=w.`kg_sk /\ pk{2}=w.`kg_pk /\
 ={workspace,ROG.m,ROH.m} ==>
 ={res,ROG.m,ROH.m} /\ res.`3{1}=clear_zero_spec].
proof.
 move=>hk; conseq(native_reencrypt_decaps SHAKEGROM SHAKEHROM w ct0 hk)=> //.
qed.
