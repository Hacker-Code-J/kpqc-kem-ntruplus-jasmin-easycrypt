require import AllCore Distr FMap.
from Jasmin require import JWord JModel_x86.
require import Array32 Array96 Array129 Array192 Array224 Array768 Array1152 Array1153 Array2336 Array13506.
require import NTRUPlus768FOModel NTRUPlus768FOAlgebra NTRUPlus768FOProcedures.
require import NTRUPlus768PKEModel NTRUPlus768PKEAlgebra NTRUPlus768PKECallProof.
require import NTRUPlus768RRecModel NTRUPlus768RRecLinearProcedures NTRUPlus768RRecLinearProof NTRUPlus768RRecNativeProcedures NTRUPlus768RRecNativeProof.
require import NTRUPlus768RRecNativeComparison NTRUPlus768RRecCodec NTRUPlus768ACWC2HashG NTRUPlus768ACWC2Oracle NTRUPlus768ACWC2Model.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDomains NTRUPlus768ROMPayloadHash.
require import NTRUPlus768DecapCompleteSpec NTRUPlus768DecapCompleteProof NTRUPlus768DecapCompleteTailProof NTRUPlus768DecapCompleteHash.
require import NTRUPlus768DecapMessageSpec NTRUPlus768DecapMessageProof NTRUPlus768DecapMessagePrepareProof NTRUPlus768DecapMessageAlgebra.
require import NTRUPlus768DecapGuardSpec NTRUPlus768DecapR2CompCaller NTRUPlus768EncapGuardSpec.
require import NTRUPlus768DecapFinishCorrectness NTRUPlus768DecapClearProof.
require import NTRUPlus768PolyCBD1CheckedProof NTRUPlus768PolyCBD1Algebra NTRUPlus768NTTProof NTRUPlus768NTTAlgebra NTRUPlus768PolyToBytesProof.
require import NTRUPlus768PolySOTPDecodeCheckedProof NTRUPlus768PolySOTPDecodeAlgebra NTRUPlus768SOTPContracts.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768DecapMaskProof.

lemma fo_cache_extension g gm0 gm1 :
 acwc2_cache_matches g gm0 =>cache_extends gm0 gm1=>acwc2_cache_matches g gm1.
proof. move=>hg he r hr; exact(he _ _ (hg r hr)). qed.
lemma fo_cache_pad_consistent g gm bs : acwc2_cache_matches g gm =>
 fo_pad_consistent g bs (oget gm.[bs]).
proof.
 move=>hg; rewrite /fo_pad_consistent=>r hr ->.
 by rewrite(hg r hr).
qed.
lemma fo_g_prepared_value g bs0 :
 hoare[SHAKEGROM.shake:
 peel1153 input=bs0 /\ acwc2_cache_matches g ROG.m ==>
 ROG.m.[bs0]=Some res /\ acwc2_cache_matches g ROG.m].
proof.
 proc; ecall(rog_get_value ROG.m bs0); auto=> />.
 smt(fo_cache_extension).
qed.

lemma fo_hash_g_actual :
 equiv[FOHashG(SHAKEGROM).run ~ ACWC2HashG.run:
 ={r,glob ROG} ==> ={res,glob ROG}].
proof. by sim. qed.
lemma fo_hash_g_prepared r0 g gm0 : pke_domain r0=>acwc2_cache_matches g gm0=>
 hoare[FOHashG(SHAKEGROM).run:r=r0 /\ ROG.m=gm0 ==>res=g r0 /\ ROG.m=gm0].
proof.
 move=>hr hg; conseq fo_hash_g_actual (acwc2_prepared_hash_g r0 g gm0 hr hg); smt().
qed.
lemma fo_hash_g_prepared_correct r0 g gm0 : pke_domain r0=>acwc2_cache_matches g gm0=>
 phoare[FOHashG(SHAKEGROM).run:r=r0 /\ ROG.m=gm0 ==>res=g r0 /\ ROG.m=gm0]=1%r.
proof.
 move=>hr hg; by conseq(fo_hash_g_lossless SHAKEGROM ro_g_shake_ll)
   (fo_hash_g_prepared r0 g gm0 hr hg).
qed.
lemma fo_message_input_payload bs : peel1153(message_hash_input bs)=bs.
proof. by rewrite payload_g_preparation peel_encode_g. qed.
lemma fo_lookup_value ['a 'b] (m:('a,'b)fmap) x y : m.[x]=Some y=>oget m.[x]=y.
proof. by move=>->. qed.

(* This observes the actual first G answer; it makes no functional SHAKE
   substitution, even when the serialized r2 is outside the trit image. *)
lemma fo_message_prepared g r20 m10 :
 NTRUPlus768PolyToBytesProof.poly_tobytes_input_qrange r20=>poly_sotp_trit_input m10=>
 hoare[DecapMessage(SHAKEGROM).run:
 serialized=witness /\ input=witness /\ msg=witness /\ r2=r20 /\ m1=m10 /\
 acwc2_cache_matches g ROG.m ==>
 res.`1=NTRUPlus768PolyToBytesProof.poly_tobytes_spec r20 /\
 res.`2=poly_sotp_decode_msg_spec m10 (oget ROG.m.[res.`1]) /\
 res.`3=W32.of_int(b2i(poly_sotp_decode_fail_spec m10 (oget ROG.m.[res.`1]))) /\
 acwc2_cache_matches g ROG.m].
proof.
 move=>hr hm; proc.
 ecall(poly_sotp_decode_functional witness m10 pad).
 call(fo_g_prepared_value g (NTRUPlus768PolyToBytesProof.poly_tobytes_spec r20)).
 call(message_prepare_functional witness witness r20 hr).
 auto=> />; smt(fo_lookup_value fo_message_input_payload).
qed.

lemma fo_finish_resultE hout df test :
 (finish_ss_spec hout (df \/ !test),W32.of_int(b2i(df \/ !test)))=
 fo_result hout (!df /\ test).
proof.
 case df; case test; rewrite /fo_result /finish_ss_spec /encap_zero_ss /decap_mask_zero_ss /b2i /=;
 done.
qed.

lemma fo_native_finish_functional bs0 hout0 df0 :
 hoare[NativeRegenerateFinish.run:
 recovered=bs0 /\ hashout=hout0 /\ decode_fail=W32.of_int(b2i df0) ==>
 res=fo_result hout0 (!df0 /\ bs0=complete_regenerated hout0)].
proof.
 proc; call(finish_functional witness hout0 bs0 (complete_regenerated hout0) df0).
 ecall(poly_tobytes_functional witness (ntt_spec(poly_cbd1_spec(complete_hash_tail hout0)))
   (complete_regeneration_qrange hout0)).
 ecall(ntt_functional witness (poly_cbd1_spec(complete_hash_tail hout0))).
 ecall(poly_cbd1_functional witness (complete_hash_tail hout0)).
 skip; rewrite /complete_regenerated; auto=> />.
 exact(fo_finish_resultE hout0 df0 (bs0=complete_regenerated hout0)).
qed.

lemma fo_native_finish_value bs0 hout0 df0 :
 phoare[NativeRegenerateFinish.run:
 recovered=bs0 /\ hashout=hout0 /\ decode_fail=W32.of_int(b2i df0) ==>
 res=fo_result hout0 (!df0 /\ bs0=complete_regenerated hout0)]=1%r.
proof. by conseq native_regenerate_finish_lossless (fo_native_finish_functional bs0 hout0 df0). qed.

lemma fo_linear_checked_functional pk0 m0 ct0 :
 hoare[LinearRRec.run:pk=pk0 /\ m=m0 /\ ct=ct0 ==>res=rrec_spec pk0 m0 ct0].
proof. by conseq(linear_rrec_checked_correct pk0 m0 ct0). qed.

lemma fo_randomnessE hout : poly_cbd1_spec(complete_hash_tail hout)=fo_randomness hout.
proof. by rewrite /fo_randomness. qed.
lemma fo_codeE g msg r : NTRUPlus768PolySOTPEncodeAlgebra.poly_sotp_encode_spec msg (g r)=acwc2_code g msg r.
proof. by rewrite /acwc2_code. qed.

lemma fo_word_flag df : (W32.of_int(b2i df)=W32.zero)=!df.
proof. case df; rewrite /b2i /=; smt(W32.to_uint0 W32.to_uint1). qed.
lemma fo_finish_option_result hout df (rr:pke_poly option) (ct ct2:W8.t Array1152.t) :
 (finish_ss_spec hout ((df \/ rr=None) \/ ct<>ct2),
  W32.of_int(b2i((df \/ rr=None) \/ ct<>ct2)))=
 fo_result hout (!df /\ rr<>None /\ ct2=ct).
proof. rewrite fo_finish_resultE; congr; smt(). qed.

lemma fo_regenerate_functional pk0 ct0 m0 msg0 hout0 df0 g gm0 :
 encap_key_canonical pk0=>acwc2_cache_matches g gm0=>
 hoare[FORegenerateFinish(SHAKEGROM).run:
 pk=pk0 /\ ct=ct0 /\ m1=m0 /\ msg=msg0 /\ hashout=hout0 /\
 decode_fail=W32.of_int(b2i df0) /\ ROG.m=gm0 ==>
 res=fo_result hout0 (!df0 /\ rrec_spec pk0 m0 ct0<>None /\
   pke_enc_spec pk0 (acwc2_code g msg0 (fo_randomness hout0)) (fo_randomness hout0)=Some ct0) /\ ROG.m=gm0].
proof.
 move=>hp hg.
 have hr:=fo_randomness_domain hout0.
 have hm:=acwc2_code_domain g msg0 (fo_randomness hout0).
 have he:=pke_enc_accept pk0 (acwc2_code g msg0 (fo_randomness hout0)) (fo_randomness hout0) hp.
 proc; seq 6:(pk=pk0 /\ ct=ct0 /\ msg=msg0 /\ hashout=hout0 /\
  decoded=(if df0 then None else Some msg0) /\ recovered=rrec_spec pk0 m0 ct0 /\
  ct2=Some(pke_ciphertext pk0 (acwc2_code g msg0 (fo_randomness hout0)) (fo_randomness hout0)) /\ ROG.m=gm0).
 + call(pke_enc_functional pk0 (acwc2_code g msg0 (fo_randomness hout0)) (fo_randomness hout0) hm hr).
   call(sotp_encode_functional msg0 (g(fo_randomness hout0))).
   call(fo_hash_g_prepared (fo_randomness hout0) g gm0 hr hg).
   call(poly_cbd1_functional witness (complete_hash_tail hout0)).
   wp; call(fo_linear_checked_functional pk0 m0 ct0).
   skip; rewrite fo_randomnessE fo_codeE he; auto=> />.
   by rewrite fo_word_flag; case df0.
 rcondt 4; first by auto.
 call(finish_functional witness hout0 ct0
   (pke_ciphertext pk0 (acwc2_code g msg0 (fo_randomness hout0)) (fo_randomness hout0))
   (df0 \/ rrec_spec pk0 m0 ct0=None)).
 auto=> />; rewrite he /=.
 rewrite fo_finish_option_result.
 case df0; auto.
qed.

lemma fo_regenerate_correct pk0 ct0 m0 msg0 hout0 df0 g gm0 :
 encap_key_canonical pk0=>acwc2_cache_matches g gm0=>
 phoare[FORegenerateFinish(SHAKEGROM).run:
 pk=pk0 /\ ct=ct0 /\ m1=m0 /\ msg=msg0 /\ hashout=hout0 /\
 decode_fail=W32.of_int(b2i df0) /\ ROG.m=gm0 ==>
 res=fo_result hout0 (!df0 /\ rrec_spec pk0 m0 ct0<>None /\
   pke_enc_spec pk0 (acwc2_code g msg0 (fo_randomness hout0)) (fo_randomness hout0)=Some ct0) /\ ROG.m=gm0]=1%r.
proof.
 move=>hp hg; by conseq(fo_regenerate_finish_lossless SHAKEGROM ro_g_shake_ll)
   (fo_regenerate_functional pk0 ct0 m0 msg0 hout0 df0 g gm0 hp hg).
qed.

lemma fo_body_equiv (H<:CompleteSHAKEH {-ROG}) (Q:(glob H)->bool) w g ct0 pad hout0 gm0 :
 pke_key_relation w=>complete_entry_accepts ct0 w.`kg_sk=>
 acwc2_cache_matches g gm0=>fo_pad_consistent g (rrec_native_bytes w ct0) pad=>
 equiv[NativeRegenerateFinish.run ~ FORegenerateFinish(SHAKEGROM).run:
 recovered{1}=rrec_native_bytes w ct0 /\
 hashout{1}=hout0 /\ hashout{2}=hout0 /\
 decode_fail{1}=W32.of_int(b2i(fo_candidate_failed w ct0 pad)) /\
 decode_fail{2}=W32.of_int(b2i(fo_candidate_failed w ct0 pad)) /\
 pk{2}=w.`kg_pk /\ ct{2}=ct0 /\ m1{2}=rrec_native_message w ct0 /\
 msg{2}=fo_candidate_message w ct0 pad /\ ROG.m{1}=gm0 /\ ROG.m{2}=gm0 /\ ={glob H} /\
 (Q(glob H){1}=>(!fo_base_bad w g (fo_candidate_message w ct0 pad) hout0 \/
   fo_reencryption w g (fo_candidate_message w ct0 pad) hout0<>Some ct0)) ==>
 ={glob H,ROG.m} /\ ROG.m{1}=gm0 /\ (Q(glob H){1}=>res{1}=res{2})].
proof.
 move=>hk ha hg hp.
 have hpk:=pke_key_canonical w hk.
 have he:=fo_acceptance_good_or_reject w g ct0 pad hout0 hk hp.
 clear hk hp.
 rewrite /fo_native_accept /fo_full_accept /fo_reencryption ha /= in he.
 proc*; ecall{1}(fo_native_finish_value (rrec_native_bytes w ct0) hout0 (fo_candidate_failed w ct0 pad)).
 ecall{2}(fo_regenerate_correct w.`kg_pk ct0 (rrec_native_message w ct0)
   (fo_candidate_message w ct0 pad) hout0 (fo_candidate_failed w ct0 pad) g gm0 hpk hg).
 skip; rewrite /fo_reencryption.
 auto=> />.
 clear ha hg hpk.
 move=> &m hb hq; by rewrite (he (hb hq)).
qed.

require import NTRUPlus768DecapHashHPrepareProof.
lemma fo_h_input_payload msg suffix : peel_h(hash_h_prepare_spec msg suffix)=(msg,suffix).
proof. by rewrite payload_h_preparation peel_encode_h. qed.

lemma fo_outlined_tail_equiv (H<:CompleteSHAKEH {-ROG})
 (I Q:(glob H)->bool) w g ct0 pad gm0 :
 pke_key_relation w=>complete_entry_accepts ct0 w.`kg_sk=>
 acwc2_cache_matches g gm0=>fo_pad_consistent g (rrec_native_bytes w ct0) pad=>
 hoare[H.shake:
 input=hash_h_prepare_spec (fo_candidate_message w ct0 pad) (complete_sk_suffix w.`kg_sk) /\ I(glob H) ==>
 I(glob H) /\ (Q(glob H)=>(!fo_base_bad w g (fo_candidate_message w ct0 pad) res \/
   fo_reencryption w g (fo_candidate_message w ct0 pad) res<>Some ct0))]=>
 equiv[NativeTailOutlined(H).run ~ FOTail(SHAKEGROM,H).run:
 recovered{1}=rrec_native_bytes w ct0 /\ pk{2}=w.`kg_pk /\ ct{2}=ct0 /\ m1{2}=rrec_native_message w ct0 /\
 msg{1}=fo_candidate_message w ct0 pad /\ msg{2}=fo_candidate_message w ct0 pad /\
 decode_fail{1}=W32.of_int(b2i(fo_candidate_failed w ct0 pad)) /\
 decode_fail{2}=W32.of_int(b2i(fo_candidate_failed w ct0 pad)) /\
 suffix{1}=complete_sk_suffix w.`kg_sk /\ suffix{2}=complete_sk_suffix w.`kg_sk /\
 ROG.m{1}=gm0 /\ ROG.m{2}=gm0 /\ ={glob H} /\ I(glob H){1} ==>
 ={glob H,ROG.m} /\ ROG.m{1}=gm0 /\ I(glob H){1} /\ (Q(glob H){1}=>res{1}=res{2})].
proof.
 move=>hk ha hg hp hH; proc.
 ecall(fo_body_equiv H Q w g ct0 pad hashout{1} gm0 hk ha hg hp).
 call(_: ={input,glob H} /\
   input{1}=hash_h_prepare_spec (fo_candidate_message w ct0 pad) (complete_sk_suffix w.`kg_sk) /\ I(glob H){1} ==>
   ={res,glob H} /\ I(glob H){1} /\
   (Q(glob H){1}=>(!fo_base_bad w g (fo_candidate_message w ct0 pad) res{1} \/
   fo_reencryption w g (fo_candidate_message w ct0 pad) res{1}<>Some ct0))).
 + conseq(_: ={input,glob H} ==> ={res,glob H}) hH _=> //; by sim.
 ecall{1}(hash_h_prepare_correct witness (fo_candidate_message w ct0 pad) (complete_sk_suffix w.`kg_sk)).
 ecall{2}(hash_h_prepare_correct witness (fo_candidate_message w ct0 pad) (complete_sk_suffix w.`kg_sk)).
 auto.
qed.

lemma fo_tail_equiv (H<:CompleteSHAKEH {-ROG})
 (I Q:(glob H)->bool) w g ct0 pad :
 pke_key_relation w=>complete_entry_accepts ct0 w.`kg_sk=>
 hoare[H.shake:
 input=hash_h_prepare_spec (fo_candidate_message w ct0 pad) (complete_sk_suffix w.`kg_sk) /\ I(glob H) ==>
 I(glob H) /\ (Q(glob H)=>(!fo_base_bad w g (fo_candidate_message w ct0 pad) res \/
   fo_reencryption w g (fo_candidate_message w ct0 pad) res<>Some ct0))]=>
 equiv[CompleteTail(H).run ~ FOTail(SHAKEGROM,H).run:
 recovered{1}=rrec_native_bytes w ct0 /\ pk{2}=w.`kg_pk /\ ct{2}=ct0 /\ m1{2}=rrec_native_message w ct0 /\
 msg{1}=fo_candidate_message w ct0 pad /\ msg{2}=fo_candidate_message w ct0 pad /\
 decode_fail{1}=W32.of_int(b2i(fo_candidate_failed w ct0 pad)) /\
 decode_fail{2}=W32.of_int(b2i(fo_candidate_failed w ct0 pad)) /\
 suffix{1}=complete_sk_suffix w.`kg_sk /\ suffix{2}=complete_sk_suffix w.`kg_sk /\
 ={glob H,ROG.m} /\ I(glob H){1} /\ acwc2_cache_matches g ROG.m{1} /\
 fo_pad_consistent g (rrec_native_bytes w ct0) pad ==>
 ={glob H,ROG.m} /\ I(glob H){1} /\ acwc2_cache_matches g ROG.m{1} /\ (Q(glob H){1}=>res{1}=res{2})].
proof.
 move=>hk ha hH.
 exists* ROG.m{1}; elim*=>gm0.
 case(acwc2_cache_matches g gm0)=>hg; last first.
 + conseq(_:false ==>_)=> //; smt().
 case(fo_pad_consistent g (rrec_native_bytes w ct0) pad)=>hp; last first.
 + conseq(_:false ==>_)=> //; smt().
 transitivity NativeTailOutlined(H).run
   (={recovered,msg,decode_fail,suffix,glob ROG,glob H} ==> ={res,glob ROG,glob H})
   (recovered{1}=rrec_native_bytes w ct0 /\ pk{2}=w.`kg_pk /\ ct{2}=ct0 /\ m1{2}=rrec_native_message w ct0 /\
    msg{1}=fo_candidate_message w ct0 pad /\ msg{2}=fo_candidate_message w ct0 pad /\
    decode_fail{1}=W32.of_int(b2i(fo_candidate_failed w ct0 pad)) /\
    decode_fail{2}=W32.of_int(b2i(fo_candidate_failed w ct0 pad)) /\
    suffix{1}=complete_sk_suffix w.`kg_sk /\ suffix{2}=complete_sk_suffix w.`kg_sk /\
    ROG.m{1}=gm0 /\ ROG.m{2}=gm0 /\ ={glob H} /\ I(glob H){1} ==>
    ={glob H,ROG.m} /\ ROG.m{1}=gm0 /\ I(glob H){1} /\ (Q(glob H){1}=>res{1}=res{2})).
 + clear hk hH; smt().
 + clear hk hH; smt().
 + exact(native_tail_outline SHAKEGROM H).
 exact(fo_outlined_tail_equiv H I Q w g ct0 pad gm0 hk ha hg hp hH).
qed.

lemma fo_message_equiv (H<:CompleteSHAKEH {-ROG}) g r20 m10 :
 NTRUPlus768PolyToBytesProof.poly_tobytes_input_qrange r20=>poly_sotp_trit_input m10=>
 equiv[DecapMessage(SHAKEGROM).run ~ DecapMessage(SHAKEGROM).run:
 serialized{1}=witness /\ serialized{2}=witness /\ input{1}=witness /\ input{2}=witness /\
 msg{1}=witness /\ msg{2}=witness /\ r2{1}=r20 /\ r2{2}=r20 /\ m1{1}=m10 /\ m1{2}=m10 /\
 ={glob H,ROG.m} /\ acwc2_cache_matches g ROG.m{1} ==>
 ={res,glob H,ROG.m} /\ acwc2_cache_matches g ROG.m{1} /\
 res.`1{1}=NTRUPlus768PolyToBytesProof.poly_tobytes_spec r20 /\
 res.`2{1}=poly_sotp_decode_msg_spec m10 (oget ROG.m{1}.[res.`1{1}]) /\
 res.`3{1}=W32.of_int(b2i(poly_sotp_decode_fail_spec m10 (oget ROG.m{1}.[res.`1{1}])))] .
proof.
 move=>hr hm.
 conseq(_: ={serialized,input,msg,r2,m1,ROG.m,glob H} ==> ={res,ROG.m,glob H})
 (fo_message_prepared g r20 m10 hr hm) _.
 + auto=> />.
 + auto=> />; smt().
 + clear hr hm; smt().
 by sim.
qed.

lemma fo_native_bytesE w ct :
 NTRUPlus768PolyToBytesProof.poly_tobytes_spec(message_r2 ct(complete_sk_poly w.`kg_sk))=rrec_native_bytes w ct.
proof. by rewrite NTRUPlus768PolyToBytesAlgebra.poly_tobytes_procedure_specE rrec_native_r2E /rrec_native_bytes. qed.

lemma fo_core_equiv (H<:CompleteSHAKEH {-ROG}) (I Q:(glob H)->bool) w g ct0 :
 pke_key_relation w=>
 (forall msg0,hoare[H.shake:
 input=hash_h_prepare_spec msg0 (complete_sk_suffix w.`kg_sk) /\ I(glob H) ==>
 I(glob H) /\ (Q(glob H)=>(!fo_base_bad w g msg0 res \/ fo_reencryption w g msg0 res<>Some ct0))])=>
 equiv[CompleteCore(SHAKEGROM,H).run ~ FOCore(SHAKEGROM,H).run:
 ct{1}=ct0 /\ ct{2}=ct0 /\ sk{1}=w.`kg_sk /\ sk{2}=w.`kg_sk /\ pk{2}=w.`kg_pk /\
 ={glob H,ROG.m} /\ I(glob H){1} /\ acwc2_cache_matches g ROG.m{1} ==>
 ={glob H,ROG.m} /\ I(glob H){1} /\ acwc2_cache_matches g ROG.m{1} /\ (Q(glob H){1}=>res{1}=res{2})].
proof.
 move=>hk hH; case(complete_entry_accepts ct0 w.`kg_sk)=>ha.
 + have [hr hm]:=message_caller_input_closure ct0 (complete_sk_poly w.`kg_sk) ha.
   proc; rcondt{1} 2.
   - move=> &ml; conseq (_:ct=ct0 /\ sk=w.`kg_sk ==> status=W32.zero)=> //.
     call(guarded_r2_functional witness witness witness witness witness encap_zero_ss ct0 (complete_sk_poly w.`kg_sk)).
     auto=> />; by rewrite complete_guarded_prefix ha.
   rcondt{2} 2.
   - move=> &ml; conseq (_:ct=ct0 /\ sk=w.`kg_sk ==> status=W32.zero)=> //.
     call(guarded_r2_functional witness witness witness witness witness encap_zero_ss ct0 (complete_sk_poly w.`kg_sk)).
     auto=> />; by rewrite complete_guarded_prefix ha.
   ecall(fo_tail_equiv H I Q w g ct0 (oget ROG.m{1}.[rrec_native_bytes w ct0]) hk ha (hH _)).
   call(fo_message_equiv H g (message_r2 ct0 (complete_sk_poly w.`kg_sk))
     (message_candidate ct0 (complete_sk_poly w.`kg_sk)) hr hm).
   ecall{1}(native_guarded_correct ct0 w.`kg_sk).
   ecall{2}(native_guarded_correct ct0 w.`kg_sk).
   skip; rewrite complete_guarded_prefix ha /= fo_native_bytesE rrec_native_messageE
     /fo_candidate_message /fo_candidate_failed.
   clear hk hH hr hm.
   auto=> />; smt(fo_cache_pad_consistent).
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

lemma fo_decaps_equiv (H<:CompleteSHAKEH {-ROG}) (I Q:(glob H)->bool) w g ct0 :
 pke_key_relation w=>
 (forall msg0,hoare[H.shake:
 input=hash_h_prepare_spec msg0 (complete_sk_suffix w.`kg_sk) /\ I(glob H) ==>
 I(glob H) /\ (Q(glob H)=>(!fo_base_bad w g msg0 res \/ fo_reencryption w g msg0 res<>Some ct0))])=>
 equiv[CompleteDecaps(SHAKEGROM,H).run ~ FODecaps(SHAKEGROM,H).run:
 ct{1}=ct0 /\ ct{2}=ct0 /\ sk{1}=w.`kg_sk /\ sk{2}=w.`kg_sk /\ pk{2}=w.`kg_pk /\
 ={workspace,glob H,ROG.m} /\ I(glob H){1} /\ acwc2_cache_matches g ROG.m{1} ==>
 ={glob H,ROG.m} /\ I(glob H){1} /\ acwc2_cache_matches g ROG.m{1} /\
 res.`3{1}=clear_zero_spec /\ res.`3{2}=clear_zero_spec /\ (Q(glob H){1}=>res{1}=res{2})].
proof.
 move=>hk hH; proc.
 ecall{1}(decap_clear_correct workspace{1}); ecall{2}(decap_clear_correct workspace{2}).
 call(fo_core_equiv H I Q w g ct0 hk hH); auto=> />; smt().
qed.

require import NTRUPlus768FOMonitorBridge NTRUPlus768FOHMonitor NTRUPlus768FOChallenge.

(* The hash response excluded from the monitor is the actual challenge
   response. A different ciphertext cannot pass its re-encryption check.
   Both real procedures retain the original H call on SOTP failure. *)
lemma fo_monitored_decaps_equiv w g ex hs cs ct0 :
 pke_key_relation w=>ct0<>cs=>
 equiv[CompleteDecaps(SHAKEGROM,FOSHAKEH).run ~ FODecaps(SHAKEGROM,FOSHAKEH).run:
 ct{1}=ct0 /\ ct{2}=ct0 /\ sk{1}=w.`kg_sk /\ sk{2}=w.`kg_sk /\ pk{2}=w.`kg_pk /\
 ={workspace,ROG.m,ROH.m,glob FOContext,glob FOBadState} /\
 FOContext.w{1}=w /\ FOContext.g{1}=g /\ FOContext.challenge_h{1}=ex /\
 (!FOBadState.bad{1}=>fo_hcache_good w g ex ROH.m{1}) /\
 fo_challenge_invariant w g ex hs cs ROH.m{1} /\ acwc2_cache_matches g ROG.m{1} ==>
 ={ROG.m,ROH.m,glob FOContext,glob FOBadState} /\
 FOContext.w{1}=w /\ FOContext.g{1}=g /\ FOContext.challenge_h{1}=ex /\
 (!FOBadState.bad{1}=>fo_hcache_good w g ex ROH.m{1}) /\
 fo_challenge_invariant w g ex hs cs ROH.m{1} /\ acwc2_cache_matches g ROG.m{1} /\
 res.`3{1}=clear_zero_spec /\ res.`3{2}=clear_zero_spec /\ (!FOBadState.bad{1}=>res{1}=res{2})].
proof.
 move=>hk hn.
 have hh:forall msg,hoare[FOSHAKEH.shake:
   input=hash_h_prepare_spec msg (complete_sk_suffix w.`kg_sk) /\
   fo_monitor_invariant w g ex hs cs (glob FOSHAKEH) ==>
   fo_monitor_invariant w g ex hs cs (glob FOSHAKEH) /\
   (fo_monitor_good(glob FOSHAKEH)=>(!fo_base_bad w g msg res \/ fo_reencryption w g msg res<>Some ct0))].
 + move=>msg; exact(fo_monitored_hash_contract w g ex hs cs ct0 msg hn).
 proc*; call(fo_decaps_equiv FOSHAKEH (fo_monitor_invariant w g ex hs cs) fo_monitor_good w g ct0 hk hh).
 clear hk hh; skip; rewrite /fo_monitor_invariant /fo_monitor_good; auto=> />; smt().
qed.
