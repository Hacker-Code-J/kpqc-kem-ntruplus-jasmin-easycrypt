require import AllCore Distr FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array768 Array1152.
require import NTRUPlus768FOModel NTRUPlus768ACWC2Model NTRUPlus768ACWC2BaseModel NTRUPlus768ACWC2Oracle.
require import NTRUPlus768PKEModel NTRUPlus768PKEAlgebra NTRUPlus768RRecModel NTRUPlus768RRecAlgebra.
require import NTRUPlus768RRecCodec NTRUPlus768RRecLinearAlgebra NTRUPlus768RRecNativeComparison.
require import NTRUPlus768RRecPublicInverse NTRUPlus768SOTPContracts.
require import NTRUPlus768DecapCompleteSpec NTRUPlus768DecapMessageAlgebra NTRUPlus768DecapGuardSpec.
require import NTRUPlus768PolySOTPDecodeAlgebra NTRUPlus768PolySOTPEncodeAlgebra.
require import NTRUPlus768PolyToBytesAlgebra NTRUPlus768PolyToBytesProof.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768EncapGuardSpec.
require import NTRUPlus768DecapFinishCorrectness.

(* Compatibility of the realized first G reply with the prepared table.
   It constrains the reply only when its byte input encodes a valid trit
   randomness. The actual ROM lookup proves this relation below. *)
op [opaque] fo_pad_consistent (g:acwc2_g_function) (bs:W8.t Array1152.t) (pad:W8.t Array192.t) =
 forall r,pke_domain r=>bs=rr_G_input r=>pad=g r.
op [opaque] fo_candidate_message (w:keygen_witness) (ct:W8.t Array1152.t) (pad:W8.t Array192.t) =
 poly_sotp_decode_msg_spec (rrec_native_message w ct) pad.
op [opaque] fo_candidate_failed (w:keygen_witness) (ct:W8.t Array1152.t) (pad:W8.t Array192.t) =
 poly_sotp_decode_fail_spec (rrec_native_message w ct) pad.
op [opaque] fo_reencryption (w:keygen_witness) (g:acwc2_g_function)
 (msg:W8.t Array96.t) (hout:W8.t Array224.t) =
 pke_enc_spec w.`kg_pk (acwc2_code g msg (fo_randomness hout)) (fo_randomness hout).
op [opaque] fo_native_accept (w:keygen_witness) (ct:W8.t Array1152.t)
 (pad:W8.t Array192.t) (hout:W8.t Array224.t) =
 complete_entry_accepts ct w.`kg_sk /\ !fo_candidate_failed w ct pad /\
 rrec_native_bytes w ct=complete_regenerated hout.
op [opaque] fo_full_accept (w:keygen_witness) (g:acwc2_g_function) (ct:W8.t Array1152.t)
 (pad:W8.t Array192.t) (hout:W8.t Array224.t) =
 complete_entry_accepts ct w.`kg_sk /\ !fo_candidate_failed w ct pad /\
 rrec_spec w.`kg_pk (rrec_native_message w ct) ct<>None /\
 fo_reencryption w g (fo_candidate_message w ct pad) hout=Some ct.
op [opaque] fo_result (hout:W8.t Array224.t) (accept:bool) =
 (if accept then finish_key_prefix hout else encap_zero_ss,
  if accept then W32.zero else W32.one).

lemma fo_some_injective ['a] (x y:'a) : Some x=Some y=>x=y.
proof. smt(). qed.

lemma fo_base_bad_reencryption w g msg hout :
 fo_base_bad w g msg hout =
 (fo_reencryption w g msg hout=None \/
  pke_dec_spec(oget(fo_reencryption w g msg hout))(pke_secret_bytes w)<>
   Some(acwc2_code g msg (fo_randomness hout))).
proof.
 by rewrite /fo_base_bad acwc2_pad_badE acwc2_base_failureE /fo_reencryption /acwc2_code.
qed.

lemma fo_randomness_domain hout : pke_domain(fo_randomness hout).
proof. rewrite /fo_randomness; exact(pke_domain_cbd _). qed.
lemma fo_regenerated_input hout : complete_regenerated hout=rr_G_input(fo_randomness hout).
proof.
 rewrite /complete_regenerated /fo_randomness poly_tobytes_procedure_specE pke_rhatE -rr_G_inputE.
 done.
qed.
lemma fo_candidate_decode w ct pad : complete_entry_accepts ct w.`kg_sk =>
 !fo_candidate_failed w ct pad =>
 sotp_decode_option (rrec_native_message w ct) pad=Some(fo_candidate_message w ct pad).
proof.
 move=>he hf; have hm:=rrec_native_message_domain w ct he.
 by rewrite /sotp_decode_option hm -/(fo_candidate_failed w ct pad) hf /= /fo_candidate_message.
qed.

lemma fo_native_reencrypt_same w ct pad hout :
 pke_key_relation w =>fo_native_accept w ct pad hout =>
 pke_enc_spec w.`kg_pk (rrec_native_message w ct) (fo_randomness hout)=Some ct.
proof.
 move=>hk; rewrite /fo_native_accept.
 move=>[he [hd hc]].
 have h:=rrec_compare_reencrypt _ _ _ _ hout (rrec_native_compare_relation w ct hk he).
 rewrite -/(fo_randomness hout) in h.
 by rewrite -h.
qed.

lemma fo_same_cipher_recovery w ct m r :
 pke_key_relation w=>pke_domain m=>pke_domain r=>
 pke_enc_spec w.`kg_pk m r=Some ct=>rrec_spec w.`kg_pk m ct=Some r.
proof.
 move=>hk hm hr he.
 have hp:=pke_enc_accept w.`kg_pk m r (pke_key_canonical w hk).
 have hs:Some ct=Some(pke_ciphertext w.`kg_pk m r) by rewrite -he hp.
 have hc:ct=pke_ciphertext w.`kg_pk m r by exact(fo_some_injective _ _ hs).
 rewrite hc; exact(rrec_keyed_forward w m r hk hm hr).
qed.

lemma fo_native_implies_full w g ct pad hout :
 pke_key_relation w =>fo_pad_consistent g (rrec_native_bytes w ct) pad =>
 fo_native_accept w ct pad hout =>fo_full_accept w g ct pad hout.
proof.
 move=>hk hp hn.
 have henc:=fo_native_reencrypt_same w ct pad hout hk hn.
 rewrite /fo_native_accept in hn; move:hn=>[he [hd hbytes]].
 have hb:rrec_native_bytes w ct=rr_G_input(fo_randomness hout)
   by rewrite -fo_regenerated_input.
 have hr:=fo_randomness_domain hout.
 have hpad:pad=g(fo_randomness hout).
 + move:hp; rewrite /fo_pad_consistent=>hp; exact(hp _ hr hb).
 have hm:=rrec_native_message_domain w ct he.
 have hdec:=fo_candidate_decode w ct pad he hd.
 have hcode:=sotp_decode_option_rigidity _ _ _ hdec.
 have hcode':acwc2_code g (fo_candidate_message w ct pad) (fo_randomness hout)=rrec_native_message w ct.
 + by rewrite /acwc2_code -hpad.
 have hrr:=fo_same_cipher_recovery w ct _ _ hk hm hr henc.
 rewrite /fo_full_accept he hd hrr /= /fo_reencryption hcode'.
 exact henc.
qed.

lemma fo_full_ciphertext w g ct pad hout :fo_full_accept w g ct pad hout =>
 pke_enc_spec w.`kg_pk
  (poly_sotp_encode_spec (fo_candidate_message w ct pad) (g(fo_randomness hout)))
  (fo_randomness hout)=Some ct.
proof. rewrite /fo_full_accept /fo_reencryption /acwc2_code; smt(). qed.

lemma fo_native_candidate_pke w ct :pke_key_relation w=>complete_entry_accepts ct w.`kg_sk=>
 pke_dec_spec ct (pke_secret_bytes w)=Some(rrec_native_message w ct).
proof.
 move=>hk he.
 have hc:encap_key_canonical ct by move:he; rewrite(rrec_native_entry w ct hk).
 rewrite(pke_dec_accept ct (pke_secret_bytes w) hc (pke_secret_canonical w hk)).
 by rewrite /rrec_native_message /message_candidate /pke_secret_bytes.
qed.

lemma fo_full_good_candidate w g ct pad hout :pke_key_relation w=>
 fo_full_accept w g ct pad hout=>!fo_base_bad w g (fo_candidate_message w ct pad) hout=>
 rrec_native_message w ct=acwc2_code g (fo_candidate_message w ct pad) (fo_randomness hout).
proof.
 move=>hk ha hb.
 rewrite /fo_full_accept in ha; move:ha=>[he [_ [_ hc]]].
 have hm:=fo_native_candidate_pke w ct hk he.
 move:hb; rewrite fo_base_bad_reencryption hc /= hm /=.
 trivial.
qed.

lemma fo_full_implies_native w g ct pad hout :pke_key_relation w=>
 fo_full_accept w g ct pad hout=>!fo_base_bad w g (fo_candidate_message w ct pad) hout=>
 fo_native_accept w ct pad hout.
proof.
 move=>hk ha hb.
 have hm:=fo_full_good_candidate w g ct pad hout hk ha hb.
 have hfull:=ha; rewrite /fo_full_accept in hfull.
 have [he [hd [_ hc]]]:=hfull.
 have hn:pke_enc_spec w.`kg_pk (rrec_native_message w ct) (fo_randomness hout)=Some ct.
 + by rewrite hm -/(fo_reencryption w g (fo_candidate_message w ct pad) hout).
 have hr:=rrec_compare_reencrypt _ _ _ _ hout (rrec_native_compare_relation w ct hk he).
 rewrite -/(fo_randomness hout) in hr.
 rewrite /fo_native_accept he hd /= hr; exact hn.
qed.

lemma fo_acceptance_good_or_reject w g ct pad hout :pke_key_relation w=>
 fo_pad_consistent g (rrec_native_bytes w ct) pad=>
 (!fo_base_bad w g (fo_candidate_message w ct pad) hout \/
  fo_reencryption w g (fo_candidate_message w ct pad) hout<>Some ct)=>
 fo_native_accept w ct pad hout=fo_full_accept w g ct pad hout.
proof.
 move=>hk hp hcase; apply eq_iff; split.
 + exact(fo_native_implies_full w g ct pad hout hk hp).
 move=>ha; apply(fo_full_implies_native w g ct pad hout hk ha).
 rewrite /fo_full_accept in ha; move:ha=>[_ [_ [_ hc]]].
 case:hcase=>hgood; first exact hgood.
 by move:hgood; rewrite hc.
qed.
