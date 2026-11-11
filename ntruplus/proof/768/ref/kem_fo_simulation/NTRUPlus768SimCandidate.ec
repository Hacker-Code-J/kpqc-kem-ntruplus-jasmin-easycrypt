require import AllCore FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array768 Array1152.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768PKEModel NTRUPlus768PKEAlgebra.
require import NTRUPlus768ACWC2Model NTRUPlus768ACWC2Oracle NTRUPlus768FOModel NTRUPlus768FOAlgebra.
require import NTRUPlus768RRecModel NTRUPlus768RRecAlgebra NTRUPlus768RRecCodec NTRUPlus768RRecNativeComparison.
require import NTRUPlus768SOTPContracts NTRUPlus768PolySOTPEncodeAlgebra NTRUPlus768PolySOTPDecodeAlgebra.
require import NTRUPlus768DecapCompleteSpec NTRUPlus768DecapFinishCorrectness NTRUPlus768KEMPayloadSpec.
require import NTRUPlus768FOChallenge.

(* Candidate regeneration uses a fixed G function and one H value. These
   lemmas do not replace actual oracle calls or erase their state effects. *)
lemma sim_reencryption_entry w g msg hout ct :
 pke_key_relation w=>fo_reencryption w g msg hout=Some ct=>
 complete_entry_accepts ct w.`kg_sk.
proof.
 move=>hk he.
 have hp:=pke_key_canonical w hk.
 have hm:=acwc2_code_domain g msg (fo_randomness hout).
 have hr:=fo_randomness_domain hout.
 move:he; rewrite /fo_reencryption (pke_enc_accept _ _ _ hp) /= =>he.
 rewrite(rrec_native_entry w ct hk) -he.
 exact(pke_cipher_canonical _ _ _ hp hm hr).
qed.

lemma sim_good_reencryption_word w g msg hout ct :
 pke_key_relation w=>!fo_base_bad w g msg hout=>fo_reencryption w g msg hout=Some ct=>
 rrec_native_message w ct=acwc2_code g msg (fo_randomness hout).
proof.
 move=>hk hb he.
 have ha:=sim_reencryption_entry w g msg hout ct hk he.
 have hd:=fo_native_candidate_pke w ct hk ha.
 by move:hb; rewrite fo_base_bad_reencryption he /= hd /=.
qed.

lemma sim_good_reencryption_recovers w g msg hout ct :
 pke_key_relation w=>!fo_base_bad w g msg hout=>fo_reencryption w g msg hout=Some ct=>
 complete_entry_accepts ct w.`kg_sk /\
 rrec_native_message w ct=acwc2_code g msg (fo_randomness hout) /\
 rrec_spec w.`kg_pk (rrec_native_message w ct) ct=Some(fo_randomness hout) /\
 rrec_native_bytes w ct=rr_G_input(fo_randomness hout) /\
 fo_candidate_message w ct (g(fo_randomness hout))=msg /\
 !fo_candidate_failed w ct (g(fo_randomness hout)).
proof.
 move=>hk hb he.
 have ha:=sim_reencryption_entry w g msg hout ct hk he.
 have hw:=sim_good_reencryption_word w g msg hout ct hk hb he.
 have hr:=fo_randomness_domain hout.
 have hm:=rrec_native_message_domain w ct ha.
 have henc:pke_enc_spec w.`kg_pk (rrec_native_message w ct) (fo_randomness hout)=Some ct.
 + by rewrite hw -/(fo_reencryption w g msg hout).
 have hrr:=fo_same_cipher_recovery w ct _ _ hk hm hr henc.
 have hc:=rrec_compare_reencrypt _ _ _ _ hout (rrec_native_compare_relation w ct hk ha).
 have hbytes:rrec_native_bytes w ct=rr_G_input(fo_randomness hout).
 + rewrite -fo_regenerated_input hc -/(fo_randomness hout); exact henc.
 have hd:sotp_decode_option (rrec_native_message w ct) (g(fo_randomness hout))=Some msg.
 + rewrite hw /acwc2_code; exact(sotp_encode_decode_option _ _).
 have [_ [hfail hmsg]]:=sotp_decode_option_success _ _ _ hd.
 split; first exact ha.
 split; first exact hw.
 split; first exact hrr.
 split; first exact hbytes.
 rewrite /fo_candidate_message /fo_candidate_failed; split; last exact hfail.
 by rewrite -hmsg.
qed.

lemma sim_good_reencryption_accepts w g msg hout ct :
 pke_key_relation w=>!fo_base_bad w g msg hout=>fo_reencryption w g msg hout=Some ct=>
 fo_native_accept w ct (g(fo_randomness hout)) hout /\
 fo_full_accept w g ct (g(fo_randomness hout)) hout.
proof.
 move=>hk hb he.
 have [ha [hw [hr [hbytes [hmsg hf]]]]]:=sim_good_reencryption_recovers w g msg hout ct hk hb he.
 split.
 + by rewrite /fo_native_accept ha hf /= fo_regenerated_input hbytes.
 rewrite /fo_full_accept ha hf hr /= hmsg; exact he.
qed.

lemma sim_result_key hout : fo_result hout true=(payload_shared_key hout,W32.zero).
proof. by rewrite /fo_result /finish_key_prefix /payload_shared_key. qed.

lemma sim_good_reencryption_result w g msg hout ct :
 pke_key_relation w=>!fo_base_bad w g msg hout=>fo_reencryption w g msg hout=Some ct=>
 fo_result hout (fo_native_accept w ct (g(fo_randomness hout)) hout)=(payload_shared_key hout,W32.zero) /\
 fo_result hout (fo_full_accept w g ct (g(fo_randomness hout)) hout)=(payload_shared_key hout,W32.zero).
proof.
 move=>hk hb he; have [hn hf]:=sim_good_reencryption_accepts w g msg hout ct hk hb he.
 by rewrite hn hf sim_result_key.
qed.

(* Both good candidates decode to the same fixed polynomial. RRec then
   fixes their randomness, and SOTP decoding fixes the original message. *)
lemma sim_good_messages_unique w g msg1 msg2 hout1 hout2 ct :
 pke_key_relation w=>!fo_base_bad w g msg1 hout1=>!fo_base_bad w g msg2 hout2=>
 fo_reencryption w g msg1 hout1=Some ct=>fo_reencryption w g msg2 hout2=Some ct=>msg1=msg2.
proof.
 move=>hk hb1 hb2 he1 he2.
 have [_ [_ [hr1 [_ [hm1 _]]]]]:=sim_good_reencryption_recovers w g msg1 hout1 ct hk hb1 he1.
 have [_ [_ [hr2 [_ [hm2 _]]]]]:=sim_good_reencryption_recovers w g msg2 hout2 ct hk hb2 he2.
 have hr:fo_randomness hout1=fo_randomness hout2.
 + apply fo_some_injective; by rewrite -hr1 -hr2.
 by rewrite -hm1 -hm2 hr.
qed.

lemma sim_good_prepared_lookup w g gm msg hout ct :
 pke_key_relation w=>acwc2_cache_matches g gm=>
 !fo_base_bad w g msg hout=>fo_reencryption w g msg hout=Some ct=>
 gm.[rrec_native_bytes w ct]=Some(g(fo_randomness hout)).
proof.
 move=>hk hg hb he.
 have [_ [_ [_ [hbytes _]]]]:=sim_good_reencryption_recovers w g msg hout ct hk hb he.
 rewrite hbytes; exact(hg _ (fo_randomness_domain hout)).
qed.

lemma sim_good_consistent_pad w g msg hout ct pad :
 pke_key_relation w=>!fo_base_bad w g msg hout=>fo_reencryption w g msg hout=Some ct=>
 fo_pad_consistent g (rrec_native_bytes w ct) pad=>pad=g(fo_randomness hout).
proof.
 move=>hk hb he hp.
 have [_ [_ [_ [hbytes _]]]]:=sim_good_reencryption_recovers w g msg hout ct hk hb he.
 move:hp; rewrite /fo_pad_consistent=>hp.
 exact(hp _ (fo_randomness_domain hout) hbytes).
qed.

lemma sim_good_entry_accepts w g (input:fo_h_input) hout ct pad :
 pke_key_relation w=>input.`2=complete_sk_suffix w.`kg_sk=>
 !fo_base_bad w g input.`1 hout=>fo_reencryption w g input.`1 hout=Some ct=>
 fo_pad_consistent g (rrec_native_bytes w ct) pad=>
 (fo_candidate_message w ct pad,complete_sk_suffix w.`kg_sk)=input /\
 fo_native_accept w ct pad hout /\ fo_full_accept w g ct pad hout /\
 fo_result hout (fo_native_accept w ct pad hout)=(payload_shared_key hout,W32.zero) /\
 fo_result hout (fo_full_accept w g ct pad hout)=(payload_shared_key hout,W32.zero).
proof.
 case input=>msg suffix /=; move=>hk hs hb he hp.
 have hpad:=sim_good_consistent_pad w g msg hout ct pad hk hb he hp.
 rewrite hpad.
 have [_ [_ [_ [_ [hm _]]]]]:=sim_good_reencryption_recovers w g msg hout ct hk hb he.
 have [hn hf]:=sim_good_reencryption_accepts w g msg hout ct hk hb he.
 have [hkn hkf]:=sim_good_reencryption_result w g msg hout ct hk hb he.
 split; first by rewrite hm hs.
 split; first exact hn.
 split; first exact hf.
 by split.
qed.

require import NTRUPlus768FONativeBridge.

lemma sim_good_prepared_entry w g gm (input:fo_h_input) hout ct :
 pke_key_relation w=>acwc2_cache_matches g gm=>input.`2=complete_sk_suffix w.`kg_sk=>
 !fo_base_bad w g input.`1 hout=>fo_reencryption w g input.`1 hout=Some ct=>
 let pad=oget gm.[rrec_native_bytes w ct] in
 (fo_candidate_message w ct pad,complete_sk_suffix w.`kg_sk)=input /\
 fo_native_accept w ct pad hout /\ fo_full_accept w g ct pad hout /\
 fo_result hout (fo_native_accept w ct pad hout)=(payload_shared_key hout,W32.zero) /\
 fo_result hout (fo_full_accept w g ct pad hout)=(payload_shared_key hout,W32.zero).
proof.
 move=>hk hg hs hb he.
 exact(sim_good_entry_accepts w g input hout ct (oget gm.[rrec_native_bytes w ct])
   hk hs hb he (fo_cache_pad_consistent g gm (rrec_native_bytes w ct) hg)).
qed.

(* The H map is essential for output/key uniqueness: distinct 224-byte
   outputs can encode the same CBD randomness. Once the input is unique,
   the actual map lookup makes its output, and hence its key, unique. *)
lemma sim_good_entries_unique w g (tab:(fo_h_input,W8.t Array224.t)fmap)
 (x1 x2:fo_h_input) hout1 hout2 ct :
 pke_key_relation w=>x1.`2=complete_sk_suffix w.`kg_sk=>x2.`2=complete_sk_suffix w.`kg_sk=>
 tab.[x1]=Some hout1=>tab.[x2]=Some hout2=>
 !fo_base_bad w g x1.`1 hout1=>!fo_base_bad w g x2.`1 hout2=>
 fo_reencryption w g x1.`1 hout1=Some ct=>fo_reencryption w g x2.`1 hout2=Some ct=>
 x1=x2 /\ hout1=hout2 /\ payload_shared_key hout1=payload_shared_key hout2.
proof.
 case x1=>msg1 suffix1; case x2=>msg2 suffix2 /=.
 move=>hk hs1 hs2 hh1 hh2 hb1 hb2 he1 he2.
 have hm:=sim_good_messages_unique w g msg1 msg2 hout1 hout2 ct hk hb1 hb2 he1 he2.
 have hx:(msg1,suffix1)=(msg2,suffix2) by rewrite hm hs1 hs2.
 have hh:hout1=hout2.
 + apply fo_some_injective; by rewrite -hh1 hx hh2.
 by rewrite hm hs1 hs2 hh.
qed.

lemma sim_challenge_no_match w g (input:fo_h_input) hout cstar ct :
 fo_challenge_relation w g input hout cstar=>ct<>cstar=>
 fo_reencryption w g input.`1 hout<>Some ct.
proof.
 move=>hc hn; rewrite /fo_reencryption /acwc2_code.
 exact(fo_challenge_other_cipher w g input hout cstar ct hc hn).
qed.

lemma sim_table_candidate_nonchallenge w g excluded hstar cstar
 (tab:(fo_h_input,W8.t Array224.t)fmap) (input:fo_h_input) hout ct :
 fo_challenge_invariant w g excluded hstar cstar tab=>tab.[input]=Some hout=>ct<>cstar=>
 fo_reencryption w g input.`1 hout=Some ct=>Some input<>excluded.
proof.
 move=>hc hh hn he; apply/negP=>hi.
 have hno:=fo_challenge_cached_other w g excluded hstar cstar tab input hout ct hc hi hh hn.
 have henc:pke_enc_spec w.`kg_pk (poly_sotp_encode_spec input.`1(g(fo_randomness hout)))
   (fo_randomness hout)=Some ct by move:he; rewrite /fo_reencryption /acwc2_code.
 by move:hno; rewrite henc.
qed.

lemma sim_table_matches_unique w g excluded hstar cstar
 (tab:(fo_h_input,W8.t Array224.t)fmap) (x1 x2:fo_h_input) hout1 hout2 ct :
 pke_key_relation w=>fo_hcache_good w g excluded tab=>
 fo_challenge_invariant w g excluded hstar cstar tab=>ct<>cstar=>
 x1.`2=complete_sk_suffix w.`kg_sk=>x2.`2=complete_sk_suffix w.`kg_sk=>
 tab.[x1]=Some hout1=>tab.[x2]=Some hout2=>
 fo_reencryption w g x1.`1 hout1=Some ct=>fo_reencryption w g x2.`1 hout2=Some ct=>
 x1=x2 /\ hout1=hout2 /\ payload_shared_key hout1=payload_shared_key hout2.
proof.
 move=>hk hg hc hn hs1 hs2 hh1 hh2 he1 he2.
 have hx1:=sim_table_candidate_nonchallenge w g excluded hstar cstar tab x1 hout1 ct hc hh1 hn he1.
 have hx2:=sim_table_candidate_nonchallenge w g excluded hstar cstar tab x2 hout2 ct hc hh2 hn he2.
 move:hg; rewrite /fo_hcache_good=>hg.
 exact(sim_good_entries_unique w g tab x1 x2 hout1 hout2 ct hk hs1 hs2 hh1 hh2
   (hg x1 hout1 hh1 hx1) (hg x2 hout2 hh2 hx2) he1 he2).
qed.
