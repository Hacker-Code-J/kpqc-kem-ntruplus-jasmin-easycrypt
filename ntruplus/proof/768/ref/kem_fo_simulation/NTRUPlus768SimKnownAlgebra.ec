require import AllCore List FMap FSet.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array768 Array1152.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768PKEModel.
require import NTRUPlus768ACWC2Oracle NTRUPlus768FOModel NTRUPlus768FOAlgebra.
require import NTRUPlus768FONativeBridge NTRUPlus768FOChallenge.
require import NTRUPlus768DecapCompleteSpec NTRUPlus768RRecNativeComparison.
require import NTRUPlus768RRecModel NTRUPlus768ACWC2Model.
require import NTRUPlus768KEMPayloadSpec NTRUPlus768CCAStatusAdapter.
require import NTRUPlus768SimModel NTRUPlus768SimCandidate NTRUPlus768SimLookup.

op [opaque] sim_request_of (w:keygen_witness) (ct:W8.t Array1152.t) (pad:W8.t Array192.t) : sim_request =
 {|sr_pk=w.`kg_pk;sr_ct=ct;sr_code=rrec_native_message w ct;
   sr_msg=fo_candidate_message w ct pad;
   sr_fail=W32.of_int(b2i(fo_candidate_failed w ct pad));
   sr_suffix=complete_sk_suffix w.`kg_sk|}.
op [opaque] sim_known_input (w:keygen_witness) (ct:W8.t Array1152.t) (pad:W8.t Array192.t) =
 (fo_candidate_message w ct pad,complete_sk_suffix w.`kg_sk).
op [opaque] sim_known_result (w:keygen_witness) (g:acwc2_g_function)
 (log:(fo_h_input,W8.t Array224.t)fmap) (ct:W8.t Array1152.t) (pad:W8.t Array192.t) =
 let input=sim_known_input w ct pad in
 if input \in log /\ fo_full_accept w g ct pad (oget log.[input])
 then Some(payload_shared_key(oget log.[input])) else None.
op [opaque] sim_answer_value (g:acwc2_g_function) (q:sim_request) (hout:W8.t Array224.t) =
 let accepted=q.`sr_fail=W32.zero /\ rrec_spec q.`sr_pk q.`sr_code q.`sr_ct<>None /\
  pke_enc_spec q.`sr_pk (acwc2_code g q.`sr_msg (fo_randomness hout)) (fo_randomness hout)=Some q.`sr_ct in
 if accepted then Some(payload_shared_key hout) else None.
op [opaque] sim_known_answer_value (g:acwc2_g_function)
 (log:(fo_h_input,W8.t Array224.t)fmap) (q:sim_request) =
 if sim_h_input q \in log then sim_answer_value g q (oget log.[sim_h_input q]) else None.
op [opaque] sim_matching_good (w:keygen_witness) (g:acwc2_g_function)
 (log:(fo_h_input,W8.t Array224.t)fmap) (ct:W8.t Array1152.t) =
 forall input hout,log.[input]=Some hout=>input.`2=complete_sk_suffix w.`kg_sk=>
 fo_reencryption w g input.`1 hout=Some ct=>!fo_base_bad w g input.`1 hout.

lemma sim_request_input w ct pad : sim_h_input(sim_request_of w ct pad)=sim_known_input w ct pad.
proof. by rewrite /sim_h_input /sim_request_of /sim_known_input. qed.

lemma sim_fo_option_result hout accept :
 cca_status_result (fo_result hout accept).`1 (fo_result hout accept).`2=
 if accept then Some(payload_shared_key hout) else None.
proof.
 case accept;rewrite /fo_result /cca_status_result /payload_shared_key /finish_key_prefix /=;
 smt(W32.to_uint0 W32.to_uint1).
qed.

(* A challenge entry may occur in the public log. It cannot match a
   different ciphertext, so only nonchallenge matches need base goodness. *)
lemma sim_matching_challenge_good w g log table ex hs cs ct :
 sim_log_included log table=>fo_hcache_good w g ex log=>
 fo_challenge_invariant w g ex hs cs table=>ct<>cs=>
 sim_matching_good w g log ct.
proof.
 move=>hi hg hc hn;rewrite /sim_matching_good=>input hout hh hsuffix he.
 have ht:table.[input]=Some hout by exact(hi input hout hh).
 have hx:=sim_table_candidate_nonchallenge w g ex hs cs table input hout ct hc ht hn he.
 exact(hg input hout hh hx).
qed.

lemma sim_known_matching_entry w g log ct pad input hout :
 pke_key_relation w=>sim_matching_good w g log ct=>
 fo_pad_consistent g (rrec_native_bytes w ct) pad=>
 log.[input]=Some hout=>input.`2=complete_sk_suffix w.`kg_sk=>
 fo_reencryption w g input.`1 hout=Some ct=>
 sim_known_input w ct pad=input /\ fo_full_accept w g ct pad hout.
proof.
 move=>hk hg hp hh hs he.
 have hb:!fo_base_bad w g input.`1 hout.
 + move:hg;rewrite /sim_matching_good=>hg;exact(hg input hout hh hs he).
 have [hi [_ [hf _]]]:=sim_good_entry_accepts w g input hout ct pad hk hs hb he hp.
 by rewrite /sim_known_input.
qed.

lemma sim_known_request_value w g log ct pad : complete_entry_accepts ct w.`kg_sk=>
 sim_known_answer_value g log (sim_request_of w ct pad)=sim_known_result w g log ct pad.
proof.
 move=>ha;rewrite /sim_known_answer_value sim_request_input /sim_known_result /=.
 case(sim_known_input w ct pad \in log)=>hi;last done.
 by rewrite /sim_answer_value /sim_request_of /= fo_word_flag /fo_full_accept ha /fo_reencryption.
qed.

lemma sim_known_invalid w g log ct pad : !complete_entry_accepts ct w.`kg_sk=>
 sim_known_result w g log ct pad=None.
proof. move=>ha;by rewrite /sim_known_result /fo_full_accept ha /=. qed.

lemma sim_candidate_reencryption w g (input:fo_h_input) hout :
 sim_candidate w.`kg_pk g input hout=fo_reencryption w g input.`1 hout.
proof. by rewrite /sim_candidate /fo_reencryption /NTRUPlus768ACWC2Model.acwc2_code. qed.

lemma sim_known_lookup_result w g log ct pad :
 pke_key_relation w=>sim_matching_good w g log ct=>
 fo_pad_consistent g (rrec_native_bytes w ct) pad=>
 sim_known_result w g log ct pad=
 sim_lookup_result w.`kg_pk (complete_sk_suffix w.`kg_sk) g log ct.
proof.
 move=>hk hg hp.
 case(sim_lookup_result w.`kg_pk (complete_sk_suffix w.`kg_sk) g log ct=None)=>hl.
 + rewrite hl /sim_known_result /=.
   case(sim_known_input w ct pad \in log /\
     fo_full_accept w g ct pad (oget log.[sim_known_input w ct pad]))=>ha;last done.
   have [hi hf]:=ha.
   have hm:sim_entry_matches w.`kg_pk (complete_sk_suffix w.`kg_sk) g log ct (sim_known_input w ct pad).
   + rewrite /sim_entry_matches sim_candidate_reencryption /sim_known_input /=.
     move:hf;rewrite /fo_full_accept;smt().
   have hn:forall input,input \in log=>
    !sim_entry_matches w.`kg_pk (complete_sk_suffix w.`kg_sk) g log ct input
    by move:hl;rewrite sim_lookup_result_none.
   by have:=hn _ hi;rewrite hm.
 pose key:=oget(sim_lookup_result w.`kg_pk (complete_sk_suffix w.`kg_sk) g log ct).
 have hlsome:sim_lookup_result w.`kg_pk (complete_sk_suffix w.`kg_sk) g log ct=Some key
  by apply some_oget.
 have [input hout [hh [hs [he hv]]]]:=sim_lookup_result_found
   w.`kg_pk (complete_sk_suffix w.`kg_sk) g log ct key hlsome.
 rewrite sim_candidate_reencryption in he.
 have [hi hf]:=sim_known_matching_entry w g log ct pad input hout hk hg hp hh hs he.
 have hd:input \in log by rewrite domE hh.
 by rewrite /sim_known_result hi /= hd hh /= hf hlsome hv.
qed.

lemma sim_known_lookup_challenge w g log table ct pad ex hs cs :
 pke_key_relation w=>sim_log_included log table=>fo_hcache_good w g ex log=>
 fo_challenge_invariant w g ex hs cs table=>ct<>cs=>
 fo_pad_consistent g (rrec_native_bytes w ct) pad=>
 sim_known_result w g log ct pad=
 sim_lookup_spec w.`kg_pk (complete_sk_suffix w.`kg_sk) (Some cs) g log ct.
proof.
 move=>hk hi hg hc hn hp.
 rewrite /sim_lookup_spec.
 have hsneq:(Some cs<>Some ct) by smt().
 rewrite hsneq /=.
 exact(sim_known_lookup_result w g log ct pad hk (sim_matching_challenge_good w g log table ex hs cs ct hi hg hc hn) hp).
qed.

lemma sim_known_nontrit_rejects w g log ct pad :
 pke_key_relation w=>sim_matching_good w g log ct=>
 (forall r,pke_domain r=>rrec_native_bytes w ct<>NTRUPlus768RRecCodec.rr_G_input r)=>
 sim_known_result w g log ct pad=None.
proof.
 move=>hk hg houtside.
 have hp:fo_pad_consistent g (rrec_native_bytes w ct) pad.
 + rewrite /fo_pad_consistent=>r hr he;by have:=houtside r hr;rewrite he.
 rewrite(sim_known_lookup_result w g log ct pad hk hg hp) sim_lookup_result_none.
 move=>input hd;apply/negP=>hm.
 rewrite /sim_entry_matches in hm;have [hs he]:=hm.
 have hh:log.[input]=Some(oget log.[input]) by apply some_oget;by move:hd;rewrite domE.
 rewrite sim_candidate_reencryption in he.
 have hb:!fo_base_bad w g input.`1 (oget log.[input]).
 + move:hg;rewrite /sim_matching_good=>hg;exact(hg _ _ hh hs he).
 have [_ [_ [_ [hbytes _]]]]:=sim_good_reencryption_recovers w g input.`1 (oget log.[input]) ct hk hb he.
 by have:=houtside (fo_randomness(oget log.[input])) (fo_randomness_domain _);rewrite hbytes.
qed.

lemma sim_lookup_invalid w g log ct : pke_key_relation w=>!complete_entry_accepts ct w.`kg_sk=>
 sim_lookup_result w.`kg_pk (complete_sk_suffix w.`kg_sk) g log ct=None.
proof.
 move=>hk hn;rewrite sim_lookup_result_none=>input hi;apply/negP=>hm.
 rewrite /sim_entry_matches in hm;have [hs he]:=hm.
 rewrite sim_candidate_reencryption in he.
 have ha:=sim_reencryption_entry w g input.`1 (oget log.[input]) ct hk he.
 by move:hn;rewrite ha.
qed.
