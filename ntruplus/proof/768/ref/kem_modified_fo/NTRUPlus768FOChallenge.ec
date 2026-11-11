require import AllCore List Distr FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152.
require import NTRUPlus768FOModel NTRUPlus768PKEModel NTRUPlus768PKEAlgebra.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteProof NTRUPlus768DecapCompleteSpec.
require import NTRUPlus768PolySOTPEncodeAlgebra NTRUPlus768ACWC2Oracle.
require import NTRUPlus768ROMOracles NTRUPlus768ROMEncap NTRUPlus768ROMKeygen.
require import NTRUPlus768KEMPayloadSpec NTRUPlus768RRecCodec.

(* The distinguished H value is the value actually used by encapsulation.
   No correctness or no-wrap property is required of this value. *)
op [opaque] fo_challenge_relation (w:keygen_witness) (g:acwc2_g_function)
 (input:fo_h_input) (hout:W8.t Array224.t) (ct:W8.t Array1152.t) =
 input.`2=complete_sk_suffix w.`kg_sk /\
 pke_enc_spec w.`kg_pk (poly_sotp_encode_spec input.`1 (g(fo_randomness hout)))
  (fo_randomness hout)=Some ct.
op [opaque] fo_challenge_invariant (w:keygen_witness) (g:acwc2_g_function)
 (input:fo_h_input option) (hout:W8.t Array224.t) (ct:W8.t Array1152.t)
 (hm:(fo_h_input,W8.t Array224.t)fmap) =
 exists x,input=Some x /\ fo_challenge_relation w g x hout ct /\ hm.[x]=Some hout.

lemma fo_challenge_other_cipher w g input hout cstar ct :
 fo_challenge_relation w g input hout cstar =>ct<>cstar =>
 pke_enc_spec w.`kg_pk (poly_sotp_encode_spec input.`1 (g(fo_randomness hout)))
  (fo_randomness hout)<>Some ct.
proof. rewrite /fo_challenge_relation; smt(). qed.
lemma fo_challenge_cached_other w g excluded hstar cstar hm input hout ct :
 fo_challenge_invariant w g excluded hstar cstar hm =>
 Some input=excluded =>hm.[input]=Some hout =>ct<>cstar =>
 pke_enc_spec w.`kg_pk (poly_sotp_encode_spec input.`1 (g(fo_randomness hout)))
  (fo_randomness hout)<>Some ct.
proof.
 rewrite /fo_challenge_invariant; move=>[x [he [hr hx]]] hi hh hc.
 have hi':input=x by move:hi; rewrite he /=.
 have hh':hout=hstar by move:hh; rewrite hi' hx /=; smt().
 rewrite hi' hh'.
 exact(fo_challenge_other_cipher w g x hstar cstar ct hr hc).
qed.
lemma fo_challenge_cache_extends w g excluded hout ct old new :
 fo_challenge_invariant w g excluded hout ct old =>cache_extends old new =>
 fo_challenge_invariant w g excluded hout ct new.
proof. rewrite /fo_challenge_invariant /cache_extends; smt(). qed.
lemma fo_challenge_singleton_good w g input hout :
 fo_hcache_good w g (Some input) empty.[input<-hout].
proof.
 rewrite /fo_hcache_good=>x y; rewrite get_setE emptyE.
 case(x=input)=>he; smt().
qed.

lemma fo_randomness_payload hout : fo_randomness hout=payload_r hout.
proof. by rewrite /fo_randomness /payload_r. qed.
lemma fo_payload_serialized hout : payload_serialized hout=rr_G_input(fo_randomness hout).
proof. by rewrite /payload_serialized /payload_rhat /rr_G_input /pke_rhat fo_randomness_payload. qed.
lemma fo_payload_cipher pk msg hout pad :
 NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec(payload_cipher pk msg hout pad)=
 pke_ciphertext pk (poly_sotp_encode_spec msg pad) (fo_randomness hout).
proof.
 by rewrite /pke_ciphertext /pke_cipher /pke_product /pke_mhat /pke_rhat
  /payload_cipher /payload_product /payload_mhat /payload_rhat /payload_m fo_randomness_payload.
qed.
lemma fo_rom_encap_relation w g msg fm gm hm er :
 pke_key_relation w =>acwc2_cache_matches g gm =>
 rom_encap_relation w.`kg_pk msg (complete_sk_suffix w.`kg_sk) fm gm hm er =>
 let hout=oget hm.[(msg,complete_sk_suffix w.`kg_sk)] in
 fo_challenge_relation w g (msg,complete_sk_suffix w.`kg_sk) hout er.`1 /\
 hm.[(msg,complete_sk_suffix w.`kg_sk)]=Some hout /\ er.`3=W32.zero /\
 er.`2=payload_shared_key hout.
proof.
 move=>hk hg; rewrite /rom_encap_relation /fo_challenge_relation /=.
 move=>[hf [hh [hp he]]]; rewrite he /=; split; last smt().
 have hr:=pke_domain_cbd(complete_hash_tail(oget hm.[(msg,complete_sk_suffix w.`kg_sk)])).
 have hcache:=hg (fo_randomness(oget hm.[(msg,complete_sk_suffix w.`kg_sk)])) hr.
 rewrite -fo_payload_serialized in hcache.
 rewrite (pke_enc_accept _ _ _ (pke_key_canonical w hk)) -fo_payload_cipher.
 by rewrite hcache /=.
qed.

require import NTRUPlus768FOAlgebra NTRUPlus768ACWC2Model NTRUPlus768RRecNativeComparison.

lemma fo_challenge_reencryption_other w g excluded hstar cstar hm msg hout ct :
 fo_challenge_invariant w g excluded hstar cstar hm =>
 Some(msg,complete_sk_suffix w.`kg_sk)=excluded =>
 hm.[(msg,complete_sk_suffix w.`kg_sk)]=Some hout =>ct<>cstar =>
 fo_reencryption w g msg hout<>Some ct.
proof.
 move=>hc hi hh hn; rewrite /fo_reencryption /acwc2_code.
 exact(fo_challenge_cached_other w g excluded hstar cstar hm
   (msg,complete_sk_suffix w.`kg_sk) hout ct hc hi hh hn).
qed.
lemma fo_challenge_full_reject w g excluded hstar cstar hm ct pad hout :
 fo_challenge_invariant w g excluded hstar cstar hm =>
 Some(fo_candidate_message w ct pad,complete_sk_suffix w.`kg_sk)=excluded =>
 hm.[(fo_candidate_message w ct pad,complete_sk_suffix w.`kg_sk)]=Some hout =>
 ct<>cstar =>!fo_full_accept w g ct pad hout.
proof.
 move=>hc hi hh hn.
 have hf:=fo_challenge_reencryption_other w g excluded hstar cstar hm
   (fo_candidate_message w ct pad) hout ct hc hi hh hn.
 rewrite /fo_full_accept; smt().
qed.
lemma fo_challenge_native_reject w g excluded hstar cstar hm ct pad hout :
 pke_key_relation w =>fo_pad_consistent g (rrec_native_bytes w ct) pad =>
 fo_challenge_invariant w g excluded hstar cstar hm =>
 Some(fo_candidate_message w ct pad,complete_sk_suffix w.`kg_sk)=excluded =>
 hm.[(fo_candidate_message w ct pad,complete_sk_suffix w.`kg_sk)]=Some hout =>
 ct<>cstar =>!fo_native_accept w ct pad hout.
proof.
 move=>hk hp hc hi hh hn.
 have hf:=fo_challenge_full_reject w g excluded hstar cstar hm ct pad hout hc hi hh hn.
 apply/negP=>ha.
 have hfull:=fo_native_implies_full w g ct pad hout hk hp ha.
 by move:hf; rewrite hfull.
qed.
lemma fo_challenge_both_reject w g excluded hstar cstar hm ct pad hout :
 pke_key_relation w =>fo_pad_consistent g (rrec_native_bytes w ct) pad =>
 fo_challenge_invariant w g excluded hstar cstar hm =>
 Some(fo_candidate_message w ct pad,complete_sk_suffix w.`kg_sk)=excluded =>
 hm.[(fo_candidate_message w ct pad,complete_sk_suffix w.`kg_sk)]=Some hout =>
 ct<>cstar =>!fo_native_accept w ct pad hout /\ !fo_full_accept w g ct pad hout.
proof.
 move=>hk hp hc hi hh hn; split.
 + exact(fo_challenge_native_reject w g excluded hstar cstar hm ct pad hout hk hp hc hi hh hn).
 exact(fo_challenge_full_reject w g excluded hstar cstar hm ct pad hout hc hi hh hn).
qed.
