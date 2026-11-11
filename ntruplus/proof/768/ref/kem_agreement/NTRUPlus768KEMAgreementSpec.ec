require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.
require import Array2336 Array1152 Array32 Array96 Array192 Array768.
require import NTRUPlus768KEMAgreementContext.
require import NTRUPlus768EncapCompleteSpec NTRUPlus768EncapCompleteAlgebra.
require import NTRUPlus768DecapCompleteSpec NTRUPlus768DecapGuardSpec NTRUPlus768EncapGuardSpec.
require import NTRUPlus768ValidKeyR2Recovery NTRUPlus768ValidKeyM1Recovery.
require import NTRUPlus768PolySOTPEncodeAlgebra NTRUPlus768PolyToBytesAlgebra.
require import NTRUPlus768NTTAlgebra NTRUPlus768NTTProof NTRUPlus768DecapHashHBridge NTRUPlus768HashFProof.

op agreement_no_wrap fbuf gbuf pk coins =
  sampled_m1_no_wrap fbuf gbuf (encap_full_r pk coins) (encap_full_m pk coins).

lemma agreement_encap_message pk coins :
  encap_full_m pk coins = r2_encap_message (encap_full_r pk coins) coins.
proof.
  by rewrite /encap_full_m /encap_full_pad /encap_full_rhat ntt_specE
    poly_tobytes_procedure_specE /r2_encap_message /serialized_hash_g_pad.
qed.

lemma agreement_encap_message_recovery fbuf gbuf finv ginv h hinv pk sk coins :
  agreement_key_relation fbuf gbuf finv ginv h hinv pk sk =>
  agreement_no_wrap fbuf gbuf pk coins =>
  let ct = NTRUPlus768PolyToBytesProof.poly_tobytes_spec (encap_full_cipher pk coins) in
  complete_entry_accepts ct sk /\
  complete_message_result ct sk =
    (NTRUPlus768PolyToBytesProof.poly_tobytes_spec (encap_full_rhat pk coins),coins,W32.zero) /\
  !complete_sotp_failed ct sk.
proof.
  move=> hk hn; simplify.
  have [hpk _] := agreement_key_canonical fbuf gbuf finv ginv h hinv pk sk hk.
  have he := encap_full_cipher_qring pk coins hpk.
  rewrite /encap_full_rhat /encap_full_mhat !ntt_specE agreement_encap_message in he.
  have hno : sampled_m1_no_wrap fbuf gbuf (encap_full_r pk coins)
      (r2_encap_message (encap_full_r pk coins) coins).
  + move: hn; by rewrite /agreement_no_wrap agreement_encap_message.
  have result := agreement_recover_message fbuf gbuf finv ginv h hinv pk sk
    (encap_full_r pk coins) (encap_full_cipher pk coins) coins hk
    (encap_full_r_input_qrange pk coins) he hno.
  by rewrite !poly_tobytes_procedure_specE /encap_full_rhat ntt_specE.
qed.

lemma agreement_hash_h_input fbuf gbuf finv ginv h hinv pk sk coins :
  agreement_key_relation fbuf gbuf finv ginv h hinv pk sk =>
  hash_h_spec coins (complete_sk_suffix sk) = encap_full_hash pk coins.
proof.
  rewrite /agreement_key_relation; move=> [_ [_ [_ [_ hs]]]].
  by rewrite hs /encap_full_hash.
qed.

lemma agreement_regeneration pk coins :
  complete_regenerated (encap_full_hash pk coins) =
  NTRUPlus768PolyToBytesProof.poly_tobytes_spec (encap_full_rhat pk coins).
proof. by rewrite /complete_regenerated /encap_full_rhat /encap_full_r. qed.

lemma agreement_spec_accepts fbuf gbuf finv ginv h hinv pk sk coins :
  agreement_key_relation fbuf gbuf finv ginv h hinv pk sk =>
  agreement_no_wrap fbuf gbuf pk coins =>
  complete_accepts
    (NTRUPlus768PolyToBytesProof.poly_tobytes_spec (encap_full_cipher pk coins)) sk.
proof.
  move=> hk hn.
  have [he [hm hf]] := agreement_encap_message_recovery fbuf gbuf finv ginv h hinv pk sk coins hk hn.
  rewrite /complete_accepts he /= /complete_tail_reject hm /= hf /=.
  by rewrite (agreement_hash_h_input fbuf gbuf finv ginv h hinv pk sk coins hk)
    agreement_regeneration.
qed.

lemma agreement_spec_key fbuf gbuf finv ginv h hinv pk sk coins :
  agreement_key_relation fbuf gbuf finv ginv h hinv pk sk =>
  agreement_no_wrap fbuf gbuf pk coins =>
  complete_spec
    (NTRUPlus768PolyToBytesProof.poly_tobytes_spec (encap_full_cipher pk coins)) sk =
  (encap_full_key pk coins,W32.zero).
proof.
  move=> hk hn.
  have ha := agreement_spec_accepts fbuf gbuf finv ginv h hinv pk sk coins hk hn.
  have [_ [hm _]] := agreement_encap_message_recovery fbuf gbuf finv ginv h hinv pk sk coins hk hn.
  rewrite (complete_accept_result _ _ ha) hm /=
    (agreement_hash_h_input fbuf gbuf finv ginv h hinv pk sk coins hk).
  done.
qed.

(* This roundtrip relates actual Encaps and Decaps value specifications.
   No-wrap is the explicit integer decryption condition; no probability or
   IND-CCA claim is inferred from this pointwise conditional theorem. *)
lemma agreement_spec_roundtrip fbuf gbuf finv ginv h hinv pk sk coins :
  agreement_key_relation fbuf gbuf finv ginv h hinv pk sk =>
  agreement_no_wrap fbuf gbuf pk coins =>
  (encap_derand_spec pk coins).`3 = W32.zero /\
  complete_spec (encap_derand_spec pk coins).`1 sk =
    ((encap_derand_spec pk coins).`2,W32.zero).
proof.
  move=> hk hn.
  have [hpk _] := agreement_key_canonical fbuf gbuf finv ginv h hinv pk sk hk.
  rewrite (encap_derand_accept pk coins hpk) /=.
  exact (agreement_spec_key fbuf gbuf finv ginv h hinv pk sk coins hk hn).
qed.
