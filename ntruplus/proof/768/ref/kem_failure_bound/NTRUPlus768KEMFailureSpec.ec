require import AllCore Distr.
from Jasmin require import JWord.
require import Array32.
require import NTRUPlus768KEMFailureModel NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteProof.
require import NTRUPlus768KeygenCompleteAgreement NTRUPlus768KEMAgreementContext NTRUPlus768KEMAgreementSpec.
require import NTRUPlus768EncapCompleteRNG NTRUPlus768EncapCompleteSpec NTRUPlus768EncapCompleteProof NTRUPlus768EncapCompleteHash.
require import NTRUPlus768DecapMessageSpec NTRUPlus768DecapCompleteHash NTRUPlus768DecapCompleteProof NTRUPlus768DecapCompleteSpec.
require import NTRUPlus768EncapClearProof NTRUPlus768EncapClearCoinsProof NTRUPlus768DecapClearProof.

lemma generated_key_encap_status (w:keygen_witness) coins :
  keygen_witness_valid w => (encap_derand_spec w.`kg_pk coins).`3=W32.zero.
proof.
  rewrite /keygen_witness_valid; move=> hk.
  have [hpk _] := agreement_key_canonical w.`kg_fbuf w.`kg_gbuf w.`kg_finv w.`kg_ginv
    w.`kg_h w.`kg_hinv w.`kg_pk w.`kg_sk hk.
  by rewrite encap_derand_status.
qed.

lemma generated_key_failure_implies_bad (w:keygen_witness) coins (er:encap_result) (dr:decap_result) :
  keygen_witness_valid w =>
  (er.`1,er.`2,er.`3)=encap_derand_spec w.`kg_pk coins =>
  (dr.`1,dr.`2)=complete_spec er.`1 w.`kg_sk =>
  kem_failure er dr => !keygen_coins_no_wrap w coins.
proof.
  move=> hk he hd; case(keygen_coins_no_wrap w coins) => hn; last by done.
  have hs := agreement_spec_roundtrip w.`kg_fbuf w.`kg_gbuf w.`kg_finv w.`kg_ginv
    w.`kg_h w.`kg_hinv w.`kg_pk w.`kg_sk coins.
  rewrite /keygen_witness_valid in hk.
  rewrite /keygen_coins_no_wrap in hn.
  have [hes hds] := hs hk hn.
  rewrite -he /= in hes.
  rewrite -he /= in hds.
  rewrite -hd in hds.
  clear hk hn hs he hd.
  have hkey := congr1 (fun (v:W8.t Array32.t * W32.t) => v.`1) _ _ hds.
  have hstatus := congr1 (fun (v:W8.t Array32.t * W32.t) => v.`2) _ _ hds.
  rewrite /= in hkey.
  rewrite /= in hstatus.
  by rewrite /kem_failure hes hstatus -hkey.
qed.

