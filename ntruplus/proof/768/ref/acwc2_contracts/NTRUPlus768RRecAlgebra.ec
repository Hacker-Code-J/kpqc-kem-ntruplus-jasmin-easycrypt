require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord.
require import Array4 Array768 Array1152.
require import NTRUPlus768PKEModel NTRUPlus768PKEAlgebra NTRUPlus768RRecModel.
require import NTRUPlus768BasemulAlgebra NTRUPlus768PolyBasemulAlgebra.
require import NTRUPlus768KeygenPublicKeyBridge NTRUPlus768PolyBaseInvBridge.
require import NTRUPlus768ValidKeyR2Algebra NTRUPlus768ValidKeyR2Recovery NTRUPlus768R2Serialization.
require import NTRUPlus768DecapR2CompSpec NTRUPlus768DecapR2CompAlgebra.
require import NTRUPlus768DecapCandidateAlgebra NTRUPlus768EncapCompleteAlgebra.
require import NTRUPlus768PolySubAlgebra NTRUPlus768EncapPolyBasemulAddAlgebra.
require import NTRUPlus768RRecPublicInverse NTRUPlus768RRecInverseAlgebra.
require import NTRUPlus768KEMPayloadSpec.
require import NTRUPlus768EncapGuardSpec NTRUPlus768CanonicalDecoder.
require import NTRUPlus768PolyCBD1Algebra NTRUPlus768PolySubDecapBridge NTRUPlus768DecapCandidateSpec.
import IntOrder Ring.IntID.

lemma rrec_public_key_range pk : encap_key_canonical pk =>
 in_qrange768(decoded_poly pk).
proof. move=>h; exact(encap_pointwise_blocks _ (candidate_canonical_decoder_qrange pk h)). qed.

lemma rrec_public_r2_algebra pk m ct :
 encap_key_canonical pk => rrec_public_inverse(decoded_poly pk)<>None => pke_domain m =>
 decap_r2_algebra (decoded_poly ct) m (oget(rrec_public_inverse(decoded_poly pk)))
  (decap_r2_spec (decoded_poly ct) m (oget(rrec_public_inverse(decoded_poly pk)))).
proof.
 move=>hp hi hm.
 apply r2_spec_algebra.
 + exact(poly_frombytes_spec_decoder_range ct).
 + by move:hm; rewrite /pke_domain /poly_cbd1_trit_output /candidate_ternary.
 + exact(rrec_public_inverse_canonical _ (rrec_public_key_range pk hp) hi).
qed.

(* Subtracting the public message and multiplying by the public inverse
   cancels an honest ciphertext at every terminal block. No coefficient
   no-wrap premise, secret key, or global representative of h is used. *)
lemma rrec_honest_r2_mod_q pk m r :
 encap_key_canonical pk => rrec_public_inverse(decoded_poly pk)<>None =>
 pke_domain m => pke_domain r =>
 poly_coeff_eq_mod_q
  (decap_r2_spec (decoded_poly(pke_ciphertext pk m r)) m
    (oget(rrec_public_inverse(decoded_poly pk)))) (pke_rhat r).
proof.
 move=>hp hi hm hr.
 have hri:=rrec_public_inverse_product _ (rrec_public_key_range pk hp) hi.
 have [_ [_ [hs [hprod _]]]]:=rrec_public_r2_algebra pk m (pke_ciphertext pk m r) hp hi hm.
 rewrite (pke_mhatE m) in hs.
 have he:=pke_cipher_qring pk m r hp hm hr.
 have hd:poly_coeff_eq_mod_q (decoded_poly(pke_ciphertext pk m r)) (pke_cipher pk m r).
 + rewrite /pke_ciphertext; exact(r2_serialized_decode_mod_q _ (pke_cipher_serializer pk m r hp hm hr)).
 exact(inverse_r2_mod_q _ _ _ _ _ _ _ _ hri he hd hs hprod).
qed.

lemma rrec_generated_inverse w : pke_key_relation w =>
 rrec_public_inverse(decoded_poly w.`kg_pk)<>None.
proof.
 move=>hk.
 have hkey:=hk; rewrite /pke_key_relation in hkey.
 have hser:=payload_secret_relation _ _ _ _ _ _ _ _ hkey.
 have [hrel hpub]:=secret_f_relation_keypair_and_public_congruence _ _ _ _ _ _ _ _ _ _ _ hser.
 have hu:=keygen_h_hinv_inverse _ _ _ _ _ _ hrel.
 have hunit:=poly_basemul_qring_left_mod_q_congr w.`kg_h (decoded_poly w.`kg_pk)
   w.`kg_hinv ntt_block_identity hpub hu.
 have [hs _]:=rrec_public_inverse_known (decoded_poly w.`kg_pk) w.`kg_hinv
   (rrec_public_key_range w.`kg_pk (pke_key_canonical w hk)) hunit.
 exact hs.
qed.

require import NTRUPlus768RRecCodec NTRUPlus768RRecWordChecks.
require import NTRUPlus768PolyBasemulInvNTTAlgebra NTRUPlus768InvNTTProof.
require import NTRUPlus768InvNTTAlgebra.

lemma rrec_honest_candidate pk m r :
 encap_key_canonical pk => rrec_public_inverse(decoded_poly pk)<>None =>
 pke_domain m => pke_domain r =>
 rrec_candidate (decoded_poly(pke_ciphertext pk m r)) m
  (oget(rrec_public_inverse(decoded_poly pk)))=r.
proof.
 move=>hp hi hm hr.
 have [_ [_ [_ [hprod _]]]]:=rrec_public_r2_algebra pk m (pke_ciphertext pk m r) hp hi hm.
 have [_ ha]:=poly_basemul_qring_implies_invntt_ready _ _ _ hprod.
 have he:=rrec_honest_r2_mod_q pk m r hp hi hm hr.
 rewrite /rrec_candidate invntt_specE.
 exact(rrec_normalized_inverse_recovers _ r ha hr he).
qed.

lemma rrec_public_forward pk m r :
 encap_key_canonical pk => rrec_public_inverse(decoded_poly pk)<>None =>
 pke_domain m => pke_domain r =>
 rrec_spec pk m (pke_ciphertext pk m r)=Some r.
proof.
 move=>hp hi hm hr.
 have hc:=pke_cipher_canonical pk m r hp hm hr.
 have he:=rrec_honest_candidate pk m r hp hi hm hr.
 rewrite /rrec_spec hp /= hi /rrec_using_inverse_spec hc hm /=.
 rewrite /rrec_finish_spec he hr /=.
 exact(rrec_verify_accept _ _ _ _ (pke_enc_accept pk m r hp)).
qed.

lemma rrec_keyed_forward w m r :
 pke_key_relation w => pke_domain m => pke_domain r =>
 rrec_spec w.`kg_pk m (pke_ciphertext w.`kg_pk m r)=Some r.
proof.
 move=>hk hm hr; exact(rrec_public_forward w.`kg_pk m r
  (pke_key_canonical w hk) (rrec_generated_inverse w hk) hm hr).
qed.

