require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord.
require import Array4 Array768 Array1152.
require import NTRUPlus768BasemulAlgebra NTRUPlus768PolyBasemulAlgebra NTRUPlus768PolyBasemulProof.
require import NTRUPlus768KeygenPublicKeyBridge NTRUPlus768PolyBaseInvBridge.
require import NTRUPlus768KeygenHBridge NTRUPlus768NTTSchedule.
require import NTRUPlus768ValidKeyR2Algebra NTRUPlus768R2Serialization.
require import NTRUPlus768PolySubAlgebra NTRUPlus768EncapPolyBasemulAddAlgebra.
require import NTRUPlus768PKEModel NTRUPlus768PKEAlgebra.
require import NTRUPlus768RRecModel NTRUPlus768RRecAlgebra NTRUPlus768RRecCodec.
require import NTRUPlus768RRecPublicInverse NTRUPlus768RRecInverseAlgebra.
require import NTRUPlus768DecapR2CompSpec NTRUPlus768DecapR2CompAlgebra.
require import NTRUPlus768CanonicalDecoder NTRUPlus768EncapGuardSpec.
require import NTRUPlus768PolyToBytesAlgebra NTRUPlus768PolyFromBytesAlgebra.
require import NTRUPlus768KEMPayloadSpec NTRUPlus768DecapCompleteSpec NTRUPlus768DecapGuardSpec.
require import NTRUPlus768ValidKeyR2Recovery.
import IntOrder Ring.IntID.

(* Reverse cancellation is local to the terminal quartic rings. The
   ciphertext is arbitrary; there is no honest-encryption or no-wrap premise. *)
lemma rrec_unit_product_mod_q a output :
 poly_basemul_qring a ntt_block_identity output 192 =>
 poly_coeff_eq_mod_q output a.
proof.
 move=>h j hj.
 have hk:0<=j %/ 4<192 by smt().
 have hi:0<=j %% 4<4 by smt().
 have hidx:4*(j %/ 4)+j %% 4=j by smt(IntDiv.divz_eq).
 have hb:=poly_basemul_qring_block_product a ntt_block_identity output (j %/ 4) h hk.
 rewrite(ntt_identity_block _ hk) in hb.
 have he:=block_product_unit_coeff (block4 a (j %/ 4))
   (block4 output (j %/ 4)) (terminal_value(j %/ 4)) (j %% 4) hb hi.
 move:he; rewrite /block4 !Array4.initiE 1:hi 1:hi; smt().
qed.

lemma rrec_inverse_product_cancel h inverse sub y r product :
 poly_basemul_qring h inverse ntt_block_identity 192 =>
 poly_basemul_qring sub inverse y 192 =>
 poly_basemul_qring h r product 192 =>
 poly_coeff_eq_mod_q y r => poly_coeff_eq_mod_q product sub.
proof.
 move=>hu hy hp he.
 have hunit:=poly_basemul_qring_comm h inverse ntt_block_identity hu.
 have hrh:=poly_basemul_qring_comm h r product hp.
 have hyh:=poly_basemul_qring_left_mod_q_congr r y h product he hrh.
 have hs:=poly_basemul_qring_reassociate sub inverse h y ntt_block_identity product hy hunit hyh.
 exact(rrec_unit_product_mod_q sub product hs).
qed.

lemma rrec_algebra_facts cp m inverse y :
 decap_r2_algebra cp m inverse y =>
 poly_sub_algebra cp (pke_mhat m) (r2_difference_spec cp m) /\
 poly_basemul_qring (r2_difference_spec cp m) inverse y 192 /\
 in_qrange768 y.
proof. rewrite /decap_r2_algebra /pke_mhat; smt(). qed.

lemma rrec_algebra_serializer cp m inverse y :
 decap_r2_algebra cp m inverse y =>
 NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange y.
proof.
 move=>h; have [_ [_ hq]]:=rrec_algebra_facts cp m inverse y h.
 exact(NTRUPlus768KeygenPublicKeyBridge.in_qrange768_poly_tobytes_input_qrange y hq).
qed.

lemma rrec_public_r2_serializer pk m ct :
 encap_key_canonical pk => rrec_public_inverse(decoded_poly pk)<>None => pke_domain m =>
 NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange(decap_r2_spec (decoded_poly ct) m
   (oget(rrec_public_inverse(decoded_poly pk)))).
proof.
 move=>hp hi hm.
 exact(rrec_algebra_serializer _ _ _ _ (rrec_public_r2_algebra pk m ct hp hi hm)).
qed.

lemma rrec_cipher_mod_q_from_r2 pk m ct r :
 encap_key_canonical pk => rrec_public_inverse(decoded_poly pk)<>None =>
 pke_domain m => pke_domain r =>
 poly_coeff_eq_mod_q
   (decap_r2_spec (decoded_poly ct) m (oget(rrec_public_inverse(decoded_poly pk)))) (pke_rhat r) =>
 poly_coeff_eq_mod_q (pke_cipher pk m r) (decoded_poly ct).
proof.
 move=>hp hi hm hr he.
 have hu:=rrec_public_inverse_product _ (rrec_public_key_range pk hp) hi.
 have [hs [hy _]]:=rrec_algebra_facts _ _ _ _ (rrec_public_r2_algebra pk m ct hp hi hm).
 have hpq:=pke_product_qring pk r hp hr.
 have hcancel:=rrec_inverse_product_cancel (decoded_poly pk)
   (oget(rrec_public_inverse(decoded_poly pk))) (r2_difference_spec (decoded_poly ct) m)
   (decap_r2_spec (decoded_poly ct) m (oget(rrec_public_inverse(decoded_poly pk))))
   (pke_rhat r) (pke_product pk r) hu hy hpq he.
 move=>j hj.
 have hc:=poly_centered_add_spec_coeff_mod_q (pke_product pk r) (pke_mhat m) j
   (pke_product_range pk r hp hr) (pke_mhat_centered m hm) hj.
 have [hsub _]:=hs j hj.
 have hprod:=hcancel j hj.
 rewrite /pke_cipher hc -modzDm hprod modzDm hsub.
 by rewrite (_:coeff(decoded_poly ct).[j]-coeff(pke_mhat m).[j]+coeff(pke_mhat m).[j]=
   coeff(decoded_poly ct).[j]) 1:/#.
qed.

lemma rrec_serialized_equal_mod_q a b :
 NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange a => NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange b =>
 NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec a=NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec b => poly_coeff_eq_mod_q a b.
proof.
 move=>ha hb he.
 have hd:r2_serialized_decode a=r2_serialized_decode b by rewrite /r2_serialized_decode he.
 have h1:=r2_serialized_decode_mod_q a ha.
 have h2:=r2_serialized_decode_mod_q b hb.
 rewrite -hd in h2; move=>j hj.
 by rewrite -(h1 j hj) (h2 j hj).
qed.

(* The stored inverse is only a proof witness. Public inversion still
   receives just the checked public polynomial. Canonical decoding makes
   the two inverse arrays exactly equal, not merely congruent. *)
lemma rrec_generated_public_inverse_stored w : pke_key_relation w =>
 rrec_public_inverse(decoded_poly w.`kg_pk)=
 Some(decoded_poly(decap_hbytes(complete_sk_poly w.`kg_sk))).
proof.
 move=>hk.
 have hrel:=hk; rewrite /pke_key_relation in hrel.
 have hser:=payload_secret_relation _ _ _ _ _ _ _ _ hrel.
 have [hkey hpub]:=secret_f_relation_keypair_and_public_congruence _ _ _ _ _ _ _ _ _ _ _ hser.
 have hbytes:decap_hbytes(complete_sk_poly w.`kg_sk)=NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec w.`kg_hinv.
 + move:hrel; rewrite /payload_key_relation; smt().
 have hq:=keygen_hinv_tobytes_input_qrange _ _ _ _ _ _ hkey.
 have hdecode:poly_coeff_eq_mod_q (decoded_poly(decap_hbytes(complete_sk_poly w.`kg_sk))) w.`kg_hinv.
 + rewrite hbytes; exact(r2_serialized_decode_mod_q w.`kg_hinv hq).
 have hunit:=decoded_h_hinv_inverse _ _ _ _ _ _ _ _ hkey hpub hdecode.
 apply rrec_public_inverse_known_canonical.
 + exact(rrec_public_key_range _ (pke_key_canonical w hk)).
 + rewrite hbytes; exact(r2_serialized_decode_canonical_range w.`kg_hinv hq).
 exact hunit.
qed.

require import NTRUPlus768RRecSerialization.

lemma rrec_r2_mod_q_reencrypt pk m ct r :
 encap_key_canonical pk => rrec_public_inverse(decoded_poly pk)<>None =>
 encap_key_canonical ct => pke_domain m => pke_domain r =>
 poly_coeff_eq_mod_q
   (decap_r2_spec (decoded_poly ct) m (oget(rrec_public_inverse(decoded_poly pk)))) (pke_rhat r) =>
 pke_enc_spec pk m r=Some ct.
proof.
 move=>hp hi hc hm hr he.
 have hmod:=rrec_cipher_mod_q_from_r2 pk m ct r hp hi hm hr he.
 have hdec:=NTRUPlus768KeygenPublicKeyBridge.in_qrange768_poly_tobytes_input_qrange _ (rrec_public_key_range ct hc).
 have hb:=poly_tobytes_mod_q_congr _ _ (pke_cipher_serializer pk m r hp hm hr) hdec hmod.
 by rewrite (pke_enc_accept pk m r hp) /pke_ciphertext hb (rrec_canonical_reencode ct hc).
qed.

lemma rrec_r2_serialized_iff pk m ct r :
 encap_key_canonical pk => rrec_public_inverse(decoded_poly pk)<>None =>
 encap_key_canonical ct => pke_domain m => pke_domain r =>
 (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec
   (decap_r2_spec (decoded_poly ct) m (oget(rrec_public_inverse(decoded_poly pk))))=
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec(pke_rhat r) <=>
  pke_enc_spec pk m r=Some ct).
proof.
 move=>hp hi hc hm hr; split.
 + move=>he; apply(rrec_r2_mod_q_reencrypt pk m ct r hp hi hc hm hr).
   exact(rrec_serialized_equal_mod_q _ _ (rrec_public_r2_serializer pk m ct hp hi hm)
     (rr_G_input_serializer r hr) he).
 move=>he.
 have hct:pke_ciphertext pk m r=ct by move:he; rewrite (pke_enc_accept pk m r hp); smt().
 have hmqr:=rrec_honest_r2_mod_q pk m r hp hi hm hr.
 rewrite hct in hmqr.
 exact(poly_tobytes_mod_q_congr _ _ (rrec_public_r2_serializer pk m ct hp hi hm)
   (rr_G_input_serializer r hr) hmqr).
qed.

require import NTRUPlus768RRecTransform.
require import NTRUPlus768PolyBasemulInvNTTAlgebra NTRUPlus768InvNTTProof.
require import NTRUPlus768InvNTTAlgebra NTRUPlus768RRecWordChecks.

lemma rrec_linear_candidate_reencrypt pk m ct :
 encap_key_canonical pk => rrec_public_inverse(decoded_poly pk)<>None =>
 encap_key_canonical ct => pke_domain m =>
 pke_domain(rrec_candidate (decoded_poly ct) m (oget(rrec_public_inverse(decoded_poly pk)))) =>
 pke_enc_spec pk m (rrec_candidate (decoded_poly ct) m
   (oget(rrec_public_inverse(decoded_poly pk))))=Some ct.
proof.
 move=>hp hi hc hm hr.
 have [_ [hq _]]:=rrec_algebra_facts _ _ _ _ (rrec_public_r2_algebra pk m ct hp hi hm).
 have [_ hshape]:=poly_basemul_qring_implies_invntt_ready _ _ _ hq.
 have he:rrec_normalize(inverse_invntt_spec
   (decap_r2_spec (decoded_poly ct) m (oget(rrec_public_inverse(decoded_poly pk)))))=
   rrec_candidate (decoded_poly ct) m (oget(rrec_public_inverse(decoded_poly pk))).
 + by rewrite /rrec_candidate invntt_specE.
 have hf:=rrec_inverse_forward_trit _ _ hshape hr he.
 apply(rrec_r2_mod_q_reencrypt pk m ct _ hp hi hc hm hr).
 move=>j hj; by rewrite -(hf j hj).
qed.
