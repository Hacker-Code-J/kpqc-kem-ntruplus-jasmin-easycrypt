require import AllCore IntDiv Distr.
from Jasmin require import JWord.
require import Array768 Array1152.
require import NTRUPlus768MRecModel NTRUPlus768PKEModel NTRUPlus768PKEAlgebra.
require import NTRUPlus768CanonicalDecoder NTRUPlus768EncapGuardSpec NTRUPlus768BasemulAlgebra.
require import NTRUPlus768RRecWordChecks NTRUPlus768RRecCodec NTRUPlus768RRecTransform NTRUPlus768RRecSerialization.
require import NTRUPlus768RRecAlgebra NTRUPlus768R2Serialization NTRUPlus768ValidKeyR2Recovery.
require import NTRUPlus768KeygenPublicKeyBridge NTRUPlus768PolyBasemulAlgebra.
require import NTRUPlus768PolySubProof NTRUPlus768PolySubAlgebra NTRUPlus768PolySubDecapBridge.
require import NTRUPlus768EncapPolyBasemulAddAlgebra NTRUPlus768PolyToBytesAlgebra.
require import NTRUPlus768NTTStage1Algebra NTRUPlus768NTTProof NTRUPlus768InvNTTProof NTRUPlus768InvNTTAlgebra NTRUPlus768InvNTTRadix2_4Algebra.
require import NTRUPlus768KeygenSecretFBridge.

lemma mrec_normalize_shape a : qrange_input_shape(rrec_normalize a).
proof.
 move=>j hj;rewrite(rrec_normalize_coeff a j hj) /q.
 have h:=rrec_center_range(coeff a.[j]);smt().
qed.
lemma mrec_difference_shape pk r ct : qrange_input_shape(mrec_difference pk r ct).
proof. rewrite /mrec_difference;exact(mrec_normalize_shape _). qed.
lemma mrec_product_range pk r : encap_key_canonical pk=>pke_domain r=>input_qrange(pke_product pk r).
proof.
 move=>hp hr j hj;exact(in_qrange768_coeff _ j (pke_product_range pk r hp hr) hj).
qed.
lemma mrec_difference_mod pk r ct : encap_key_canonical pk=>pke_domain r=>
 forall j,0<=j<768=>coeff(mrec_difference pk r ct).[j] %%q=
 (coeff(decoded_poly ct).[j]-coeff(pke_product pk r).[j]) %%q.
proof.
 move=>hp hr j hj;rewrite /mrec_difference (rrec_normalize_mod _ j hj).
 exact(poly_sub_spec_decoder_forward_modq _ _ j
  (poly_frombytes_spec_decoder_range ct) (mrec_product_range pk r hp hr) hj).
qed.
lemma mrec_sub_cancel (x y z:int) : x %%q=(y+z) %%q=>(x-y) %%q=z %%q.
proof.
 move=>h;rewrite -modzBm h modzBm.
 by rewrite (_:y+z-y=z) 1:/#.
qed.
lemma mrec_add_cancel (x y z:int) : z %%q=(x-y) %%q=>(y+z) %%q=x %%q.
proof.
 move=>h;rewrite -modzDm h modzDm.
 by rewrite (_:y+(x-y)=x) 1:/#.
qed.

lemma mrec_honest_difference pk m r : encap_key_canonical pk=>pke_domain m=>pke_domain r=>
 poly_coeff_eq_mod_q(mrec_difference pk r (pke_ciphertext pk m r))(pke_mhat m).
proof.
 move=>hp hm hr.
 have hd:poly_coeff_eq_mod_q(decoded_poly(pke_ciphertext pk m r))(pke_cipher pk m r).
 + rewrite /pke_ciphertext;exact(r2_serialized_decode_mod_q _ (pke_cipher_serializer pk m r hp hm hr)).
 move=>j hj;rewrite(mrec_difference_mod pk r (pke_ciphertext pk m r) hp hr j hj).
 apply mrec_sub_cancel.
 rewrite(hd j hj) /pke_cipher.
 exact(poly_centered_add_spec_coeff_mod_q _ _ j (pke_product_range pk r hp hr) (pke_mhat_centered m hm) hj).
qed.
lemma mrec_honest_candidate pk m r : encap_key_canonical pk=>pke_domain m=>pke_domain r=>
 mrec_candidate pk r (pke_ciphertext pk m r)=m.
proof.
 move=>hp hm hr;rewrite /mrec_candidate invntt_specE.
 apply(rrec_normalized_inverse_recovers _ m (mrec_difference_shape _ _ _) hm).
 have h:=mrec_honest_difference pk m r hp hm hr.
 by move:h;rewrite /pke_mhat /pke_rhat.
qed.

lemma mrec_candidate_transform pk r ct : pke_domain(mrec_candidate pk r ct)=>
 poly_coeff_eq_mod_q(pke_mhat(mrec_candidate pk r ct))(mrec_difference pk r ct).
proof.
 move=>hm.
 have he:rrec_normalize(inverse_invntt_spec(mrec_difference pk r ct))=mrec_candidate pk r ct
 by rewrite /mrec_candidate invntt_specE.
 have h:=rrec_inverse_forward_trit _ _ (mrec_difference_shape pk r ct) hm he.
 by move:h;rewrite /pke_mhat /pke_rhat.
qed.
lemma mrec_cipher_mod pk r ct : encap_key_canonical pk=>pke_domain r=>
 pke_domain(mrec_candidate pk r ct)=>
 poly_coeff_eq_mod_q(pke_cipher pk (mrec_candidate pk r ct) r)(decoded_poly ct).
proof.
 move=>hp hr hm;have hback:=mrec_candidate_transform pk r ct hm.
 move=>j hj;rewrite /pke_cipher.
 rewrite(poly_centered_add_spec_coeff_mod_q _ _ j
  (pke_product_range pk r hp hr) (pke_mhat_centered _ hm) hj).
 apply mrec_add_cancel.
 by rewrite(hback j hj) (mrec_difference_mod pk r ct hp hr j hj).
qed.
lemma mrec_candidate_reencrypt pk r ct :
 encap_key_canonical pk=>encap_key_canonical ct=>pke_domain r=>
 pke_domain(mrec_candidate pk r ct)=>
 pke_enc_spec pk (mrec_candidate pk r ct) r=Some ct.
proof.
 move=>hp hc hr hm.
 have hs:=pke_cipher_serializer pk (mrec_candidate pk r ct) r hp hm hr.
 have hd:=in_qrange768_poly_tobytes_input_qrange _ (rrec_public_key_range ct hc).
 have he:=poly_tobytes_mod_q_congr _ _ hs hd (mrec_cipher_mod pk r ct hp hr hm).
 by rewrite(pke_enc_accept _ _ _ hp) /pke_ciphertext he (rrec_canonical_reencode ct hc).
qed.

(* AC-MR holds for every accepted public input, including adversarial
   ciphertexts. Acceptance tests no guessed honest-encryption witness. *)
lemma mrec_acmr pk r ct m : mrec_spec pk r ct=Some m=>pke_enc_spec pk m r=Some ct.
proof.
 move=>hs;have [hp [hc [hr [hm he]]]]:=mrec_spec_some pk r ct m hs.
 subst m;exact(mrec_candidate_reencrypt pk r ct hp hc hr hm).
qed.
(* VC-MR is exact and has no coefficient no-wrap or decryption-failure
   premise: the public randomness is supplied to the recovery algorithm. *)
lemma mrec_vcmr pk m r ct : encap_key_canonical pk=>pke_domain m=>pke_domain r=>
 pke_enc_spec pk m r=Some ct=>mrec_spec pk r ct=Some m.
proof.
 move=>hp hm hr;rewrite(pke_enc_accept pk m r hp)=>/someI hc.
 rewrite -hc /mrec_spec hp (pke_cipher_canonical pk m r hp hm hr) hr /=
 (mrec_honest_candidate pk m r hp hm hr) hm;done.
qed.
lemma mrec_generated_forward w m r : pke_key_relation w=>pke_domain m=>pke_domain r=>
 mrec_spec w.`kg_pk r (pke_ciphertext w.`kg_pk m r)=Some m.
proof.
 move=>hk hm hr;have hp:=pke_key_canonical w hk.
 exact(mrec_vcmr _ _ _ _ hp hm hr (pke_enc_accept _ _ _ hp)).
qed.
