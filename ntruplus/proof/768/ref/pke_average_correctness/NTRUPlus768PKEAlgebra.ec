require import AllCore IntDiv Ring StdOrder FMap.
from Jasmin require import JWord.
require import Array192 Array768 Array1152.
require import NTRUPlus768PKEModel NTRUPlus768BasemulAlgebra.
require import NTRUPlus768PolyCBD1Algebra NTRUPlus768PolyBasemulAlgebra NTRUPlus768PolyBasemulProof.
require import NTRUPlus768NTTProof NTRUPlus768NTTAlgebra NTRUPlus768NTTStage1Algebra NTRUPlus768NTTRadix2_4Algebra.
require import NTRUPlus768EncapCompleteAlgebra NTRUPlus768EncapPolyBasemulAddAlgebra.
require import NTRUPlus768DecapCandidateSpec NTRUPlus768DecapCandidateAlgebra.
require import NTRUPlus768EncapGuardSpec NTRUPlus768DecapGuardSpec NTRUPlus768DecapCompleteSpec.
require import NTRUPlus768DecapMessageAlgebra NTRUPlus768CanonicalDecoder.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768KeygenHBridge NTRUPlus768PolyBaseInvBridge.
require import NTRUPlus768KeygenSamplerAlgebra NTRUPlus768KeygenSamplerBridge.
require import NTRUPlus768KeygenPublicKeyBridge NTRUPlus768KeygenSecretFBridge.
require import NTRUPlus768KEMPayloadSpec NTRUPlus768KEMPayloadAlgebra NTRUPlus768ValidKeyM1Recovery.
require import NTRUPlus768PolyToBytesAlgebra NTRUPlus768R2Serialization.
require import NTRUPlus768CyclotomicFactorization NTRUPlus768EvaluationSemantics NTRUPlus768TerminalRepresentation.
require import NTRUPlus768ForwardNTTSemantics NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768InverseNTTSemantics NTRUPlus768InvNTTAlgebra NTRUPlus768InvNTTRadix2_4Algebra.
require import NTRUPlus768ValidKeyDecapM1Semantics NTRUPlus768PolyBasemulInvNTTAlgebra.
require import NTRUPlus768CoefficientRecovery NTRUPlus768Crepmod3Algebra NTRUPlus768Crepmod3Recovery.
require import NTRUPlus768Crepmod3Proof NTRUPlus768Crepmod3DecapBridge NTRUPlus768InvNTTProof.
import IntOrder Ring.IntID.

abbrev ( + ) = NTRUPoly.PolyComRing.( + ).
abbrev ( * ) = NTRUPoly.PolyComRing.( * ).

lemma pke_domain_qrange p : pke_domain p => input_qrange p.
proof. rewrite /pke_domain; exact(trit_polynomial_input_qrange p). qed.
lemma pke_rhat_range r : pke_domain r => input_qrange(pke_rhat r).
proof.
 move=> hr; rewrite /pke_rhat ntt_specE; move=>j hj.
 exact(forward_ntt_centered_coeff_range r j (pke_domain_qrange r hr) hj).
qed.
lemma pke_mhat_centered m : pke_domain m => centered_input_shape(pke_mhat m).
proof.
 move=>hm; rewrite /pke_mhat ntt_specE.
 exact(forward_ntt_centered_output_shape m (pke_domain_qrange m hm)).
qed.
lemma pke_product_qring pk r : encap_key_canonical pk => pke_domain r =>
 poly_basemul_qring (decoded_poly pk) (pke_rhat r) (pke_product pk r) 192.
proof.
 move=>hk hr; rewrite /pke_product; apply poly_basemul_word_to_qring.
 + apply encap_pointwise_blocks; exact(candidate_canonical_decoder_qrange pk hk).
 + apply encap_pointwise_blocks; exact(pke_rhat_range r hr).
 exact(candidate_product_word _ _).
qed.
lemma pke_product_range pk r : encap_key_canonical pk => pke_domain r =>
 in_qrange768(pke_product pk r).
proof.
 move=>hk hr; exact(poly_basemul_qring_product_in_qrange768 _ _ _ (pke_product_qring pk r hk hr)).
qed.
lemma pke_cipher_qring pk m r : encap_key_canonical pk => pke_domain m => pke_domain r =>
 poly_basemul_add_qring (decoded_poly pk) (pke_rhat r) (pke_mhat m) (pke_cipher pk m r) 192.
proof.
 move=>hk hm hr; rewrite /pke_cipher.
 exact(poly_basemul_add_spec_qring _ _ _ _ (pke_product_qring pk r hk hr) (pke_mhat_centered m hm)).
qed.
lemma pke_cipher_serializer pk m r : encap_key_canonical pk => pke_domain m => pke_domain r =>
 NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange(pke_cipher pk m r).
proof.
 move=>hk hm hr; exact(encap_cipher_tobytes_input_qrange _ _ _ _ (pke_cipher_qring pk m r hk hm hr)).
qed.
lemma pke_cipher_canonical pk m r : encap_key_canonical pk => pke_domain m => pke_domain r =>
 encap_key_canonical(pke_ciphertext pk m r).
proof.
 move=>hk hm hr; rewrite /pke_ciphertext.
 exact(payload_serialized_canonical _ (pke_cipher_serializer pk m r hk hm hr)).
qed.

lemma pke_key_canonical w : pke_key_relation w => encap_key_canonical w.`kg_pk.
proof.
 rewrite /pke_key_relation=>hk.
 have [hp _]:=payload_key_canonical _ _ _ _ _ _ _ _ hk; exact hp.
qed.
lemma pke_secret_canonical w : pke_key_relation w => encap_key_canonical(pke_secret_bytes w).
proof.
 rewrite /pke_key_relation=>hk.
 have [_ hf]:=payload_key_canonical _ _ _ _ _ _ _ _ hk.
 by move:hf; rewrite /decap_key_encoding_valid /pke_secret_bytes; smt().
qed.
lemma pke_key_inverse_relation w : pke_key_relation w =>
 keygen_keypair_ntt_relation (keygen_f_ntt_spec w.`kg_fbuf) w.`kg_finv
   (keygen_g_ntt_spec w.`kg_gbuf) w.`kg_ginv w.`kg_h w.`kg_hinv.
proof. by rewrite /pke_key_relation /payload_key_relation; smt(). qed.
lemma pke_actual_inverse_predicates w : pke_key_relation w =>
 poly_baseinv_success (keygen_f_ntt_spec w.`kg_fbuf) w.`kg_finv /\
 poly_baseinv_success (keygen_g_ntt_spec w.`kg_gbuf) w.`kg_ginv.
proof.
 move=>hk; have h:=pke_key_inverse_relation w hk.
 by move:h; rewrite /keygen_keypair_ntt_relation; smt().
qed.
lemma pke_key_shapes w :
 input_poly(keygen_f_pre_ntt_spec w.`kg_fbuf)=
   poly1+polyC(lift_int 3)*input_poly(poly_cbd1_spec w.`kg_fbuf) /\
 input_poly(keygen_g_pre_ntt_spec w.`kg_gbuf)=
   polyC(lift_int 3)*input_poly(poly_cbd1_spec w.`kg_gbuf).
proof. by rewrite keygen_f_input_poly_shape keygen_g_input_poly_shape. qed.

lemma pke_cipher_represents pk m r H :
 encap_key_canonical pk => pke_domain m => pke_domain r =>
 terminal_represents (decoded_poly pk) H =>
 terminal_represents (pke_cipher pk m r) (H*input_poly r+input_poly m).
proof.
 move=>hk hm hr hH.
 apply(poly_basemul_add_qring_represents_product_plus
   (decoded_poly pk) (pke_rhat r) (pke_mhat m) (pke_cipher pk m r) H (input_poly r) (input_poly m)).
 + exact hH.
 + rewrite /pke_rhat ntt_specE; exact(forward_ntt_spec_terminal_represents r (pke_domain_qrange r hr)).
 + rewrite /pke_mhat ntt_specE; exact(forward_ntt_spec_terminal_represents m (pke_domain_qrange m hm)).
 + exact(pke_cipher_qring pk m r hk hm hr).
qed.
lemma pke_serialized_cipher_represents pk m r H :
 encap_key_canonical pk => pke_domain m => pke_domain r =>
 terminal_represents (decoded_poly pk) H =>
 terminal_represents (decoded_poly(pke_ciphertext pk m r)) (H*input_poly r+input_poly m).
proof.
 move=>hk hm hr hH; apply(terminal_represents_mod_q_replacement (pke_cipher pk m r)).
 + rewrite /pke_ciphertext.
   exact(r2_serialized_decode_mod_q (pke_cipher pk m r) (pke_cipher_serializer pk m r hk hm hr)).
 + exact(pke_cipher_represents pk m r H hk hm hr hH).
qed.

lemma pke_no_wrap_recovery w m r :
 pke_key_relation w => pke_domain m => pke_domain r =>
 sampled_m1_no_wrap w.`kg_fbuf w.`kg_gbuf r m =>
 pke_dec_spec (pke_ciphertext w.`kg_pk m r) (pke_secret_bytes w)=Some m.
proof.
 move=>hk hm hr hn.
 have hp:=pke_key_canonical w hk.
 have henc:=pke_cipher_qring w.`kg_pk m r hp hm hr.
 rewrite /pke_rhat /pke_mhat !ntt_specE in henc.
 have hkey:=hk; rewrite /pke_key_relation in hkey.
 have htrit:poly_cbd1_trit_output m by move:hm; rewrite /pke_domain.
 have hmsg:=payload_actual_prefix_recovery
   w.`kg_fbuf w.`kg_gbuf w.`kg_finv w.`kg_ginv w.`kg_h w.`kg_hinv
   w.`kg_pk w.`kg_sk r m (pke_cipher w.`kg_pk m r)
   hkey (pke_domain_qrange r hr) htrit henc hn.
 move:hmsg=> /= [he [hc _]].
 rewrite /complete_entry_accepts /decap_guard_accepts /decap_key_encoding_valid in he.
 move:he=>[hct [hf _]].
 rewrite /pke_dec_spec /pke_secret_bytes /pke_ciphertext hct hf /=.
 by move:hc; rewrite /message_candidate=>->.
qed.
lemma pke_no_wrap_correct w m r :
 pke_key_relation w => pke_domain m => pke_domain r =>
 sampled_m1_no_wrap w.`kg_fbuf w.`kg_gbuf r m =>
 pke_enc_spec w.`kg_pk m r=Some(pke_ciphertext w.`kg_pk m r) /\
 pke_dec_spec(pke_ciphertext w.`kg_pk m r)(pke_secret_bytes w)=Some m.
proof.
 move=>hk hm hr hn; split.
 + exact(pke_enc_accept _ _ _ (pke_key_canonical w hk)).
 + exact(pke_no_wrap_recovery w m r hk hm hr hn).
qed.

(* An independent quotient-ring Dec relation: select the unique centered
   integer representative, then the unique ternary residues modulo 3.
   Its definition contains no NTT, basemul, inverse NTT, or input message. *)
op [opaque] pke_ring_decodes (P:poly) (candidate:pke_poly) =
 exists (v:int Array768.t),
  (forall j,0<=j<768 => -1728<=v.[j]<=1728) /\
  eqm_global P (int_poly v) /\ message_mod3_witness v candidate.
op [opaque] pke_centered_coefficients (a:pke_poly) : int Array768.t =
 Array768.init(fun j=>centered_q_input(coeff a.[j])).

lemma pke_centered_coefficients_range a : input_qrange a =>
 forall j,0<=j<768 => -1728<=(pke_centered_coefficients a).[j]<=1728.
proof.
 move=>ha j hj; rewrite /pke_centered_coefficients Array768.initiE 1:hj.
 exact(centered_q_input_range (coeff a.[j]) (ha j hj)).
qed.
lemma pke_centered_poly a : input_qrange a =>
 input_poly a=int_poly(pke_centered_coefficients a).
proof.
 move=>ha; rewrite -integer_coefficients_poly /int_poly.
 apply NTRUPoly.BigPoly.PCA.eq_big_int=>j hj /=.
 rewrite integer_coefficients_get 1:hj.
 have he:lift_int(coeff a.[j])=lift_int((pke_centered_coefficients a).[j]).
 + apply lift_int_eq; rewrite /pke_centered_coefficients Array768.initiE 1:hj.
   apply/eq_sym; exact(centered_q_input_congr (coeff a.[j]) (ha j hj)).
 by rewrite he.
qed.
lemma pke_crepmod3_ring_decodes P a :
 eqm_global P (input_poly a) => input_qrange a =>
 pke_ring_decodes P (poly_crepmod3_spec a).
proof.
 move=>hP ha; rewrite /pke_ring_decodes; exists(pke_centered_coefficients a).
 split; first exact(pke_centered_coefficients_range a ha).
 split; first by rewrite -(pke_centered_poly a ha).
 rewrite /message_mod3_witness=>j hj.
 have [ht hc]:=poly_crepmod3_spec_algebra a ha j hj.
 split; first exact ht.
 rewrite /pke_centered_coefficients Array768.initiE 1:hj; apply/eq_sym; exact hc.
qed.
lemma pke_ring_decodes_unique P a b :
 pke_ring_decodes P a => pke_ring_decodes P b => a=b.
proof.
 move=>hA hB.
 rewrite /pke_ring_decodes in hA.
 rewrite /pke_ring_decodes in hB.
 move:hA hB=>[va [hva [ha hma]]] [vb [hvb [hb hmb]]].
 have hab:=eqm_global_trans _ _ _ (eqm_global_sym _ _ ha) hb.
 have hv:va=vb.
 + apply Array768.tP=>j hj.
   exact(centered_representative_unique va.[j] vb.[j] (hva j hj) (hvb j hj)
     (eqm_global_int_poly_coeff va vb j hab hj)).
 subst vb.
 apply Array768.tP=>j hj.
 have [hat ham]:=hma j hj; have [hbt hbm]:=hmb j hj.
 have he:coeff a.[j]=coeff b.[j].
 + apply(trit_mod3_unique _ _ hat hbt); by rewrite -ham -hbm.
 by rewrite (word_from_coeff a.[j]) (word_from_coeff b.[j]) he.
qed.

lemma pke_candidate_ring_decodes ct fbytes C F :
 terminal_represents (decoded_poly ct) C =>
 terminal_represents (decoded_poly fbytes) F =>
 pke_ring_decodes (C*F) (decap_candidate_spec(decoded_poly ct)(decoded_poly fbytes)).
proof.
 move=>hc hf.
 have [hp _]:=candidate_decoded_spec_algebra ct fbytes.
 have ht:=poly_basemul_qring_represents_product _ _ _ C F hc hf hp.
 have [_ hs]:=poly_basemul_qring_implies_invntt_ready _ _ _ hp.
 have hsem:=inverse_invntt_spec_semantics (C*F) _ ht hs.
 have hr:=inverse_invntt_spec_ntt_input_qrange _ hs.
 rewrite /decap_candidate_spec invntt_specE.
 exact(pke_crepmod3_ring_decodes (C*F) _ hsem hr).
qed.
lemma pke_dec_ring_semantics ct fbytes C F :
 encap_key_canonical ct => encap_key_canonical fbytes =>
 terminal_represents (decoded_poly ct) C =>
 terminal_represents (decoded_poly fbytes) F =>
 exists candidate,pke_dec_spec ct fbytes=Some candidate /\ pke_ring_decodes (C*F) candidate.
proof.
 move=>hct hfb hc hf.
 exists(decap_candidate_spec(decoded_poly ct)(decoded_poly fbytes)); split.
 + exact(pke_dec_accept ct fbytes hct hfb).
 + exact(pke_candidate_ring_decodes ct fbytes C F hc hf).
qed.

(* This closed identity for generated keys needs no assumed public-key
   representative H and no no-wrap premise. No-wrap is used only later
   to identify the result of centered mod-3 reduction with the message. *)
lemma pke_valid_key_cf_semantics w m r :
 pke_key_relation w => pke_domain m => pke_domain r =>
 invntt_semantics
  (input_poly(keygen_g_pre_ntt_spec w.`kg_gbuf)*input_poly r +
   input_poly m*input_poly(keygen_f_pre_ntt_spec w.`kg_fbuf))
  (inverse_invntt_spec(candidate_product_spec
    (decoded_poly(pke_ciphertext w.`kg_pk m r))(decoded_poly(pke_secret_bytes w)))).
proof.
 move=>hk hm hr; rewrite /pke_ciphertext /pke_secret_bytes.
 have hp:=pke_key_canonical w hk.
 have hkey:=hk; rewrite /pke_key_relation in hkey.
 have hser:=payload_secret_relation _ _ _ _ _ _ _ _ hkey.
 have henc:=pke_cipher_qring w.`kg_pk m r hp hm hr.
 rewrite /pke_rhat /pke_mhat !ntt_specE in henc.
 have [hprod _]:=candidate_decoded_spec_algebra
   (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec (pke_cipher w.`kg_pk m r))(decap_fbytes (complete_sk_poly w.`kg_sk)).
 have htransfer:=decoded_cipher_product_transfer
   (pke_cipher w.`kg_pk m r) (decoded_poly(decap_fbytes (complete_sk_poly w.`kg_sk)))
   (candidate_product_spec (decoded_poly(NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec (pke_cipher w.`kg_pk m r)))
    (decoded_poly(decap_fbytes (complete_sk_poly w.`kg_sk))))
   (pke_cipher_serializer w.`kg_pk m r hp hm hr) hprod.
 have hg:=forward_ntt_spec_terminal_represents (keygen_g_pre_ntt_spec w.`kg_gbuf)
   (keygen_g_pre_ntt_input_qrange w.`kg_gbuf).
 have hrr:=forward_ntt_spec_terminal_represents r (pke_domain_qrange r hr).
 have hmm:=forward_ntt_spec_terminal_represents m (pke_domain_qrange m hm).
 exact(keygen_secret_f_valid_key_m1_spec_semantics
   (keygen_f_ntt_spec w.`kg_fbuf) w.`kg_finv
   (keygen_g_ntt_spec w.`kg_gbuf) w.`kg_ginv w.`kg_h w.`kg_hinv
   (decoded_poly w.`kg_pk) (decoded_poly(decap_fbytes (complete_sk_poly w.`kg_sk)))
   (forward_ntt_spec r) (forward_ntt_spec m) (pke_cipher w.`kg_pk m r)
   (candidate_product_spec (decoded_poly(NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec (pke_cipher w.`kg_pk m r)))
    (decoded_poly(decap_fbytes (complete_sk_poly w.`kg_sk))))
   w.`kg_pk (decap_fbytes (complete_sk_poly w.`kg_sk))
   (input_poly(keygen_f_pre_ntt_spec w.`kg_fbuf))
   (input_poly(keygen_g_pre_ntt_spec w.`kg_gbuf)) (input_poly r) (input_poly m)
   hser hg hrr hmm henc htransfer).
qed.
lemma pke_valid_key_cf_shape w m r :
 pke_key_relation w => pke_domain m => pke_domain r =>
 pke_ring_decodes
  ((polyC(lift_int 3)*input_poly(poly_cbd1_spec w.`kg_gbuf))*input_poly r +
   input_poly m*(poly1+polyC(lift_int 3)*input_poly(poly_cbd1_spec w.`kg_fbuf)))
  (decap_candidate_spec(decoded_poly(pke_ciphertext w.`kg_pk m r))
    (decoded_poly(pke_secret_bytes w))).
proof.
 move=>hk hm hr.
 have hs:=pke_valid_key_cf_semantics w m r hk hm hr.
 rewrite keygen_g_input_poly_shape keygen_f_input_poly_shape in hs.
 have [hp _]:=candidate_decoded_spec_algebra
   (pke_ciphertext w.`kg_pk m r)(pke_secret_bytes w).
 have [_ hshape]:=poly_basemul_qring_implies_invntt_ready _ _ _ hp.
 have hrange:=inverse_invntt_spec_ntt_input_qrange _ hshape.
 rewrite /decap_candidate_spec invntt_specE.
 exact(pke_crepmod3_ring_decodes _ _ hs hrange).
qed.
