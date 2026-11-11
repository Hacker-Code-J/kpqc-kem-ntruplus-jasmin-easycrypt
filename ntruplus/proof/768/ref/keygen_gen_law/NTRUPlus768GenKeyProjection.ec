require import AllCore Ring.
from Jasmin require import JWord.
require import Array192 Array768 Array1152 Array2336.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteProof.
require import NTRUPlus768KeygenCompleteInverse NTRUPlus768KeygenHBridge NTRUPlus768KeygenInverseBridge.
require import NTRUPlus768KeygenSamplerAlgebra NTRUPlus768KeygenSamplerBridge.
require import NTRUPlus768KeygenSecretFBridge NTRUPlus768KeygenPublicKeyBridge.
require import NTRUPlus768PKEModel NTRUPlus768PKEAlgebra NTRUPlus768PKEKeyDistribution.
require import NTRUPlus768KEMPayloadSpec NTRUPlus768CanonicalDecoder NTRUPlus768DecapCompleteSpec.
require import NTRUPlus768DecapGuardSpec NTRUPlus768DecapCandidateAlgebra NTRUPlus768DecapCandidateSpec.
require import NTRUPlus768ValidKeyR2Recovery.
require import NTRUPlus768PolyBasemulAlgebra NTRUPlus768PolyBaseInvBridge.
require import NTRUPlus768PolyBasemulInvNTTAlgebra NTRUPlus768InvNTTRadix2_4Algebra.
require import NTRUPlus768InvNTTAlgebra NTRUPlus768InverseNTTSemantics.
require import NTRUPlus768ForwardNTTSemantics NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768CyclotomicFactorization NTRUPlus768EvaluationSemantics.
require import NTRUPlus768TerminalRepresentation NTRUPlus768CoefficientRecovery.
require import NTRUPlus768RRecTransform NTRUPlus768RRecAlgebra NTRUPlus768RRecInverseAlgebra NTRUPlus768RRecPublicInverse.
require import NTRUPlus768KeygenTerminalUnit NTRUPlus768KeygenGlobalUnit NTRUPlus768GenModel.
abbrev ( * ) = NTRUPoly.PolyComRing.( * ).

(* The core observation is read from the returned byte arrays, not from
   unreturned sampler buffers. Witness fields enter only the proved bridge. *)
op [opaque] gen_inverse_poly (a:W16.t Array768.t) = input_poly(inverse_invntt_spec a).
op [opaque] gen_serialized_core (pk:W8.t Array1152.t) (sk:W8.t Array2336.t) =
 (gen_inverse_poly(decoded_poly pk),
  gen_inverse_poly(decoded_poly(decap_fbytes(complete_sk_poly sk)))).
op [opaque] gen_actual_core (w:keygen_witness) = gen_serialized_core w.`kg_pk w.`kg_sk.

lemma gen_actual_coreE w : gen_actual_core w=
 (gen_inverse_poly(decoded_poly w.`kg_pk),gen_inverse_poly(decoded_poly(pke_secret_bytes w))).
proof. by rewrite /gen_actual_core /gen_serialized_core /pke_secret_bytes. qed.

lemma gen_input_poly_degree a : NTRUPoly.deg(input_poly a)<=768.
proof. rewrite -int_poly_words; exact(int_poly_degree _). qed.
lemma gen_inverse_poly_degree a : NTRUPoly.deg(gen_inverse_poly a)<=768.
proof. rewrite /gen_inverse_poly; exact(gen_input_poly_degree _). qed.
lemma gen_inverse_poly_represents a : qrange_input_shape a =>
 terminal_represents a (gen_inverse_poly a).
proof. rewrite /gen_inverse_poly; exact(rrec_terminal_inverse_represents a). qed.

lemma gen_inverse_poly_recovers a p :
 qrange_input_shape a =>terminal_represents a p =>NTRUPoly.deg p<=768 =>
 gen_inverse_poly a=p.
proof.
 move=>ha hp hd.
 have he:=inverse_invntt_spec_semantics p a hp ha.
 apply(eqm_global_low_degree_unique _ _ (gen_inverse_poly_degree a) hd).
 rewrite /gen_inverse_poly.
 apply eqm_global_sym; exact he.
qed.

lemma gen_inverse_poly_mod a b :
 qrange_input_shape a =>qrange_input_shape b =>poly_coeff_eq_mod_q a b =>
 gen_inverse_poly a=gen_inverse_poly b.
proof.
 move=>ha hb he; apply(gen_inverse_poly_recovers a _ ha).
 + exact(terminal_represents_mod_q_replacement b a _ he (gen_inverse_poly_represents b hb)).
 exact(gen_inverse_poly_degree b).
qed.

lemma gen_public_product_relation fb gb finv h :
 poly_baseinv_success(keygen_f_ntt_spec fb)finv =>
 poly_basemul_qring(keygen_g_ntt_spec gb)finv h 192 =>
 gen_public_relation (input_poly(keygen_f_pre_ntt_spec fb))
   (pke_cbd_field gb) (gen_inverse_poly h).
proof.
 move=>hi hp.
 have hr:=poly_basemul_qring_output_in_qrange768 _ _ _ hp.
 have hshape:=in_qrange768_implies_invntt_input_shape h hr.
 have hh:=gen_inverse_poly_represents h hshape.
 have hf:=keygen_sampled_secret_f_terminal_represents fb.
 have hprod:=keygen_h_f_equals_g fb gb finv h hi hp.
 have hhf:=poly_basemul_qring_represents_product h (keygen_f_ntt_spec fb)
   (keygen_g_ntt_spec gb) _ _ hh hf hprod.
 have hg:terminal_represents(keygen_g_ntt_spec gb)(input_poly(keygen_g_pre_ntt_spec gb)).
 + rewrite /keygen_g_ntt_spec; exact(forward_ntt_spec_terminal_represents _ (keygen_g_pre_ntt_input_qrange gb)).
 have hgshape:=in_qrange768_implies_invntt_input_shape _ (keygen_g_ntt_qrange gb).
 have he:=gen_terminal_global_congr (keygen_g_ntt_spec gb) _ _ hgshape hhf hg.
 rewrite /gen_public_relation; split; first exact(gen_inverse_poly_degree h).
 rewrite pke_g_field_shape in he; exact he.
qed.

lemma gen_accepted_buffers_defined fb gb :
 keygen_f_accept fb =>keygen_g_accept gb =>
 gen_public_defined (input_poly(keygen_f_pre_ntt_spec fb)) (pke_cbd_field gb).
proof.
 move=>hf hg.
 have hs:keygen_inverse_status(keygen_f_ntt_spec fb)=W64.zero.
 + exact(iffRL _ _ (keygen_f_attempt_accept fb) hf).
 have hi:=rrec_raw_inverse_success _ (keygen_f_ntt_qrange fb) hs.
 have hir:=poly_baseinv_success_output_qrange _ _ hi.
 have hp:poly_basemul_qring (keygen_g_ntt_spec gb) (keygen_inverse_value(keygen_f_ntt_spec fb))
   (candidate_product_spec (keygen_g_ntt_spec gb) (keygen_inverse_value(keygen_f_ntt_spec fb))) 192.
 + exact(poly_basemul_word_to_qring _ _ _ (keygen_g_ntt_qrange gb) hir (candidate_product_word _ _)).
 apply(gen_public_defined_witness _ _
   (gen_inverse_poly(candidate_product_spec (keygen_g_ntt_spec gb) (keygen_inverse_value(keygen_f_ntt_spec fb))))).
 exact(gen_public_product_relation fb gb _ _ hi hp).
qed.

lemma gen_secret_relation_rep f finv g ginv h hinv dh df pk sf F :
 keygen_secret_f_serialization_relation f finv g ginv h hinv dh df pk sf F =>
 terminal_represents df F.
proof. rewrite /keygen_secret_f_serialization_relation; smt(). qed.

lemma gen_valid_key_secret_projection w : pke_key_relation w =>
 gen_inverse_poly(decoded_poly(pke_secret_bytes w))=input_poly(keygen_f_pre_ntt_spec w.`kg_fbuf).
proof.
 move=>hk.
 have hkey:=hk; rewrite /pke_key_relation in hkey.
 have hs:=payload_secret_relation _ _ _ _ _ _ _ _ hkey.
 have ht:=gen_secret_relation_rep _ _ _ _ _ _ _ _ _ _ _ hs.
 have hrep:terminal_represents(decoded_poly(pke_secret_bytes w))
   (input_poly(keygen_f_pre_ntt_spec w.`kg_fbuf)).
 + rewrite /pke_secret_bytes; exact ht.
 have hr:=rrec_public_key_range _ (pke_secret_canonical w hk).
 exact(gen_inverse_poly_recovers _ _ (in_qrange768_implies_invntt_input_shape _ hr)
   hrep (gen_input_poly_degree _)).
qed.

lemma gen_valid_key_public_projection w : pke_key_relation w =>
 gen_inverse_poly(decoded_poly w.`kg_pk)=gen_inverse_poly w.`kg_h.
proof.
 move=>hk.
 have hkey:=hk; rewrite /pke_key_relation in hkey.
 have hs:=payload_secret_relation _ _ _ _ _ _ _ _ hkey.
 have [hrel he]:=secret_f_relation_keypair_and_public_congruence _ _ _ _ _ _ _ _ _ _ _ hs.
 have hp:=rrec_public_key_range _ (pke_key_canonical w hk).
 have hh:=keygen_public_h_qrange _ _ _ _ _ _ hrel.
 exact(gen_inverse_poly_mod _ _ (in_qrange768_implies_invntt_input_shape _ hp)
   (in_qrange768_implies_invntt_input_shape _ hh) he).
qed.

lemma gen_valid_key_public_relation w : pke_key_relation w =>
 gen_public_relation (input_poly(keygen_f_pre_ntt_spec w.`kg_fbuf))
   (pke_cbd_field w.`kg_gbuf) (gen_inverse_poly(decoded_poly w.`kg_pk)).
proof.
 move=>hk; rewrite(gen_valid_key_public_projection w hk).
 have hrel:=pke_key_inverse_relation w hk.
 rewrite /keygen_keypair_ntt_relation in hrel.
 have [hf [_ [hp _]]]:=hrel.
 exact(gen_public_product_relation w.`kg_fbuf w.`kg_gbuf w.`kg_finv w.`kg_h hf hp).
qed.

lemma gen_valid_key_f_unit w : pke_key_relation w =>
 pke_rq_unit(input_poly(keygen_f_pre_ntt_spec w.`kg_fbuf)).
proof.
 move=>hk.
 have [hf _]:=pke_actual_inverse_predicates w hk.
 have hu:gen_terminal_unit(keygen_f_ntt_spec w.`kg_fbuf).
 + rewrite /gen_terminal_unit; exists w.`kg_finv.
   exact(poly_baseinv_success_product_identity _ _ hf).
 exact(gen_terminal_unit_implies_rq _ _
   (keygen_sampled_secret_f_terminal_represents w.`kg_fbuf) hu).
qed.

lemma gen_valid_key_defined w : pke_key_relation w =>
 gen_public_defined (input_poly(keygen_f_pre_ntt_spec w.`kg_fbuf)) (pke_cbd_field w.`kg_gbuf).
proof.
 move=>hk; exact(gen_public_defined_witness _ _ _ (gen_valid_key_public_relation w hk)).
qed.

lemma gen_valid_key_projection w : pke_key_relation w =>
 gen_actual_core w=gen_key_from_fg(input_poly(keygen_f_pre_ntt_spec w.`kg_fbuf),pke_cbd_field w.`kg_gbuf).
proof.
 move=>hk.
 rewrite(gen_key_from_fgE _ _ _ (gen_valid_key_f_unit w hk) (gen_valid_key_public_relation w hk)).
 rewrite gen_actual_coreE (gen_valid_key_secret_projection w hk).
 done.
qed.

lemma gen_valid_key_shape_projection w : pke_key_relation w =>
 gen_actual_core w=gen_key_from_fg(gen_shape_f(pke_cbd_field w.`kg_fbuf),pke_cbd_field w.`kg_gbuf).
proof.
 move=>hk; rewrite -(gen_shape_fE _) -pke_f_field_shape.
 exact(gen_valid_key_projection w hk).
qed.
