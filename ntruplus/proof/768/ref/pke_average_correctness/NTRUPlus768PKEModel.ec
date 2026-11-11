require import AllCore Distr FMap.
from Jasmin require import JWord.
require import Array192 Array768 Array1152 Array2336.
require import NTRUPlus768PolyCBD1Algebra NTRUPlus768NTTProof.
require import NTRUPlus768DecapCandidateSpec NTRUPlus768CanonicalDecoder.
require import NTRUPlus768EncapPolyBasemulAddAlgebra NTRUPlus768PolyToBytesAlgebra.
require import NTRUPlus768EncapGuardSpec NTRUPlus768DecapGuardSpec NTRUPlus768DecapCompleteSpec.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768KEMPayloadSpec NTRUPlus768ROMKeygen.

(* Figure 18 messages and randomness are ternary coefficient polynomials.
   Packed keys/ciphertexts remain the actual 1152-byte NTT representation. *)
type pke_poly = W16.t Array768.t.
op [opaque] pke_domain (p:pke_poly) = poly_cbd1_trit_output p.
op [opaque] pke_rhat (r:pke_poly) = ntt_spec r.
op [opaque] pke_mhat (m:pke_poly) = ntt_spec m.
op [opaque] pke_product (pk:W8.t Array1152.t) (r:pke_poly) =
 candidate_product_spec (decoded_poly pk) (pke_rhat r).
op [opaque] pke_cipher (pk:W8.t Array1152.t) (m r:pke_poly) =
 poly_centered_add_spec (pke_product pk r) (pke_mhat m).
op [opaque] pke_ciphertext (pk:W8.t Array1152.t) (m r:pke_poly) =
 NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec (pke_cipher pk m r).
op [opaque] pke_enc_spec (pk:W8.t Array1152.t) (m r:pke_poly) : W8.t Array1152.t option =
 if encap_key_canonical pk then Some(pke_ciphertext pk m r) else None.

(* The PKE secret is f's serialized transform, without the KEM inverse-h
   block or HashF suffix. Decryption computes its own candidate from c*f;
   the original message is not an argument. SOTP/FO checks are separate. *)
op [opaque] pke_secret_bytes (w:keygen_witness) =
 decap_fbytes (complete_sk_poly w.`kg_sk).
op [opaque] pke_dec_spec (ct fbytes:W8.t Array1152.t) : pke_poly option =
 if encap_key_canonical ct /\ encap_key_canonical fbytes then
   Some(decap_candidate_spec (decoded_poly ct) (decoded_poly fbytes))
 else None.
op [opaque] pke_key_relation (w:keygen_witness) =
 payload_key_relation w.`kg_fbuf w.`kg_gbuf w.`kg_finv w.`kg_ginv
   w.`kg_h w.`kg_hinv w.`kg_pk w.`kg_sk.

(* Fold each actual value contract at its caller boundary before reducing
   later expressions; this keeps the full 768-coefficient definitions opaque. *)
lemma pke_rhatE r : ntt_spec r=pke_rhat r.
proof. by rewrite /pke_rhat. qed.
lemma pke_mhatE m : ntt_spec m=pke_mhat m.
proof. by rewrite /pke_mhat. qed.
lemma pke_productE pk r :
 candidate_product_spec(decoded_poly pk)(pke_rhat r)=pke_product pk r.
proof. by rewrite /pke_product. qed.
lemma pke_cipherE pk m r :
 poly_centered_add_spec(pke_product pk r)(pke_mhat m)=pke_cipher pk m r.
proof. by rewrite /pke_cipher. qed.
lemma pke_ciphertextE pk m r :
 NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec(pke_cipher pk m r)=pke_ciphertext pk m r.
proof. by rewrite /pke_ciphertext. qed.

lemma pke_domain_cbd buf : pke_domain(poly_cbd1_spec buf).
proof. rewrite /pke_domain; exact(poly_cbd1_spec_trit_output buf). qed.
lemma pke_key_from_rom w fm : rom_key_relation w fm => pke_key_relation w.
proof. by rewrite /rom_key_relation /pke_key_relation; smt(). qed.
lemma pke_enc_accept pk m r : encap_key_canonical pk =>
 pke_enc_spec pk m r=Some(pke_ciphertext pk m r).
proof. by move=>h; rewrite /pke_enc_spec h. qed.
lemma pke_enc_reject pk m r : !encap_key_canonical pk => pke_enc_spec pk m r=None.
proof. by move=>h; rewrite /pke_enc_spec h. qed.
lemma pke_dec_accept ct fbytes :
 encap_key_canonical ct => encap_key_canonical fbytes =>
 pke_dec_spec ct fbytes=Some(decap_candidate_spec(decoded_poly ct)(decoded_poly fbytes)).
proof. by move=>hc hf; rewrite /pke_dec_spec hc hf. qed.
lemma pke_dec_reject_cipher ct fbytes : !encap_key_canonical ct => pke_dec_spec ct fbytes=None.
proof. by move=>hc; rewrite /pke_dec_spec hc. qed.
lemma pke_dec_reject_secret ct fbytes : !encap_key_canonical fbytes => pke_dec_spec ct fbytes=None.
proof. by move=>hf; rewrite /pke_dec_spec hf; smt(). qed.
lemma pke_dec_none ct fbytes :
 pke_dec_spec ct fbytes=None <=> !(encap_key_canonical ct /\ encap_key_canonical fbytes).
proof. rewrite /pke_dec_spec; case(encap_key_canonical ct /\ encap_key_canonical fbytes); smt(). qed.
