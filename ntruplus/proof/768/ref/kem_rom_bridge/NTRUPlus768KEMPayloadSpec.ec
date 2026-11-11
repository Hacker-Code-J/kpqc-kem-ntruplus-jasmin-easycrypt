require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.
require import Array2336 Array2304 Array1152 Array32 Array96 Array192 Array224 Array768.
require import NTRUPlus768EncapCompleteAlgebra NTRUPlus768PolyCenteredAddCorrectness.
require import NTRUPlus768NTTStage1Algebra NTRUPlus768NTTRadix2_4Algebra.
require import NTRUPlus768PolyCBD1Algebra NTRUPlus768PolySOTPEncodeAlgebra NTRUPlus768ValidKeyM1Recovery.
require import NTRUPlus768PolyCenteredAddCorrectness NTRUPlus768EncapPolyBasemulAddAlgebra.
require import NTRUPlus768ValidKeyR2Recovery NTRUPlus768R2Serialization.
require import NTRUPlus768KeygenSecretFBridge NTRUPlus768KeygenPublicKeyBridge.
require import NTRUPlus768KeygenSamplerBridge NTRUPlus768KeygenHBridge.
require import NTRUPlus768EvaluationSemantics NTRUPlus768ForwardNTTStage1Semantics NTRUPlus768TerminalRepresentation.
require import NTRUPlus768DecapCompleteSpec NTRUPlus768DecapMessageAlgebra.
require import NTRUPlus768DecapCandidateSpec NTRUPlus768DecapCandidateAlgebra.
require import NTRUPlus768DecapR2CompSpec NTRUPlus768DecapR2CompAlgebra.
require import NTRUPlus768DecapGuardSpec NTRUPlus768EncapGuardSpec NTRUPlus768CanonicalDecoder.
require import NTRUPlus768PolyToBytesAlgebra NTRUPlus768PolyFromBytesAlgebra.
require import NTRUPlus768Crepmod3DecapBridge NTRUPlus768InvNTTAlgebra.
require import NTRUPlus768DecapR2Bridge NTRUPlus768PolySubDecapBridge.
require import NTRUPlus768PolyBasemulAlgebra NTRUPlus768BasemulAlgebra.
require import NTRUPlus768KeygenSamplerAlgebra NTRUPlus768NTTAlgebra NTRUPlus768NTTProof NTRUPlus768InvNTTProof.

(* Hash-free successful sampled-key arithmetic and byte layout are explicit premises.
   There is no assumption here that decapsulation succeeds or recovers a
   message. Canonical entry encodings are derived from these premises. *)
op [opaque] payload_key_relation
    (fbuf gbuf : W8.t Array192.t) (finv ginv h hinv : W16.t Array768.t)
    (pk : W8.t Array1152.t) (sk : W8.t Array2336.t) : bool =
  keygen_keypair_ntt_relation (keygen_f_ntt_spec fbuf) finv
    (keygen_g_ntt_spec gbuf) ginv h hinv /\
  pk = keygen_public_key_bytes h /\
  decap_fbytes (complete_sk_poly sk) = keygen_secret_f_bytes (keygen_f_ntt_spec fbuf) /\
  decap_hbytes (complete_sk_poly sk) = NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec hinv /\
  true.

lemma payload_serialized_canonical p :
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange p =>
  encap_key_canonical (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec p).
proof.
  move=> hp j hj.
  have hs := r2_serialized_decode_coeff_range p j hp hj.
  have hu := NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec_coeff_range
    (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec p) j hj.
  have he := NTRUPlus768PolyFromBytesAlgebra.coeff_uint_small
    (r2_serialized_decode p).[j] _; first smt().
  move: hs; rewrite /coeff he /q; smt().
qed.

lemma payload_raw_key_canonical f finv g ginv h hinv pk sk :
 keygen_keypair_ntt_relation f finv g ginv h hinv =>
 pk=keygen_public_key_bytes h =>
 decap_fbytes(complete_sk_poly sk)=keygen_secret_f_bytes f =>
 decap_hbytes(complete_sk_poly sk)=NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec hinv =>
 encap_key_canonical pk /\
 decap_key_encoding_valid (decap_fbytes(complete_sk_poly sk)) (decap_hbytes(complete_sk_poly sk)).
proof.
 move=> hk hp hf hh.
 have hfr := keygen_secret_f_tobytes_input_qrange f (keygen_secret_f_qrange f finv g ginv h hinv hk).
 have hhr := keygen_public_h_tobytes_input_qrange f finv g ginv h hinv hk.
 have hir := keygen_hinv_tobytes_input_qrange f finv g ginv h hinv hk.
 split.
 + rewrite hp /keygen_public_key_bytes; exact(payload_serialized_canonical h hhr).
 rewrite /decap_key_encoding_valid; split.
 + rewrite hf /keygen_secret_f_bytes; exact(payload_serialized_canonical f hfr).
 rewrite hh; exact(payload_serialized_canonical hinv hir).
qed.
lemma payload_key_canonical fbuf gbuf finv ginv h hinv pk sk :
  payload_key_relation fbuf gbuf finv ginv h hinv pk sk =>
  encap_key_canonical pk /\
  decap_key_encoding_valid (decap_fbytes (complete_sk_poly sk))
    (decap_hbytes (complete_sk_poly sk)).
proof.
 rewrite /payload_key_relation; move=> [hk [hp [hf [hh _]]]].
 move: hk hf.
 move: (keygen_f_ntt_spec fbuf) (keygen_g_ntt_spec gbuf) => f g hk hf.
 exact(payload_raw_key_canonical f finv g ginv h hinv pk sk hk hp hf hh).
qed.

lemma payload_raw_secret_relation (f finv g ginv h hinv:W16.t Array768.t)
    (F:poly) (pk sk_f:W8.t Array1152.t) :
 keygen_keypair_ntt_relation f finv g ginv h hinv => terminal_represents f F =>
 pk=keygen_public_key_bytes h => sk_f=keygen_secret_f_bytes f =>
 keygen_secret_f_serialization_relation f finv g ginv h hinv
   (decoded_poly pk) (decoded_poly sk_f) pk sk_f F.
proof.
 move=> hk ht hp hf.
 have H := keygen_secret_f_serialization_relation_intro f finv g ginv h hinv F hk ht.
 rewrite /keygen_decoded_public_key /keygen_decoded_secret_f -hp -hf in H.
 exact H.
qed.

lemma payload_secret_relation fbuf gbuf finv ginv h hinv pk sk :
  payload_key_relation fbuf gbuf finv ginv h hinv pk sk =>
  keygen_secret_f_serialization_relation
    (keygen_f_ntt_spec fbuf) finv (keygen_g_ntt_spec gbuf) ginv h hinv
    (decoded_poly pk) (decoded_poly (decap_fbytes (complete_sk_poly sk)))
    pk (decap_fbytes (complete_sk_poly sk)) (input_poly (keygen_f_pre_ntt_spec fbuf)).
proof.
 rewrite /payload_key_relation; move=> [hk [hp [hf _]]].
 have Hterm := keygen_sampled_secret_f_terminal_represents fbuf.
 move: hk hf Hterm.
 move: (keygen_f_ntt_spec fbuf) (keygen_g_ntt_spec gbuf)
   (input_poly(keygen_f_pre_ntt_spec fbuf)) => f g F hk hf Hterm.
 exact(payload_raw_secret_relation f finv g ginv h hinv F pk
   (decap_fbytes(complete_sk_poly sk)) hk Hterm hp hf).
qed.

lemma payload_entry_accepts fbuf gbuf finv ginv h hinv pk sk c :
  payload_key_relation fbuf gbuf finv ginv h hinv pk sk =>
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange c =>
  complete_entry_accepts (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c) sk.
proof.
  move=> hk hc.
  have [_ hs] := payload_key_canonical fbuf gbuf finv ginv h hinv pk sk hk.
  rewrite /complete_entry_accepts /decap_guard_accepts.
  split; last exact hs.
  exact (payload_serialized_canonical c hc).
qed.

lemma payload_candidate_value ct sk :
  message_candidate ct sk = inverse_invntt_crepmod3_spec
    (candidate_product_spec (decoded_poly ct) (decoded_poly (decap_fbytes sk))).
proof.
  by rewrite /message_candidate /decap_candidate_spec
    /inverse_invntt_crepmod3_spec invntt_specE.
qed.

lemma payload_difference_value ct sk :
  r2_difference_spec (decoded_poly ct) (message_candidate ct sk) =
  decap_sub_spec (decoded_poly ct)
    (candidate_product_spec (decoded_poly ct) (decoded_poly (decap_fbytes sk))).
proof.
  by rewrite /r2_difference_spec /decap_sub_spec payload_candidate_value ntt_specE.
qed.

lemma payload_hinv_encoding fbuf gbuf finv ginv h hinv pk sk :
  payload_key_relation fbuf gbuf finv ginv h hinv pk sk =>
  decap_hbytes (complete_sk_poly sk) = NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec hinv.
proof.
  move=> hrel; rewrite /payload_key_relation in hrel.
  have [_ [_ [_ [hbytes _]]]] := hrel.
  exact hbytes.
qed.


(* Payload operations name the arrays actually returned by HashH and HashG.
   They do not idealize either hash by a fixed SHAKE function. *)
op [opaque] payload_r (hout:W8.t Array224.t) = poly_cbd1_spec (complete_hash_tail hout).
op [opaque] payload_rhat (hout:W8.t Array224.t) = ntt_spec (payload_r hout).
op [opaque] payload_serialized (hout:W8.t Array224.t) =
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec (payload_rhat hout).
op [opaque] payload_m (coins:W8.t Array96.t) (pad:W8.t Array192.t) = poly_sotp_encode_spec coins pad.
op [opaque] payload_mhat (coins:W8.t Array96.t) (pad:W8.t Array192.t) = ntt_spec (payload_m coins pad).
op [opaque] payload_product (pk:W8.t Array1152.t) (hout:W8.t Array224.t) =
  candidate_product_spec (decoded_poly pk) (payload_rhat hout).
op [opaque] payload_cipher (pk:W8.t Array1152.t) (coins:W8.t Array96.t)
    (hout:W8.t Array224.t) (pad:W8.t Array192.t) =
  poly_centered_add_spec (payload_product pk hout) (payload_mhat coins pad).
op [opaque] payload_shared_key (hout:W8.t Array224.t) = Array32.init (fun i => hout.[i]).

lemma payload_rE hout : poly_cbd1_spec(complete_hash_tail hout)=payload_r hout.
proof. by rewrite /payload_r. qed.
lemma payload_rhatE hout : ntt_spec(payload_r hout)=payload_rhat hout.
proof. by rewrite /payload_rhat. qed.
lemma payload_serializedE hout : NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec(payload_rhat hout)=payload_serialized hout.
proof. by rewrite /payload_serialized. qed.
lemma payload_mE coins pad : poly_sotp_encode_spec coins pad=payload_m coins pad.
proof. by rewrite /payload_m. qed.
lemma payload_mhatE coins pad : ntt_spec(payload_m coins pad)=payload_mhat coins pad.
proof. by rewrite /payload_mhat. qed.
lemma payload_productE pk hout : candidate_product_spec(decoded_poly pk)(payload_rhat hout)=payload_product pk hout.
proof. by rewrite /payload_product. qed.
lemma payload_cipherE pk coins hout pad : poly_centered_add_spec(payload_product pk hout)(payload_mhat coins pad)=payload_cipher pk coins hout pad.
proof. by rewrite /payload_cipher. qed.
lemma payload_shared_keyE hout : Array32.init(fun i=>hout.[i])=payload_shared_key hout.
proof. by rewrite /payload_shared_key. qed.

lemma payload_r_range hout : input_qrange (payload_r hout).
proof. rewrite /payload_r; exact (poly_cbd1_spec_input_qrange _). qed.
lemma payload_rhat_range hout : input_qrange (payload_rhat hout).
proof.
  rewrite /payload_rhat ntt_specE; move=> j hj.
  exact (forward_ntt_centered_coeff_range _ j (payload_r_range hout) hj).
qed.
lemma payload_m_trit coins pad : poly_cbd1_trit_output (payload_m coins pad).
proof. rewrite /payload_m /poly_sotp_encode_spec; exact (poly_cbd1_spec_trit_output _). qed.
lemma payload_m_range coins pad : input_qrange (payload_m coins pad).
proof. exact (trit_polynomial_input_qrange _ (payload_m_trit coins pad)). qed.
lemma payload_mhat_centered coins pad : centered_input_shape (payload_mhat coins pad).
proof.
  rewrite /payload_mhat ntt_specE.
  exact (forward_ntt_centered_output_shape _ (payload_m_range coins pad)).
qed.
lemma payload_product_qring pk hout : encap_key_canonical pk =>
  poly_basemul_qring (decoded_poly pk) (payload_rhat hout) (payload_product pk hout) 192.
proof.
  move=> hk; rewrite /payload_product; apply poly_basemul_word_to_qring.
  + apply encap_pointwise_blocks; exact (candidate_canonical_decoder_qrange pk hk).
  + apply encap_pointwise_blocks; exact (payload_rhat_range hout).
  exact (candidate_product_word _ _).
qed.
lemma payload_product_range pk hout : encap_key_canonical pk => in_qrange768 (payload_product pk hout).
proof.
  move=> hk; exact (poly_basemul_qring_product_in_qrange768 _ _ _ (payload_product_qring pk hout hk)).
qed.
lemma payload_cipher_qring pk coins hout pad : encap_key_canonical pk =>
  poly_basemul_add_qring (decoded_poly pk) (payload_rhat hout) (payload_mhat coins pad)
    (payload_cipher pk coins hout pad) 192.
proof.
  move=> hk; rewrite /payload_cipher.
  exact (poly_basemul_add_spec_qring _ _ _ _
    (payload_product_qring pk hout hk) (payload_mhat_centered coins pad)).
qed.
lemma payload_cipher_serializer pk coins hout pad : encap_key_canonical pk =>
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange (payload_cipher pk coins hout pad).
proof.
  move=> hk; exact (encap_cipher_tobytes_input_qrange _ _ _ _ (payload_cipher_qring pk coins hout pad hk)).
qed.
