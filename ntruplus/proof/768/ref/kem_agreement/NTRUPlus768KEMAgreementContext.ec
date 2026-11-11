require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.
require import Array2336 Array2304 Array1152 Array32 Array96 Array192 Array768.
require import NTRUPlus768ValidKeyR2Recovery NTRUPlus768R2Serialization.
require import NTRUPlus768KeygenSecretFBridge NTRUPlus768KeygenPublicKeyBridge.
require import NTRUPlus768KeygenSamplerBridge NTRUPlus768KeygenHBridge.
require import NTRUPlus768EvaluationSemantics NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768DecapCompleteSpec NTRUPlus768DecapMessageAlgebra.
require import NTRUPlus768DecapCandidateSpec NTRUPlus768DecapCandidateAlgebra.
require import NTRUPlus768DecapR2CompSpec NTRUPlus768DecapR2CompAlgebra.
require import NTRUPlus768DecapGuardSpec NTRUPlus768EncapGuardSpec NTRUPlus768CanonicalDecoder.
require import NTRUPlus768PolyToBytesAlgebra NTRUPlus768PolyFromBytesAlgebra.
require import NTRUPlus768Crepmod3DecapBridge NTRUPlus768InvNTTAlgebra.
require import NTRUPlus768DecapR2Bridge NTRUPlus768PolySubDecapBridge.
require import NTRUPlus768PolyBasemulAlgebra NTRUPlus768BasemulAlgebra.
require import NTRUPlus768HashFProof.
require import NTRUPlus768KeygenSamplerAlgebra NTRUPlus768NTTAlgebra NTRUPlus768NTTProof NTRUPlus768InvNTTProof.

(* Successful sampled-key arithmetic and byte layout are explicit premises.
   There is no assumption here that decapsulation succeeds or recovers a
   message. Canonical entry encodings are derived from these premises. *)
op agreement_key_relation
    (fbuf gbuf : W8.t Array192.t) (finv ginv h hinv : W16.t Array768.t)
    (pk : W8.t Array1152.t) (sk : W8.t Array2336.t) : bool =
  keygen_keypair_ntt_relation (keygen_f_ntt_spec fbuf) finv
    (keygen_g_ntt_spec gbuf) ginv h hinv /\
  pk = keygen_public_key_bytes h /\
  decap_fbytes (complete_sk_poly sk) = keygen_secret_f_bytes (keygen_f_ntt_spec fbuf) /\
  decap_hbytes (complete_sk_poly sk) = NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec hinv /\
  complete_sk_suffix sk = hash_f_spec pk.

lemma agreement_serialized_canonical p :
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

lemma agreement_key_canonical fbuf gbuf finv ginv h hinv pk sk :
  agreement_key_relation fbuf gbuf finv ginv h hinv pk sk =>
  encap_key_canonical pk /\
  decap_key_encoding_valid (decap_fbytes (complete_sk_poly sk))
    (decap_hbytes (complete_sk_poly sk)).
proof.
  rewrite /agreement_key_relation /decap_key_encoding_valid.
  move=> [hk [hp [hf [hh hs]]]].
  split.
  + rewrite hp /keygen_public_key_bytes.
    exact (agreement_serialized_canonical h
      (keygen_public_h_tobytes_input_qrange _ _ _ _ _ _ hk)).
  split.
  + rewrite hf /keygen_secret_f_bytes.
    exact (agreement_serialized_canonical _ (keygen_sampled_secret_f_tobytes_input_qrange fbuf)).
  rewrite hh; exact (agreement_serialized_canonical hinv
    (keygen_hinv_tobytes_input_qrange _ _ _ _ _ _ hk)).
qed.

lemma agreement_secret_relation fbuf gbuf finv ginv h hinv pk sk :
  agreement_key_relation fbuf gbuf finv ginv h hinv pk sk =>
  keygen_secret_f_serialization_relation
    (keygen_f_ntt_spec fbuf) finv (keygen_g_ntt_spec gbuf) ginv h hinv
    (decoded_poly pk) (decoded_poly (decap_fbytes (complete_sk_poly sk)))
    pk (decap_fbytes (complete_sk_poly sk)) (input_poly (keygen_f_pre_ntt_spec fbuf)).
proof.
  rewrite /agreement_key_relation; move=> [hk [hp [hf _]]].
  rewrite hp hf.
  exact (keygen_sampled_secret_f_serialization_relation_intro fbuf gbuf finv ginv h hinv hk).
qed.

lemma agreement_entry_accepts fbuf gbuf finv ginv h hinv pk sk c :
  agreement_key_relation fbuf gbuf finv ginv h hinv pk sk =>
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange c =>
  complete_entry_accepts (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c) sk.
proof.
  move=> hk hc.
  have [_ hs] := agreement_key_canonical fbuf gbuf finv ginv h hinv pk sk hk.
  rewrite /complete_entry_accepts /decap_guard_accepts.
  split; last exact hs.
  exact (agreement_serialized_canonical c hc).
qed.

lemma agreement_candidate_value ct sk :
  message_candidate ct sk = inverse_invntt_crepmod3_spec
    (candidate_product_spec (decoded_poly ct) (decoded_poly (decap_fbytes sk))).
proof.
  by rewrite /message_candidate /decap_candidate_spec
    /inverse_invntt_crepmod3_spec invntt_specE.
qed.

lemma agreement_difference_value ct sk :
  r2_difference_spec (decoded_poly ct) (message_candidate ct sk) =
  decap_sub_spec (decoded_poly ct)
    (candidate_product_spec (decoded_poly ct) (decoded_poly (decap_fbytes sk))).
proof.
  by rewrite /r2_difference_spec /decap_sub_spec agreement_candidate_value ntt_specE.
qed.

lemma agreement_hinv_encoding fbuf gbuf finv ginv h hinv pk sk :
  agreement_key_relation fbuf gbuf finv ginv h hinv pk sk =>
  decap_hbytes (complete_sk_poly sk) = NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec hinv.
proof.
  move=> hrel.
  have [_ [_ [_ [hbytes _]]]] := hrel.
  exact hbytes.
qed.

(* Arithmetic premises for the ciphertext are supplied by the actual Encaps
   specification in the next theory; both Decaps product premises are derived
   here from the exact guarded candidate/r2 calculations. *)
lemma agreement_recover_message fbuf gbuf finv ginv h hinv pk sk r c msg :
  agreement_key_relation fbuf gbuf finv ginv h hinv pk sk =>
  NTRUPlus768NTTStage1Algebra.input_qrange r =>
  NTRUPlus768EncapPolyBasemulAddAlgebra.poly_basemul_add_qring
    (decoded_poly pk) (forward_ntt_spec r)
    (forward_ntt_spec (r2_encap_message r msg)) c 192 =>
  NTRUPlus768ValidKeyM1Recovery.sampled_m1_no_wrap fbuf gbuf r (r2_encap_message r msg) =>
  let ct = NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c in
  complete_entry_accepts ct sk /\
  complete_message_result ct sk =
    (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec (forward_ntt_spec r),msg,W32.zero) /\
  !complete_sotp_failed ct sk.
proof.
  move=> hk hr he hn; simplify.
  have hc := encap_cipher_tobytes_input_qrange _ _ _ _ he.
  have ha := agreement_entry_accepts fbuf gbuf finv ginv h hinv pk sk c hk hc.
  have hkey := agreement_secret_relation fbuf gbuf finv ginv h hinv pk sk hk.
  have hser : r2_serialization_relation c hinv (decoded_poly (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c))
      (decoded_poly (decap_hbytes (complete_sk_poly sk))) (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c) (decap_hbytes (complete_sk_poly sk)).
  + rewrite /r2_serialization_relation.
    split; first done.
    split.
    - exact (agreement_hinv_encoding fbuf gbuf finv ginv h hinv pk sk hk).
    by split.
  have hca := candidate_decoded_spec_algebra (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c) (decap_fbytes (complete_sk_poly sk)).
  have hfirst : poly_basemul_qring (decoded_poly (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c)) (decoded_poly (decap_fbytes (complete_sk_poly sk)))
      (candidate_product_spec (decoded_poly (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c)) (decoded_poly (decap_fbytes (complete_sk_poly sk)))) 192.
  + move: hca; rewrite /decap_candidate_algebra; move=> [hf _]; exact hf.
  have [hd [hm hh]] := r2_guard_candidate_inputs (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c) (complete_sk_poly sk) ha.
  have h2 := r2_spec_algebra (decoded_poly (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c)) (message_candidate (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c) (complete_sk_poly sk))
    (decoded_poly (decap_hbytes (complete_sk_poly sk))) hd hm hh.
  have hsecond : poly_basemul_qring
      (decap_sub_spec (decoded_poly (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c))
        (candidate_product_spec (decoded_poly (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c)) (decoded_poly (decap_fbytes (complete_sk_poly sk)))))
      (decoded_poly (decap_hbytes (complete_sk_poly sk))) (message_r2 (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c) (complete_sk_poly sk)) 192.
  + rewrite -agreement_difference_value.
    move: h2; rewrite /decap_r2_algebra /message_r2; move=> [_ [_ [_ [hb _]]]]; exact hb.
  have recovery := no_wrap_serialized_message_recovery fbuf gbuf finv ginv h hinv
    (decoded_poly pk) (decoded_poly (decap_fbytes (complete_sk_poly sk))) (decoded_poly (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c))
    (decoded_poly (decap_hbytes (complete_sk_poly sk))) r c
    (candidate_product_spec (decoded_poly (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c)) (decoded_poly (decap_fbytes (complete_sk_poly sk))))
    (message_r2 (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c) (complete_sk_poly sk)) pk (decap_fbytes (complete_sk_poly sk)) (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c) (decap_hbytes (complete_sk_poly sk)) msg
    hkey hser hr he hfirst hsecond hn.
  move: recovery; rewrite /r2_pad_message_recovery -agreement_candidate_value.
  move=> [hmessage [hmod [hbytes [hpad hdecode]]]].
  have hdmsg : NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_decode_msg_spec
      (message_candidate (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c) (complete_sk_poly sk)) (serialized_hash_g_pad (message_r2 (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c) (complete_sk_poly sk))) = msg.
  + move: hdecode; rewrite /NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_decode_spec; by move=> [] -> _.
  have hdfail : !NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_decode_fail_spec
      (message_candidate (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c) (complete_sk_poly sk)) (serialized_hash_g_pad (message_r2 (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c) (complete_sk_poly sk))).
  + move: hdecode; rewrite /NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_decode_spec; by move=> [] _ ->.
  split; first exact ha.
  split.
  + rewrite /complete_message_result /NTRUPlus768DecapMessageSpec.decap_message_spec
      NTRUPlus768PolyToBytesAlgebra.poly_tobytes_procedure_specE.
    change ((NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec (message_r2 (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c) (complete_sk_poly sk)),
      NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_decode_msg_spec (message_candidate (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c) (complete_sk_poly sk))
        (serialized_hash_g_pad (message_r2 (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c) (complete_sk_poly sk))),
      W32.of_int (b2i (NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_decode_fail_spec
        (message_candidate (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c) (complete_sk_poly sk)) (serialized_hash_g_pad (message_r2 (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c) (complete_sk_poly sk)))))) =
      (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec (forward_ntt_spec r),msg,W32.zero)).
    by rewrite hbytes hdmsg hdfail.
  rewrite /complete_sotp_failed NTRUPlus768PolyToBytesAlgebra.poly_tobytes_procedure_specE.
  exact hdfail.
qed.
