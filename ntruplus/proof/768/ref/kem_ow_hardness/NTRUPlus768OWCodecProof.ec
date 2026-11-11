require import AllCore IntDiv Ring.
from Jasmin require import JWord.
require import Array768 Array1152.
require import NTRUPlus768OWCodec NTRUPlus768OWUniform.
require import NTRUPlus768PKEModel NTRUPlus768PKEAlgebra NTRUPlus768PKEKeyDistribution.
require import NTRUPlus768CanonicalDecoder NTRUPlus768EncapGuardSpec NTRUPlus768KEMPayloadSpec.
require import NTRUPlus768BasemulAlgebra NTRUPlus768Crepmod3Algebra NTRUPlus768KeygenSecretFBridge NTRUPlus768KeygenPublicKeyBridge.
require import NTRUPlus768RRecCanonical NTRUPlus768RRecTransform NTRUPlus768RRecTerminal NTRUPlus768RRecSerialization.
require import NTRUPlus768RRecPublicInverse NTRUPlus768RRecInverseAlgebra NTRUPlus768RRecAlgebra.
require import NTRUPlus768RRecModel NTRUPlus768RRecLinearModel NTRUPlus768RRecLinearProof.
require import NTRUPlus768R2Serialization NTRUPlus768ValidKeyR2Recovery NTRUPlus768PolyToBytesAlgebra NTRUPlus768PolyFromBytesAlgebra.
require import NTRUPlus768CyclotomicFactorization NTRUPlus768EvaluationSemantics NTRUPlus768TerminalRepresentation.
require import NTRUPlus768ForwardNTTStage1Semantics NTRUPlus768ForwardNTTSemantics NTRUPlus768CoefficientRecovery.
require import NTRUPlus768NTTStage1Algebra NTRUPlus768NTTProof NTRUPlus768NTTAlgebra.
require import NTRUPlus768InvNTTAlgebra NTRUPlus768InvNTTRadix2_4Algebra NTRUPlus768InverseNTTSemantics.
require import NTRUPlus768GenKeyProjection NTRUPlus768KeygenTerminalUnit NTRUPlus768KeygenGlobalUnit.
abbrev ( + ) = NTRUPoly.PolyComRing.( + ).
abbrev ( * ) = NTRUPoly.PolyComRing.( * ).

lemma ow_coeff_words_coeff p i : 0<=i<768=>
 coeff(ow_coeff_words p).[i]=CycloFq.asint(NTRUPoly."_.[_]" p i).
proof.
 move=>hi;rewrite /ow_coeff_words Array768.initiE //.
 apply coeff_of_word_small;have h:=CycloFq.rg_asint(NTRUPoly."_.[_]" p i).
 move:h;rewrite /q;smt().
qed.
lemma ow_coeff_words_canonical p : rrec_canonical_domain(ow_coeff_words p).
proof. move=>i hi;rewrite(ow_coeff_words_coeff p i hi);exact(CycloFq.rg_asint _). qed.
lemma ow_coeff_words_poly p : ow_rq_domain p=>input_poly(ow_coeff_words p)=p.
proof.
 rewrite /ow_rq_domain=>hp;apply/NTRUPoly.poly_eqP=>i hi.
 rewrite -int_poly_words.
 case(i<768)=>hn.
 + rewrite int_poly_coeff 1:/# Array768.mapiE 1:/# (ow_coeff_words_coeff p i _) 1:/# /lift_int.
   exact(CycloFq.asintK _).
 rewrite int_poly_coeff_out 1:/# (NTRUPoly.gedeg_coeff p i _) 1:/#;done.
qed.
lemma ow_decode_canonical bytes : rrec_canonical_domain(ow_decode bytes).
proof. rewrite /ow_decode;exact(rrec_canonical_inverse_closed _). qed.
lemma ow_key_poly_domain bytes : ow_rq_domain(ow_key_poly bytes).
proof. rewrite /ow_rq_domain ow_decode_poly;exact(gen_inverse_poly_degree _). qed.
lemma ow_words_key_poly bytes : ow_coeff_words(ow_key_poly bytes)=ow_decode bytes.
proof.
 apply rrec_canonical_domain_unique.
 + exact(ow_coeff_words_canonical _).
 + exact(ow_decode_canonical _).
 rewrite(ow_coeff_words_poly _ (ow_key_poly_domain bytes)) /ow_key_poly.
 exact(eqm_global_refl _).
qed.
lemma ow_encoded_terminal_canonical p :
 rrec_canonical_domain(rrec_canonical_forward(ow_coeff_words p)).
proof. exact(rrec_canonical_forward_closed _ (ow_coeff_words_canonical p)). qed.
lemma ow_encoded_terminal_serializer p :
 poly_tobytes_input_qrange(rrec_canonical_forward(ow_coeff_words p)).
proof.
 apply in_qrange768_poly_tobytes_input_qrange.
 exact(gen_canonical_block_range _ (ow_encoded_terminal_canonical p)).
qed.
lemma ow_encode_canonical p : encap_key_canonical(ow_encode p).
proof. rewrite /ow_encode;exact(payload_serialized_canonical _ (ow_encoded_terminal_serializer p)). qed.
lemma ow_decoded_canonical bytes : encap_key_canonical bytes=>rrec_canonical_domain(decoded_poly bytes).
proof.
 move=>hb i hi;have hu:=hb i hi.
 have he:coeff(decoded_poly bytes).[i]=W16.to_uint(decoded_poly bytes).[i].
 + apply NTRUPlus768PolyFromBytesAlgebra.coeff_uint_small;smt(W16.to_uint_cmp).
 rewrite he /q;have h:=W16.to_uint_cmp(decoded_poly bytes).[i];smt().
qed.
lemma ow_decoded_encode p : decoded_poly(ow_encode p)=rrec_canonical_forward(ow_coeff_words p).
proof.
 have hd:=ow_decoded_canonical _ (ow_encode_canonical p).
 have ht:=ow_encoded_terminal_canonical p.
 have he:poly_coeff_eq_mod_q(decoded_poly(ow_encode p))(rrec_canonical_forward(ow_coeff_words p)).
 + rewrite /ow_encode;exact(r2_serialized_decode_mod_q _ (ow_encoded_terminal_serializer p)).
 rewrite -(rrec_canonical_fixed _ hd) -(rrec_canonical_fixed _ ht).
 exact(rrec_canonical_congruent _ _ he).
qed.
lemma ow_decode_encode p : ow_rq_domain p=>ow_key_poly(ow_encode p)=p.
proof.
 move=>hp;rewrite /ow_key_poly /ow_decode ow_decoded_encode
 (rrec_canonical_left_inverse _ (ow_coeff_words_canonical p)).
 exact(ow_coeff_words_poly p hp).
qed.
lemma ow_encode_decode bytes : encap_key_canonical bytes=>ow_encode(ow_key_poly bytes)=bytes.
proof.
 move=>hb;rewrite /ow_encode ow_words_key_poly /ow_decode
 (rrec_canonical_right_inverse _ (ow_decoded_canonical bytes hb)).
 exact(rrec_canonical_reencode bytes hb).
qed.
lemma ow_encode_injective p q : ow_rq_domain p=>ow_rq_domain q=>ow_encode p=ow_encode q=>p=q.
proof. move=>hp hq he;by rewrite -(ow_decode_encode p hp) -(ow_decode_encode q hq) he. qed.
lemma ow_encoded_represents p : ow_rq_domain p=>terminal_represents(decoded_poly(ow_encode p))p.
proof.
 move=>hp;have h:=rrec_canonical_forward_represents (ow_coeff_words p) (ow_coeff_words_canonical p).
 rewrite(ow_coeff_words_poly p hp) in h.
 by rewrite ow_decoded_encode.
qed.

lemma ow_bytes_representation_unique x y p :
 encap_key_canonical x=>encap_key_canonical y=>
 terminal_represents(decoded_poly x)p=>terminal_represents(decoded_poly y)p=>x=y.
proof.
 move=>hx hy hxp hyp.
 have hm:=rrec_terminal_same_poly_mod_q _ _ p hxp hyp.
 apply rrec_decoded_poly_injective.
 rewrite -(rrec_canonical_fixed _ (ow_decoded_canonical x hx))
 -(rrec_canonical_fixed _ (ow_decoded_canonical y hy)).
 exact(rrec_canonical_congruent _ _ hm).
qed.

require import NTRUPlus768KeygenCompleteInverse.
lemma ow_unit_test_iff a : ow_rq_domain a=>
 (ow_unit_test a <=> pke_rq_unit a).
proof.
 move=>ha.
 have hr:=rrec_public_key_range _ (ow_encode_canonical a).
 have hrep:=ow_encoded_represents a ha.
 rewrite -(gen_terminal_unit_iff_rq _ a hr hrep) -(gen_inverse_status_iff _ hr)
 /ow_unit_test /rrec_public_inverse.
 by case(keygen_inverse_status(decoded_poly(ow_encode a))=W64.zero).
qed.

(* This bridge is valid for every canonical a, including nonunits. It is
   the ordinary quotient-ring equation, independent of public inversion. *)
lemma ow_encode_madd a b secret error :
 ow_rq_domain a=>ow_rq_domain b=>pke_domain secret=>pke_domain error=>
 eqm_global b (a*input_poly secret+input_poly error)=>
 ow_encode b=pke_ciphertext(ow_encode a)error secret.
proof.
 move=>ha hb hs he hrel.
 have hct:=pke_serialized_cipher_represents (ow_encode a) error secret a
  (ow_encode_canonical a) he hs (ow_encoded_represents a ha).
 apply(ow_bytes_representation_unique _ _ (a*input_poly secret+input_poly error)
  (ow_encode_canonical b) (pke_cipher_canonical _ _ _ (ow_encode_canonical a) he hs)).
 + exact(terminal_represents_global_congr _ b _ hrel (ow_encoded_represents b hb)).
 exact hct.
qed.
lemma ow_rlwe_value_domain a secret error : ow_rq_domain(ow_rlwe_value a secret error).
proof. rewrite /ow_rlwe_value;exact(ow_key_poly_domain _). qed.
lemma ow_rlwe_value_relation a secret error :
 ow_rq_domain a=>pke_domain secret=>pke_domain error=>
 eqm_global(ow_rlwe_value a secret error)(a*input_poly secret+input_poly error).
proof.
 move=>ha hs he;rewrite /ow_rlwe_value ow_decode_poly.
 have hc:=pke_cipher_canonical _ _ _ (ow_encode_canonical a) he hs.
 have hshape:=rrec_canonical_domain_qrange _ (ow_decoded_canonical _ hc).
 have hrep:=pke_serialized_cipher_represents (ow_encode a) error secret a
  (ow_encode_canonical a) he hs (ow_encoded_represents a ha).
 exact(gen_terminal_global_congr _ _ _ hshape (gen_inverse_poly_represents _ hshape) hrep).
qed.
lemma ow_rlwe_value_unique a secret error b :
 ow_rq_domain a=>pke_domain secret=>pke_domain error=>ow_rq_domain b=>
 eqm_global b (a*input_poly secret+input_poly error)=>b=ow_rlwe_value a secret error.
proof.
 move=>ha hs he hb hrel.
 apply(eqm_global_low_degree_unique _ _ hb (ow_rlwe_value_domain a secret error)).
 exact(eqm_global_trans _ _ _ hrel (eqm_global_sym _ _ (ow_rlwe_value_relation a secret error ha hs he))).
qed.
lemma ow_encode_rlwe a secret error :
 ow_rq_domain a=>pke_domain secret=>pke_domain error=>
 ow_encode(ow_rlwe_value a secret error)=pke_ciphertext(ow_encode a)error secret.
proof.
 move=>ha hs he;rewrite /ow_rlwe_value.
 exact(ow_encode_decode _ (pke_cipher_canonical _ _ _ (ow_encode_canonical a) he hs)).
qed.
lemma ow_recover_rlwe a secret error :
 ow_rq_domain a=>pke_domain secret=>pke_domain error=>ow_unit_test a=>
 ow_recover a (ow_rlwe_value a secret error) error=input_poly secret.
proof.
 move=>ha hs he hu;have hi:=hu;rewrite /ow_unit_test in hi.
 have hr:=rrec_public_forward (ow_encode a) error secret (ow_encode_canonical a) hi he hs.
 by rewrite /ow_recover (ow_encode_rlwe a secret error ha hs he)
 rrec_linear_checked_equivalence hr /=.
qed.
lemma ow_recover_equation a b secret error :
 ow_rq_domain a=>ow_rq_domain b=>pke_domain secret=>pke_domain error=>pke_rq_unit a=>
 eqm_global b (a*input_poly secret+input_poly error)=>
 ow_recover a b error=input_poly secret.
proof.
 move=>ha hb hs he hu hrel.
 rewrite(ow_rlwe_value_unique a secret error b ha hs he hb hrel).
 exact(ow_recover_rlwe a secret error ha hs he (iffRL _ _ (ow_unit_test_iff a ha) hu)).
qed.
