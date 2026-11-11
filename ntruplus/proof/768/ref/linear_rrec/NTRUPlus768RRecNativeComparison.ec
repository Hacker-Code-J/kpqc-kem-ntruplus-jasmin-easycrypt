require import AllCore Distr.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array768 Array1152 Array2304 Array2336.
require import NTRUPlus768PKEModel NTRUPlus768PKEAlgebra.
require import NTRUPlus768RRecLinearAlgebra NTRUPlus768RRecPublicInverse.
require import NTRUPlus768DecapCompleteSpec NTRUPlus768DecapGuardSpec.
require import NTRUPlus768DecapMessageAlgebra NTRUPlus768DecapMessageSpec.
require import NTRUPlus768DecapR2CompSpec NTRUPlus768PolyToBytesAlgebra.
require import NTRUPlus768EncapGuardSpec NTRUPlus768CanonicalDecoder.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768KEMPayloadSpec.
require import NTRUPlus768PolyCBD1Algebra NTRUPlus768SOTPContracts.

(* Same decoded message polynomial throughout. This relation does not
   replace it by a new SOTP encoding using a possibly different G input. *)
op [opaque] rrec_compare_relation (pk ct:W8.t Array1152.t) (m:pke_poly)
 (bs:W8.t Array1152.t) =
 encap_key_canonical pk /\ rrec_public_inverse(decoded_poly pk)<>None /\
 encap_key_canonical ct /\ pke_domain m /\
 bs=NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec
   (decap_r2_spec (decoded_poly ct) m (oget(rrec_public_inverse(decoded_poly pk)))).
op [opaque] rrec_native_message (w:keygen_witness) (ct:W8.t Array1152.t) =
 message_candidate ct (complete_sk_poly w.`kg_sk).
op [opaque] rrec_native_r2 (w:keygen_witness) (ct:W8.t Array1152.t) =
 message_r2 ct (complete_sk_poly w.`kg_sk).
op [opaque] rrec_native_bytes (w:keygen_witness) (ct:W8.t Array1152.t) =
 NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec(rrec_native_r2 w ct).

lemma rrec_compare_pk_canonical pk ct m bs : rrec_compare_relation pk ct m bs=>encap_key_canonical pk.
proof. rewrite /rrec_compare_relation; smt(). qed.
lemma rrec_compare_message_domain pk ct m bs : rrec_compare_relation pk ct m bs=>pke_domain m.
proof. rewrite /rrec_compare_relation; smt(). qed.
lemma rrec_compare_reencrypt pk ct m bs hout : rrec_compare_relation pk ct m bs=>
 ((bs=complete_regenerated hout)=
 (pke_enc_spec pk m (poly_cbd1_spec(complete_hash_tail hout))=Some ct)).
proof.
 rewrite /rrec_compare_relation; move=>[hp [hi [hc [hm hbs]]]].
 have hr:=pke_domain_cbd(complete_hash_tail hout).
 have he:=rrec_r2_serialized_iff pk m ct (poly_cbd1_spec(complete_hash_tail hout)) hp hi hc hm hr.
 have heq:=eq_iff_imp _ _ he.
 move:heq; rewrite -hbs /complete_regenerated poly_tobytes_procedure_specE /pke_rhat.
 done.
qed.
lemma rrec_compare_failure pk ct m bs hout df : rrec_compare_relation pk ct m bs=>
 (df \/ bs<>complete_regenerated hout)=
 (df \/ pke_enc_spec pk m (poly_cbd1_spec(complete_hash_tail hout))<>Some ct).
proof. move=>h; by rewrite (rrec_compare_reencrypt pk ct m bs hout h). qed.

lemma rrec_native_messageE w ct : message_candidate ct(complete_sk_poly w.`kg_sk)=rrec_native_message w ct.
proof. by rewrite /rrec_native_message. qed.
lemma rrec_native_r2E w ct : message_r2 ct(complete_sk_poly w.`kg_sk)=rrec_native_r2 w ct.
proof. by rewrite /rrec_native_r2. qed.
lemma rrec_native_public_r2 w ct : pke_key_relation w=>
 decap_r2_spec (decoded_poly ct) (rrec_native_message w ct)
   (oget(rrec_public_inverse(decoded_poly w.`kg_pk)))=rrec_native_r2 w ct.
proof.
 move=>hk; rewrite(rrec_generated_public_inverse_stored w hk) /=.
 by rewrite /rrec_native_r2 /message_r2 rrec_native_messageE.
qed.
lemma rrec_native_entry w ct : pke_key_relation w=>
 complete_entry_accepts ct w.`kg_sk=encap_key_canonical ct.
proof.
 move=>hk.
 have h:=hk; rewrite /pke_key_relation in h.
 have [_ hs]:=payload_key_canonical _ _ _ _ _ _ _ _ h.
 by rewrite /complete_entry_accepts /decap_guard_accepts hs /=.
qed.
lemma rrec_native_message_domain w ct : complete_entry_accepts ct w.`kg_sk=>
 pke_domain(rrec_native_message w ct).
proof.
 move=>he.
 have [_ hm]:=message_caller_input_closure ct (complete_sk_poly w.`kg_sk) he.
 rewrite /rrec_native_message sotp_domainE; exact hm.
qed.
lemma rrec_native_message_result_bytes w ct :
 (complete_message_result ct w.`kg_sk).`1=rrec_native_bytes w ct.
proof.
 by rewrite /complete_message_result /decap_message_spec /=
 poly_tobytes_procedure_specE rrec_native_r2E /rrec_native_bytes.
qed.
lemma rrec_native_compare_relation w ct : pke_key_relation w=>
 complete_entry_accepts ct w.`kg_sk=>
 rrec_compare_relation w.`kg_pk ct (rrec_native_message w ct)(rrec_native_bytes w ct).
proof.
 move=>hk he.
 have hp:=pke_key_canonical w hk.
 have hi:rrec_public_inverse(decoded_poly w.`kg_pk)<>None.
 + by rewrite(rrec_generated_public_inverse_stored w hk).
 have hc:encap_key_canonical ct by move:he; rewrite(rrec_native_entry w ct hk).
 have hm:=rrec_native_message_domain w ct he.
 rewrite /rrec_compare_relation hp hi hc hm /= (rrec_native_public_r2 w ct hk).
 by rewrite /rrec_native_bytes.
qed.
lemma rrec_native_compare_reencrypt w ct hout : pke_key_relation w=>
 complete_entry_accepts ct w.`kg_sk=>
 ((NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec(message_r2 ct(complete_sk_poly w.`kg_sk))=
   complete_regenerated hout)=
  (pke_enc_spec w.`kg_pk (message_candidate ct(complete_sk_poly w.`kg_sk))
    (poly_cbd1_spec(complete_hash_tail hout))=Some ct)).
proof.
 move=>hk he.
 have h:=rrec_compare_reencrypt _ _ _ _ hout (rrec_native_compare_relation w ct hk he).
 by move:h; rewrite /rrec_native_bytes -rrec_native_r2E -rrec_native_messageE.
qed.

lemma rrec_native_compare_relation_procedure w ct : pke_key_relation w=>
 complete_entry_accepts ct w.`kg_sk=>
 rrec_compare_relation w.`kg_pk ct (message_candidate ct(complete_sk_poly w.`kg_sk))
   (NTRUPlus768PolyToBytesProof.poly_tobytes_spec(message_r2 ct(complete_sk_poly w.`kg_sk))).
proof.
 move=>hk he; rewrite poly_tobytes_procedure_specE rrec_native_messageE rrec_native_r2E.
 have hh:=rrec_native_compare_relation w ct hk he.
 by move:hh; rewrite /rrec_native_bytes.
qed.
