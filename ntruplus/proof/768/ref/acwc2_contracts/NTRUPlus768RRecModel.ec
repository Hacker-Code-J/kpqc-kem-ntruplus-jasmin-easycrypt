require import AllCore.
from Jasmin require import JWord.
require import Array768 Array1152.
require import NTRUPlus768PKEModel NTRUPlus768EncapGuardSpec NTRUPlus768CanonicalDecoder.
require import NTRUPlus768DecapR2CompSpec NTRUPlus768InvNTTProof.
require import NTRUPlus768RRecPublicInverse NTRUPlus768RRecWordChecks.

(* Efficient public randomness recovery with an explicit re-encryption
   check. The only inputs are the public key, message, and ciphertext. *)
op [opaque] rrec_candidate (cp m inverse:pke_poly) : pke_poly =
 rrec_normalize(invntt_spec(decap_r2_spec cp m inverse)).
op [opaque] rrec_finish_spec (cp m inverse:pke_poly) : pke_poly option =
 if pke_domain(rrec_candidate cp m inverse) then Some(rrec_candidate cp m inverse) else None.
op [opaque] rrec_verify_spec (pk:W8.t Array1152.t) (m:pke_poly)
 (ct:W8.t Array1152.t) (candidate:pke_poly option) : pke_poly option =
 if candidate=None then None else
 if pke_enc_spec pk m (oget candidate)=Some ct then candidate else None.
op [opaque] rrec_using_inverse_spec (pk:W8.t Array1152.t) (m:pke_poly)
 (ct:W8.t Array1152.t) (inverse:pke_poly) : pke_poly option =
 if encap_key_canonical ct /\ pke_domain m then
 rrec_verify_spec pk m ct (rrec_finish_spec (decoded_poly ct) m inverse) else None.
op [opaque] rrec_spec (pk:W8.t Array1152.t) (m:pke_poly)
 (ct:W8.t Array1152.t) : pke_poly option =
 if encap_key_canonical pk then
 let inverse=rrec_public_inverse(decoded_poly pk) in
 if inverse=None then None else rrec_using_inverse_spec pk m ct (oget inverse)
 else None.

lemma rrec_candidateE cp m inverse :
 rrec_normalize(invntt_spec(decap_r2_spec cp m inverse))=rrec_candidate cp m inverse.
proof. by rewrite /rrec_candidate. qed.
lemma rrec_finish_accept cp m inverse : pke_domain(rrec_candidate cp m inverse) =>
 rrec_finish_spec cp m inverse=Some(rrec_candidate cp m inverse).
proof. by move=>h; rewrite /rrec_finish_spec h. qed.
lemma rrec_finish_some cp m inverse r : rrec_finish_spec cp m inverse=Some r =>
 r=rrec_candidate cp m inverse /\ pke_domain r.
proof. rewrite /rrec_finish_spec; case(pke_domain(rrec_candidate cp m inverse)); smt(). qed.
lemma rrec_finish_domain cp m inverse : rrec_finish_spec cp m inverse<>None =>
 pke_domain(oget(rrec_finish_spec cp m inverse)).
proof. rewrite /rrec_finish_spec; case(pke_domain(rrec_candidate cp m inverse)); auto. qed.
lemma rrec_verify_spec_sound pk m ct candidate r : rrec_verify_spec pk m ct candidate=Some r =>
 candidate=Some r /\ pke_enc_spec pk m r=Some ct.
proof.
 rewrite /rrec_verify_spec; case(candidate=None)=>hn //.
 case(pke_enc_spec pk m (oget candidate)=Some ct)=>he //.
qed.
lemma rrec_verify_accept pk m ct r : pke_enc_spec pk m r=Some ct =>
 rrec_verify_spec pk m ct (Some r)=Some r.
proof. by move=>h; rewrite /rrec_verify_spec /= h. qed.
lemma rrec_spec_sound pk m ct r : rrec_spec pk m ct=Some r =>
 pke_domain m /\ pke_domain r /\ pke_enc_spec pk m r=Some ct.
proof.
 rewrite /rrec_spec /=; case(encap_key_canonical pk)=>hpk; last by smt().
 case(rrec_public_inverse(decoded_poly pk)=None)=>hi; first by smt().
 rewrite /rrec_using_inverse_spec; case(encap_key_canonical ct /\ pke_domain m)=>hc; last by smt().
 move=>h.
 have [hf he]:=rrec_verify_spec_sound _ _ _ _ _ h.
 have [_ hr]:=rrec_finish_some _ _ _ _ hf.
 smt().
qed.
lemma rrec_spec_reject_key pk m ct : !encap_key_canonical pk =>rrec_spec pk m ct=None.
proof. by move=>h; rewrite /rrec_spec h. qed.
lemma rrec_spec_reject_cipher pk m ct : !encap_key_canonical ct =>rrec_spec pk m ct=None.
proof.
 move=>h; rewrite /rrec_spec /=; case(encap_key_canonical pk)=>hpk=>//.
 case(rrec_public_inverse(decoded_poly pk)=None)=>hi=>//.
 by rewrite /rrec_using_inverse_spec h.
qed.
