require import AllCore.
from Jasmin require import JWord.
require import Array768 Array1152.
require import NTRUPlus768PKEModel NTRUPlus768EncapGuardSpec NTRUPlus768CanonicalDecoder.
require import NTRUPlus768RRecModel NTRUPlus768RRecPublicInverse.

(* Same guards, public inverse, and candidate as checked RRec. Only the
   final PKE re-encryption verification is absent from this model. *)
op [opaque] rrec_linear_using_inverse_spec (pk:W8.t Array1152.t) (m:pke_poly)
 (ct:W8.t Array1152.t) (inverse:pke_poly) : pke_poly option =
 if encap_key_canonical ct /\ pke_domain m then
 rrec_finish_spec (decoded_poly ct) m inverse else None.
op [opaque] rrec_linear_spec (pk:W8.t Array1152.t) (m:pke_poly)
 (ct:W8.t Array1152.t) : pke_poly option =
 if encap_key_canonical pk then
 let inverse=rrec_public_inverse(decoded_poly pk) in
 if inverse=None then None else rrec_linear_using_inverse_spec pk m ct (oget inverse)
 else None.

lemma rrec_linear_reject_key pk m ct : !encap_key_canonical pk =>rrec_linear_spec pk m ct=None.
proof. by move=>h; rewrite /rrec_linear_spec h. qed.
lemma rrec_linear_reject_cipher pk m ct : !encap_key_canonical ct =>rrec_linear_spec pk m ct=None.
proof.
 move=>h; rewrite /rrec_linear_spec /=; case(encap_key_canonical pk)=>hk //=.
 case(rrec_public_inverse(decoded_poly pk)=None)=>hi //=.
 by rewrite /rrec_linear_using_inverse_spec h.
qed.
lemma rrec_linear_reject_message pk m ct : !pke_domain m =>rrec_linear_spec pk m ct=None.
proof.
 move=>h; rewrite /rrec_linear_spec /=; case(encap_key_canonical pk)=>hk //=.
 case(rrec_public_inverse(decoded_poly pk)=None)=>hi //=.
 by rewrite /rrec_linear_using_inverse_spec h.
qed.
lemma rrec_linear_reject_inverse pk m ct : rrec_public_inverse(decoded_poly pk)=None =>
 rrec_linear_spec pk m ct=None.
proof. move=>h; rewrite /rrec_linear_spec /= h; by case(encap_key_canonical pk). qed.
lemma rrec_linear_some pk m ct r : rrec_linear_spec pk m ct=Some r =>
 encap_key_canonical pk /\ rrec_public_inverse(decoded_poly pk)<>None /\
 encap_key_canonical ct /\ pke_domain m /\
 r=rrec_candidate (decoded_poly ct) m (oget(rrec_public_inverse(decoded_poly pk))) /\ pke_domain r.
proof.
 rewrite /rrec_linear_spec /=; case(encap_key_canonical pk)=>hk //=.
 case(rrec_public_inverse(decoded_poly pk)=None)=>hi //=.
 rewrite /rrec_linear_using_inverse_spec; case(encap_key_canonical ct /\ pke_domain m)=>hc //=.
 move=>hs; have [he hr]:=rrec_finish_some _ _ _ _ hs; smt().
qed.
lemma rrec_linear_from_checked pk m ct r : rrec_spec pk m ct=Some r =>rrec_linear_spec pk m ct=Some r.
proof.
 rewrite /rrec_spec /rrec_linear_spec /=; case(encap_key_canonical pk)=>hk //=.
 case(rrec_public_inverse(decoded_poly pk)=None)=>hi //=.
 rewrite /rrec_using_inverse_spec /rrec_linear_using_inverse_spec.
 case(encap_key_canonical ct /\ pke_domain m)=>hc //=.
 move=>hs; have [h _]:=rrec_verify_spec_sound _ _ _ _ _ hs; exact h.
qed.
