require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.
require import Array768.
require import NTRUPlus768NTTProof NTRUPlus768PolySubProof NTRUPlus768PolyBasemulProof.
require import NTRUPlus768DecapCandidateSpec.

(* Exact word specification of the local verified NTT schedule. This is not
   an equivalence claim to the current official C reduction trace. *)
op r2_difference_spec (cp mp : W16.t Array768.t) : W16.t Array768.t =
  poly_sub_spec cp (ntt_spec mp).

op decap_r2_spec (cp mp hp : W16.t Array768.t) : W16.t Array768.t =
  candidate_product_spec (r2_difference_spec cp mp) hp.

lemma decap_r2_word cp mp hp :
  is_poly_basemul (r2_difference_spec cp mp) hp (decap_r2_spec cp mp hp) 192.
proof. exact (candidate_product_word (r2_difference_spec cp mp) hp). qed.
