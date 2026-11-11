require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.
require import Array768 Array1152 Array1153 Array2304 Array32 Array192 Array96.
require import NTRUPlus768DecapMessagePrepareProof NTRUPlus768DecapMessageSpec.
require import NTRUPlus768DecapR2CompSpec NTRUPlus768DecapR2CompAlgebra.
require import NTRUPlus768DecapCandidateSpec NTRUPlus768DecapCandidateAlgebra.
require import NTRUPlus768DecapGuardSpec NTRUPlus768EncapGuardSpec NTRUPlus768CanonicalDecoder.
require import NTRUPlus768DecapR2Bridge NTRUPlus768PolyToBytesProof NTRUPlus768PolyToBytesAlgebra.
require import NTRUPlus768PolySOTPDecodeAlgebra.

op message_candidate ct sk = decap_candidate_spec (decoded_poly ct) (decoded_poly (decap_fbytes sk)).
op message_r2 ct sk = decap_r2_spec (decoded_poly ct) (message_candidate ct sk) (decoded_poly (decap_hbytes sk)).

lemma message_caller_input_closure ct sk :
  decap_guard_accepts ct (decap_fbytes sk) (decap_hbytes sk) =>
  NTRUPlus768PolyToBytesProof.poly_tobytes_input_qrange (message_r2 ct sk) /\
  poly_sotp_trit_input (message_candidate ct sk).
proof.
  move=> ha.
  have [hc [hm hh]] := r2_guard_candidate_inputs ct sk ha.
  have halg := r2_spec_algebra (decoded_poly ct) (message_candidate ct sk)
    (decoded_poly (decap_hbytes sk)) hc hm hh.
  split.
  + apply in_qrange768_poly_tobytes_input_qrange.
    move: halg; rewrite /decap_r2_algebra /message_r2; smt().
  exact hm.
qed.

(* Canonical serialization includes both a coefficient-range theorem and
   congruence modulo q. It asserts no recovery of encapsulation randomness. *)
lemma message_caller_serialization ct sk j :
  decap_guard_accepts ct (decap_fbytes sk) (decap_hbytes sk) => 0 <= j < 768 =>
  let p = message_r2 ct sk in
  let bs = NTRUPlus768PolyToBytesProof.poly_tobytes_spec p in
  0 <= NTRUPlus768BasemulAlgebra.coeff
    (NTRUPlus768PolyToBytesAlgebra.poly_frombytes_spec bs).[j] < NTRUPlus768BasemulAlgebra.q /\
  NTRUPlus768BasemulAlgebra.coeff
    (NTRUPlus768PolyToBytesAlgebra.poly_frombytes_spec bs).[j] %% NTRUPlus768BasemulAlgebra.q =
  NTRUPlus768BasemulAlgebra.coeff p.[j] %% NTRUPlus768BasemulAlgebra.q.
proof.
  move=> ha hj; simplify.
  have [hr _] := message_caller_input_closure ct sk ha.
  rewrite poly_tobytes_procedure_input_qrangeE in hr.
  rewrite poly_tobytes_procedure_specE.
  split.
  + exact (poly_frombytes_poly_tobytes_roundtrip_coeff_range _ j hr hj).
  exact (poly_frombytes_poly_tobytes_roundtrip_coeff_mod_q _ j hr hj).
qed.

