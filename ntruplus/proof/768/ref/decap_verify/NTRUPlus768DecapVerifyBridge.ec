require import AllCore Distr.
from Jasmin require import JWord.

require import Array1152.
require import NTRUPlus768VerifyProof.

(* Keccak-free comparison boundary for the two established serialization
   frontiers.  [buf1_flow] and [buf2_flow] are typed unary predicates so the
   r2 and r1 proof trees do not have to be reloaded together.  Callers
   instantiate them with closures over the already-proved
   decap_r2_tobytes_value_flow and decap_r1_tobytes_value_flow predicates.
   This is an array-value composition, not a C shared-memory theorem. *)
op decap_verify_value_flow
    (buf1_flow buf2_flow : W8.t Array1152.t -> bool)
    (buf1 buf2 : W8.t Array1152.t)
    (compare_result : W64.t) : bool =
  buf1_flow buf1 /\
  buf2_flow buf2 /\
  compare_result = verify_spec buf1 buf2.

lemma decap_verify_value_flow_intro
    (buf1_flow buf2_flow : W8.t Array1152.t -> bool)
    (buf1 buf2 : W8.t Array1152.t) :
  buf1_flow buf1 =>
  buf2_flow buf2 =>
  decap_verify_value_flow
    buf1_flow buf2_flow buf1 buf2 (verify_spec buf1 buf2).
proof. by rewrite /decap_verify_value_flow. qed.

lemma decap_verify_value_flow_result_range
    (buf1_flow buf2_flow : W8.t Array1152.t -> bool)
    (buf1 buf2 : W8.t Array1152.t)
    (compare_result : W64.t) :
  decap_verify_value_flow
    buf1_flow buf2_flow buf1 buf2 compare_result =>
  compare_result = W64.of_int 0 \/ compare_result = W64.of_int 1.
proof.
  move=> [_ [_ ->]].
  exact (verify_spec_range buf1 buf2).
qed.

lemma decap_verify_value_flow_equal_iff
    (buf1_flow buf2_flow : W8.t Array1152.t -> bool)
    (buf1 buf2 : W8.t Array1152.t)
    (compare_result : W64.t) :
  decap_verify_value_flow
    buf1_flow buf2_flow buf1 buf2 compare_result =>
  (compare_result = W64.of_int 0 <=> buf1 = buf2).
proof.
  move=> [_ [_ ->]].
  exact (verify_spec_eq_iff buf1 buf2).
qed.

lemma decap_verify_value_flow_mismatch_iff
    (buf1_flow buf2_flow : W8.t Array1152.t -> bool)
    (buf1 buf2 : W8.t Array1152.t)
    (compare_result : W64.t) :
  decap_verify_value_flow
    buf1_flow buf2_flow buf1 buf2 compare_result =>
  (compare_result = W64.of_int 1 <=> buf1 <> buf2).
proof.
  move=> [_ [_ ->]].
  exact (verify_spec_neq_iff buf1 buf2).
qed.

lemma decap_verify_value_flow_mismatch_exists
    (buf1_flow buf2_flow : W8.t Array1152.t -> bool)
    (buf1 buf2 : W8.t Array1152.t)
    (compare_result : W64.t) :
  decap_verify_value_flow
    buf1_flow buf2_flow buf1 buf2 compare_result =>
  compare_result = W64.of_int 1 <=>
  exists k, 0 <= k < 1152 /\ buf1.[k] <> buf2.[k].
proof.
  move=> [_ [_ ->]].
  exact (verify_spec_mismatch_iff buf1 buf2).
qed.

lemma decap_verify_procedure_functional
    (buf1_flow buf2_flow : W8.t Array1152.t -> bool)
    (buf1 buf2 : W8.t Array1152.t)
    (compare_result : W64.t) :
  decap_verify_value_flow
    buf1_flow buf2_flow buf1 buf2 compare_result =>
  hoare [Verify.verify :
    arg = (buf1, buf2) ==> res = compare_result].
proof.
  move=> [_ [_ ->]].
  exact (verify_functional buf1 buf2).
qed.

lemma decap_verify_procedure_correct
    (buf1_flow buf2_flow : W8.t Array1152.t -> bool)
    (buf1 buf2 : W8.t Array1152.t)
    (compare_result : W64.t) :
  decap_verify_value_flow
    buf1_flow buf2_flow buf1 buf2 compare_result =>
  phoare [Verify.verify :
    arg = (buf1, buf2) ==> res = compare_result] = 1%r.
proof.
  move=> [_ [_ ->]].
  exact (verify_correct buf1 buf2).
qed.
