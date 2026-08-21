require import AllCore Distr.
from Jasmin require import JWord.

require import Array1152.
require import NTRUPlus768DecapFailProof.

(* Typed value-level composition for
     fail = poly_sotp_decode(...);
     fail |= verify(buf1, buf2, NTRUPLUS_POLYBYTES);
   The producer proof trees remain behind predicates to avoid reloading their
   full arithmetic dependencies together.  The explicit 0/1 encodings make
   the promoted OR and int8_t store lossless for this seam.  No C equivalence
   or shared-secret masking theorem is claimed. *)
op decap_fail_value_flow
    (decode_frontier : bool -> W8.t -> bool)
    (compare_frontier :
      W8.t Array1152.t -> W8.t Array1152.t -> bool -> W64.t -> bool)
    (decode_failed compare_failed : bool)
    (decode_fail_byte : W8.t)
    (buf1 buf2 : W8.t Array1152.t)
    (compare_result : W64.t)
    (final_fail : W8.t) : bool =
  decode_frontier decode_failed decode_fail_byte /\
  compare_frontier buf1 buf2 compare_failed compare_result /\
  decode_fail_byte = fail_byte decode_failed /\
  compare_result = fail_word compare_failed /\
  compare_failed = (buf1 <> buf2) /\
  final_fail = decap_fail_spec_bool decode_failed compare_failed.

lemma decap_fail_value_flow_intro
    (decode_frontier : bool -> W8.t -> bool)
    (compare_frontier :
      W8.t Array1152.t -> W8.t Array1152.t -> bool -> W64.t -> bool)
    (decode_failed : bool)
    (buf1 buf2 : W8.t Array1152.t) :
  decode_frontier decode_failed (fail_byte decode_failed) =>
  compare_frontier
    buf1 buf2 (buf1 <> buf2) (fail_word (buf1 <> buf2)) =>
  decap_fail_value_flow
    decode_frontier compare_frontier
    decode_failed (buf1 <> buf2)
    (fail_byte decode_failed) buf1 buf2
    (fail_word (buf1 <> buf2))
    (decap_fail_spec_bool decode_failed (buf1 <> buf2)).
proof. by rewrite /decap_fail_value_flow. qed.

lemma decap_fail_value_flow_decode_range
    (decode_frontier : bool -> W8.t -> bool)
    (compare_frontier :
      W8.t Array1152.t -> W8.t Array1152.t -> bool -> W64.t -> bool)
    (decode_failed compare_failed : bool)
    (decode_fail_byte : W8.t)
    (buf1 buf2 : W8.t Array1152.t)
    (compare_result : W64.t)
    (final_fail : W8.t) :
  decap_fail_value_flow
    decode_frontier compare_frontier decode_failed compare_failed
    decode_fail_byte buf1 buf2 compare_result final_fail =>
  decode_fail_byte = W8.of_int 0 \/ decode_fail_byte = W8.of_int 1.
proof.
  move=> [_ [_ [-> _]]].
  case decode_failed => /=; by rewrite /fail_byte.
qed.

lemma decap_fail_value_flow_compare_range
    (decode_frontier : bool -> W8.t -> bool)
    (compare_frontier :
      W8.t Array1152.t -> W8.t Array1152.t -> bool -> W64.t -> bool)
    (decode_failed compare_failed : bool)
    (decode_fail_byte : W8.t)
    (buf1 buf2 : W8.t Array1152.t)
    (compare_result : W64.t)
    (final_fail : W8.t) :
  decap_fail_value_flow
    decode_frontier compare_frontier decode_failed compare_failed
    decode_fail_byte buf1 buf2 compare_result final_fail =>
  compare_result = W64.of_int 0 \/ compare_result = W64.of_int 1.
proof.
  move=> [_ [_ [_ [-> _]]]].
  case compare_failed => /=; by rewrite /fail_word.
qed.

lemma decap_fail_value_flow_result_range
    (decode_frontier : bool -> W8.t -> bool)
    (compare_frontier :
      W8.t Array1152.t -> W8.t Array1152.t -> bool -> W64.t -> bool)
    (decode_failed compare_failed : bool)
    (decode_fail_byte : W8.t)
    (buf1 buf2 : W8.t Array1152.t)
    (compare_result : W64.t)
    (final_fail : W8.t) :
  decap_fail_value_flow
    decode_frontier compare_frontier decode_failed compare_failed
    decode_fail_byte buf1 buf2 compare_result final_fail =>
  final_fail = W8.of_int 0 \/ final_fail = W8.of_int 1.
proof.
  move=> [_ [_ [_ [_ [_ ->]]]]].
  exact (decap_fail_spec_range decode_failed compare_failed).
qed.

lemma decap_fail_value_flow_combined_fail
    (decode_frontier : bool -> W8.t -> bool)
    (compare_frontier :
      W8.t Array1152.t -> W8.t Array1152.t -> bool -> W64.t -> bool)
    (decode_failed compare_failed : bool)
    (decode_fail_byte : W8.t)
    (buf1 buf2 : W8.t Array1152.t)
    (compare_result : W64.t)
    (final_fail : W8.t) :
  decap_fail_value_flow
    decode_frontier compare_frontier decode_failed compare_failed
    decode_fail_byte buf1 buf2 compare_result final_fail =>
  final_fail = fail_byte (decode_failed \/ compare_failed).
proof.
  move=> [_ [_ [_ [_ [_ ->]]]]].
  by rewrite /decap_fail_spec_bool.
qed.

lemma decap_fail_value_flow_zero_iff
    (decode_frontier : bool -> W8.t -> bool)
    (compare_frontier :
      W8.t Array1152.t -> W8.t Array1152.t -> bool -> W64.t -> bool)
    (decode_failed compare_failed : bool)
    (decode_fail_byte : W8.t)
    (buf1 buf2 : W8.t Array1152.t)
    (compare_result : W64.t)
    (final_fail : W8.t) :
  decap_fail_value_flow
    decode_frontier compare_frontier decode_failed compare_failed
    decode_fail_byte buf1 buf2 compare_result final_fail =>
  (final_fail = W8.of_int 0 <=> ! decode_failed /\ buf1 = buf2).
proof.
  move=> [_ [_ [_ [_ [Hcompare ->]]]]].
  rewrite decap_fail_spec_zero_iff Hcompare.
  by smt().
qed.

lemma decap_fail_value_flow_one_iff
    (decode_frontier : bool -> W8.t -> bool)
    (compare_frontier :
      W8.t Array1152.t -> W8.t Array1152.t -> bool -> W64.t -> bool)
    (decode_failed compare_failed : bool)
    (decode_fail_byte : W8.t)
    (buf1 buf2 : W8.t Array1152.t)
    (compare_result : W64.t)
    (final_fail : W8.t) :
  decap_fail_value_flow
    decode_frontier compare_frontier decode_failed compare_failed
    decode_fail_byte buf1 buf2 compare_result final_fail =>
  (final_fail = W8.of_int 1 <=> decode_failed \/ buf1 <> buf2).
proof.
  move=> [_ [_ [_ [_ [Hcompare ->]]]]].
  rewrite decap_fail_spec_one_iff Hcompare.
  done.
qed.

lemma decap_fail_procedure_functional
    (decode_frontier : bool -> W8.t -> bool)
    (compare_frontier :
      W8.t Array1152.t -> W8.t Array1152.t -> bool -> W64.t -> bool)
    (decode_failed compare_failed : bool)
    (decode_fail_byte : W8.t)
    (buf1 buf2 : W8.t Array1152.t)
    (compare_result : W64.t)
    (final_fail : W8.t) :
  decap_fail_value_flow
    decode_frontier compare_frontier decode_failed compare_failed
    decode_fail_byte buf1 buf2 compare_result final_fail =>
  hoare [DecapFail.combine :
    arg = (decode_fail_byte, compare_result) ==> res = final_fail].
proof.
  move=> [_ [_ [-> [-> [_ ->]]]]].
  exact (decap_fail_functional decode_failed compare_failed).
qed.

lemma decap_fail_procedure_correct
    (decode_frontier : bool -> W8.t -> bool)
    (compare_frontier :
      W8.t Array1152.t -> W8.t Array1152.t -> bool -> W64.t -> bool)
    (decode_failed compare_failed : bool)
    (decode_fail_byte : W8.t)
    (buf1 buf2 : W8.t Array1152.t)
    (compare_result : W64.t)
    (final_fail : W8.t) :
  decap_fail_value_flow
    decode_frontier compare_frontier decode_failed compare_failed
    decode_fail_byte buf1 buf2 compare_result final_fail =>
  phoare [DecapFail.combine :
    arg = (decode_fail_byte, compare_result) ==> res = final_fail] = 1%r.
proof.
  move=> [_ [_ [-> [-> [_ ->]]]]].
  exact (decap_fail_correct decode_failed compare_failed).
qed.
