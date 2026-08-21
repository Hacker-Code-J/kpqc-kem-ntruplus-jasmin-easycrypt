require import AllCore.
from Jasmin require import JWord.

require import Array192 Array224 Array768.
require import NTRUPlus768PolyCBD1Algebra.

(* Keccak-free downstream interface for the already-verified hash_h frontier.
   [predecessor_flow] is intended to be instantiated with the preceding
   decap_hash_h value-flow predicate over the same [buf3_prefix].  Its function
   type enforces that the predicate is applied to this exact prefix. Keeping it
   abstract here avoids reloading the monolithic FIPS202 procedure proof while
   preserving the exact value passed to this boundary. *)

op hash_h_cbd1_input_from_prefix
    (buf3_prefix : W8.t Array224.t) : W8.t Array192.t =
  Array192.init (fun i => buf3_prefix.[32 + i]).

op decap_poly_cbd1_value_flow
    (predecessor_flow : W8.t Array224.t -> bool)
    (buf3_prefix : W8.t Array224.t)
    (cbd1_input : W8.t Array192.t)
    (r1 : W16.t Array768.t) : bool =
  predecessor_flow buf3_prefix /\
  cbd1_input = hash_h_cbd1_input_from_prefix buf3_prefix /\
  r1 = NTRUPlus768PolyCBD1Algebra.poly_cbd1_spec cbd1_input.

lemma hash_h_cbd1_input_is_tail
    (buf3_prefix : W8.t Array224.t) (i : int) :
  0 <= i < 192 =>
  (hash_h_cbd1_input_from_prefix buf3_prefix).[i] =
    buf3_prefix.[32 + i].
proof.
  move=> Hi.
  by rewrite /hash_h_cbd1_input_from_prefix Array192.initiE.
qed.

lemma hash_h_cbd1_input_first
    (buf3_prefix : W8.t Array224.t) :
  (hash_h_cbd1_input_from_prefix buf3_prefix).[0] = buf3_prefix.[32].
proof. exact (hash_h_cbd1_input_is_tail buf3_prefix 0 _). qed.

lemma hash_h_cbd1_input_last
    (buf3_prefix : W8.t Array224.t) :
  (hash_h_cbd1_input_from_prefix buf3_prefix).[191] = buf3_prefix.[223].
proof. exact (hash_h_cbd1_input_is_tail buf3_prefix 191 _). qed.

lemma hash_h_output_to_poly_cbd1_value_flow
    (predecessor_flow : W8.t Array224.t -> bool)
    (buf3_prefix : W8.t Array224.t) :
  predecessor_flow buf3_prefix =>
  decap_poly_cbd1_value_flow
    predecessor_flow
    buf3_prefix
    (hash_h_cbd1_input_from_prefix buf3_prefix)
    (NTRUPlus768PolyCBD1Algebra.poly_cbd1_spec
      (hash_h_cbd1_input_from_prefix buf3_prefix)).
proof. by move=> Hflow; rewrite /decap_poly_cbd1_value_flow. qed.

(* Generic terminal composition theorem.  Instantiating [predecessor_flow]
   with the existing decap_hash_h predicate retains its concrete SHAKE256
   meaning and the equality for this same [buf3_prefix]. *)
lemma decap_terminal_poly_cbd1_value_flow
    (predecessor_flow : W8.t Array224.t -> bool)
    (buf3_prefix : W8.t Array224.t) :
  predecessor_flow buf3_prefix =>
  decap_poly_cbd1_value_flow
    predecessor_flow
    buf3_prefix
    (hash_h_cbd1_input_from_prefix buf3_prefix)
    (NTRUPlus768PolyCBD1Algebra.poly_cbd1_spec
      (hash_h_cbd1_input_from_prefix buf3_prefix)).
proof. exact (hash_h_output_to_poly_cbd1_value_flow predecessor_flow buf3_prefix). qed.

lemma decap_poly_cbd1_r1_trit_output
    (predecessor_flow : W8.t Array224.t -> bool)
    (buf3_prefix : W8.t Array224.t)
    (cbd1_input : W8.t Array192.t)
    (r1 : W16.t Array768.t) :
  decap_poly_cbd1_value_flow
    predecessor_flow buf3_prefix cbd1_input r1 =>
  NTRUPlus768PolyCBD1Algebra.poly_cbd1_trit_output r1.
proof.
  rewrite /decap_poly_cbd1_value_flow.
  move=> [_ [_ ->]].
  exact (NTRUPlus768PolyCBD1Algebra.poly_cbd1_spec_trit_output cbd1_input).
qed.

lemma decap_poly_cbd1_r1_input_qrange
    (predecessor_flow : W8.t Array224.t -> bool)
    (buf3_prefix : W8.t Array224.t)
    (cbd1_input : W8.t Array192.t)
    (r1 : W16.t Array768.t) :
  decap_poly_cbd1_value_flow
    predecessor_flow buf3_prefix cbd1_input r1 =>
  NTRUPlus768NTTStage1Algebra.input_qrange r1.
proof.
  rewrite /decap_poly_cbd1_value_flow.
  move=> [_ [_ ->]].
  exact (NTRUPlus768PolyCBD1Algebra.poly_cbd1_spec_input_qrange cbd1_input).
qed.

(* The predecessor failure theorem proves equality of the complete hash_h
   output against the zero-prefix case.  This congruence lemma transports that
   equality through the tail projection and deterministic sampler. *)
lemma poly_cbd1_preserves_hash_output_equality
    (buf3_1 buf3_2 : W8.t Array224.t) :
  buf3_1 = buf3_2 =>
  NTRUPlus768PolyCBD1Algebra.poly_cbd1_spec
    (hash_h_cbd1_input_from_prefix buf3_1) =
  NTRUPlus768PolyCBD1Algebra.poly_cbd1_spec
    (hash_h_cbd1_input_from_prefix buf3_2).
proof. by move=> ->. qed.
