require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array96 Array192 Array768.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768Crepmod3Algebra.

import Ring.IntID IntOrder.

(* This file fixes the exact array-value meaning of poly_sotp_decode.
   It does not claim a C/Jasmin procedure proof, pointer/alias model,
   or an encode/decode inverse theorem. *)

op poly_sotp_bit (b : W8.t) (j : int) : int =
  (W8.to_uint b %/ 2 ^ j) %% 2.

op poly_sotp_head_bit (buf : W8.t Array192.t) (i j : int) : int =
  poly_sotp_bit buf.[i] j.

op poly_sotp_tail_bit (buf : W8.t Array192.t) (i j : int) : int =
  poly_sotp_bit buf.[96 + i] j.

op poly_sotp_sum_int
    (a : W16.t Array768.t) (buf : W8.t Array192.t) (i j : int) : int =
  coeff a.[8 * i + j] + poly_sotp_tail_bit buf i j.

op poly_sotp_sum_valid
    (a : W16.t Array768.t) (buf : W8.t Array192.t) (i j : int) : bool =
  poly_sotp_sum_int a buf i j = 0 \/ poly_sotp_sum_int a buf i j = 1.

op poly_sotp_trit_input (a : W16.t Array768.t) : bool =
  forall k, 0 <= k < 768 => NTRUPlus768Crepmod3Algebra.is_trit (coeff a.[k]).

op poly_sotp_decoded_bit_int
    (a : W16.t Array768.t) (buf : W8.t Array192.t) (i j : int) : int =
  (poly_sotp_sum_int a buf i j + poly_sotp_head_bit buf i j) %% 2.

op poly_sotp_raw_byte_int
    (a : W16.t Array768.t) (buf : W8.t Array192.t) (i : int) : int =
  poly_sotp_decoded_bit_int a buf i 0 +
  2 * poly_sotp_decoded_bit_int a buf i 1 +
  4 * poly_sotp_decoded_bit_int a buf i 2 +
  8 * poly_sotp_decoded_bit_int a buf i 3 +
  16 * poly_sotp_decoded_bit_int a buf i 4 +
  32 * poly_sotp_decoded_bit_int a buf i 5 +
  64 * poly_sotp_decoded_bit_int a buf i 6 +
  128 * poly_sotp_decoded_bit_int a buf i 7.

op poly_sotp_raw_msg_spec
    (a : W16.t Array768.t) (buf : W8.t Array192.t) : W8.t Array96.t =
  Array96.init (fun i => W8.of_int (poly_sotp_raw_byte_int a buf i)).

op poly_sotp_decode_fail_spec
    (a : W16.t Array768.t) (buf : W8.t Array192.t) : bool =
  exists i j,
    0 <= i < 96 /\ 0 <= j < 8 /\ ! poly_sotp_sum_valid a buf i j.

op poly_sotp_zero_msg_spec : W8.t Array96.t =
  Array96.init (fun _ => W8.zero).

op poly_sotp_decode_msg_spec
    (a : W16.t Array768.t) (buf : W8.t Array192.t) : W8.t Array96.t =
  if poly_sotp_decode_fail_spec a buf then
    poly_sotp_zero_msg_spec
  else
    poly_sotp_raw_msg_spec a buf.

op poly_sotp_decode_spec
    (a : W16.t Array768.t) (buf : W8.t Array192.t) : W8.t Array96.t * bool =
  (poly_sotp_decode_msg_spec a buf, poly_sotp_decode_fail_spec a buf).

lemma poly_sotp_bit_bound (b : W8.t) (j : int) :
  0 <= poly_sotp_bit b j < 2.
proof.
  rewrite /poly_sotp_bit.
  have Huint := W8.to_uint_cmp b.
  smt().
qed.

lemma poly_sotp_head_bit_bound
    (buf : W8.t Array192.t) (i j : int) :
  0 <= i < 96 =>
  0 <= poly_sotp_head_bit buf i j < 2.
proof.
  move=> _.
  exact (poly_sotp_bit_bound buf.[i] j).
qed.

lemma poly_sotp_tail_bit_bound
    (buf : W8.t Array192.t) (i j : int) :
  0 <= i < 96 =>
  0 <= poly_sotp_tail_bit buf i j < 2.
proof.
  move=> Hi.
  exact (poly_sotp_bit_bound buf.[96 + i] j).
qed.

lemma poly_sotp_decoded_bit_bound
    (a : W16.t Array768.t) (buf : W8.t Array192.t) (i j : int) :
  0 <= i < 96 =>
  0 <= poly_sotp_decoded_bit_int a buf i j < 2.
proof.
  move=> _.
  rewrite /poly_sotp_decoded_bit_int.
  smt().
qed.

lemma poly_sotp_raw_byte_int_range
    (a : W16.t Array768.t) (buf : W8.t Array192.t) (i : int) :
  0 <= i < 96 =>
  0 <= poly_sotp_raw_byte_int a buf i < 256.
proof.
  move=> Hi.
  have H0 := poly_sotp_decoded_bit_bound a buf i 0 Hi.
  have H1 := poly_sotp_decoded_bit_bound a buf i 1 Hi.
  have H2 := poly_sotp_decoded_bit_bound a buf i 2 Hi.
  have H3 := poly_sotp_decoded_bit_bound a buf i 3 Hi.
  have H4 := poly_sotp_decoded_bit_bound a buf i 4 Hi.
  have H5 := poly_sotp_decoded_bit_bound a buf i 5 Hi.
  have H6 := poly_sotp_decoded_bit_bound a buf i 6 Hi.
  have H7 := poly_sotp_decoded_bit_bound a buf i 7 Hi.
  rewrite /poly_sotp_raw_byte_int.
  smt().
qed.

lemma poly_sotp_trit_sum_range
    (a : W16.t Array768.t) (buf : W8.t Array192.t) (i j : int) :
  poly_sotp_trit_input a =>
  0 <= i < 96 =>
  0 <= j < 8 =>
  -1 <= poly_sotp_sum_int a buf i j <= 2.
proof.
  move=> Htrit Hi Hj.
  have Hcoeff :=
    Htrit (8 * i + j) _.
  + smt().
  have Hbit := poly_sotp_tail_bit_bound buf i j Hi.
  rewrite /poly_sotp_sum_int.
  move: Hcoeff.
  rewrite /NTRUPlus768Crepmod3Algebra.is_trit.
  smt().
qed.

lemma poly_sotp_decode_fail_spec_iff
    (a : W16.t Array768.t) (buf : W8.t Array192.t) :
  poly_sotp_decode_fail_spec a buf <=>
  exists i j,
    0 <= i < 96 /\ 0 <= j < 8 /\ ! poly_sotp_sum_valid a buf i j.
proof. by rewrite /poly_sotp_decode_fail_spec. qed.

lemma poly_sotp_decode_success_valid
    (a : W16.t Array768.t) (buf : W8.t Array192.t) :
  ! poly_sotp_decode_fail_spec a buf <=>
  (forall i j, 0 <= i < 96 => 0 <= j < 8 => poly_sotp_sum_valid a buf i j).
proof.
  rewrite /poly_sotp_decode_fail_spec.
  smt().
qed.

lemma poly_sotp_decode_success_raw
    (a : W16.t Array768.t) (buf : W8.t Array192.t) :
  ! poly_sotp_decode_fail_spec a buf =>
  poly_sotp_decode_msg_spec a buf = poly_sotp_raw_msg_spec a buf.
proof.
  move=> Hsuccess.
  rewrite /poly_sotp_decode_msg_spec.
  case (poly_sotp_decode_fail_spec a buf) => Hfail; first smt().
  done.
qed.

lemma poly_sotp_decode_failure_zero
    (a : W16.t Array768.t) (buf : W8.t Array192.t) :
  poly_sotp_decode_fail_spec a buf =>
  poly_sotp_decode_msg_spec a buf = poly_sotp_zero_msg_spec.
proof.
  move=> Hfail.
  rewrite /poly_sotp_decode_msg_spec.
  case (poly_sotp_decode_fail_spec a buf) => Hcase; first done.
  smt().
qed.

lemma poly_sotp_decode_spec_fst
    (a : W16.t Array768.t) (buf : W8.t Array192.t) :
  (poly_sotp_decode_spec a buf).`1 = poly_sotp_decode_msg_spec a buf.
proof. by rewrite /poly_sotp_decode_spec. qed.

lemma poly_sotp_decode_spec_snd
    (a : W16.t Array768.t) (buf : W8.t Array192.t) :
  (poly_sotp_decode_spec a buf).`2 = poly_sotp_decode_fail_spec a buf.
proof. by rewrite /poly_sotp_decode_spec. qed.
