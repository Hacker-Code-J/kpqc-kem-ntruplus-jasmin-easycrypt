require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array96 Array192 Array768.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768Crepmod3Algebra.
require import NTRUPlus768PolyCBD1Algebra.
require import NTRUPlus768PolySOTPDecodeAlgebra.

import Ring.IntID IntOrder.

(* Exact value specification of poly_sotp_encode.  This theory only models
   the Array96/Array192 layout that feeds poly_cbd1; it does not claim a
   C/Jasmin procedure proof or any downstream KEM relation. *)

op poly_sotp_encode_input
    (msg : W8.t Array96.t)
    (pad : W8.t Array192.t) : W8.t Array192.t =
  Array192.init
    (fun k =>
      if 0 <= k < 96 then
        pad.[k] +^ msg.[k]
      else
        pad.[k]).

op poly_sotp_encode_spec
    (msg : W8.t Array96.t)
    (pad : W8.t Array192.t) : W16.t Array768.t =
  NTRUPlus768PolyCBD1Algebra.poly_cbd1_spec
    (poly_sotp_encode_input msg pad).

lemma poly_sotp_bit_b2i (b : W8.t) (j : int) :
  0 <= j < 8 =>
  NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_bit b j = b2i b.[j].
proof.
  move=> Hj.
  rewrite /NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_bit.
  by rewrite -W8.b2i_get 1:/#.
qed.

lemma poly_sotp_encode_input_head_byte
    (msg : W8.t Array96.t)
    (pad : W8.t Array192.t)
    (i : int) :
  0 <= i < 96 =>
  (poly_sotp_encode_input msg pad).[i] = pad.[i] +^ msg.[i].
proof.
  move=> Hi.
  rewrite /poly_sotp_encode_input Array192.initiE 1:/#.
  by smt().
qed.

lemma poly_sotp_encode_input_tail_byte
    (msg : W8.t Array96.t)
    (pad : W8.t Array192.t)
    (i : int) :
  0 <= i < 96 =>
  (poly_sotp_encode_input msg pad).[96 + i] = pad.[96 + i].
proof.
  move=> Hi.
  rewrite /poly_sotp_encode_input Array192.initiE 1:/#.
  by smt().
qed.

lemma poly_sotp_encode_input_head_bit
    (msg : W8.t Array96.t)
    (pad : W8.t Array192.t)
    (i j : int) :
  0 <= i < 96 =>
  0 <= j < 8 =>
  NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_bit
    (poly_sotp_encode_input msg pad).[i] j =
  b2i (Bool.(^^) pad.[i].[j] msg.[i].[j]).
proof.
  move=> Hi Hj.
  rewrite poly_sotp_encode_input_head_byte 1:Hi.
  rewrite poly_sotp_bit_b2i 1:Hj.
  by rewrite W8.xorwE.
qed.

lemma poly_sotp_encode_input_tail_bit
    (msg : W8.t Array96.t)
    (pad : W8.t Array192.t)
    (i j : int) :
  0 <= i < 96 =>
  0 <= j < 8 =>
  NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_bit
    (poly_sotp_encode_input msg pad).[96 + i] j =
  NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_bit pad.[96 + i] j.
proof.
  move=> Hi Hj.
  rewrite poly_sotp_encode_input_tail_byte 1:Hi.
  done.
qed.

lemma poly_sotp_encode_spec_coeff
    (msg : W8.t Array96.t)
    (pad : W8.t Array192.t)
    (i j : int) :
  0 <= i < 96 =>
  0 <= j < 8 =>
  coeff (poly_sotp_encode_spec msg pad).[8 * i + j] =
    NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_bit
      ((pad.[i] +^ msg.[i])) j -
    NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_bit
      pad.[96 + i] j.
proof.
  move=> Hi Hj.
  rewrite /poly_sotp_encode_spec.
  rewrite NTRUPlus768PolyCBD1Algebra.poly_cbd1_coeff_layout 1:Hi 1:Hj.
  rewrite poly_sotp_encode_input_head_byte 1:Hi.
  rewrite poly_sotp_encode_input_tail_byte 1:Hi.
  done.
qed.

lemma poly_sotp_encode_sum_int_xor
    (msg : W8.t Array96.t)
    (pad : W8.t Array192.t)
    (i j : int) :
  0 <= i < 96 =>
  0 <= j < 8 =>
  NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_sum_int
    (poly_sotp_encode_spec msg pad) pad i j =
  b2i (Bool.(^^) pad.[i].[j] msg.[i].[j]).
proof.
  move=> Hi Hj.
  rewrite /NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_sum_int.
  rewrite poly_sotp_encode_spec_coeff 1:Hi 1:Hj.
  rewrite /NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_tail_bit.
  rewrite poly_sotp_bit_b2i 1:Hj W8.xorwE.
  ring.
qed.

lemma poly_sotp_encode_sum_valid
    (msg : W8.t Array96.t)
    (pad : W8.t Array192.t)
    (i j : int) :
  0 <= i < 96 =>
  0 <= j < 8 =>
  NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_sum_valid
    (poly_sotp_encode_spec msg pad) pad i j.
proof.
  move=> Hi Hj.
  rewrite /NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_sum_valid.
  rewrite poly_sotp_encode_sum_int_xor 1:Hi 1:Hj.
  case (pad.[i].[j]); case (msg.[i].[j]); rewrite /b2i /=; auto.
qed.

lemma poly_sotp_encode_fail_spec
    (msg : W8.t Array96.t)
    (pad : W8.t Array192.t) :
  ! NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_decode_fail_spec
      (poly_sotp_encode_spec msg pad) pad.
proof.
  rewrite NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_decode_success_valid.
  move=> i j Hi Hj.
  exact (poly_sotp_encode_sum_valid msg pad i j Hi Hj).
qed.

lemma poly_sotp_encode_fail_spec_false
    (msg : W8.t Array96.t)
    (pad : W8.t Array192.t) :
  NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_decode_fail_spec
    (poly_sotp_encode_spec msg pad) pad = false.
proof.
  move: (poly_sotp_encode_fail_spec msg pad).
  case
    (NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_decode_fail_spec
      (poly_sotp_encode_spec msg pad) pad); smt().
qed.
