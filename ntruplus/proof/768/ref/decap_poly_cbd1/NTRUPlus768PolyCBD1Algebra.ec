require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array192 Array768.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768Crepmod3Algebra.
require import NTRUPlus768PolySOTPDecodeAlgebra.
require import NTRUPlus768NTTStage1Algebra.

import Ring.IntID IntOrder.

(* Array-value specification of the NTRU+768 poly_cbd1 sampler.  The
   authoritative C implementation is checked and tested separately; this
   theory does not claim C-AST, pointer, or binary equivalence. *)

op poly_cbd1_bit (b : W8.t) (j : int) : int =
  NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_bit b j.

op poly_cbd1_head_bit (buf : W8.t Array192.t) (i j : int) : int =
  poly_cbd1_bit buf.[i] j.

op poly_cbd1_tail_bit (buf : W8.t Array192.t) (i j : int) : int =
  poly_cbd1_bit buf.[96 + i] j.

op poly_cbd1_coeff_int (buf : W8.t Array192.t) (k : int) : int =
  poly_cbd1_head_bit buf (k %/ 8) (k %% 8) -
  poly_cbd1_tail_bit buf (k %/ 8) (k %% 8).

op poly_cbd1_spec (buf : W8.t Array192.t) : W16.t Array768.t =
  Array768.init (fun k => W16.of_int (poly_cbd1_coeff_int buf k)).

op poly_cbd1_trit_output (r : W16.t Array768.t) : bool =
  forall k, 0 <= k < 768 =>
    NTRUPlus768Crepmod3Algebra.is_trit (coeff r.[k]).

lemma poly_cbd1_bit_bound (b : W8.t) (j : int) :
  0 <= poly_cbd1_bit b j < 2.
proof.
  exact
    (NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_bit_bound b j).
qed.

lemma poly_cbd1_coeff_int_range (buf : W8.t Array192.t) (k : int) :
  0 <= k < 768 =>
  -1 <= poly_cbd1_coeff_int buf k <= 1.
proof.
  move=> Hk.
  have Hhead := poly_cbd1_bit_bound buf.[k %/ 8] (k %% 8).
  have Htail := poly_cbd1_bit_bound buf.[96 + k %/ 8] (k %% 8).
  rewrite /poly_cbd1_coeff_int /poly_cbd1_head_bit /poly_cbd1_tail_bit.
  smt().
qed.

lemma poly_cbd1_spec_word (buf : W8.t Array192.t) (k : int) :
  0 <= k < 768 =>
  (poly_cbd1_spec buf).[k] = W16.of_int (poly_cbd1_coeff_int buf k).
proof. by move=> Hk; rewrite /poly_cbd1_spec Array768.initiE. qed.

lemma poly_cbd1_spec_coeff (buf : W8.t Array192.t) (k : int) :
  0 <= k < 768 =>
  coeff (poly_cbd1_spec buf).[k] = poly_cbd1_coeff_int buf k.
proof.
  move=> Hk.
  rewrite poly_cbd1_spec_word 1:Hk.
  apply NTRUPlus768Crepmod3Algebra.coeff_of_word_small.
  have Hrange := poly_cbd1_coeff_int_range buf k Hk.
  smt().
qed.

lemma poly_cbd1_coeff_layout
    (buf : W8.t Array192.t) (i j : int) :
  0 <= i < 96 =>
  0 <= j < 8 =>
  coeff (poly_cbd1_spec buf).[8 * i + j] =
    poly_cbd1_bit buf.[i] j - poly_cbd1_bit buf.[96 + i] j.
proof.
  move=> Hi Hj.
  rewrite poly_cbd1_spec_coeff 1:/#.
  rewrite /poly_cbd1_coeff_int /poly_cbd1_head_bit /poly_cbd1_tail_bit.
  have Hdiv : (8 * i + j) %/ 8 = i by smt().
  have Hmod : (8 * i + j) %% 8 = j by smt().
  by rewrite Hdiv Hmod.
qed.

lemma poly_cbd1_spec_trit_output (buf : W8.t Array192.t) :
  poly_cbd1_trit_output (poly_cbd1_spec buf).
proof.
  move=> k Hk.
  rewrite poly_cbd1_spec_coeff 1:Hk.
  have Hrange := poly_cbd1_coeff_int_range buf k Hk.
  rewrite /NTRUPlus768Crepmod3Algebra.is_trit.
  smt().
qed.

lemma poly_cbd1_spec_sotp_trit_input (buf : W8.t Array192.t) :
  NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_trit_input
    (poly_cbd1_spec buf).
proof.
  move=> k Hk.
  exact (poly_cbd1_spec_trit_output buf k Hk).
qed.

(* This is the exact range hypothesis consumed by the already-proved NTT
   algebra, making the value seam ready for the next milestone. *)
lemma poly_cbd1_spec_input_qrange (buf : W8.t Array192.t) :
  NTRUPlus768NTTStage1Algebra.input_qrange (poly_cbd1_spec buf).
proof.
  move=> k Hk.
  rewrite /NTRUPlus768BasemulAlgebra.in_qrange.
  rewrite poly_cbd1_spec_coeff 1:Hk.
  have Hrange := poly_cbd1_coeff_int_range buf k Hk.
  rewrite /NTRUPlus768BasemulAlgebra.q.
  smt().
qed.
