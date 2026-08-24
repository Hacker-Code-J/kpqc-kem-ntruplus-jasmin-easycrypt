require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord.

require import Array4.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768BaseInvAlgebra.
require import NTRUPlus768FqInvAlgebra.

(* Pure mathematical corollary.  This does not connect the current C
   baseinv return code or intermediate words to inverse_determinant. *)

lemma determinant_power_witness
    (a : W16.t Array4.t) (z : int) :
  inverse_determinant a z %% q <> 0 =>
  determinant_inverse_witness
    a z (exp (inverse_determinant a z) 3455).
proof.
  move=> Hnonzero.
  rewrite /determinant_inverse_witness.
  have He : 3455 = 3455 by done.
  exact (NTRUPlus768FqInvPrime.pow_qminus2_inverse
    (inverse_determinant a z) 3455 He Hnonzero).
qed.

lemma baseinv_math_spec_nonzero_block_inverse
    (a : W16.t Array4.t) (z : int) :
  inverse_determinant a z %% q <> 0 =>
  block_inverse_qring a
    (baseinv_math_spec
      a z (exp (inverse_determinant a z) 3455)) z.
proof.
  move=> Hnonzero.
  exact (baseinv_math_spec_block_inverse
    a z (exp (inverse_determinant a z) 3455)
    (determinant_power_witness a z Hnonzero)).
qed.
