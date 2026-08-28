(* Forward NTT followed by inverse NTT is globally congruent to the input. *)
require import AllCore.
from Jasmin require import JWord.

require import Array768.
require import NTRUPlus768EvaluationSemantics.
require import NTRUPlus768NTTAlgebra.
require import NTRUPlus768NTTStage1Algebra.
require import NTRUPlus768InvNTTAlgebra.
require import NTRUPlus768InvNTTRadix2_4Algebra.
require import NTRUPlus768TerminalRepresentation.
require import NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768ForwardNTTSemantics.
require import NTRUPlus768InverseNTTSemantics.

op ntt_invntt_roundtrip_semantics
    (original output : W16.t Array768.t) : bool =
  eqm_global (input_poly original) (input_poly output).

lemma forward_ntt_spec_invntt_input_shape
    (input : W16.t Array768.t) :
  NTRUPlus768NTTStage1Algebra.input_qrange input =>
  NTRUPlus768InvNTTRadix2_4Algebra.qrange_input_shape
    (NTRUPlus768NTTAlgebra.forward_ntt_spec input).
proof.
  move=> Hinput.
  rewrite /NTRUPlus768InvNTTRadix2_4Algebra.qrange_input_shape.
  move=> j Hj.
  exact
    (NTRUPlus768NTTAlgebra.forward_ntt_centered_coeff_range
      input j Hinput Hj).
qed.

lemma ntt_invntt_spec_roundtrip
    (input : W16.t Array768.t) :
  NTRUPlus768NTTStage1Algebra.input_qrange input =>
  ntt_invntt_roundtrip_semantics input
    (NTRUPlus768InvNTTAlgebra.inverse_invntt_spec
      (NTRUPlus768NTTAlgebra.forward_ntt_spec input)).
proof.
  move=> Hinput.
  rewrite /ntt_invntt_roundtrip_semantics
          /NTRUPlus768InverseNTTSemantics.invntt_semantics.
  apply
    (NTRUPlus768InverseNTTSemantics.inverse_invntt_spec_semantics
      (input_poly input)
      (NTRUPlus768NTTAlgebra.forward_ntt_spec input)).
  + exact
      (NTRUPlus768ForwardNTTSemantics.forward_ntt_spec_terminal_represents
        input Hinput).
  exact (forward_ntt_spec_invntt_input_shape input Hinput).
qed.
