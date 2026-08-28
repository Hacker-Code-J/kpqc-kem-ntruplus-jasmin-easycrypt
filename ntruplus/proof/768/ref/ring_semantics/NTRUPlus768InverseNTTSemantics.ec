(* Global polynomial semantics for the full inverse NTT wrapper. *)
require import AllCore IntDiv List Ring StdBigop StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array768.
require import NTRUPlus768CyclotomicFactorization.
require import NTRUPlus768EvaluationSemantics.
require import NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768TerminalRepresentation.
require import NTRUPlus768InvNTT.
require import NTRUPlus768InvNTTAlgebra NTRUPlus768InvNTTProof.
require import NTRUPlus768InvNTTRadix2_4Algebra.
require import NTRUPlus768InverseNTTRadix2_4Semantics.
require import NTRUPlus768InverseNTTRadix2_8Semantics.
require import NTRUPlus768InverseNTTRadix2_16Semantics.
require import NTRUPlus768InverseNTTRadix2_32Semantics.
require import NTRUPlus768InverseNTTRadix2_64Semantics.
require import NTRUPlus768InverseNTTRadix3Semantics.
require import NTRUPlus768InverseNTTFinalSemantics.

op invntt_semantics
    (p : NTRUPoly.poly) (output : W16.t Array768.t) : bool =
  eqm_global p (input_poly output).

lemma inverse_invntt_algebra_refines_terminal_representation
    (p : NTRUPoly.poly) (input output : W16.t Array768.t) :
  terminal_represents input p =>
  NTRUPlus768InvNTTAlgebra.inverse_invntt_algebra input output =>
  invntt_semantics p output.
proof.
  move=> Hrep Halg.
  rewrite /NTRUPlus768InvNTTAlgebra.inverse_invntt_algebra in Halg.
  move: Halg => [_ [Hradix2_4 [Hradix2_8 [Hradix2_16 [Hradix2_32
      [Hradix2_64 [Hradix3 [Hfinal _]]]]]]]].
  have Hradix2_4_sem :
      NTRUPlus768InverseNTTRadix2_4Semantics.invntt_radix2_4_semantics p
        (NTRUPlus768InvNTTAlgebra.inverse_radix2_4_spec input).
  + exact
      (NTRUPlus768InverseNTTRadix2_4Semantics
         .invntt_radix2_4_algebra_refines_terminal_representation
         p input
         (NTRUPlus768InvNTTAlgebra.inverse_radix2_4_spec input)
         Hrep Hradix2_4).
  have Hradix2_8_sem :
      NTRUPlus768InverseNTTRadix2_8Semantics.invntt_radix2_8_semantics p
        (NTRUPlus768InvNTTAlgebra.inverse_radix2_8_spec input).
  + exact
      (NTRUPlus768InverseNTTRadix2_8Semantics
         .invntt_radix2_8_algebra_refines_invntt_radix2_4_semantics
         p
         (NTRUPlus768InvNTTAlgebra.inverse_radix2_4_spec input)
         (NTRUPlus768InvNTTAlgebra.inverse_radix2_8_spec input)
         Hradix2_4_sem Hradix2_8).
  have Hradix2_16_sem :
      NTRUPlus768InverseNTTRadix2_16Semantics.invntt_radix2_16_semantics p
        (NTRUPlus768InvNTTAlgebra.inverse_radix2_16_spec input).
  + exact
      (NTRUPlus768InverseNTTRadix2_16Semantics
         .invntt_radix2_16_algebra_refines_invntt_radix2_8_semantics
         p
         (NTRUPlus768InvNTTAlgebra.inverse_radix2_8_spec input)
         (NTRUPlus768InvNTTAlgebra.inverse_radix2_16_spec input)
         Hradix2_8_sem Hradix2_16).
  have Hradix2_32_sem :
      NTRUPlus768InverseNTTRadix2_32Semantics.invntt_radix2_32_semantics p
        (NTRUPlus768InvNTTAlgebra.inverse_radix2_32_spec input).
  + exact
      (NTRUPlus768InverseNTTRadix2_32Semantics
         .invntt_radix2_32_algebra_refines_invntt_radix2_16_semantics
         p
         (NTRUPlus768InvNTTAlgebra.inverse_radix2_16_spec input)
         (NTRUPlus768InvNTTAlgebra.inverse_radix2_32_spec input)
         Hradix2_16_sem Hradix2_32).
  have Hradix2_64_sem :
      NTRUPlus768InverseNTTRadix2_64Semantics.invntt_radix2_64_semantics p
        (NTRUPlus768InvNTTAlgebra.inverse_radix2_64_spec input).
  + exact
      (NTRUPlus768InverseNTTRadix2_64Semantics
         .invntt_radix2_64_algebra_refines_invntt_radix2_32_semantics
         p
         (NTRUPlus768InvNTTAlgebra.inverse_radix2_32_spec input)
         (NTRUPlus768InvNTTAlgebra.inverse_radix2_64_spec input)
         Hradix2_32_sem Hradix2_64).
  have Hradix3_sem :
      NTRUPlus768InverseNTTRadix3Semantics.invntt_radix3_semantics p
        (NTRUPlus768InvNTTAlgebra.inverse_radix3_spec input).
  + exact
      (NTRUPlus768InverseNTTRadix3Semantics
         .invntt_radix3_algebra_refines_invntt_radix2_64_semantics
         p
         (NTRUPlus768InvNTTAlgebra.inverse_radix2_64_spec input)
         (NTRUPlus768InvNTTAlgebra.inverse_radix3_spec input)
         Hradix2_64_sem Hradix3).
  exact
    (NTRUPlus768InverseNTTFinalSemantics
       .invntt_final_algebra_refines_invntt_radix3_semantics
       p
       (NTRUPlus768InvNTTAlgebra.inverse_radix3_spec input)
       output Hradix3_sem Hfinal).
qed.

lemma inverse_invntt_spec_semantics
    (p : NTRUPoly.poly) (input : W16.t Array768.t) :
  terminal_represents input p =>
  NTRUPlus768InvNTTRadix2_4Algebra.qrange_input_shape input =>
  invntt_semantics p (NTRUPlus768InvNTTAlgebra.inverse_invntt_spec input).
proof.
  move=> Hrep Hshape.
  apply (inverse_invntt_algebra_refines_terminal_representation
    p input (NTRUPlus768InvNTTAlgebra.inverse_invntt_spec input)).
  + exact Hrep.
  exact (NTRUPlus768InvNTTAlgebra.inverse_invntt_spec_algebra input Hshape).
qed.

lemma invntt_semantics_functional
    (p : NTRUPoly.poly) (rp0 ap0 : W16.t Array768.t) :
  terminal_represents ap0 p =>
  NTRUPlus768InvNTTRadix2_4Algebra.qrange_input_shape ap0 =>
  hoare [NTRUPlus768InvNTT.M.jade_ntruplus_ntruplus768_amd64_ref_invntt :
    rp = rp0 /\ ap = ap0 ==> invntt_semantics p res].
proof.
  move=> Hrep Hshape.
  conseq (NTRUPlus768InvNTTProof.invntt_functional rp0 ap0) => /> &hr Hap.
  rewrite Hap NTRUPlus768InvNTTAlgebra.invntt_specE.
  exact (inverse_invntt_spec_semantics p ap0 Hrep Hshape).
qed.

lemma invntt_correct_semantics
    (p : NTRUPoly.poly) (rp0 ap0 : W16.t Array768.t) :
  terminal_represents ap0 p =>
  NTRUPlus768InvNTTRadix2_4Algebra.qrange_input_shape ap0 =>
  phoare [NTRUPlus768InvNTT.M.jade_ntruplus_ntruplus768_amd64_ref_invntt :
    rp = rp0 /\ ap = ap0 ==> invntt_semantics p res] = 1%r.
proof.
  move=> Hrep Hshape.
  have Hfunctional :
      hoare [NTRUPlus768InvNTT.M.jade_ntruplus_ntruplus768_amd64_ref_invntt :
        rp = rp0 /\ ap = ap0 ==> invntt_semantics p res].
  + exact (invntt_semantics_functional p rp0 ap0 Hrep Hshape).
  by conseq NTRUPlus768InvNTTProof.invntt_lossless Hfunctional.
qed.
