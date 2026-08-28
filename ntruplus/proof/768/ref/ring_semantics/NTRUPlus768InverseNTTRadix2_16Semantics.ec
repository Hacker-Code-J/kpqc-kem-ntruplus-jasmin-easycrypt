(* Semantic and executable endpoints for the third inverse NTT layer. *)
require import AllCore IntDiv List Ring StdBigop StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array768.
require import NTRUPlus768CyclotomicFactorization.
require import NTRUPlus768EvaluationSemantics.
require import NTRUPlus768TerminalRepresentation.
require import NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768ForwardNTTRadix3Semantics.
require import NTRUPlus768ForwardNTTRadix2_16Semantics.
require import NTRUPlus768ForwardNTTRadix2_8Semantics.
require import NTRUPlus768ForwardNTTRadix2_4Semantics.
require import NTRUPlus768NTTSchedule.
require import NTRUPlus768PolyBasemulAlgebra.
require import NTRUPlus768InvNTTRadix2_4.
require import NTRUPlus768InvNTTRadix2_4Algebra NTRUPlus768InvNTTRadix2_4Proof.
require import NTRUPlus768InvNTTRadix2_8.
require import NTRUPlus768InvNTTRadix2_8Algebra NTRUPlus768InvNTTRadix2_8Proof.
require import NTRUPlus768InvNTTRadix2_16.
require import NTRUPlus768InvNTTRadix2_16Algebra NTRUPlus768InvNTTRadix2_16Proof.
require import NTRUPlus768InverseNTTRadix2_4Semantics.
require import NTRUPlus768InverseNTTRadix2_8Recombination.
require import NTRUPlus768InverseNTTRadix2_8Semantics.
require import NTRUPlus768InverseNTTRadix2_16Recombination.

op doubled_thrice (p : NTRUPoly.poly) : NTRUPoly.poly =
  NTRUPoly.PolyComRing.( + ) (doubled_twice p) (doubled_twice p).

op invntt_radix2_16_semantics
    (p : NTRUPoly.poly) (output : W16.t Array768.t) : bool =
  forall b, 0 <= b < 24 =>
    factor_eqm 32 (8 * terminal_exp (4 * b))
      (doubled_thrice p)
      (segment_poly output (32 * b) 32).

lemma invntt_radix2_16_algebra_refines_invntt_radix2_8_semantics
    (p : NTRUPoly.poly) (input output : W16.t Array768.t) :
  invntt_radix2_8_semantics p input =>
  NTRUPlus768InvNTTRadix2_16Algebra.invntt_radix2_16_algebra input output =>
  invntt_radix2_16_semantics p output.
proof.
  move=> Hsem Halg.
  rewrite /invntt_radix2_16_semantics.
  move=> b Hb.
  have Hleft :=
    invntt_radix2_8_semantics_child_left p input b Hsem Hb.
  have Hright :=
    invntt_radix2_8_semantics_child_right p input b Hsem Hb.
  rewrite (invntt_radix2_16_output_segmentE input output b Hb Halg).
  rewrite (invntt_radix2_16_scaled_diff_polyE input (32 * b)
    (NTRUPlus768InvNTTRadix2_16Algebra.invntt_radix2_16_zeta_root b)).
  have HrootE :
      NTRUPlus768InverseNTTRadix2_16Recombination.polyC
        (lift_int
          (NTRUPlus768InvNTTRadix2_16Algebra.invntt_radix2_16_zeta_root b)) =
      root_poly (invntt_radix2_16_schedule_exp b).
  + rewrite /NTRUPlus768InvNTTRadix2_16Algebra.invntt_radix2_16_zeta_root.
    rewrite schedule_root_fieldE 1:(invntt_radix2_16_schedule_nonneg b Hb).
    done.
  rewrite HrootE.
  rewrite /doubled_thrice.
  have Hparent_exp :
      8 * terminal_exp (4 * b) =
      2 * (4 * terminal_exp (4 * b)).
  + ring.
  rewrite Hparent_exp.
  apply (invntt_radix2_16_recombine_factor_eqm
    (doubled_twice p)
    (segment_poly input (32 * b) 16)
    (segment_poly input (32 * b + 16) 16)
    (4 * terminal_exp (4 * b))
    (invntt_radix2_16_schedule_exp b)).
  + exact (invntt_radix2_16_child_exp_nonneg b Hb).
  + exact (invntt_radix2_16_schedule_nonneg b Hb).
  + exact (invntt_radix2_16_schedule_sumE b Hb).
  + exact Hleft.
  + exact Hright.
qed.

lemma invntt_radix2_16_spec_semantics
    (p : NTRUPoly.poly) (input : W16.t Array768.t) :
  invntt_radix2_8_semantics p input =>
  NTRUPlus768InvNTTRadix2_16Algebra.invntt_radix2_16_input_shape input =>
  invntt_radix2_16_semantics p
    (NTRUPlus768InvNTTRadix2_16Proof.invntt_radix2_16_spec input).
proof.
  move=> Hsem Hshape.
  apply (invntt_radix2_16_algebra_refines_invntt_radix2_8_semantics
    p input (NTRUPlus768InvNTTRadix2_16Proof.invntt_radix2_16_spec input)).
  + exact Hsem.
  exact (NTRUPlus768InvNTTRadix2_16Algebra.invntt_radix2_16_spec_algebra input Hshape).
qed.

lemma invntt_radix2_16_semantics_functional
    (p : NTRUPoly.poly) (rp0 : W16.t Array768.t) :
  invntt_radix2_8_semantics p rp0 =>
  NTRUPlus768InvNTTRadix2_16Algebra.invntt_radix2_16_input_shape rp0 =>
  hoare [NTRUPlus768InvNTTRadix2_16.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_16 :
    rp = rp0 ==> invntt_radix2_16_semantics p res].
proof.
  move=> Hsem Hshape.
  conseq
    (NTRUPlus768InvNTTRadix2_16Algebra.invntt_radix2_16_algebra_functional
      rp0 Hshape) => />.
  move=> result Halg.
  apply (invntt_radix2_16_algebra_refines_invntt_radix2_8_semantics p rp0 result).
  + exact Hsem.
  + exact Halg.
qed.

lemma invntt_radix2_16_correct_semantics
    (p : NTRUPoly.poly) (rp0 : W16.t Array768.t) :
  invntt_radix2_8_semantics p rp0 =>
  NTRUPlus768InvNTTRadix2_16Algebra.invntt_radix2_16_input_shape rp0 =>
  phoare [NTRUPlus768InvNTTRadix2_16.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_16 :
    rp = rp0 ==> invntt_radix2_16_semantics p res] = 1%r.
proof.
  move=> Hsem Hshape.
  have Hfunctional :
      hoare [NTRUPlus768InvNTTRadix2_16.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_16 :
        rp = rp0 ==> invntt_radix2_16_semantics p res].
  + apply invntt_radix2_16_semantics_functional.
    - exact Hsem.
    - exact Hshape.
  by conseq NTRUPlus768InvNTTRadix2_16Proof.invntt_radix2_16_lossless Hfunctional.
qed.
