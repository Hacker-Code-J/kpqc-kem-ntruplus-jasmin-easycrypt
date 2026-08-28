(* Semantic and executable endpoints for the fifth inverse NTT layer. *)
require import AllCore IntDiv List Ring StdBigop StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array768.
require import NTRUPlus768CyclotomicFactorization.
require import NTRUPlus768EvaluationSemantics.
require import NTRUPlus768TerminalRepresentation.
require import NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768ForwardNTTRadix3Semantics.
require import NTRUPlus768ForwardNTTRadix2_64Semantics.
require import NTRUPlus768ForwardNTTRadix2_32Semantics.
require import NTRUPlus768ForwardNTTRadix2_16Semantics.
require import NTRUPlus768ForwardNTTRadix2_8Semantics.
require import NTRUPlus768NTTSchedule.
require import NTRUPlus768PolyBasemulAlgebra.
require import NTRUPlus768InvNTTRadix2_16.
require import NTRUPlus768InvNTTRadix2_16Algebra NTRUPlus768InvNTTRadix2_16Proof.
require import NTRUPlus768InvNTTRadix2_32.
require import NTRUPlus768InvNTTRadix2_32Algebra NTRUPlus768InvNTTRadix2_32Proof.
require import NTRUPlus768InvNTTRadix2_64.
require import NTRUPlus768InvNTTRadix2_64Algebra NTRUPlus768InvNTTRadix2_64Proof.
require import NTRUPlus768InverseNTTRadix2_16Recombination.
require import NTRUPlus768InverseNTTRadix2_16Semantics.
require import NTRUPlus768InverseNTTRadix2_32Recombination.
require import NTRUPlus768InverseNTTRadix2_32Semantics.
require import NTRUPlus768InverseNTTRadix2_64Recombination.

op doubled_five_times (p : NTRUPoly.poly) : NTRUPoly.poly =
  NTRUPoly.PolyComRing.( + ) (doubled_four_times p) (doubled_four_times p).

op invntt_radix2_64_semantics
    (p : NTRUPoly.poly) (output : W16.t Array768.t) : bool =
  forall b, 0 <= b < 6 =>
    factor_eqm 128 (32 * terminal_exp (16 * b))
      (doubled_five_times p)
      (segment_poly output (128 * b) 128).

lemma invntt_radix2_64_algebra_refines_invntt_radix2_32_semantics
    (p : NTRUPoly.poly) (input output : W16.t Array768.t) :
  invntt_radix2_32_semantics p input =>
  NTRUPlus768InvNTTRadix2_64Algebra.invntt_radix2_64_algebra input output =>
  invntt_radix2_64_semantics p output.
proof.
  move=> Hsem Halg.
  rewrite /invntt_radix2_64_semantics.
  move=> b Hb.
  have Hleft :=
    invntt_radix2_32_semantics_child_left p input b Hsem Hb.
  have Hright :=
    invntt_radix2_32_semantics_child_right p input b Hsem Hb.
  rewrite (invntt_radix2_64_output_segmentE input output b Hb Halg).
  rewrite (invntt_radix2_64_scaled_diff_polyE input (128 * b)
    (NTRUPlus768InvNTTRadix2_64Algebra.invntt_radix2_64_zeta_root b)).
  have HrootE :
      NTRUPlus768InverseNTTRadix2_64Recombination.polyC
        (lift_int
          (NTRUPlus768InvNTTRadix2_64Algebra.invntt_radix2_64_zeta_root b)) =
      root_poly (invntt_radix2_64_schedule_exp b).
  + rewrite /NTRUPlus768InvNTTRadix2_64Algebra.invntt_radix2_64_zeta_root.
    rewrite schedule_root_fieldE 1:(invntt_radix2_64_schedule_nonneg b Hb).
    done.
  rewrite HrootE.
  rewrite /doubled_five_times.
  have Hparent_exp :
      32 * terminal_exp (16 * b) =
      2 * (16 * terminal_exp (16 * b)).
  + ring.
  rewrite Hparent_exp.
  apply (invntt_radix2_64_recombine_factor_eqm
    (doubled_four_times p)
    (segment_poly input (128 * b) 64)
    (segment_poly input (128 * b + 64) 64)
    (16 * terminal_exp (16 * b))
    (invntt_radix2_64_schedule_exp b)).
  + exact (invntt_radix2_64_child_exp_nonneg b Hb).
  + exact (invntt_radix2_64_schedule_nonneg b Hb).
  + exact (invntt_radix2_64_schedule_sumE b Hb).
  + exact Hleft.
  + exact Hright.
qed.

lemma invntt_radix2_64_spec_semantics
    (p : NTRUPoly.poly) (input : W16.t Array768.t) :
  invntt_radix2_32_semantics p input =>
  NTRUPlus768InvNTTRadix2_64Algebra.invntt_radix2_64_input_shape input =>
  invntt_radix2_64_semantics p
    (NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_spec input).
proof.
  move=> Hsem Hshape.
  apply (invntt_radix2_64_algebra_refines_invntt_radix2_32_semantics
    p input (NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_spec input)).
  + exact Hsem.
  exact (NTRUPlus768InvNTTRadix2_64Algebra.invntt_radix2_64_spec_algebra input Hshape).
qed.

lemma invntt_radix2_64_semantics_functional
    (p : NTRUPoly.poly) (rp0 : W16.t Array768.t) :
  invntt_radix2_32_semantics p rp0 =>
  NTRUPlus768InvNTTRadix2_64Algebra.invntt_radix2_64_input_shape rp0 =>
  hoare [NTRUPlus768InvNTTRadix2_64.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_64 :
    rp = rp0 ==> invntt_radix2_64_semantics p res].
proof.
  move=> Hsem Hshape.
  conseq
    (NTRUPlus768InvNTTRadix2_64Algebra.invntt_radix2_64_algebra_functional
      rp0 Hshape) => />.
  move=> result Halg.
  apply (invntt_radix2_64_algebra_refines_invntt_radix2_32_semantics p rp0 result).
  + exact Hsem.
  + exact Halg.
qed.

lemma invntt_radix2_64_correct_semantics
    (p : NTRUPoly.poly) (rp0 : W16.t Array768.t) :
  invntt_radix2_32_semantics p rp0 =>
  NTRUPlus768InvNTTRadix2_64Algebra.invntt_radix2_64_input_shape rp0 =>
  phoare [NTRUPlus768InvNTTRadix2_64.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_64 :
    rp = rp0 ==> invntt_radix2_64_semantics p res] = 1%r.
proof.
  move=> Hsem Hshape.
  have Hfunctional :
      hoare [NTRUPlus768InvNTTRadix2_64.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_64 :
        rp = rp0 ==> invntt_radix2_64_semantics p res].
  + apply invntt_radix2_64_semantics_functional.
    - exact Hsem.
    - exact Hshape.
  by conseq NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_lossless Hfunctional.
qed.
