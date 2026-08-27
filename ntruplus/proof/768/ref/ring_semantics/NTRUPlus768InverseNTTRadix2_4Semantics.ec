(* Semantic and executable endpoints for the first inverse NTT layer. *)
require import AllCore IntDiv List Ring StdBigop StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array768.
require import NTRUPlus768CyclotomicFactorization.
require import NTRUPlus768EvaluationSemantics.
require import NTRUPlus768TerminalRepresentation.
require import NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768ForwardNTTRadix3Semantics.
require import NTRUPlus768ForwardNTTRadix2_4Semantics.
require import NTRUPlus768NTTSchedule.
require import NTRUPlus768PolyBasemulAlgebra.
require import NTRUPlus768InvNTTRadix2_4.
require import NTRUPlus768InvNTTRadix2_4Algebra NTRUPlus768InvNTTRadix2_4Proof.
require import NTRUPlus768InverseNTTRadix2_4Recombination.

op invntt_radix2_4_semantics
    (p : NTRUPoly.poly) (output : W16.t Array768.t) : bool =
  forall b, 0 <= b < 96 =>
    factor_eqm 8 (2 * terminal_exp b)
      (NTRUPoly.PolyComRing.( + ) p p)
      (segment_poly output (8 * b) 8).

lemma invntt_radix2_4_algebra_refines_terminal_representation
    (p : NTRUPoly.poly) (input output : W16.t Array768.t) :
  terminal_represents input p =>
  NTRUPlus768InvNTTRadix2_4Algebra.invntt_radix2_4_algebra input output =>
  invntt_radix2_4_semantics p output.
proof.
  move=> Hrep Halg.
  rewrite /invntt_radix2_4_semantics.
  move=> b Hb.
  have Hleft :=
    terminal_represents_factor_eqm_left input p b Hrep Hb.
  have Hright :=
    terminal_represents_factor_eqm_right input p b Hrep Hb.
  rewrite (invntt_radix2_4_output_segmentE input output b Hb Halg).
  rewrite (invntt_radix2_4_scaled_diff_polyE input (8 * b)
    (NTRUPlus768InvNTTRadix2_4Algebra.invntt_radix2_4_zeta_root b)).
  rewrite /radix2_4_eval_poly /root_poly.
  have Hroot0 :
      CycloFq.exp zeta_field 0 = CycloFq.one
    by rewrite zeta_field_expE 1:// /=.
  rewrite Hroot0.
  have Hone :
      NTRUPoly.polyC CycloFq.one = NTRUPoly.PolyComRing.oner by done.
  rewrite Hone.
  have Hshape :
      NTRUPoly.PolyComRing.( * )
        (segment_poly input (8 * b + 4) 4)
        NTRUPlus768InverseNTTRadix2_4Recombination.poly1 =
      segment_poly input (8 * b + 4) 4.
  + exact
      (NTRUPoly.PolyComRing.mulr1
        (segment_poly input (8 * b + 4) 4)).
  rewrite Hshape.
  have HrootE :
      NTRUPoly.polyC (lift_int
        (NTRUPlus768InvNTTRadix2_4Algebra.invntt_radix2_4_zeta_root b)) =
      root_poly (invntt_radix2_4_schedule_exp b).
  + rewrite /NTRUPlus768InvNTTRadix2_4Algebra.invntt_radix2_4_zeta_root.
    rewrite schedule_root_fieldE 1:(invntt_radix2_4_schedule_nonneg b Hb).
    done.
  rewrite HrootE.
  apply (invntt_radix2_4_recombine_factor_eqm
    p
    (segment_poly input (8 * b) 4)
    (segment_poly input (8 * b + 4) 4)
    (terminal_exp b)
    (invntt_radix2_4_schedule_exp b)).
  + exact (terminal_exp_nonneg b Hb).
  + exact (invntt_radix2_4_schedule_nonneg b Hb).
  + exact (invntt_radix2_4_schedule_sumE b Hb).
  + exact Hleft.
  + exact Hright.
qed.

lemma invntt_radix2_4_spec_semantics
    (p : NTRUPoly.poly) (input : W16.t Array768.t) :
  terminal_represents input p =>
  NTRUPlus768InvNTTRadix2_4Algebra.qrange_input_shape input =>
  invntt_radix2_4_semantics p
    (NTRUPlus768InvNTTRadix2_4Proof.invntt_radix2_4_spec input).
proof.
  move=> Hrep Hshape.
  apply (invntt_radix2_4_algebra_refines_terminal_representation
    p input (NTRUPlus768InvNTTRadix2_4Proof.invntt_radix2_4_spec input)).
  + exact Hrep.
  exact (NTRUPlus768InvNTTRadix2_4Algebra.invntt_radix2_4_spec_algebra input Hshape).
qed.

lemma invntt_radix2_4_semantics_functional
    (p : NTRUPoly.poly) (rp0 : W16.t Array768.t) :
  terminal_represents rp0 p =>
  NTRUPlus768InvNTTRadix2_4Algebra.qrange_input_shape rp0 =>
  hoare [NTRUPlus768InvNTTRadix2_4.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4 :
    rp = rp0 ==> invntt_radix2_4_semantics p res].
proof.
  move=> Hrep Hshape.
  conseq
    (NTRUPlus768InvNTTRadix2_4Algebra.invntt_radix2_4_algebra_functional
      rp0 Hshape) => />.
  move=> result Halg.
  apply (invntt_radix2_4_algebra_refines_terminal_representation p rp0 result).
  + exact Hrep.
  + exact Halg.
qed.

lemma invntt_radix2_4_correct_semantics
    (p : NTRUPoly.poly) (rp0 : W16.t Array768.t) :
  terminal_represents rp0 p =>
  NTRUPlus768InvNTTRadix2_4Algebra.qrange_input_shape rp0 =>
  phoare [NTRUPlus768InvNTTRadix2_4.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4 :
    rp = rp0 ==> invntt_radix2_4_semantics p res] = 1%r.
proof.
  move=> Hrep Hshape.
  have Hfunctional :
      hoare [NTRUPlus768InvNTTRadix2_4.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4 :
        rp = rp0 ==> invntt_radix2_4_semantics p res].
  + apply invntt_radix2_4_semantics_functional.
    - exact Hrep.
    - exact Hshape.
  by conseq NTRUPlus768InvNTTRadix2_4Proof.invntt_radix2_4_lossless Hfunctional.
qed.
