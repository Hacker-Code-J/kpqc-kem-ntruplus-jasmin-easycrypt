(* Semantic and executable endpoints for the second inverse NTT layer. *)
require import AllCore IntDiv List Ring StdBigop StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array768.
require import NTRUPlus768CyclotomicFactorization.
require import NTRUPlus768EvaluationSemantics.
require import NTRUPlus768TerminalRepresentation.
require import NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768ForwardNTTRadix3Semantics.
require import NTRUPlus768ForwardNTTRadix2_8Semantics.
require import NTRUPlus768ForwardNTTRadix2_4Semantics.
require import NTRUPlus768NTTSchedule.
require import NTRUPlus768PolyBasemulAlgebra.
require import NTRUPlus768InvNTTRadix2_4.
require import NTRUPlus768InvNTTRadix2_4Algebra NTRUPlus768InvNTTRadix2_4Proof.
require import NTRUPlus768InvNTTRadix2_8.
require import NTRUPlus768InvNTTRadix2_8Algebra NTRUPlus768InvNTTRadix2_8Proof.
require import NTRUPlus768InverseNTTRadix2_4Semantics.
require import NTRUPlus768InverseNTTRadix2_8Recombination.

op doubled_twice (p : NTRUPoly.poly) : NTRUPoly.poly =
  NTRUPoly.PolyComRing.( + )
    (NTRUPoly.PolyComRing.( + ) p p)
    (NTRUPoly.PolyComRing.( + ) p p).

op invntt_radix2_8_semantics
    (p : NTRUPoly.poly) (output : W16.t Array768.t) : bool =
  forall b, 0 <= b < 48 =>
    factor_eqm 16 (4 * terminal_exp (2 * b))
      (doubled_twice p)
      (segment_poly output (16 * b) 16).

lemma invntt_radix2_8_algebra_refines_invntt_radix2_4_semantics
    (p : NTRUPoly.poly) (input output : W16.t Array768.t) :
  invntt_radix2_4_semantics p input =>
  NTRUPlus768InvNTTRadix2_8Algebra.invntt_radix2_8_algebra input output =>
  invntt_radix2_8_semantics p output.
proof.
  move=> Hsem Halg.
  rewrite /invntt_radix2_8_semantics.
  move=> b Hb.
  have Hleft :=
    invntt_radix2_4_semantics_child_left p input b Hsem Hb.
  have Hright :=
    invntt_radix2_4_semantics_child_right p input b Hsem Hb.
  rewrite (invntt_radix2_8_output_segmentE input output b Hb Halg).
  rewrite (invntt_radix2_8_scaled_diff_polyE input (16 * b)
    (NTRUPlus768InvNTTRadix2_8Algebra.invntt_radix2_8_zeta_root b)).
  have HrootE :
      NTRUPlus768InverseNTTRadix2_8Recombination.polyC
        (lift_int
          (NTRUPlus768InvNTTRadix2_8Algebra.invntt_radix2_8_zeta_root b)) =
      root_poly (invntt_radix2_8_schedule_exp b).
  + rewrite /NTRUPlus768InvNTTRadix2_8Algebra.invntt_radix2_8_zeta_root.
    rewrite schedule_root_fieldE 1:(invntt_radix2_8_schedule_nonneg b Hb).
    done.
  rewrite HrootE.
  rewrite /doubled_twice.
  have Hparent_exp :
      4 * terminal_exp (2 * b) =
      2 * (2 * terminal_exp (2 * b)).
  + ring.
  rewrite Hparent_exp.
  apply (invntt_radix2_8_recombine_factor_eqm
    (NTRUPoly.PolyComRing.( + ) p p)
    (segment_poly input (16 * b) 8)
    (segment_poly input (16 * b + 8) 8)
    (2 * terminal_exp (2 * b))
    (invntt_radix2_8_schedule_exp b)).
  + exact (invntt_radix2_8_child_exp_nonneg b Hb).
  + exact (invntt_radix2_8_schedule_nonneg b Hb).
  + exact (invntt_radix2_8_schedule_sumE b Hb).
  + exact Hleft.
  + exact Hright.
qed.

lemma invntt_radix2_8_spec_semantics
    (p : NTRUPoly.poly) (input : W16.t Array768.t) :
  invntt_radix2_4_semantics p input =>
  NTRUPlus768InvNTTRadix2_8Algebra.invntt_radix2_8_input_shape input =>
  invntt_radix2_8_semantics p
    (NTRUPlus768InvNTTRadix2_8Proof.invntt_radix2_8_spec input).
proof.
  move=> Hsem Hshape.
  apply (invntt_radix2_8_algebra_refines_invntt_radix2_4_semantics
    p input (NTRUPlus768InvNTTRadix2_8Proof.invntt_radix2_8_spec input)).
  + exact Hsem.
  exact (NTRUPlus768InvNTTRadix2_8Algebra.invntt_radix2_8_spec_algebra input Hshape).
qed.

lemma invntt_radix2_8_semantics_functional
    (p : NTRUPoly.poly) (rp0 : W16.t Array768.t) :
  invntt_radix2_4_semantics p rp0 =>
  NTRUPlus768InvNTTRadix2_8Algebra.invntt_radix2_8_input_shape rp0 =>
  hoare [NTRUPlus768InvNTTRadix2_8.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_8 :
    rp = rp0 ==> invntt_radix2_8_semantics p res].
proof.
  move=> Hsem Hshape.
  conseq
    (NTRUPlus768InvNTTRadix2_8Algebra.invntt_radix2_8_algebra_functional
      rp0 Hshape) => />.
  move=> result Halg.
  apply (invntt_radix2_8_algebra_refines_invntt_radix2_4_semantics p rp0 result).
  + exact Hsem.
  + exact Halg.
qed.

lemma invntt_radix2_8_correct_semantics
    (p : NTRUPoly.poly) (rp0 : W16.t Array768.t) :
  invntt_radix2_4_semantics p rp0 =>
  NTRUPlus768InvNTTRadix2_8Algebra.invntt_radix2_8_input_shape rp0 =>
  phoare [NTRUPlus768InvNTTRadix2_8.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_8 :
    rp = rp0 ==> invntt_radix2_8_semantics p res] = 1%r.
proof.
  move=> Hsem Hshape.
  have Hfunctional :
      hoare [NTRUPlus768InvNTTRadix2_8.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_8 :
        rp = rp0 ==> invntt_radix2_8_semantics p res].
  + apply invntt_radix2_8_semantics_functional.
    - exact Hsem.
    - exact Hshape.
  by conseq NTRUPlus768InvNTTRadix2_8Proof.invntt_radix2_8_lossless Hfunctional.
qed.
