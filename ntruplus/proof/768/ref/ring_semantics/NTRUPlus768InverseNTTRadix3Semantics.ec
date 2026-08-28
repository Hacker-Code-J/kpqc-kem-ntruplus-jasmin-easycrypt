(* Semantic and executable endpoints for the inverse radix-3 layer. *)
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
require import NTRUPlus768InvNTTRadix3.
require import NTRUPlus768InvNTTRadix3Algebra NTRUPlus768InvNTTRadix3Proof.
require import NTRUPlus768InverseNTTRadix2_16Recombination.
require import NTRUPlus768InverseNTTRadix2_16Semantics.
require import NTRUPlus768InverseNTTRadix2_32Recombination.
require import NTRUPlus768InverseNTTRadix2_32Semantics.
require import NTRUPlus768InverseNTTRadix2_64Recombination.
require import NTRUPlus768InverseNTTRadix2_64Semantics.
require import NTRUPlus768InverseNTTRadix3Recombination.
require import NTRUPlus768InverseNTTRadix3Interpolation.

abbrev ( + ) = NTRUPoly.PolyComRing.( + ).

op tripled_five_times (p : NTRUPoly.poly) : NTRUPoly.poly =
  doubled_five_times p + doubled_five_times p + doubled_five_times p.

op invntt_radix3_semantics
    (p : NTRUPoly.poly) (output : W16.t Array768.t) : bool =
  factor_eqm 384 96
    (tripled_five_times p)
    (segment_poly output 0 384) /\
  factor_eqm 384 480
    (tripled_five_times p)
    (segment_poly output 384 384).

lemma invntt_radix2_64_semantics_child_32
    (p : NTRUPoly.poly) (input : W16.t Array768.t) :
  invntt_radix2_64_semantics p input =>
  factor_eqm 128 32
    (doubled_five_times p)
    (segment_poly input 0 128).
proof.
  move=> Hsem.
  have H := Hsem 0 _; first smt().
  have Hsched := radix2_64_schedule_exp_terminalE 0 _; first smt().
  rewrite (radix2_64_schedule_exp6E 0) 1:/# in Hsched.
  move: Hsched H; smt().
qed.

lemma invntt_radix2_64_semantics_child_224
    (p : NTRUPoly.poly) (input : W16.t Array768.t) :
  invntt_radix2_64_semantics p input =>
  factor_eqm 128 224
    (doubled_five_times p)
    (segment_poly input 128 128).
proof.
  move=> Hsem.
  have H := Hsem 1 _; first smt().
  have Hsched := radix2_64_schedule_exp_terminalE 1 _; first smt().
  rewrite (radix2_64_schedule_exp6E 1) 1:/# in Hsched.
  move: Hsched H; smt().
qed.

lemma invntt_radix2_64_semantics_child_416
    (p : NTRUPoly.poly) (input : W16.t Array768.t) :
  invntt_radix2_64_semantics p input =>
  factor_eqm 128 416
    (doubled_five_times p)
    (segment_poly input 256 128).
proof.
  move=> Hsem.
  have H := Hsem 2 _; first smt().
  have Hsched := radix2_64_schedule_exp_terminalE 2 _; first smt().
  rewrite (radix2_64_schedule_exp6E 2) 1:/# in Hsched.
  move: Hsched H; smt().
qed.

lemma invntt_radix2_64_semantics_child_160
    (p : NTRUPoly.poly) (input : W16.t Array768.t) :
  invntt_radix2_64_semantics p input =>
  factor_eqm 128 160
    (doubled_five_times p)
    (segment_poly input 384 128).
proof.
  move=> Hsem.
  have H := Hsem 3 _; first smt().
  have Hsched := radix2_64_schedule_exp_terminalE 3 _; first smt().
  rewrite (radix2_64_schedule_exp6E 3) 1:/# in Hsched.
  move: Hsched H; smt().
qed.

lemma invntt_radix2_64_semantics_child_352
    (p : NTRUPoly.poly) (input : W16.t Array768.t) :
  invntt_radix2_64_semantics p input =>
  factor_eqm 128 352
    (doubled_five_times p)
    (segment_poly input 512 128).
proof.
  move=> Hsem.
  have H := Hsem 4 _; first smt().
  have Hsched := radix2_64_schedule_exp_terminalE 4 _; first smt().
  rewrite (radix2_64_schedule_exp6E 4) 1:/# in Hsched.
  move: Hsched H; smt().
qed.

lemma invntt_radix2_64_semantics_child_544
    (p : NTRUPoly.poly) (input : W16.t Array768.t) :
  invntt_radix2_64_semantics p input =>
  factor_eqm 128 544
    (doubled_five_times p)
    (segment_poly input 640 128).
proof.
  move=> Hsem.
  have H := Hsem 5 _; first smt().
  have Hsched := radix2_64_schedule_exp_terminalE 5 _; first smt().
  rewrite (radix2_64_schedule_exp6E 5) 1:/# in Hsched.
  move: Hsched H; smt().
qed.

lemma invntt_radix3_algebra_refines_invntt_radix2_64_semantics
    (p : NTRUPoly.poly) (input output : W16.t Array768.t) :
  invntt_radix2_64_semantics p input =>
  NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_algebra input output =>
  invntt_radix3_semantics p output.
proof.
  move=> Hsem Halg.
  have H32 := invntt_radix2_64_semantics_child_32 p input Hsem.
  have H224 := invntt_radix2_64_semantics_child_224 p input Hsem.
  have H416 := invntt_radix2_64_semantics_child_416 p input Hsem.
  have H160 := invntt_radix2_64_semantics_child_160 p input Hsem.
  have H352 := invntt_radix2_64_semantics_child_352 p input Hsem.
  have H544 := invntt_radix2_64_semantics_child_544 p input Hsem.
  rewrite /invntt_radix3_semantics /tripled_five_times.
  split.
  + rewrite (invntt_radix3_output_segment_0_recombineE input output Halg).
    apply (invntt_radix3_recombine_factor_eqm
      (doubled_five_times p)
      (segment_poly input 0 128)
      (segment_poly input 128 128)
      (segment_poly input 256 128)
      32 160 320).
    - smt().
    - smt().
    - smt().
    - ring.
    - ring.
    - exact H32.
    - exact H224.
    - exact H416.
  + rewrite (invntt_radix3_output_segment_384_recombineE input output Halg).
    apply (invntt_radix3_recombine_factor_eqm
      (doubled_five_times p)
      (segment_poly input 384 128)
      (segment_poly input 512 128)
      (segment_poly input 640 128)
      160 32 64).
    - smt().
    - smt().
    - smt().
    - ring.
    - ring.
    - exact H160.
    - exact H352.
    - exact H544.
qed.

lemma invntt_radix3_spec_semantics
    (p : NTRUPoly.poly) (input : W16.t Array768.t) :
  invntt_radix2_64_semantics p input =>
  NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_input_shape input =>
  invntt_radix3_semantics p
    (NTRUPlus768InvNTTRadix3Proof.invntt_radix3_spec input).
proof.
  move=> Hsem Hshape.
  apply (invntt_radix3_algebra_refines_invntt_radix2_64_semantics
    p input (NTRUPlus768InvNTTRadix3Proof.invntt_radix3_spec input)).
  + exact Hsem.
  + exact (NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_spec_algebra input Hshape).
qed.

lemma invntt_radix3_semantics_functional
    (p : NTRUPoly.poly) (rp0 : W16.t Array768.t) :
  invntt_radix2_64_semantics p rp0 =>
  NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_input_shape rp0 =>
  hoare [NTRUPlus768InvNTTRadix3.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_radix3 :
    rp = rp0 ==> invntt_radix3_semantics p res].
proof.
  move=> Hsem Hshape.
  conseq
    (NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_algebra_functional
      rp0 Hshape) => />.
  move=> result Halg.
  apply (invntt_radix3_algebra_refines_invntt_radix2_64_semantics p rp0 result).
  + exact Hsem.
  + exact Halg.
qed.

lemma invntt_radix3_correct_semantics
    (p : NTRUPoly.poly) (rp0 : W16.t Array768.t) :
  invntt_radix2_64_semantics p rp0 =>
  NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_input_shape rp0 =>
  phoare [NTRUPlus768InvNTTRadix3.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_radix3 :
    rp = rp0 ==> invntt_radix3_semantics p res] = 1%r.
proof.
  move=> Hsem Hshape.
  have Hfunctional :
      hoare [NTRUPlus768InvNTTRadix3.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_radix3 :
        rp = rp0 ==> invntt_radix3_semantics p res].
  + apply invntt_radix3_semantics_functional.
    - exact Hsem.
    - exact Hshape.
  by conseq NTRUPlus768InvNTTRadix3Proof.invntt_radix3_lossless Hfunctional.
qed.
