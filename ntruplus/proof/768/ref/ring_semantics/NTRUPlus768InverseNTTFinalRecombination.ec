(* Polynomial reconstruction for the inverse-NTT final pair layer. *)
require import AllCore IntDiv List Ring StdBigop StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array768.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768CyclotomicFactorization.
require import NTRUPlus768EvaluationSemantics.
require import NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768InvNTTFinalAlgebra.
require import NTRUPlus768InverseNTTRadix3Recombination.

import NTRUPoly.BigPoly.

abbrev poly0 = NTRUPoly.PolyComRing.zeror.
abbrev poly1 = NTRUPoly.PolyComRing.oner.
abbrev polyC = NTRUPoly.polyC.
abbrev X = NTRUPoly.X.
abbrev ( + ) = NTRUPoly.PolyComRing.( + ).
abbrev [ - ] = NTRUPoly.PolyComRing.([-]).
abbrev ( * ) = NTRUPoly.PolyComRing.( * ).
abbrev ( - ) p q = p + (-q).
abbrev exp = NTRUPoly.PolyComRing.exp.

op invntt_final_low0_coeff : int =
  (1 - NTRUPlus768InvNTTFinalAlgebra.zminusz5inv_root) *
    NTRUPlus768InvNTTFinalAlgebra.ninv_root.

op invntt_final_low1_coeff : int =
  (1 + NTRUPlus768InvNTTFinalAlgebra.zminusz5inv_root) *
    NTRUPlus768InvNTTFinalAlgebra.ninv_root.

op invntt_final_high0_coeff : int =
  NTRUPlus768InvNTTFinalAlgebra.zminusz5inv_root *
    NTRUPlus768InvNTTFinalAlgebra.twoninv_root.

op invntt_final_high1_coeff : int =
  (-NTRUPlus768InvNTTFinalAlgebra.zminusz5inv_root) *
    NTRUPlus768InvNTTFinalAlgebra.twoninv_root.

op weighted2_remainder_poly
    (a : W16.t Array768.t) (c0 c1 : int) : poly =
  PCA.bigi predT
    (fun i =>
      polyC
        (lift_int
          (c0 * coeff a.[i] + c1 * coeff a.[i + 384])) *
      exp X i)
    0 384.

op invntt_final_recombine_value (a0 a1 : poly) : poly =
  polyC (lift_int invntt_final_low0_coeff) * a0 +
  polyC (lift_int invntt_final_low1_coeff) * a1 +
  (polyC (lift_int invntt_final_high0_coeff) * a0 +
   polyC (lift_int invntt_final_high1_coeff) * a1) * exp X 384.

lemma poly_lift_zeroE : polyC (lift_int 0) = poly0.
proof.
  rewrite /lift_int.
  change
    (polyC (CycloFq.incyclocoeff 0) = polyC CycloFq.zero).
  congr.
  have H := CycloFq.asintK CycloFq.zero.
  rewrite CycloFq.zeroE in H.
  exact H.
qed.

lemma poly_lift_weighted2_monomial
    (a0 a1 c0 c1 : int) (x : poly) :
  polyC (lift_int (c0 * a0 + c1 * a1)) * x =
  polyC (lift_int c0) * (polyC (lift_int a0) * x) +
  polyC (lift_int c1) * (polyC (lift_int a1) * x).
proof.
  have H := poly_lift_weighted3_monomial
    a0 a1 0 c0 c1 0 x.
  rewrite /= in H.
  rewrite poly_lift_zeroE in H.
  apply: (eq_trans _
    (polyC (lift_int c0) * (polyC (lift_int a0) * x) +
     polyC (lift_int c1) * (polyC (lift_int a1) * x) +
     poly0 * (poly0 * x))).
  + exact H.
  + ring.
qed.

lemma weighted2_remainder_polyE
    (a : W16.t Array768.t) (c0 c1 : int) :
  weighted2_remainder_poly a c0 c1 =
  polyC (lift_int c0) * segment_poly a 0 384 +
  polyC (lift_int c1) * segment_poly a 384 384.
proof.
  rewrite /weighted2_remainder_poly /segment_poly.
  have Hdist0 :
      polyC (lift_int c0) *
        PCA.bigi predT
          (fun i => polyC (lift_word a.[i]) * exp X i)
          0 384 =
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c0) *
            (polyC (lift_word a.[i]) * exp X i))
        0 384.
  + exact
      (PCA.mulr_sumr predT
        (fun i => polyC (lift_word a.[i]) * exp X i)
        (range 0 384) (polyC (lift_int c0))).
  have Hdist1 :
      polyC (lift_int c1) *
        PCA.bigi predT
          (fun i => polyC (lift_word a.[i + 384]) * exp X i)
          0 384 =
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c1) *
            (polyC (lift_word a.[i + 384]) * exp X i))
        0 384.
  + exact
      (PCA.mulr_sumr predT
        (fun i => polyC (lift_word a.[i + 384]) * exp X i)
        (range 0 384) (polyC (lift_int c1))).
  have Hsplit :
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c0) *
            (polyC (lift_word a.[i]) * exp X i))
        0 384 +
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c1) *
            (polyC (lift_word a.[i + 384]) * exp X i))
        0 384 =
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c0) *
            (polyC (lift_word a.[i]) * exp X i) +
          polyC (lift_int c1) *
            (polyC (lift_word a.[i + 384]) * exp X i))
        0 384.
  + apply/eq_sym.
    exact
      (PCA.big_split predT
        (fun i =>
          polyC (lift_int c0) *
            (polyC (lift_word a.[i]) * exp X i))
        (fun i =>
          polyC (lift_int c1) *
            (polyC (lift_word a.[i + 384]) * exp X i))
        (range 0 384)).
  rewrite Hdist0 Hdist1 Hsplit.
  apply PCA.eq_big_int => i Hi.
  rewrite /lift_word /=.
  exact (poly_lift_weighted2_monomial
    (coeff a.[i]) (coeff a.[i + 384]) c0 c1 (exp X i)).
qed.

lemma segment_poly_weighted2E
    (input output : W16.t Array768.t)
    (output_base c0 c1 : int) :
  (forall i, 0 <= i < 384 =>
    coeff output.[i + output_base] %% q =
    (c0 * coeff input.[i] + c1 * coeff input.[i + 384]) %% q) =>
  segment_poly output output_base 384 =
    weighted2_remainder_poly input c0 c1.
proof.
  move=> Hcoeff.
  rewrite /segment_poly /weighted2_remainder_poly.
  apply PCA.eq_big_int => i Hi.
  have Hmod := Hcoeff i Hi.
  have Elift :
      lift_word output.[i + output_base] =
      lift_int
        (c0 * coeff input.[i] + c1 * coeff input.[i + 384]).
  + rewrite /lift_word.
    apply lift_int_eq.
    exact Hmod.
  by rewrite /= Elift.
qed.

lemma invntt_final_low_linearE (a b : int) :
  ((a + b -
    (a - b) * NTRUPlus768InvNTTFinalAlgebra.zminusz5inv_root) *
    NTRUPlus768InvNTTFinalAlgebra.ninv_root) =
  invntt_final_low0_coeff * a + invntt_final_low1_coeff * b.
proof.
  rewrite /invntt_final_low0_coeff /invntt_final_low1_coeff.
  ring.
qed.

lemma invntt_final_high_linearE (a b : int) :
  ((a - b) * NTRUPlus768InvNTTFinalAlgebra.zminusz5inv_root *
    NTRUPlus768InvNTTFinalAlgebra.twoninv_root) =
  invntt_final_high0_coeff * a + invntt_final_high1_coeff * b.
proof.
  rewrite /invntt_final_high0_coeff /invntt_final_high1_coeff.
  ring.
qed.

lemma invntt_final_low_coeffE
    (input output : W16.t Array768.t) (i : int) :
  0 <= i < 384 =>
  NTRUPlus768InvNTTFinalAlgebra.invntt_final_algebra input output =>
  coeff output.[i] %% q =
  (invntt_final_low0_coeff * coeff input.[i] +
   invntt_final_low1_coeff * coeff input.[i + 384]) %% q.
proof.
  move=> Hi Halg.
  have [_ Hcoeff] := Halg i _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768InvNTTFinalAlgebra.invntt_final_math
          ifT 1:/#
          /NTRUPlus768InvNTTFinalAlgebra.invntt_final_pair_math /=.
  move=> Hcoeff.
  rewrite (invntt_final_low_linearE
    (coeff input.[i]) (coeff input.[i + 384])) in Hcoeff.
  exact Hcoeff.
qed.

lemma invntt_final_high_coeffE
    (input output : W16.t Array768.t) (i : int) :
  0 <= i < 384 =>
  NTRUPlus768InvNTTFinalAlgebra.invntt_final_algebra input output =>
  coeff output.[i + 384] %% q =
  (invntt_final_high0_coeff * coeff input.[i] +
   invntt_final_high1_coeff * coeff input.[i + 384]) %% q.
proof.
  move=> Hi Halg.
  have [_ Hcoeff] := Halg (i + 384) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768InvNTTFinalAlgebra.invntt_final_math
          ifF 1:/#.
  have -> : i + 384 - NTRUPlus768InvNTTFinalProof.half = i.
  + rewrite /NTRUPlus768InvNTTFinalProof.half.
    ring.
  rewrite /NTRUPlus768InvNTTFinalAlgebra.invntt_final_pair_math /=.
  move=> Hcoeff.
  rewrite (invntt_final_high_linearE
    (coeff input.[i]) (coeff input.[i + 384])) in Hcoeff.
  exact Hcoeff.
qed.

lemma invntt_final_low_segmentE
    (input output : W16.t Array768.t) :
  NTRUPlus768InvNTTFinalAlgebra.invntt_final_algebra input output =>
  segment_poly output 0 384 =
    weighted2_remainder_poly input
      invntt_final_low0_coeff invntt_final_low1_coeff.
proof.
  move=> Halg.
  apply segment_poly_weighted2E => i Hi.
  have H := invntt_final_low_coeffE input output i Hi Halg.
  exact H.
qed.

lemma invntt_final_high_segmentE
    (input output : W16.t Array768.t) :
  NTRUPlus768InvNTTFinalAlgebra.invntt_final_algebra input output =>
  segment_poly output 384 384 =
    weighted2_remainder_poly input
      invntt_final_high0_coeff invntt_final_high1_coeff.
proof.
  move=> Halg.
  apply segment_poly_weighted2E => i Hi.
  exact (invntt_final_high_coeffE input output i Hi Halg).
qed.

lemma invntt_final_input_polyE
    (input output : W16.t Array768.t) :
  NTRUPlus768InvNTTFinalAlgebra.invntt_final_algebra input output =>
  input_poly output =
    invntt_final_recombine_value
      (segment_poly input 0 384) (segment_poly input 384 384).
proof.
  move=> Halg.
  rewrite /input_poly
          (invntt_final_low_segmentE input output Halg)
          (invntt_final_high_segmentE input output Halg).
  rewrite !weighted2_remainder_polyE
          /invntt_final_recombine_value.
  done.
qed.
