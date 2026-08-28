(* Algebraic reconstruction for the inverse radix-3 layer. *)
require import AllCore IntDiv List Ring StdBigop StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array768.
require import NTRUPlus768CyclotomicFactorization.
require import NTRUPlus768EvaluationSemantics.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768ForwardNTTRadix3Semantics.
require import NTRUPlus768NTTSchedule.
require import NTRUPlus768InvNTTRadix3.
require import NTRUPlus768InvNTTRadix3Algebra NTRUPlus768InvNTTRadix3Proof.

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

instance ring with NTRUPoly.poly
  op rzero = NTRUPoly.PolyComRing.zeror
  op rone = NTRUPoly.PolyComRing.oner
  op add = NTRUPoly.PolyComRing.( + )
  op mul = NTRUPoly.PolyComRing.( * )
  op opp = NTRUPoly.PolyComRing.([-])
  op expr = NTRUPoly.PolyComRing.exp
  op ofint = NTRUPoly.PolyComRing.ofint

  proof oner_neq0 by exact NTRUPoly.PolyComRing.oner_neq0
  proof addr0 by exact NTRUPoly.PolyComRing.addr0
  proof addrA by exact NTRUPoly.PolyComRing.addrA
  proof addrC by exact NTRUPoly.PolyComRing.addrC
  proof addrN by exact NTRUPoly.PolyComRing.addrN
  proof mulr1 by exact NTRUPoly.PolyComRing.mulr1
  proof mulrA by exact NTRUPoly.PolyComRing.mulrA
  proof mulrC by exact NTRUPoly.PolyComRing.mulrC
  proof mulrDl by exact NTRUPoly.PolyComRing.mulrDl
  proof expr0 by exact NTRUPoly.PolyComRing.expr0
  proof exprS by exact NTRUPoly.PolyComRing.exprS
  proof ofint0 by exact NTRUPoly.PolyComRing.ofint0
  proof ofint1 by exact NTRUPoly.PolyComRing.ofint1
  proof ofintS by exact NTRUPoly.PolyComRing.ofintS
  proof ofintN by exact NTRUPoly.PolyComRing.ofintN.

op weighted3_remainder_poly
    (a : W16.t Array768.t) (base c0 c1 c2 : int) : poly =
  PCA.bigi predT
    (fun i =>
      polyC
        (lift_int
          (c0 * coeff a.[i + base] +
           c1 * coeff a.[i + base + 128] +
           c2 * coeff a.[i + base + 256])) *
      exp X i)
    0 128.

lemma root_poly_scheduleE (e : int) :
  0 <= e =>
  root_poly e = polyC (lift_int (schedule_root e)).
proof.
  move=> He.
  rewrite /root_poly.
  rewrite -(schedule_root_fieldE e He).
  done.
qed.

lemma poly_lift_scheduleE (e : int) :
  0 <= e =>
  polyC (lift_int (schedule_root e)) = root_poly e.
proof.
  move=> He.
  apply/eq_sym.
  exact (root_poly_scheduleE e He).
qed.

lemma root_poly_mulE (e1 e2 : int) :
  0 <= e1 =>
  0 <= e2 =>
  root_poly e1 * root_poly e2 = root_poly (e1 + e2).
proof.
  move=> He1 He2.
  rewrite /root_poly.
  rewrite (zeta_field_expE e1 He1) (zeta_field_expE e2 He2).
  have Hsum : 0 <= e1 + e2 by smt().
  rewrite (zeta_field_expE (e1 + e2) Hsum).
  have Hpoly :
      polyC (CycloFq.incyclocoeff (zeta_root ^ e1)) *
        polyC (CycloFq.incyclocoeff (zeta_root ^ e2)) =
      polyC
        (CycloFq.( * )
          (CycloFq.incyclocoeff (zeta_root ^ e1))
          (CycloFq.incyclocoeff (zeta_root ^ e2))).
  + apply/eq_sym.
    exact (NTRUPoly.polyCM
      (CycloFq.incyclocoeff (zeta_root ^ e1))
      (CycloFq.incyclocoeff (zeta_root ^ e2))).
  rewrite Hpoly.
  have Hfield :
      CycloFq.( * )
        (CycloFq.incyclocoeff (zeta_root ^ e1))
        (CycloFq.incyclocoeff (zeta_root ^ e2)) =
      CycloFq.incyclocoeff ((zeta_root ^ e1) * (zeta_root ^ e2)).
  + apply/eq_sym.
    exact (CycloFq.incyclocoeffM
      (zeta_root ^ e1) (zeta_root ^ e2)).
  rewrite Hfield.
  have Hexpr :
      (zeta_root ^ e1) * (zeta_root ^ e2) =
      zeta_root ^ (e1 + e2).
  + apply/eq_sym.
    exact (Ring.IntID.exprD_nneg zeta_root e1 e2 He1 He2).
  by rewrite Hexpr.
qed.

lemma omega_poly_sumE :
  poly1 + root_poly 192 + root_poly 384 = poly0.
proof.
  rewrite /root_poly.
  change
    (polyC CycloFq.one + polyC (CycloFq.exp zeta_field 192) +
       polyC (CycloFq.exp zeta_field 384) = polyC CycloFq.zero).
  have Hleft :
      polyC CycloFq.one + polyC (CycloFq.exp zeta_field 192) =
      polyC (CycloFq.( + ) CycloFq.one
        (CycloFq.exp zeta_field 192)).
  + apply/eq_sym.
    exact (NTRUPoly.polyCD
      CycloFq.one (CycloFq.exp zeta_field 192)).
  rewrite Hleft.
  have Hall :
      polyC (CycloFq.( + ) CycloFq.one
          (CycloFq.exp zeta_field 192)) +
        polyC (CycloFq.exp zeta_field 384) =
      polyC
        (CycloFq.( + )
          (CycloFq.( + ) CycloFq.one
            (CycloFq.exp zeta_field 192))
          (CycloFq.exp zeta_field 384)).
  + apply/eq_sym.
    exact (NTRUPoly.polyCD
      (CycloFq.( + ) CycloFq.one
        (CycloFq.exp zeta_field 192))
      (CycloFq.exp zeta_field 384)).
  rewrite Hall.
  rewrite zeta192_sum.
  done.
qed.

lemma omega_poly_384E :
  root_poly 384 = -poly1 - root_poly 192.
proof.
  have Hsum := omega_poly_sumE.
  have Hfactor :
      root_poly 384 - (-poly1 - root_poly 192) =
      poly1 + root_poly 192 + root_poly 384 by ring.
  rewrite Hsum in Hfactor.
  rewrite -NTRUPoly.PolyComRing.subr_eq0.
  exact Hfactor.
qed.

lemma invntt_radix3_weighted_firstE
    (a0 a1 a2 u w : poly) :
  ((-poly1 - w) * u) * a0 + (w * u) * a1 + u * a2 =
  u * (a2 - a0 + w * (a1 - a0)).
proof. ring. qed.

lemma invntt_radix3_weighted_secondE
    (a0 a1 a2 v w : poly) :
  (w * v) * a0 + ((-poly1 - w) * v) * a1 + v * a2 =
  v * (a2 - a1 - w * (a1 - a0)).
proof. ring. qed.

lemma omega_square_complement (w : poly) :
  poly1 + w + w * w = poly0 =>
  -poly1 - w = w * w.
proof.
  move=> Hw.
  have Hfactor :
      (-poly1 - w) - w * w = -(poly1 + w + w * w) by ring.
  rewrite Hw in Hfactor.
  have Hzero : (-poly1 - w) - w * w = poly0.
  + exact (eq_trans _ _ _ Hfactor NTRUPoly.PolyComRing.oppr0).
  rewrite -NTRUPoly.PolyComRing.subr_eq0.
  exact Hzero.
qed.

lemma invntt_radix3_algorithm_firstE
    (a0 a1 a2 u w : poly) :
  poly1 + w + w * w = poly0 =>
  u * (a2 - a0 + w * (a1 - a0)) =
    (w * w * u) * a0 + (w * u) * a1 + u * a2.
proof.
  move=> Hw.
  have H := invntt_radix3_weighted_firstE a0 a1 a2 u w.
  rewrite (omega_square_complement w Hw) in H.
  apply/eq_sym.
  exact H.
qed.

lemma invntt_radix3_algorithm_secondE
    (a0 a1 a2 v w : poly) :
  poly1 + w + w * w = poly0 =>
  v * (a2 - a1 - w * (a1 - a0)) =
    (w * v) * a0 + (w * w * v) * a1 + v * a2.
proof.
  move=> Hw.
  have H := invntt_radix3_weighted_secondE a0 a1 a2 v w.
  rewrite (omega_square_complement w Hw) in H.
  apply/eq_sym.
  exact H.
qed.

lemma invntt_radix3_residual_decomp
    (a0 a1 a2 u v w x : poly) :
  poly1 + w + w * w = poly0 =>
  a0 + a1 + a2 +
    u * (a2 - a0 + w * (a1 - a0)) * x +
    v * (a2 - a1 - w * (a1 - a0)) * (x * x) =
  a0 * (poly1 + u * w * w * x + v * w * x * x) +
  a1 * (poly1 + u * w * x + v * w * w * x * x) +
  a2 * (poly1 + u * x + v * x * x).
proof.
  move=> Hw.
  rewrite (invntt_radix3_algorithm_firstE a0 a1 a2 u w Hw).
  rewrite (invntt_radix3_algorithm_secondE a0 a1 a2 v w Hw).
  ring.
qed.

lemma exp_X128_2 :
  exp (exp X 128) 2 = exp X 256.
proof.
  change (exp (exp X 128) 2 = exp X (128 * 2)).
  rewrite Ring.IntID.mulrC.
  apply/eq_sym.
  exact (NTRUPoly.PolyComRing.exprM X 128 2).
qed.

lemma segment3_layout (a0 a1 a2 x : poly) :
  a0 + (a1 + a2 * x) * x =
  a0 + a1 * x + a2 * (x * x).
proof.
  have Hadd := NTRUPoly.PolyComRing.addrA
    a0 (a1 * x) (a2 * x * x).
  have Hmul := NTRUPoly.PolyComRing.mulrA a2 x x.
  apply: (eq_trans _ (a0 + a1 * x + a2 * x * x)).
  + rewrite poly_mul_add_right.
    exact Hadd.
  + congr.
    apply/eq_sym.
    exact Hmul.
qed.

lemma poly_lift_mul_monomial (a c : int) (x : poly) :
  polyC (lift_int (c * a)) * x =
  polyC (lift_int c) * (polyC (lift_int a) * x).
proof.
  rewrite /lift_int.
  rewrite CycloFq.incyclocoeffM NTRUPoly.polyCM.
  apply/eq_sym.
  exact (NTRUPoly.PolyComRing.mulrA
    (polyC (CycloFq.incyclocoeff c))
    (polyC (CycloFq.incyclocoeff a)) x).
qed.

lemma poly_lift_mulE (a c : int) :
  polyC (lift_int (c * a)) =
  polyC (lift_int c) * polyC (lift_int a).
proof.
  rewrite /lift_int.
  rewrite CycloFq.incyclocoeffM NTRUPoly.polyCM.
  done.
qed.

lemma poly_lift_oneE : polyC (lift_int 1) = poly1.
proof.
  rewrite /lift_int.
  change
    (polyC (CycloFq.incyclocoeff 1) = polyC CycloFq.one).
  congr.
  have H := CycloFq.asintK CycloFq.one.
  rewrite CycloFq.oneE in H.
  exact H.
qed.

lemma poly_lift_weighted3_monomial
    (a0 a1 a2 c0 c1 c2 : int) (x : poly) :
  polyC (lift_int (c0 * a0 + c1 * a1 + c2 * a2)) * x =
  polyC (lift_int c0) * (polyC (lift_int a0) * x) +
  polyC (lift_int c1) * (polyC (lift_int a1) * x) +
  polyC (lift_int c2) * (polyC (lift_int a2) * x).
proof.
  have Hsum := poly_lift_linear3_monomial
    (c0 * a0) a1 a2 c1 c2 x.
  rewrite (mulzC a1 c1) (mulzC a2 c2) in Hsum.
  rewrite (poly_lift_mul_monomial a0 c0 x) in Hsum.
  exact Hsum.
qed.

lemma weighted3_remainder_polyE
    (a : W16.t Array768.t) (base c0 c1 c2 : int) :
  weighted3_remainder_poly a base c0 c1 c2 =
  polyC (lift_int c0) * segment_poly a base 128 +
  polyC (lift_int c1) * segment_poly a (base + 128) 128 +
  polyC (lift_int c2) * segment_poly a (base + 256) 128.
proof.
  rewrite /weighted3_remainder_poly /segment_poly.
  have Hdist0 :
      polyC (lift_int c0) *
        PCA.bigi predT
          (fun i => polyC (lift_word a.[i + base]) * exp X i)
          0 128 =
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c0) *
            (polyC (lift_word a.[i + base]) * exp X i))
        0 128.
  + exact
      (PCA.mulr_sumr predT
        (fun i => polyC (lift_word a.[i + base]) * exp X i)
        (range 0 128) (polyC (lift_int c0))).
  have Hdist1 :
      polyC (lift_int c1) *
        PCA.bigi predT
          (fun i => polyC (lift_word a.[i + (base + 128)]) * exp X i)
          0 128 =
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c1) *
            (polyC (lift_word a.[i + (base + 128)]) * exp X i))
        0 128.
  + exact
      (PCA.mulr_sumr predT
        (fun i => polyC (lift_word a.[i + (base + 128)]) * exp X i)
        (range 0 128) (polyC (lift_int c1))).
  have Hdist2 :
      polyC (lift_int c2) *
        PCA.bigi predT
          (fun i => polyC (lift_word a.[i + (base + 256)]) * exp X i)
          0 128 =
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c2) *
            (polyC (lift_word a.[i + (base + 256)]) * exp X i))
        0 128.
  + exact
      (PCA.mulr_sumr predT
        (fun i => polyC (lift_word a.[i + (base + 256)]) * exp X i)
        (range 0 128) (polyC (lift_int c2))).
  have Hsplit01 :
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c0) *
            (polyC (lift_word a.[i + base]) * exp X i))
        0 128 +
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c1) *
            (polyC (lift_word a.[i + (base + 128)]) * exp X i))
        0 128 =
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c0) *
            (polyC (lift_word a.[i + base]) * exp X i) +
          polyC (lift_int c1) *
            (polyC (lift_word a.[i + (base + 128)]) * exp X i))
        0 128.
  + apply/eq_sym.
    exact
      (PCA.big_split predT
        (fun i =>
          polyC (lift_int c0) *
            (polyC (lift_word a.[i + base]) * exp X i))
        (fun i =>
          polyC (lift_int c1) *
            (polyC (lift_word a.[i + (base + 128)]) * exp X i))
        (range 0 128)).
  have Hsplit012 :
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c0) *
            (polyC (lift_word a.[i + base]) * exp X i) +
          polyC (lift_int c1) *
            (polyC (lift_word a.[i + (base + 128)]) * exp X i))
        0 128 +
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c2) *
            (polyC (lift_word a.[i + (base + 256)]) * exp X i))
        0 128 =
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c0) *
            (polyC (lift_word a.[i + base]) * exp X i) +
          polyC (lift_int c1) *
            (polyC (lift_word a.[i + (base + 128)]) * exp X i) +
          polyC (lift_int c2) *
            (polyC (lift_word a.[i + (base + 256)]) * exp X i))
        0 128.
  + apply/eq_sym.
    exact
      (PCA.big_split predT
        (fun i =>
          polyC (lift_int c0) *
            (polyC (lift_word a.[i + base]) * exp X i) +
          polyC (lift_int c1) *
            (polyC (lift_word a.[i + (base + 128)]) * exp X i))
        (fun i =>
          polyC (lift_int c2) *
            (polyC (lift_word a.[i + (base + 256)]) * exp X i))
        (range 0 128)).
  rewrite Hdist0 Hdist1 Hdist2 Hsplit01 Hsplit012.
  apply PCA.eq_big_int => i Hi.
  rewrite /lift_word /=.
  rewrite poly_lift_weighted3_monomial.
  have Hidx1 : i + base + 128 = i + (base + 128) by ring.
  have Hidx2 : i + base + 256 = i + (base + 256) by ring.
  by rewrite Hidx1 Hidx2.
qed.

lemma weighted3_remainder_poly_oneE
    (a : W16.t Array768.t) (base : int) :
  weighted3_remainder_poly a base 1 1 1 =
  segment_poly a base 128 +
  segment_poly a (base + 128) 128 +
  segment_poly a (base + 256) 128.
proof.
  rewrite weighted3_remainder_polyE !poly_lift_oneE.
  congr.
  + congr.
    - exact (NTRUPoly.PolyComRing.mul1r (segment_poly a base 128)).
    - exact (NTRUPoly.PolyComRing.mul1r
        (segment_poly a (base + 128) 128)).
  + exact (NTRUPoly.PolyComRing.mul1r
      (segment_poly a (base + 256) 128)).
qed.

lemma weighted3_remainder_scheduleE
    (a : W16.t Array768.t) (base e : int) :
  0 <= e =>
  weighted3_remainder_poly a base
      ((schedule_root 384) * (schedule_root e))
      ((schedule_root 192) * (schedule_root e))
      (schedule_root e) =
    (root_poly 384 * root_poly e) * segment_poly a base 128 +
    (root_poly 192 * root_poly e) *
      segment_poly a (base + 128) 128 +
    root_poly e * segment_poly a (base + 256) 128.
proof.
  move=> He.
  rewrite weighted3_remainder_polyE !poly_lift_mulE.
  rewrite (poly_lift_scheduleE 384) 1:/#.
  rewrite (poly_lift_scheduleE 192) 1:/#.
  rewrite (poly_lift_scheduleE e He).
  done.
qed.

lemma weighted3_remainder_schedule_swappedE
    (a : W16.t Array768.t) (base e : int) :
  0 <= e =>
  weighted3_remainder_poly a base
      ((schedule_root 192) * (schedule_root e))
      ((schedule_root 384) * (schedule_root e))
      (schedule_root e) =
    (root_poly 192 * root_poly e) * segment_poly a base 128 +
    (root_poly 384 * root_poly e) *
      segment_poly a (base + 128) 128 +
    root_poly e * segment_poly a (base + 256) 128.
proof.
  move=> He.
  rewrite weighted3_remainder_polyE !poly_lift_mulE.
  rewrite (poly_lift_scheduleE 384) 1:/#.
  rewrite (poly_lift_scheduleE 192) 1:/#.
  rewrite (poly_lift_scheduleE e He).
  done.
qed.

lemma segment_poly_weighted3E
    (input output : W16.t Array768.t)
    (input_base output_base c0 c1 c2 : int) :
  (forall i, 0 <= i < 128 =>
    coeff output.[i + output_base] %% q =
    (coeff input.[i + input_base] * c0 +
     coeff input.[i + input_base + 128] * c1 +
     coeff input.[i + input_base + 256] * c2) %% q) =>
  segment_poly output output_base 128 =
  weighted3_remainder_poly input input_base c0 c1 c2.
proof.
  move=> Hcoeff.
  rewrite /segment_poly /weighted3_remainder_poly.
  apply PCA.eq_big_int => i Hi.
  have Hmod := Hcoeff i Hi.
  have Elift :
      lift_word output.[i + output_base] =
      lift_int
        (c0 * coeff input.[i + input_base] +
         c1 * coeff input.[i + input_base + 128] +
         c2 * coeff input.[i + input_base + 256]).
  + rewrite /lift_word.
    apply lift_int_eq.
    rewrite (mulzC c0 (coeff input.[i + input_base])).
    rewrite (mulzC c1 (coeff input.[i + input_base + 128])).
    rewrite (mulzC c2 (coeff input.[i + input_base + 256])).
    exact Hmod.
  by rewrite /= Elift.
qed.

lemma invntt_radix3_segment_0E
    (input output : W16.t Array768.t) :
  NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_algebra input output =>
  segment_poly output 0 128 =
  weighted3_remainder_poly input 0 1 1 1.
proof.
  move=> Halg.
  apply segment_poly_weighted3E => i Hi.
  have [_ Hcoeff] := Halg i _; first smt().
  rewrite /NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_math
          /NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_block_math_at
          /NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_block_math
          /NTRUPlus768InvNTTRadix3Proof.block
          /NTRUPlus768InvNTTRadix3Proof.double_block
          /NTRUPlus768InvNTTRadix3Proof.second_base
          ifT 1:/# /= in Hcoeff.
  rewrite Hcoeff.
  by rewrite !mulz1.
qed.

lemma invntt_radix3_segment_128E
    (input output : W16.t Array768.t) :
  NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_algebra input output =>
  segment_poly output 128 128 =
  weighted3_remainder_poly input 0
    ((schedule_root 384) * (schedule_root 160))
    ((schedule_root 192) * (schedule_root 160))
    (schedule_root 160).
proof.
  move=> Halg.
  apply segment_poly_weighted3E => i Hi.
  have [_ Hcoeff] := Halg (i + 128) _; first smt().
  rewrite /NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_math
          /NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_block_math_at
          /NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_block_math
          /NTRUPlus768InvNTTRadix3Proof.block
          /NTRUPlus768InvNTTRadix3Proof.double_block
          /NTRUPlus768InvNTTRadix3Proof.second_base
          ifF 1:/# ifT 1:/# /= in Hcoeff.
  rewrite Hcoeff.
  rewrite /NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_omega_root
          /NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_zeta4_root
          /schedule_root /zeta_root /q /=.
  apply/IntDiv.eqmodP.
  exists (2333 * coeff input.[i]).
  ring.
qed.

lemma invntt_radix3_segment_256E
    (input output : W16.t Array768.t) :
  NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_algebra input output =>
  segment_poly output 256 128 =
  weighted3_remainder_poly input 0
    ((schedule_root 192) * (schedule_root 320))
    ((schedule_root 384) * (schedule_root 320))
    (schedule_root 320).
proof.
  move=> Halg.
  apply segment_poly_weighted3E => i Hi.
  have [_ Hcoeff] := Halg (i + 256) _; first smt().
  rewrite /NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_math
          /NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_block_math_at
          /NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_block_math
          /NTRUPlus768InvNTTRadix3Proof.block
          /NTRUPlus768InvNTTRadix3Proof.double_block
          /NTRUPlus768InvNTTRadix3Proof.second_base
          ifF 1:/# ifF 1:/# ifT 1:/# /= in Hcoeff.
  rewrite Hcoeff.
  rewrite /NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_omega_root
          /NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_zeta5_root
          /schedule_root /zeta_root /q /=.
  apply/IntDiv.eqmodP.
  exists (1571 * coeff input.[i + 128]).
  ring.
qed.

lemma invntt_radix3_segment_384E
    (input output : W16.t Array768.t) :
  NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_algebra input output =>
  segment_poly output 384 128 =
  weighted3_remainder_poly input 384 1 1 1.
proof.
  move=> Halg.
  apply segment_poly_weighted3E => i Hi.
  have [_ Hcoeff] := Halg (i + 384) _; first smt().
  rewrite /NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_math
          /NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_block_math_at
          /NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_block_math
          /NTRUPlus768InvNTTRadix3Proof.block
          /NTRUPlus768InvNTTRadix3Proof.double_block
          /NTRUPlus768InvNTTRadix3Proof.second_base
          ifF 1:/# ifF 1:/# ifF 1:/# ifT 1:/# /= in Hcoeff.
  rewrite [384 + i]addrC [512 + i]addrC [640 + i]addrC in Hcoeff.
  rewrite Hcoeff.
  by rewrite !mulz1.
qed.

lemma invntt_radix3_segment_512E
    (input output : W16.t Array768.t) :
  NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_algebra input output =>
  segment_poly output 512 128 =
  weighted3_remainder_poly input 384
    ((schedule_root 384) * (schedule_root 32))
    ((schedule_root 192) * (schedule_root 32))
    (schedule_root 32).
proof.
  move=> Halg.
  apply segment_poly_weighted3E => i Hi.
  have [_ Hcoeff] := Halg (i + 512) _; first smt().
  rewrite /NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_math
          /NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_block_math_at
          /NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_block_math
          /NTRUPlus768InvNTTRadix3Proof.block
          /NTRUPlus768InvNTTRadix3Proof.double_block
          /NTRUPlus768InvNTTRadix3Proof.second_base
          ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifT 1:/# /= in Hcoeff.
  rewrite [384 + i]addrC [512 + i]addrC [640 + i]addrC in Hcoeff.
  rewrite Hcoeff.
  rewrite /NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_omega_root
          /NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_zeta2_root
          /schedule_root /zeta_root /q /=.
  apply/IntDiv.eqmodP.
  exists (1886 * coeff input.[i + 384]).
  ring.
qed.

lemma invntt_radix3_segment_640E
    (input output : W16.t Array768.t) :
  NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_algebra input output =>
  segment_poly output 640 128 =
  weighted3_remainder_poly input 384
    ((schedule_root 192) * (schedule_root 64))
    ((schedule_root 384) * (schedule_root 64))
    (schedule_root 64).
proof.
  move=> Halg.
  apply segment_poly_weighted3E => i Hi.
  have [_ Hcoeff] := Halg (i + 640) _; first smt().
  rewrite /NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_math
          /NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_block_math_at
          /NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_block_math
          /NTRUPlus768InvNTTRadix3Proof.block
          /NTRUPlus768InvNTTRadix3Proof.double_block
          /NTRUPlus768InvNTTRadix3Proof.second_base
          ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# /= in Hcoeff.
  rewrite [384 + i]addrC [512 + i]addrC [640 + i]addrC in Hcoeff.
  rewrite Hcoeff.
  rewrite /NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_omega_root
          /NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_zeta3_root
          /schedule_root /zeta_root /q /=.
  apply/IntDiv.eqmodP.
  exists (3200 * coeff input.[i + 512]).
  ring.
qed.

lemma invntt_radix3_output_segment_0E
    (input output : W16.t Array768.t) :
  NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_algebra input output =>
  segment_poly output 0 384 =
    weighted3_remainder_poly input 0 1 1 1 +
    weighted3_remainder_poly input 0
      ((schedule_root 384) * (schedule_root 160))
      ((schedule_root 192) * (schedule_root 160))
      (schedule_root 160) * exp X 128 +
    weighted3_remainder_poly input 0
      ((schedule_root 192) * (schedule_root 320))
      ((schedule_root 384) * (schedule_root 320))
      (schedule_root 320) * exp X 256.
proof.
  move=> Halg.
  rewrite segment_poly_split3 /segment3_poly.
  rewrite (invntt_radix3_segment_0E input output Halg).
  rewrite (invntt_radix3_segment_128E input output Halg).
  rewrite (invntt_radix3_segment_256E input output Halg).
  rewrite -exp_X128_2 NTRUPoly.PolyComRing.expr2.
  apply segment3_layout.
qed.

lemma invntt_radix3_output_segment_384E
    (input output : W16.t Array768.t) :
  NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_algebra input output =>
  segment_poly output 384 384 =
    weighted3_remainder_poly input 384 1 1 1 +
    weighted3_remainder_poly input 384
      ((schedule_root 384) * (schedule_root 32))
      ((schedule_root 192) * (schedule_root 32))
      (schedule_root 32) * exp X 128 +
    weighted3_remainder_poly input 384
      ((schedule_root 192) * (schedule_root 64))
      ((schedule_root 384) * (schedule_root 64))
      (schedule_root 64) * exp X 256.
proof.
  move=> Halg.
  rewrite segment_poly_split3 /segment3_poly.
  rewrite (invntt_radix3_segment_384E input output Halg).
  rewrite (invntt_radix3_segment_512E input output Halg).
  rewrite (invntt_radix3_segment_640E input output Halg).
  rewrite -exp_X128_2 NTRUPoly.PolyComRing.expr2.
  apply segment3_layout.
qed.

lemma invntt_radix3_output_segment_0_recombineE
    (input output : W16.t Array768.t) :
  NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_algebra input output =>
  segment_poly output 0 384 =
    segment_poly input 0 128 +
    segment_poly input 128 128 +
    segment_poly input 256 128 +
    root_poly 160 *
      (segment_poly input 256 128 - segment_poly input 0 128 +
       root_poly 192 * (segment_poly input 128 128 - segment_poly input 0 128)) *
      exp X 128 +
    root_poly 320 *
      (segment_poly input 256 128 - segment_poly input 128 128 -
       root_poly 192 * (segment_poly input 128 128 - segment_poly input 0 128)) *
      exp (exp X 128) 2.
proof.
  move=> Halg.
  rewrite (invntt_radix3_output_segment_0E input output Halg).
  rewrite (weighted3_remainder_poly_oneE input 0).
  rewrite (weighted3_remainder_scheduleE input 0 160) 1:/#.
  rewrite (weighted3_remainder_schedule_swappedE input 0 320) 1:/#.
  rewrite exp_X128_2.
  rewrite omega_poly_384E.
  rewrite (invntt_radix3_weighted_firstE
    (segment_poly input 0 128)
    (segment_poly input 128 128)
    (segment_poly input 256 128)
    (root_poly 160) (root_poly 192)).
  rewrite (invntt_radix3_weighted_secondE
    (segment_poly input 0 128)
    (segment_poly input 128 128)
    (segment_poly input 256 128)
    (root_poly 320) (root_poly 192)).
  done.
qed.

lemma invntt_radix3_output_segment_384_recombineE
    (input output : W16.t Array768.t) :
  NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_algebra input output =>
  segment_poly output 384 384 =
    segment_poly input 384 128 +
    segment_poly input 512 128 +
    segment_poly input 640 128 +
    root_poly 32 *
      (segment_poly input 640 128 - segment_poly input 384 128 +
       root_poly 192 * (segment_poly input 512 128 - segment_poly input 384 128)) *
      exp X 128 +
    root_poly 64 *
      (segment_poly input 640 128 - segment_poly input 512 128 -
       root_poly 192 * (segment_poly input 512 128 - segment_poly input 384 128)) *
      exp (exp X 128) 2.
proof.
  move=> Halg.
  rewrite (invntt_radix3_output_segment_384E input output Halg).
  rewrite (weighted3_remainder_poly_oneE input 384).
  rewrite (weighted3_remainder_scheduleE input 384 32) 1:/#.
  rewrite (weighted3_remainder_schedule_swappedE input 384 64) 1:/#.
  rewrite exp_X128_2.
  rewrite omega_poly_384E.
  rewrite (invntt_radix3_weighted_firstE
    (segment_poly input 384 128)
    (segment_poly input 512 128)
    (segment_poly input 640 128)
    (root_poly 32) (root_poly 192)).
  rewrite (invntt_radix3_weighted_secondE
    (segment_poly input 384 128)
    (segment_poly input 512 128)
    (segment_poly input 640 128)
    (root_poly 64) (root_poly 192)).
  done.
qed.
