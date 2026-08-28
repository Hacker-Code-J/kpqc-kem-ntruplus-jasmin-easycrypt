(* Interpolation lemmas for the inverse radix-3 layer. *)
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

op invntt_radix3_child0 (r x : poly) : poly = x - r.

op invntt_radix3_child1 (r w x : poly) : poly = x - r * w.

op invntt_radix3_child2 (r w x : poly) : poly = x - r * (w * w).

op invntt_radix3_interp0_poly (u v w x : poly) : poly =
  poly1 + u * w * w * x + v * w * x * x.

op invntt_radix3_interp1_poly (u v w x : poly) : poly =
  poly1 + u * w * x + v * w * w * x * x.

op invntt_radix3_interp2_poly (u v x : poly) : poly =
  poly1 + u * x + v * x * x.

op invntt_radix3_factor_product (r w x : poly) : poly =
  invntt_radix3_child0 r x *
    (invntt_radix3_child1 r w x * invntt_radix3_child2 r w x).

op invntt_radix3_witness
    (s0 s1 s2 v w : poly) : poly =
  v * w * s0 + v * w * w * s1 + v * s2.

op invntt_radix3_recombine_value
    (a0 a1 a2 u v w x : poly) : poly =
  a0 + a1 + a2 +
    u * (a2 - a0 + w * (a1 - a0)) * x +
    v * (a2 - a1 - w * (a1 - a0)) * (x * x).

lemma invntt_radix3_interp0_polyE
    (u v r w x : poly) :
  poly1 + w + w * w = poly0 =>
  u * r = w =>
  v * r = u * w =>
  invntt_radix3_interp0_poly u v w x =
    v * w *
      (invntt_radix3_child1 r w x * invntt_radix3_child2 r w x).
proof.
  move=> Hw Hu Hv.
  rewrite /invntt_radix3_interp0_poly
          /invntt_radix3_child1 /invntt_radix3_child2.
  have Hfactor :
      (poly1 + u * w * w * x + v * w * x * x) -
        v * w * ((x - r * w) * (x - r * (w * w))) =
      (v * w * r * x -
        (w - poly1) * (w * w * w + poly1)) *
          (poly1 + w + w * w) -
      (w * w * w * w * w) * (u * r - w) -
      (w * x + r * w * w * w * w) * (v * r - u * w) by ring.
  rewrite Hw Hu Hv in Hfactor.
  have Hzero :
      (poly1 + u * w * w * x + v * w * x * x) -
        v * w * ((x - r * w) * (x - r * (w * w))) = poly0.
  + rewrite Hfactor.
    ring.
  rewrite -NTRUPoly.PolyComRing.subr_eq0.
  exact Hzero.
qed.

lemma invntt_radix3_interp1_polyE
    (u v r w x : poly) :
  poly1 + w + w * w = poly0 =>
  u * r = w =>
  v * r = u * w =>
  invntt_radix3_interp1_poly u v w x =
    v * w * w *
      (invntt_radix3_child0 r x * invntt_radix3_child2 r w x).
proof.
  move=> Hw Hu Hv.
  rewrite /invntt_radix3_interp1_poly
          /invntt_radix3_child0 /invntt_radix3_child2.
  have Hfactor :
      (poly1 + u * w * x + v * w * w * x * x) -
        v * w * w * ((x - r) * (x - r * (w * w))) =
      (v * r * w * w * x - u * w * (w - poly1) * x -
        (w - poly1) * (w * w * w + poly1)) *
          (poly1 + w + w * w) -
      (w * w * w * w * w) * (u * r - w) -
      (w * w * w * x + r * w * w * w * w) *
        (v * r - u * w) by ring.
  rewrite Hw Hu Hv in Hfactor.
  have Hzero :
      (poly1 + u * w * x + v * w * w * x * x) -
        v * w * w * ((x - r) * (x - r * (w * w))) = poly0.
  + rewrite Hfactor.
    ring.
  rewrite -NTRUPoly.PolyComRing.subr_eq0.
  exact Hzero.
qed.

lemma invntt_radix3_interp2_polyE
    (u v r w x : poly) :
  poly1 + w + w * w = poly0 =>
  u * r = w =>
  v * r = u * w =>
  invntt_radix3_interp2_poly u v x =
    v * (invntt_radix3_child0 r x * invntt_radix3_child1 r w x).
proof.
  move=> Hw Hu Hv.
  rewrite /invntt_radix3_interp2_poly
          /invntt_radix3_child0 /invntt_radix3_child1.
  have Hfactor :
      (poly1 + u * x + v * x * x) -
        v * ((x - r) * (x - r * w)) =
      ((v * r - u * (w - poly1)) * x - (w - poly1)) *
          (poly1 + w + w * w) -
      (w * w) * (u * r - w) -
      (w * w * x + r * w) * (v * r - u * w) by ring.
  rewrite Hw Hu Hv in Hfactor.
  have Hzero :
      (poly1 + u * x + v * x * x) -
        v * ((x - r) * (x - r * w)) = poly0.
  + rewrite Hfactor.
    ring.
  rewrite -NTRUPoly.PolyComRing.subr_eq0.
  exact Hzero.
qed.

lemma invntt_radix3_weighted_factorE
    (s0 s1 s2 v w f0 f1 f2 : poly) :
  s0 * f0 * (v * w * (f1 * f2)) +
    s1 * f1 * (v * w * w * (f0 * f2)) +
    s2 * f2 * (v * (f0 * f1)) =
  (v * w * s0 + v * w * w * s1 + v * s2) *
    (f0 * (f1 * f2)).
proof. ring. qed.

lemma invntt_radix3_interpolation_components_factorE
    (s0 s1 s2 u v r w x : poly) :
  poly1 + w + w * w = poly0 =>
  u * r = w =>
  v * r = u * w =>
  s0 * invntt_radix3_child0 r x * invntt_radix3_interp0_poly u v w x +
    s1 * invntt_radix3_child1 r w x *
      invntt_radix3_interp1_poly u v w x +
    s2 * invntt_radix3_child2 r w x *
      invntt_radix3_interp2_poly u v x =
  invntt_radix3_witness s0 s1 s2 v w *
    invntt_radix3_factor_product r w x.
proof.
  move=> Hw Hu Hv.
  rewrite (invntt_radix3_interp0_polyE u v r w x Hw Hu Hv).
  rewrite (invntt_radix3_interp1_polyE u v r w x Hw Hu Hv).
  rewrite (invntt_radix3_interp2_polyE u v r w x Hw Hu Hv).
  rewrite /invntt_radix3_witness /invntt_radix3_factor_product.
  exact (invntt_radix3_weighted_factorE s0 s1 s2 v w
    (invntt_radix3_child0 r x)
    (invntt_radix3_child1 r w x)
    (invntt_radix3_child2 r w x)).
qed.

lemma invntt_radix3_recombine_valueE
    (a0 a1 a2 u v w x : poly) :
  poly1 + w + w * w = poly0 =>
  invntt_radix3_recombine_value a0 a1 a2 u v w x =
    a0 * invntt_radix3_interp0_poly u v w x +
    a1 * invntt_radix3_interp1_poly u v w x +
    a2 * invntt_radix3_interp2_poly u v x.
proof.
  move=> Hw.
  rewrite /invntt_radix3_recombine_value
          /invntt_radix3_interp0_poly
          /invntt_radix3_interp1_poly
          /invntt_radix3_interp2_poly.
  exact (invntt_radix3_residual_decomp a0 a1 a2 u v w x Hw).
qed.

lemma invntt_radix3_abstract_recombine
    (p a0 a1 a2 u v r w x : poly) :
  poly1 + w + w * w = poly0 =>
  u * r = w =>
  v * r = u * w =>
  (exists s0, a0 - p = s0 * invntt_radix3_child0 r x) =>
  (exists s1, a1 - p = s1 * invntt_radix3_child1 r w x) =>
  (exists s2, a2 - p = s2 * invntt_radix3_child2 r w x) =>
  exists h,
    invntt_radix3_recombine_value a0 a1 a2 u v w x -
      (p + p + p) =
    h * invntt_radix3_factor_product r w x.
proof.
  move=> Hw Hu Hv [s0 H0] [s1 H1] [s2 H2].
  exists (invntt_radix3_witness s0 s1 s2 v w).
  have Hlhs :
      invntt_radix3_recombine_value a0 a1 a2 u v w x - (p + p + p) =
      invntt_radix3_recombine_value
        (a0 - p) (a1 - p) (a2 - p) u v w x by
        rewrite /invntt_radix3_recombine_value; ring.
  rewrite Hlhs H0 H1 H2.
  rewrite (invntt_radix3_recombine_valueE
    (s0 * invntt_radix3_child0 r x)
    (s1 * invntt_radix3_child1 r w x)
    (s2 * invntt_radix3_child2 r w x) u v w x Hw).
  exact (invntt_radix3_interpolation_components_factorE
    s0 s1 s2 u v r w x Hw Hu Hv).
qed.

lemma invntt_radix3_sub_right_congr (a b c : poly) :
  b = c => a - b = a - c.
proof. move=> ->; done. qed.

lemma invntt_radix3_mul_right_congr (a b c : poly) :
  b = c => a * b = a * c.
proof. move=> ->; done. qed.

lemma invntt_radix3_schedule_factor_rootE (m e : int) :
  schedule_factor_modulus m e = exp X m - root_poly e.
proof. rewrite /schedule_factor_modulus /root_poly; done. qed.

lemma invntt_radix3_schedule_factor_shift192E (m e : int) :
  0 <= e =>
  schedule_factor_modulus m (e + 192) =
    exp X m - root_poly e * root_poly 192.
proof.
  move=> He.
  have H192 : 0 <= 192 by smt().
  have Hmul := root_poly_mulE e 192 He H192.
  rewrite /schedule_factor_modulus.
  apply invntt_radix3_sub_right_congr.
  change (root_poly (e + 192) = root_poly e * root_poly 192).
  apply/eq_sym.
  exact Hmul.
qed.

lemma invntt_radix3_schedule_factor_shift384E (m e : int) :
  0 <= e =>
  schedule_factor_modulus m (e + 384) =
    exp X m - root_poly e * (root_poly 192 * root_poly 192).
proof.
  move=> He.
  have H192 : 0 <= 192 by smt().
  have H384 : 0 <= 384 by smt().
  have Hsquare := root_poly_mulE 192 192 H192 H192.
  have Houter := root_poly_mulE e 384 He H384.
  rewrite /schedule_factor_modulus.
  apply invntt_radix3_sub_right_congr.
  change
    (root_poly (e + 384) =
     root_poly e * (root_poly 192 * root_poly 192)).
  apply/eq_sym.
  apply: (eq_trans _ (root_poly e * root_poly 384)).
  + apply invntt_radix3_mul_right_congr.
    exact Hsquare.
  + exact Houter.
qed.

lemma invntt_radix3_factor_modulusE (e : int) :
  0 <= e =>
  schedule_factor_modulus 384 (3 * e) =
    invntt_radix3_factor_product
      (root_poly e) (root_poly 192) (exp X 128).
proof.
  move=> He.
  have Hsplit :
      schedule_factor_modulus 384 (3 * e) =
      schedule_factor_modulus 128 e *
        (schedule_factor_modulus 128 (e + 192) *
         schedule_factor_modulus 128 (e + 384)).
  + move: (factor_split3 X 128 e _ _); 1,2: smt().
    rewrite /factor /schedule_factor_modulus /=.
    done.
  rewrite Hsplit.
  rewrite (invntt_radix3_schedule_factor_rootE 128 e).
  rewrite (invntt_radix3_schedule_factor_shift192E 128 e He).
  rewrite (invntt_radix3_schedule_factor_shift384E 128 e He).
  rewrite /invntt_radix3_factor_product
          /invntt_radix3_child0 /invntt_radix3_child1
          /invntt_radix3_child2.
  done.
qed.

lemma invntt_radix3_recombine_value_algorithmE
    (a0 a1 a2 u v w x : poly) :
  invntt_radix3_recombine_value a0 a1 a2 u v w x =
    a0 + a1 + a2 +
      u * (a2 - a0 + w * (a1 - a0)) * x +
      v * (a2 - a1 - w * (a1 - a0)) * exp x 2.
proof.
  rewrite /invntt_radix3_recombine_value
          NTRUPoly.PolyComRing.expr2.
  done.
qed.

lemma invntt_radix3_recombine_factor_eqm_core
    (p a0 a1 a2 : NTRUPoly.poly) (e u v : int) :
  0 <= e =>
  0 <= u =>
  0 <= v =>
  u + e = 192 =>
  v + 2 * e = 384 =>
  factor_eqm 128 e p a0 =>
  factor_eqm 128 (e + 192) p a1 =>
  factor_eqm 128 (e + 384) p a2 =>
  factor_eqm 384 (3 * e) (p + p + p)
    (invntt_radix3_recombine_value
      a0 a1 a2 (root_poly u) (root_poly v) (root_poly 192) (exp X 128)).
proof.
  move=> He Hu Hv Hsum1 Hsum2 H0 H1 H2.
  rewrite /factor_eqm (invntt_radix3_factor_modulusE e He).
  rewrite /factor_eqm (invntt_radix3_schedule_factor_rootE 128 e) in H0.
  rewrite /factor_eqm (invntt_radix3_schedule_factor_shift192E 128 e He) in H1.
  rewrite /factor_eqm (invntt_radix3_schedule_factor_shift384E 128 e He) in H2.
  have H192 : 0 <= 192 by smt().
  have HuE : root_poly u * root_poly e = root_poly 192.
  + have Hmul := root_poly_mulE u e Hu He.
    rewrite Hsum1 in Hmul.
    exact Hmul.
  have HvrE :
      root_poly v * root_poly e = root_poly u * root_poly 192.
  + have Hvroot := root_poly_mulE v e Hv He.
    have Huroot := root_poly_mulE u 192 Hu H192.
    rewrite Hvroot Huroot.
    congr.
    smt().
  have Hroot384 :
      root_poly 192 * root_poly 192 = root_poly 384.
  + exact (root_poly_mulE 192 192 H192 H192).
  have Homega :
      poly1 + root_poly 192 + root_poly 192 * root_poly 192 = poly0.
  + rewrite Hroot384.
    exact omega_poly_sumE.
  apply (invntt_radix3_abstract_recombine
    p a0 a1 a2
    (root_poly u) (root_poly v) (root_poly e) (root_poly 192) (exp X 128)).
  + exact Homega.
  + exact HuE.
  + exact HvrE.
  + exact H0.
  + exact H1.
  + exact H2.
qed.

lemma invntt_radix3_recombine_factor_eqm
    (p a0 a1 a2 : NTRUPoly.poly) (e u v : int) :
  0 <= e =>
  0 <= u =>
  0 <= v =>
  u + e = 192 =>
  v + 2 * e = 384 =>
  factor_eqm 128 e p a0 =>
  factor_eqm 128 (e + 192) p a1 =>
  factor_eqm 128 (e + 384) p a2 =>
  factor_eqm 384 (3 * e) (p + p + p)
    (a0 + a1 + a2 +
     root_poly u * (a2 - a0 + root_poly 192 * (a1 - a0)) * exp X 128 +
     root_poly v * (a2 - a1 - root_poly 192 * (a1 - a0)) * exp (exp X 128) 2).
proof.
  move=> He Hu Hv Hsum1 Hsum2 H0 H1 H2.
  rewrite -(invntt_radix3_recombine_value_algorithmE
    a0 a1 a2 (root_poly u) (root_poly v) (root_poly 192) (exp X 128)).
  apply (invntt_radix3_recombine_factor_eqm_core
    p a0 a1 a2 e u v).
  + exact He.
  + exact Hu.
  + exact Hv.
  + exact Hsum1.
  + exact Hsum2.
  + exact H0.
  + exact H1.
  + exact H2.
qed.
