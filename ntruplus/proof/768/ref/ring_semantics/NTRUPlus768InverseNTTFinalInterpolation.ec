(* CRT interpolation and scale cancellation for inverse-NTT finalization. *)
require import AllCore IntDiv List Ring StdBigop StdOrder.

require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768CyclotomicFactorization.
require import NTRUPlus768EvaluationSemantics.
require import NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768ForwardNTTRadix3Semantics.
require import NTRUPlus768TerminalRepresentation.
require import NTRUPlus768InvNTTFinalAlgebra.
require import NTRUPlus768InverseNTTRadix2_8Semantics.
require import NTRUPlus768InverseNTTRadix2_16Semantics.
require import NTRUPlus768InverseNTTRadix2_32Semantics.
require import NTRUPlus768InverseNTTRadix2_64Semantics.
require import NTRUPlus768InverseNTTRadix3Recombination.
require import NTRUPlus768InverseNTTRadix3Semantics.
require import NTRUPlus768InverseNTTFinalRecombination.

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

op invntt_final_scale_poly : poly =
  polyC
    (lift_int NTRUPlus768InvNTTFinalAlgebra.twoninv_root).

op invntt_final_linear_recombine
    (a0 a1 l0 l1 h0 h1 y : poly) : poly =
  l0 * a0 + l1 * a1 + (h0 * a0 + h1 * a1) * y.

lemma poly_lift_addE (a b : int) :
  polyC (lift_int (a + b)) =
  polyC (lift_int a) + polyC (lift_int b).
proof.
  rewrite /lift_int CycloFq.incyclocoeffD NTRUPoly.polyCD.
  done.
qed.

lemma poly_lift_modE (a b : int) :
  a %% q = b %% q =>
  polyC (lift_int a) = polyC (lift_int b).
proof.
  move=> Hab.
  rewrite (lift_int_eq a b Hab).
  done.
qed.

lemma invntt_final_low0_modE :
  invntt_final_low0_coeff %% q = 1738 %% q.
proof.
  rewrite /invntt_final_low0_coeff
          /NTRUPlus768InvNTTFinalAlgebra.zminusz5inv_root
          /NTRUPlus768InvNTTFinalAlgebra.ninv_root /q /=.
  done.
qed.

lemma invntt_final_low1_modE :
  invntt_final_low1_coeff %% q = 1683 %% q.
proof.
  rewrite /invntt_final_low1_coeff
          /NTRUPlus768InvNTTFinalAlgebra.zminusz5inv_root
          /NTRUPlus768InvNTTFinalAlgebra.ninv_root /q /=.
  done.
qed.

lemma invntt_final_high0_modE :
  invntt_final_high0_coeff %% q = 3402 %% q.
proof.
  rewrite /invntt_final_high0_coeff
          /NTRUPlus768InvNTTFinalAlgebra.zminusz5inv_root
          /NTRUPlus768InvNTTFinalAlgebra.twoninv_root /q /=.
  done.
qed.

lemma invntt_final_high1_modE :
  invntt_final_high1_coeff %% q = 55 %% q.
proof.
  rewrite /invntt_final_high1_coeff
          /NTRUPlus768InvNTTFinalAlgebra.zminusz5inv_root
          /NTRUPlus768InvNTTFinalAlgebra.twoninv_root /q /=.
  done.
qed.

lemma invntt_final_low0_polyE :
  polyC (lift_int invntt_final_low0_coeff) = polyC (lift_int 1738).
proof. exact (poly_lift_modE _ _ invntt_final_low0_modE). qed.

lemma invntt_final_low1_polyE :
  polyC (lift_int invntt_final_low1_coeff) = polyC (lift_int 1683).
proof. exact (poly_lift_modE _ _ invntt_final_low1_modE). qed.

lemma invntt_final_high0_polyE :
  polyC (lift_int invntt_final_high0_coeff) = polyC (lift_int 3402).
proof. exact (poly_lift_modE _ _ invntt_final_high0_modE). qed.

lemma invntt_final_high1_polyE :
  polyC (lift_int invntt_final_high1_coeff) = polyC (lift_int 55).
proof. exact (poly_lift_modE _ _ invntt_final_high1_modE). qed.

lemma invntt_final_root96E :
  root_poly 96 = polyC (lift_int 2735).
proof. by rewrite /root_poly zeta96E /lift_int. qed.

lemma invntt_final_root480E :
  root_poly 480 = polyC (lift_int 723).
proof. by rewrite /root_poly zeta480E /lift_int. qed.

lemma invntt_final_low_sumE :
  polyC (lift_int invntt_final_low0_coeff) +
    polyC (lift_int invntt_final_low1_coeff) =
  invntt_final_scale_poly.
proof.
  rewrite invntt_final_low0_polyE invntt_final_low1_polyE.
  rewrite /invntt_final_scale_poly
          /NTRUPlus768InvNTTFinalAlgebra.twoninv_root.
  rewrite -(poly_lift_addE 1738 1683).
  apply poly_lift_modE.
  rewrite /q /=.
  done.
qed.

lemma invntt_final_high_sumE :
  polyC (lift_int invntt_final_high0_coeff) +
    polyC (lift_int invntt_final_high1_coeff) = poly0.
proof.
  rewrite invntt_final_high0_polyE invntt_final_high1_polyE.
  rewrite -(poly_lift_addE 3402 55).
  have Hmod : (3402 + 55) %% q = 0 %% q by rewrite /q /=.
  rewrite (poly_lift_modE (3402 + 55) 0 Hmod) poly_lift_zeroE.
  done.
qed.

lemma invntt_final_low_at_root480E :
  polyC (lift_int invntt_final_low0_coeff) +
    polyC (lift_int invntt_final_high0_coeff) * root_poly 480 = poly0.
proof.
  rewrite invntt_final_low0_polyE invntt_final_high0_polyE
          invntt_final_root480E.
  rewrite -(poly_lift_mulE 723 3402).
  rewrite -(poly_lift_addE 1738 (3402 * 723)).
  have Hmod : (1738 + 3402 * 723) %% q = 0 %% q by rewrite /q /=.
  rewrite (poly_lift_modE (1738 + 3402 * 723) 0 Hmod)
          poly_lift_zeroE.
  done.
qed.

lemma invntt_final_high_at_root96E :
  polyC (lift_int invntt_final_low1_coeff) +
    polyC (lift_int invntt_final_high1_coeff) * root_poly 96 = poly0.
proof.
  rewrite invntt_final_low1_polyE invntt_final_high1_polyE
          invntt_final_root96E.
  rewrite -(poly_lift_mulE 2735 55).
  rewrite -(poly_lift_addE 1683 (55 * 2735)).
  have Hmod : (1683 + 55 * 2735) %% q = 0 %% q by rewrite /q /=.
  rewrite (poly_lift_modE (1683 + 55 * 2735) 0 Hmod)
          poly_lift_zeroE.
  done.
qed.

lemma poly_scale_sumE (a b : int) (p : poly) :
  polyC (lift_int a) * p + polyC (lift_int b) * p =
    polyC (lift_int (a + b)) * p.
proof.
  rewrite (poly_lift_addE a b).
  ring.
qed.

lemma poly_scale_sum_modE (a b c : int) (p : poly) :
  (a + b) %% q = c %% q =>
  polyC (lift_int a) * p + polyC (lift_int b) * p =
    polyC (lift_int c) * p.
proof.
  move=> Hmod.
  rewrite (poly_scale_sumE a b p).
  rewrite (poly_lift_modE (a + b) c Hmod).
  done.
qed.

lemma poly_doubleE (p : poly) :
  p + p = polyC (lift_int 2) * p.
proof.
  apply: (eq_trans _
    (polyC (lift_int 1) * p + polyC (lift_int 1) * p)).
  + rewrite !poly_lift_oneE.
    ring.
  + exact (poly_scale_sumE 1 1 p).
qed.

lemma doubled_twice_polyE (p : poly) :
  doubled_twice p = polyC (lift_int 4) * p.
proof.
  apply: (eq_trans _
    (polyC (lift_int 2) * p + polyC (lift_int 2) * p)).
  + rewrite /doubled_twice !poly_doubleE.
    done.
  have Hmod : (2 + 2) %% q = 4 %% q by rewrite /q /=.
  exact (poly_scale_sum_modE 2 2 4 p Hmod).
qed.

lemma doubled_thrice_polyE (p : poly) :
  doubled_thrice p = polyC (lift_int 8) * p.
proof.
  apply: (eq_trans _
    (polyC (lift_int 4) * p + polyC (lift_int 4) * p)).
  + rewrite /doubled_thrice !doubled_twice_polyE.
    done.
  have Hmod : (4 + 4) %% q = 8 %% q by rewrite /q /=.
  exact (poly_scale_sum_modE 4 4 8 p Hmod).
qed.

lemma doubled_four_times_polyE (p : poly) :
  doubled_four_times p = polyC (lift_int 16) * p.
proof.
  apply: (eq_trans _
    (polyC (lift_int 8) * p + polyC (lift_int 8) * p)).
  + rewrite /doubled_four_times !doubled_thrice_polyE.
    done.
  have Hmod : (8 + 8) %% q = 16 %% q by rewrite /q /=.
  exact (poly_scale_sum_modE 8 8 16 p Hmod).
qed.

lemma doubled_five_times_polyE (p : poly) :
  doubled_five_times p = polyC (lift_int 32) * p.
proof.
  apply: (eq_trans _
    (polyC (lift_int 16) * p + polyC (lift_int 16) * p)).
  + rewrite /doubled_five_times !doubled_four_times_polyE.
    done.
  have Hmod : (16 + 16) %% q = 32 %% q by rewrite /q /=.
  exact (poly_scale_sum_modE 16 16 32 p Hmod).
qed.

lemma tripled_five_times_polyE (p : poly) :
  tripled_five_times p = polyC (lift_int 96) * p.
proof.
  apply: (eq_trans _
    (polyC (lift_int 32) * p + polyC (lift_int 32) * p +
     polyC (lift_int 32) * p)).
  + rewrite /tripled_five_times !doubled_five_times_polyE.
    done.
  have H64 :
      polyC (lift_int 32) * p + polyC (lift_int 32) * p =
      polyC (lift_int 64) * p.
  + have Hmod : (32 + 32) %% q = 64 %% q by rewrite /q /=.
    exact (poly_scale_sum_modE 32 32 64 p Hmod).
  rewrite H64.
  have Hmod : (64 + 32) %% q = 96 %% q by rewrite /q /=.
  exact (poly_scale_sum_modE 64 32 96 p Hmod).
qed.

lemma invntt_final_scale_inverseE :
  invntt_final_scale_poly * polyC (lift_int 96) = poly1.
proof.
  rewrite /invntt_final_scale_poly
          /NTRUPlus768InvNTTFinalAlgebra.twoninv_root.
  rewrite -(poly_lift_mulE 96 3421).
  have Hmod : (3421 * 96) %% q = 1 %% q by rewrite /q /=.
  rewrite (poly_lift_modE (3421 * 96) 1 Hmod) poly_lift_oneE.
  done.
qed.

lemma invntt_final_scale_cancels_tripled (p : poly) :
  invntt_final_scale_poly * tripled_five_times p = p.
proof.
  rewrite tripled_five_times_polyE.
  apply: (eq_trans _
    ((invntt_final_scale_poly * polyC (lift_int 96)) * p)).
  + exact (NTRUPoly.PolyComRing.mulrA
      invntt_final_scale_poly (polyC (lift_int 96)) p).
  + rewrite invntt_final_scale_inverseE.
    ring.
qed.

lemma invntt_final_interpolation_residualE
    (s t l0 l1 h0 h1 z0 z1 y : poly) :
  l0 + h0 * z1 = poly0 =>
  l1 + h1 * z0 = poly0 =>
  invntt_final_linear_recombine
      (s * (y - z0)) (t * (y - z1)) l0 l1 h0 h1 y =
    (s * h0 + t * h1) * ((y - z0) * (y - z1)).
proof.
  move=> Hlow Hhigh.
  have Hfactor :
      invntt_final_linear_recombine
          (s * (y - z0)) (t * (y - z1)) l0 l1 h0 h1 y -
        (s * h0 + t * h1) * ((y - z0) * (y - z1)) =
      s * (y - z0) * (l0 + h0 * z1) +
        t * (y - z1) * (l1 + h1 * z0) by
        rewrite /invntt_final_linear_recombine; ring.
  rewrite Hlow Hhigh in Hfactor.
  have Hzero :
      invntt_final_linear_recombine
          (s * (y - z0)) (t * (y - z1)) l0 l1 h0 h1 y -
        (s * h0 + t * h1) * ((y - z0) * (y - z1)) = poly0.
  + rewrite Hfactor.
    ring.
  rewrite -NTRUPoly.PolyComRing.subr_eq0.
  exact Hzero.
qed.

lemma invntt_final_abstract_recombine
    (p scaled a0 a1 l0 l1 h0 h1 scale z0 z1 y : poly) :
  l0 + l1 = scale =>
  h0 + h1 = poly0 =>
  l0 + h0 * z1 = poly0 =>
  l1 + h1 * z0 = poly0 =>
  scale * scaled = p =>
  (exists s, a0 - scaled = s * (y - z0)) =>
  (exists t, a1 - scaled = t * (y - z1)) =>
  exists h,
    invntt_final_linear_recombine a0 a1 l0 l1 h0 h1 y - p =
      h * ((y - z0) * (y - z1)).
proof.
  move=> Hlsum Hhsum Hlow Hhigh Hscale [s H0] [t H1].
  exists (s * h0 + t * h1).
  have Hdecomp :
      invntt_final_linear_recombine a0 a1 l0 l1 h0 h1 y - p =
      invntt_final_linear_recombine
        (a0 - scaled) (a1 - scaled) l0 l1 h0 h1 y +
      (invntt_final_linear_recombine
        scaled scaled l0 l1 h0 h1 y - p) by
        rewrite /invntt_final_linear_recombine; ring.
  have Hbase :
      invntt_final_linear_recombine
        scaled scaled l0 l1 h0 h1 y = scale * scaled.
  + have Hfactor :
        invntt_final_linear_recombine
            scaled scaled l0 l1 h0 h1 y - scale * scaled =
        (l0 + l1 - scale) * scaled +
          (h0 + h1) * scaled * y by
          rewrite /invntt_final_linear_recombine; ring.
    rewrite Hlsum Hhsum in Hfactor.
    have Hzero :
        invntt_final_linear_recombine
            scaled scaled l0 l1 h0 h1 y - scale * scaled = poly0.
    + rewrite Hfactor.
      ring.
    rewrite -NTRUPoly.PolyComRing.subr_eq0.
    exact Hzero.
  rewrite Hdecomp H0 H1 Hbase Hscale.
  have Hres := invntt_final_interpolation_residualE
    s t l0 l1 h0 h1 z0 z1 y Hlow Hhigh.
  rewrite Hres.
  ring.
qed.

lemma invntt_final_recombine_valueE (a0 a1 : poly) :
  invntt_final_recombine_value a0 a1 =
  invntt_final_linear_recombine a0 a1
    (polyC (lift_int invntt_final_low0_coeff))
    (polyC (lift_int invntt_final_low1_coeff))
    (polyC (lift_int invntt_final_high0_coeff))
    (polyC (lift_int invntt_final_high1_coeff))
    (exp X 384).
proof. rewrite /invntt_final_recombine_value /invntt_final_linear_recombine; done. qed.

lemma invntt_final_factor_product_globalE :
  (exp X 384 - root_poly 96) *
    (exp X 384 - root_poly 480) = global_modulus.
proof.
  move: stage1_factor_moduli_global.
  rewrite /schedule_factor_modulus -/root_poly.
  done.
qed.

lemma invntt_final_recombine_eqm_global
    (p a0 a1 : poly) :
  factor_eqm 384 96 (tripled_five_times p) a0 =>
  factor_eqm 384 480 (tripled_five_times p) a1 =>
  eqm_global p (invntt_final_recombine_value a0 a1).
proof.
  move=> H0 H1.
  rewrite /factor_eqm /schedule_factor_modulus -/root_poly in H0.
  rewrite /factor_eqm /schedule_factor_modulus -/root_poly in H1.
  rewrite /eqm_global invntt_final_recombine_valueE.
  have H := invntt_final_abstract_recombine
    p (tripled_five_times p) a0 a1
    (polyC (lift_int invntt_final_low0_coeff))
    (polyC (lift_int invntt_final_low1_coeff))
    (polyC (lift_int invntt_final_high0_coeff))
    (polyC (lift_int invntt_final_high1_coeff))
    invntt_final_scale_poly
    (root_poly 96) (root_poly 480) (exp X 384)
    invntt_final_low_sumE invntt_final_high_sumE
    invntt_final_low_at_root480E invntt_final_high_at_root96E
    (invntt_final_scale_cancels_tripled p) H0 H1.
  move: H => [h Hh].
  exists h.
  rewrite Hh invntt_final_factor_product_globalE.
  done.
qed.
