require import AllCore IntDiv List Ring StdBigop StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array768.
require import NTRUPlus768CyclotomicFactorization.
require import NTRUPlus768EvaluationSemantics.
require import NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768NTTSchedule.
require import NTRUPlus768NTTRadix3.
require import NTRUPlus768NTTRadix3Algebra NTRUPlus768NTTRadix3Proof.

import NTRUPoly.BigPoly.

(* The mixed-radix layer refines each degree-384 stage1 representative into
   three degree-128 representatives. *)

lemma segment_poly_split
    (a : W16.t Array768.t) (base l1 l2 : int) :
  0 <= l1 =>
  0 <= l2 =>
  segment_poly a base (l1 + l2) =
    segment_poly a base l1 +
    segment_poly a (base + l1) l2 * exp X l1.
proof.
  move=> Hl1 Hl2.
  rewrite /segment_poly.
  rewrite (PCA.big_cat_int l1) 1:/# 1:/#.
  have Hshift :
      PCA.bigi predT
        (fun i => polyC (lift_word a.[i + base]) * exp X i)
        l1 (l1 + l2) =
      PCA.bigi predT
        (fun i =>
          polyC (lift_word a.[(i + l1) + base]) * exp X (i + l1))
        0 l2.
  + rewrite (PCA.big_addn 0 (l1 + l2) l1) /=.
    have -> : l1 + l2 - l1 = l2 by ring.
    done.
  have Hdist :
      PCA.bigi predT
        (fun i => polyC (lift_word a.[i + (base + l1)]) * exp X i)
        0 l2 * exp X l1 =
      PCA.bigi predT
        (fun i =>
          (polyC (lift_word a.[i + (base + l1)]) * exp X i) *
            exp X l1)
        0 l2.
  + exact
      (PCA.mulr_suml predT
        (fun i => polyC (lift_word a.[i + (base + l1)]) * exp X i)
        (range 0 l2) (exp X l1)).
  have Htail :
      PCA.bigi predT
        (fun i => polyC (lift_word a.[i + base]) * exp X i)
        l1 (l1 + l2) =
      PCA.bigi predT
        (fun i => polyC (lift_word a.[i + (base + l1)]) * exp X i)
        0 l2 * exp X l1.
  + rewrite Hshift Hdist.
    apply PCA.eq_big_int => i Hi.
    have Hidx : (i + l1) + base = i + (base + l1) by ring.
    have Hexp : exp X (i + l1) = exp X i * exp X l1.
    + have [Hi0 _] := Hi.
      exact (NTRUPoly.PolyComRing.exprD_nneg X i l1 Hi0 Hl1).
    rewrite /= Hidx Hexp.
    ring.
  by rewrite Htail.
qed.

op schedule_root (e : int) : int =
  (zeta_root ^ e) %% q.

(* The two radix-3 butterflies are evaluations at the three cubic children
   of each stage1 root.  These six congruences make that schedule explicit. *)

lemma radix3_first_child0_eqm (a0 a1 a2 : int) :
  (NTRUPlus768NTTRadix3Algebra.radix3_block_math
     a0 a1 a2
     NTRUPlus768NTTRadix3Algebra.radix3_zeta2_root
     NTRUPlus768NTTRadix3Algebra.radix3_zeta3_root).`1 %% q =
  (a0 + a1 * schedule_root 32 + a2 * schedule_root 64) %% q.
proof.
  by rewrite /NTRUPlus768NTTRadix3Algebra.radix3_block_math
             /NTRUPlus768NTTRadix3Algebra.radix3_zeta2_root
             /NTRUPlus768NTTRadix3Algebra.radix3_zeta3_root
             /schedule_root.
qed.

lemma radix3_first_child1_eqm (a0 a1 a2 : int) :
  (NTRUPlus768NTTRadix3Algebra.radix3_block_math
     a0 a1 a2
     NTRUPlus768NTTRadix3Algebra.radix3_zeta2_root
     NTRUPlus768NTTRadix3Algebra.radix3_zeta3_root).`2 %% q =
  (a0 + a1 * schedule_root 224 + a2 * schedule_root 448) %% q.
proof.
  rewrite /NTRUPlus768NTTRadix3Algebra.radix3_block_math
          /NTRUPlus768NTTRadix3Algebra.radix3_zeta2_root
          /NTRUPlus768NTTRadix3Algebra.radix3_zeta3_root
          /NTRUPlus768NTTRadix3Algebra.radix3_omega_root
          /schedule_root /zeta_root /q /=.
  apply/IntDiv.eqmodP.
  exists (-1491 * a1 + 2532 * a2).
  ring.
qed.

lemma radix3_first_child2_eqm (a0 a1 a2 : int) :
  (NTRUPlus768NTTRadix3Algebra.radix3_block_math
     a0 a1 a2
     NTRUPlus768NTTRadix3Algebra.radix3_zeta2_root
     NTRUPlus768NTTRadix3Algebra.radix3_zeta3_root).`3 %% q =
  (a0 + a1 * schedule_root 416 + a2 * schedule_root 832) %% q.
proof.
  rewrite /NTRUPlus768NTTRadix3Algebra.radix3_block_math
          /NTRUPlus768NTTRadix3Algebra.radix3_zeta2_root
          /NTRUPlus768NTTRadix3Algebra.radix3_zeta3_root
          /NTRUPlus768NTTRadix3Algebra.radix3_omega_root
          /schedule_root /zeta_root /q /=.
  apply/IntDiv.eqmodP.
  exists (1493 * a1 - 2530 * a2).
  ring.
qed.

lemma radix3_second_child0_eqm (a0 a1 a2 : int) :
  (NTRUPlus768NTTRadix3Algebra.radix3_block_math
     a0 a1 a2
     NTRUPlus768NTTRadix3Algebra.radix3_zeta4_root
     NTRUPlus768NTTRadix3Algebra.radix3_zeta5_root).`1 %% q =
  (a0 + a1 * schedule_root 160 + a2 * schedule_root 320) %% q.
proof.
  by rewrite /NTRUPlus768NTTRadix3Algebra.radix3_block_math
             /NTRUPlus768NTTRadix3Algebra.radix3_zeta4_root
             /NTRUPlus768NTTRadix3Algebra.radix3_zeta5_root
             /schedule_root.
qed.

lemma radix3_second_child1_eqm (a0 a1 a2 : int) :
  (NTRUPlus768NTTRadix3Algebra.radix3_block_math
     a0 a1 a2
     NTRUPlus768NTTRadix3Algebra.radix3_zeta4_root
     NTRUPlus768NTTRadix3Algebra.radix3_zeta5_root).`2 %% q =
  (a0 + a1 * schedule_root 352 + a2 * schedule_root 704) %% q.
proof.
  rewrite /NTRUPlus768NTTRadix3Algebra.radix3_block_math
          /NTRUPlus768NTTRadix3Algebra.radix3_zeta4_root
          /NTRUPlus768NTTRadix3Algebra.radix3_zeta5_root
          /NTRUPlus768NTTRadix3Algebra.radix3_omega_root
          /schedule_root /zeta_root /q /=.
  apply/IntDiv.eqmodP.
  exists (-1845 * a1 + 1243 * a2).
  ring.
qed.

lemma radix3_second_child2_eqm (a0 a1 a2 : int) :
  (NTRUPlus768NTTRadix3Algebra.radix3_block_math
     a0 a1 a2
     NTRUPlus768NTTRadix3Algebra.radix3_zeta4_root
     NTRUPlus768NTTRadix3Algebra.radix3_zeta5_root).`3 %% q =
  (a0 + a1 * schedule_root 544 + a2 * schedule_root 1088) %% q.
proof.
  rewrite /NTRUPlus768NTTRadix3Algebra.radix3_block_math
          /NTRUPlus768NTTRadix3Algebra.radix3_zeta4_root
          /NTRUPlus768NTTRadix3Algebra.radix3_zeta5_root
          /NTRUPlus768NTTRadix3Algebra.radix3_omega_root
          /schedule_root /zeta_root /q /=.
  apply/IntDiv.eqmodP.
  exists (1846 * a1 - 1242 * a2).
  ring.
qed.

op root_poly (e : int) : poly =
  polyC (CycloFq.exp zeta_field e).

op segment3_poly (a : W16.t Array768.t) (base : int) : poly =
  segment_poly a base 128 +
  (segment_poly a (base + 128) 128 +
   segment_poly a (base + 256) 128 * exp X 128) *
  exp X 128.

op radix3_eval_poly
    (a : W16.t Array768.t) (base e : int) : poly =
  segment_poly a base 128 +
  (segment_poly a (base + 128) 128 +
   segment_poly a (base + 256) 128 * root_poly e) *
  root_poly e.

lemma segment_poly_split3 (a : W16.t Array768.t) (base : int) :
  segment_poly a base 384 = segment3_poly a base.
proof.
  rewrite /segment3_poly.
  rewrite (segment_poly_split a base 128 256) 1:// 1://.
  rewrite (segment_poly_split a (base + 128) 128 128) 1:// 1://.
  have Hbase : base + 128 + 128 = base + 256 by ring.
  by rewrite Hbase.
qed.

lemma radix3_eval_factor_eqm
    (a : W16.t Array768.t) (base e : int) :
  factor_eqm 128 e (segment3_poly a base) (radix3_eval_poly a base e).
proof.
  rewrite /factor_eqm /schedule_factor_modulus.
  exists
    (-(segment_poly a (base + 128) 128 +
       segment_poly a (base + 256) 128 *
         (root_poly e + exp X 128))).
  rewrite /segment3_poly /radix3_eval_poly /root_poly.
  ring.
qed.

lemma factor_eqm_weaken
    (pm pe cm ce : int) (p q : poly) :
  (exists g,
    schedule_factor_modulus pm pe = schedule_factor_modulus cm ce * g) =>
  factor_eqm pm pe p q =>
  factor_eqm cm ce p q.
proof.
  move=> [g Hfactor].
  rewrite /factor_eqm.
  move=> [h Hh].
  exists (h * g).
  rewrite Hh Hfactor.
  ring.
qed.

lemma stage1_low_modulus_split3 :
  schedule_factor_modulus 384 96 =
  schedule_factor_modulus 128 32 *
    (schedule_factor_modulus 128 224 *
     schedule_factor_modulus 128 416).
proof.
  move: (factor_split3 X 128 32 _ _); 1,2: smt().
  rewrite /factor /schedule_factor_modulus /=.
  done.
qed.

lemma stage1_high_modulus_split3 :
  schedule_factor_modulus 384 480 =
  schedule_factor_modulus 128 160 *
    (schedule_factor_modulus 128 352 *
     schedule_factor_modulus 128 544).
proof.
  move: (factor_split3 X 128 160 _ _); 1,2: smt().
  rewrite /factor /schedule_factor_modulus /=.
  done.
qed.

lemma factor_eqm_384_96_to_128_32 (p q : poly) :
  factor_eqm 384 96 p q => factor_eqm 128 32 p q.
proof.
  apply factor_eqm_weaken.
  exists
    (schedule_factor_modulus 128 224 *
     schedule_factor_modulus 128 416).
  exact stage1_low_modulus_split3.
qed.

lemma factor_eqm_384_96_to_128_224 (p q : poly) :
  factor_eqm 384 96 p q => factor_eqm 128 224 p q.
proof.
  apply factor_eqm_weaken.
  exists
    (schedule_factor_modulus 128 32 *
     schedule_factor_modulus 128 416).
  rewrite stage1_low_modulus_split3.
  ring.
qed.

lemma factor_eqm_384_96_to_128_416 (p q : poly) :
  factor_eqm 384 96 p q => factor_eqm 128 416 p q.
proof.
  apply factor_eqm_weaken.
  exists
    (schedule_factor_modulus 128 32 *
     schedule_factor_modulus 128 224).
  rewrite stage1_low_modulus_split3.
  ring.
qed.

lemma factor_eqm_384_480_to_128_160 (p q : poly) :
  factor_eqm 384 480 p q => factor_eqm 128 160 p q.
proof.
  apply factor_eqm_weaken.
  exists
    (schedule_factor_modulus 128 352 *
     schedule_factor_modulus 128 544).
  exact stage1_high_modulus_split3.
qed.

lemma factor_eqm_384_480_to_128_352 (p q : poly) :
  factor_eqm 384 480 p q => factor_eqm 128 352 p q.
proof.
  apply factor_eqm_weaken.
  exists
    (schedule_factor_modulus 128 160 *
     schedule_factor_modulus 128 544).
  rewrite stage1_high_modulus_split3.
  ring.
qed.

lemma factor_eqm_384_480_to_128_544 (p q : poly) :
  factor_eqm 384 480 p q => factor_eqm 128 544 p q.
proof.
  apply factor_eqm_weaken.
  exists
    (schedule_factor_modulus 128 160 *
     schedule_factor_modulus 128 352).
  rewrite stage1_high_modulus_split3.
  ring.
qed.

lemma schedule_root_fieldE (e : int) :
  0 <= e => lift_int (schedule_root e) = CycloFq.exp zeta_field e.
proof.
  move=> He.
  rewrite /schedule_root /lift_int.
  rewrite -CycloFq.incyclocoeff_mod.
  by rewrite zeta_field_expE 1:He.
qed.

op linear3_remainder_poly
    (a : W16.t Array768.t) (base c1 c2 : int) : poly =
  PCA.bigi predT
    (fun i =>
      polyC
        (lift_int
          (coeff a.[i + base] +
           coeff a.[i + base + 128] * c1 +
           coeff a.[i + base + 256] * c2)) *
      exp X i)
    0 128.

lemma poly_linear3_monomial
    (a0 a1 a2 r1 r2 x : poly) :
  (a0 + a1 * r1 + a2 * r2) * x =
  a0 * x + r1 * (a1 * x) + r2 * (a2 * x).
proof.
  rewrite (poly_mul_add_right (a0 + a1 * r1) (a2 * r2) x).
  rewrite (poly_mul_add_right a0 (a1 * r1) x).
  rewrite (poly_mul_reorder a1 r1 x).
  rewrite (poly_mul_reorder a2 r2 x).
  done.
qed.

lemma poly_lift_linear3_monomial
    (a0 a1 a2 c1 c2 : int) (x : poly) :
  polyC (lift_int (a0 + a1 * c1 + a2 * c2)) * x =
  polyC (lift_int a0) * x +
  polyC (lift_int c1) * (polyC (lift_int a1) * x) +
  polyC (lift_int c2) * (polyC (lift_int a2) * x).
proof.
  rewrite /lift_int.
  rewrite !CycloFq.incyclocoeffD !CycloFq.incyclocoeffM.
  rewrite !NTRUPoly.polyCD !NTRUPoly.polyCM.
  exact
    (poly_linear3_monomial
      (polyC (CycloFq.incyclocoeff a0))
      (polyC (CycloFq.incyclocoeff a1))
      (polyC (CycloFq.incyclocoeff a2))
      (polyC (CycloFq.incyclocoeff c1))
      (polyC (CycloFq.incyclocoeff c2)) x).
qed.

lemma linear3_remainder_polyE
    (a : W16.t Array768.t) (base c1 c2 : int) :
  linear3_remainder_poly a base c1 c2 =
  segment_poly a base 128 +
  polyC (lift_int c1) * segment_poly a (base + 128) 128 +
  polyC (lift_int c2) * segment_poly a (base + 256) 128.
proof.
  rewrite /linear3_remainder_poly /segment_poly.
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
        (fun i => polyC (lift_word a.[i + base]) * exp X i)
        0 128 +
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c1) *
            (polyC (lift_word a.[i + (base + 128)]) * exp X i))
        0 128 =
      PCA.bigi predT
        (fun i =>
          polyC (lift_word a.[i + base]) * exp X i +
          polyC (lift_int c1) *
            (polyC (lift_word a.[i + (base + 128)]) * exp X i))
        0 128.
  + apply/eq_sym.
    exact
      (PCA.big_split predT
        (fun i => polyC (lift_word a.[i + base]) * exp X i)
        (fun i =>
          polyC (lift_int c1) *
            (polyC (lift_word a.[i + (base + 128)]) * exp X i))
        (range 0 128)).
  have Hsplit012 :
      PCA.bigi predT
        (fun i =>
          polyC (lift_word a.[i + base]) * exp X i +
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
          polyC (lift_word a.[i + base]) * exp X i +
          polyC (lift_int c1) *
            (polyC (lift_word a.[i + (base + 128)]) * exp X i) +
          polyC (lift_int c2) *
            (polyC (lift_word a.[i + (base + 256)]) * exp X i))
        0 128.
  + apply/eq_sym.
    exact
      (PCA.big_split predT
        (fun i =>
          polyC (lift_word a.[i + base]) * exp X i +
          polyC (lift_int c1) *
            (polyC (lift_word a.[i + (base + 128)]) * exp X i))
        (fun i =>
          polyC (lift_int c2) *
            (polyC (lift_word a.[i + (base + 256)]) * exp X i))
        (range 0 128)).
  rewrite Hdist1 Hdist2 Hsplit01 Hsplit012.
  apply PCA.eq_big_int => i Hi.
  rewrite /lift_word /=.
  rewrite poly_lift_linear3_monomial.
  have Hidx1 : i + base + 128 = i + (base + 128) by ring.
  have Hidx2 : i + base + 256 = i + (base + 256) by ring.
  by rewrite Hidx1 Hidx2.
qed.

lemma segment_poly_linear3E
    (input output : W16.t Array768.t)
    (input_base output_base c1 c2 : int) :
  (forall i, 0 <= i < 128 =>
    coeff output.[i + output_base] %% q =
    (coeff input.[i + input_base] +
     coeff input.[i + input_base + 128] * c1 +
     coeff input.[i + input_base + 256] * c2) %% q) =>
  segment_poly output output_base 128 =
  linear3_remainder_poly input input_base c1 c2.
proof.
  move=> Hcoeff.
  rewrite /segment_poly /linear3_remainder_poly.
  apply PCA.eq_big_int => i Hi.
  have Hmod := Hcoeff i Hi.
  have Elift :
      lift_word output.[i + output_base] =
      lift_int
        (coeff input.[i + input_base] +
         coeff input.[i + input_base + 128] * c1 +
         coeff input.[i + input_base + 256] * c2).
  + rewrite /lift_word.
    apply lift_int_eq.
    exact Hmod.
  by rewrite /= Elift.
qed.

lemma radix3_segment_0E
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix3Algebra.radix3_algebra input output =>
  segment_poly output 0 128 =
  linear3_remainder_poly input 0 (schedule_root 32) (schedule_root 64).
proof.
  move=> Halg.
  apply segment_poly_linear3E => i Hi.
  have [_ Hcoeff] := Halg i _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix3Algebra.radix3_math
          /NTRUPlus768NTTRadix3Algebra.radix3_block_math_at
          /NTRUPlus768NTTRadix3Proof.block
          /NTRUPlus768NTTRadix3Proof.double_block
          /NTRUPlus768NTTRadix3Proof.second_base
          ifT 1:/# /=.
  rewrite radix3_first_child0_eqm.
  done.
qed.

lemma radix3_segment_128E
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix3Algebra.radix3_algebra input output =>
  segment_poly output 128 128 =
  linear3_remainder_poly input 0 (schedule_root 224) (schedule_root 448).
proof.
  move=> Halg.
  apply segment_poly_linear3E => i Hi.
  have [_ Hcoeff] := Halg (i + 128) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix3Algebra.radix3_math
          /NTRUPlus768NTTRadix3Algebra.radix3_block_math_at
          /NTRUPlus768NTTRadix3Proof.block
          /NTRUPlus768NTTRadix3Proof.double_block
          /NTRUPlus768NTTRadix3Proof.second_base
          ifF 1:/# ifT 1:/# /=.
  rewrite radix3_first_child1_eqm.
  done.
qed.

lemma radix3_segment_256E
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix3Algebra.radix3_algebra input output =>
  segment_poly output 256 128 =
  linear3_remainder_poly input 0 (schedule_root 416) (schedule_root 832).
proof.
  move=> Halg.
  apply segment_poly_linear3E => i Hi.
  have [_ Hcoeff] := Halg (i + 256) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix3Algebra.radix3_math
          /NTRUPlus768NTTRadix3Algebra.radix3_block_math_at
          /NTRUPlus768NTTRadix3Proof.block
          /NTRUPlus768NTTRadix3Proof.double_block
          /NTRUPlus768NTTRadix3Proof.second_base
          ifF 1:/# ifF 1:/# ifT 1:/# /=.
  rewrite radix3_first_child2_eqm.
  done.
qed.

lemma radix3_segment_384E
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix3Algebra.radix3_algebra input output =>
  segment_poly output 384 128 =
  linear3_remainder_poly input 384 (schedule_root 160) (schedule_root 320).
proof.
  move=> Halg.
  apply segment_poly_linear3E => i Hi.
  have [_ Hcoeff] := Halg (i + 384) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix3Algebra.radix3_math
          /NTRUPlus768NTTRadix3Algebra.radix3_block_math_at
          /NTRUPlus768NTTRadix3Proof.block
          /NTRUPlus768NTTRadix3Proof.double_block
          /NTRUPlus768NTTRadix3Proof.second_base
          ifF 1:/# ifF 1:/# ifF 1:/# ifT 1:/# /=.
  rewrite radix3_second_child0_eqm.
  move=> Hcoeff.
  rewrite [384 + i]addrC [512 + i]addrC [640 + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix3_segment_512E
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix3Algebra.radix3_algebra input output =>
  segment_poly output 512 128 =
  linear3_remainder_poly input 384 (schedule_root 352) (schedule_root 704).
proof.
  move=> Halg.
  apply segment_poly_linear3E => i Hi.
  have [_ Hcoeff] := Halg (i + 512) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix3Algebra.radix3_math
          /NTRUPlus768NTTRadix3Algebra.radix3_block_math_at
          /NTRUPlus768NTTRadix3Proof.block
          /NTRUPlus768NTTRadix3Proof.double_block
          /NTRUPlus768NTTRadix3Proof.second_base
          ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifT 1:/# /=.
  rewrite radix3_second_child1_eqm.
  move=> Hcoeff.
  rewrite [384 + i]addrC [512 + i]addrC [640 + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix3_segment_640E
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix3Algebra.radix3_algebra input output =>
  segment_poly output 640 128 =
  linear3_remainder_poly input 384 (schedule_root 544) (schedule_root 1088).
proof.
  move=> Halg.
  apply segment_poly_linear3E => i Hi.
  have [_ Hcoeff] := Halg (i + 640) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix3Algebra.radix3_math
          /NTRUPlus768NTTRadix3Algebra.radix3_block_math_at
          /NTRUPlus768NTTRadix3Proof.block
          /NTRUPlus768NTTRadix3Proof.double_block
          /NTRUPlus768NTTRadix3Proof.second_base
          ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# /=.
  rewrite radix3_second_child2_eqm.
  move=> Hcoeff.
  rewrite [384 + i]addrC [512 + i]addrC [640 + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma schedule_root_double_fieldE (e : int) :
  0 <= e =>
  lift_int (schedule_root (2 * e)) =
  CycloFq.exp (lift_int (schedule_root e)) 2.
proof.
  move=> He.
  rewrite schedule_root_fieldE 1:/# schedule_root_fieldE 1:He.
  have -> : CycloFq.exp zeta_field (2 * e) =
      CycloFq.exp (CycloFq.exp zeta_field e) 2.
  + exact (zeta_doubleE e).
  done.
qed.

lemma linear3_remainder_radix3_evalE
    (a : W16.t Array768.t) (base e : int) :
  0 <= e =>
  linear3_remainder_poly a base
    (schedule_root e) (schedule_root (2 * e)) =
  radix3_eval_poly a base e.
proof.
  move=> He.
  rewrite linear3_remainder_polyE /radix3_eval_poly /root_poly.
  rewrite schedule_root_fieldE 1:He.
  rewrite schedule_root_fieldE 1:/#.
  rewrite poly_zeta_doubleE.
  ring.
  rewrite NTRUPoly.PolyComRing.expr2.
  ring.
qed.

lemma radix3_segment_0_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix3Algebra.radix3_algebra input output =>
  segment_poly output 0 128 = radix3_eval_poly input 0 32.
proof.
  move=> Halg.
  have Hseg : segment_poly output 0 128 =
      linear3_remainder_poly input 0 (schedule_root 32) (schedule_root 64).
  + apply radix3_segment_0E.
    exact Halg.
  rewrite Hseg.
  change
    (linear3_remainder_poly input 0
       (schedule_root 32) (schedule_root (2 * 32)) =
     radix3_eval_poly input 0 32).
  apply linear3_remainder_radix3_evalE.
  done.
qed.

lemma radix3_segment_128_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix3Algebra.radix3_algebra input output =>
  segment_poly output 128 128 = radix3_eval_poly input 0 224.
proof.
  move=> Halg.
  have Hseg : segment_poly output 128 128 =
      linear3_remainder_poly input 0 (schedule_root 224) (schedule_root 448).
  + apply radix3_segment_128E.
    exact Halg.
  rewrite Hseg.
  change
    (linear3_remainder_poly input 0
       (schedule_root 224) (schedule_root (2 * 224)) =
     radix3_eval_poly input 0 224).
  apply linear3_remainder_radix3_evalE.
  done.
qed.

lemma radix3_segment_256_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix3Algebra.radix3_algebra input output =>
  segment_poly output 256 128 = radix3_eval_poly input 0 416.
proof.
  move=> Halg.
  have Hseg : segment_poly output 256 128 =
      linear3_remainder_poly input 0 (schedule_root 416) (schedule_root 832).
  + apply radix3_segment_256E.
    exact Halg.
  rewrite Hseg.
  change
    (linear3_remainder_poly input 0
       (schedule_root 416) (schedule_root (2 * 416)) =
     radix3_eval_poly input 0 416).
  apply linear3_remainder_radix3_evalE.
  done.
qed.

lemma radix3_segment_384_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix3Algebra.radix3_algebra input output =>
  segment_poly output 384 128 = radix3_eval_poly input 384 160.
proof.
  move=> Halg.
  have Hseg : segment_poly output 384 128 =
      linear3_remainder_poly input 384 (schedule_root 160) (schedule_root 320).
  + apply radix3_segment_384E.
    exact Halg.
  rewrite Hseg.
  change
    (linear3_remainder_poly input 384
       (schedule_root 160) (schedule_root (2 * 160)) =
     radix3_eval_poly input 384 160).
  apply linear3_remainder_radix3_evalE.
  done.
qed.

lemma radix3_segment_512_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix3Algebra.radix3_algebra input output =>
  segment_poly output 512 128 = radix3_eval_poly input 384 352.
proof.
  move=> Halg.
  have Hseg : segment_poly output 512 128 =
      linear3_remainder_poly input 384 (schedule_root 352) (schedule_root 704).
  + apply radix3_segment_512E.
    exact Halg.
  rewrite Hseg.
  change
    (linear3_remainder_poly input 384
       (schedule_root 352) (schedule_root (2 * 352)) =
     radix3_eval_poly input 384 352).
  apply linear3_remainder_radix3_evalE.
  done.
qed.

lemma radix3_segment_640_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix3Algebra.radix3_algebra input output =>
  segment_poly output 640 128 = radix3_eval_poly input 384 544.
proof.
  move=> Halg.
  have Hseg : segment_poly output 640 128 =
      linear3_remainder_poly input 384 (schedule_root 544) (schedule_root 1088).
  + apply radix3_segment_640E.
    exact Halg.
  rewrite Hseg.
  change
    (linear3_remainder_poly input 384
       (schedule_root 544) (schedule_root (2 * 544)) =
     radix3_eval_poly input 384 544).
  apply linear3_remainder_radix3_evalE.
  done.
qed.

lemma radix3_segment_factor_eqm
    (input output : W16.t Array768.t) (input_base output_base e : int) :
  segment_poly output output_base 128 =
    radix3_eval_poly input input_base e =>
  factor_eqm 128 e
    (segment_poly input input_base 384)
    (segment_poly output output_base 128).
proof.
  move=> Houtput.
  rewrite segment_poly_split3 Houtput.
  exact (radix3_eval_factor_eqm input input_base e).
qed.

op radix3_semantics
    (original output : W16.t Array768.t) : bool =
  factor_eqm 128 32
    (input_poly original) (segment_poly output 0 128) /\
  factor_eqm 128 224
    (input_poly original) (segment_poly output 128 128) /\
  factor_eqm 128 416
    (input_poly original) (segment_poly output 256 128) /\
  factor_eqm 128 160
    (input_poly original) (segment_poly output 384 128) /\
  factor_eqm 128 352
    (input_poly original) (segment_poly output 512 128) /\
  factor_eqm 128 544
    (input_poly original) (segment_poly output 640 128).

lemma radix3_algebra_refines_stage1_semantics
    (original input output : W16.t Array768.t) :
  stage1_semantics original input =>
  NTRUPlus768NTTRadix3Algebra.radix3_algebra input output =>
  radix3_semantics original output.
proof.
  move=> [Hstage_low Hstage_high] Halg.

  have Hlocal32 : factor_eqm 128 32
      (segment_poly input 0 384) (segment_poly output 0 128).
  + apply radix3_segment_factor_eqm.
    apply radix3_segment_0_evalE.
    exact Halg.
  have Hlocal224 : factor_eqm 128 224
      (segment_poly input 0 384) (segment_poly output 128 128).
  + apply radix3_segment_factor_eqm.
    apply radix3_segment_128_evalE.
    exact Halg.
  have Hlocal416 : factor_eqm 128 416
      (segment_poly input 0 384) (segment_poly output 256 128).
  + apply radix3_segment_factor_eqm.
    apply radix3_segment_256_evalE.
    exact Halg.
  have Hlocal160 : factor_eqm 128 160
      (segment_poly input 384 384) (segment_poly output 384 128).
  + apply radix3_segment_factor_eqm.
    apply radix3_segment_384_evalE.
    exact Halg.
  have Hlocal352 : factor_eqm 128 352
      (segment_poly input 384 384) (segment_poly output 512 128).
  + apply radix3_segment_factor_eqm.
    apply radix3_segment_512_evalE.
    exact Halg.
  have Hlocal544 : factor_eqm 128 544
      (segment_poly input 384 384) (segment_poly output 640 128).
  + apply radix3_segment_factor_eqm.
    apply radix3_segment_640_evalE.
    exact Halg.

  have Hstage32 : factor_eqm 128 32
      (input_poly original) (segment_poly input 0 384).
  + apply factor_eqm_384_96_to_128_32.
    exact Hstage_low.
  have Hstage224 : factor_eqm 128 224
      (input_poly original) (segment_poly input 0 384).
  + apply factor_eqm_384_96_to_128_224.
    exact Hstage_low.
  have Hstage416 : factor_eqm 128 416
      (input_poly original) (segment_poly input 0 384).
  + apply factor_eqm_384_96_to_128_416.
    exact Hstage_low.
  have Hstage160 : factor_eqm 128 160
      (input_poly original) (segment_poly input 384 384).
  + apply factor_eqm_384_480_to_128_160.
    exact Hstage_high.
  have Hstage352 : factor_eqm 128 352
      (input_poly original) (segment_poly input 384 384).
  + apply factor_eqm_384_480_to_128_352.
    exact Hstage_high.
  have Hstage544 : factor_eqm 128 544
      (input_poly original) (segment_poly input 384 384).
  + apply factor_eqm_384_480_to_128_544.
    exact Hstage_high.

  rewrite /radix3_semantics.
  split.
  + apply (factor_eqm_trans 128 32
      (input_poly original) (segment_poly input 0 384)
      (segment_poly output 0 128)).
    - exact Hstage32.
    - exact Hlocal32.
  split.
  + apply (factor_eqm_trans 128 224
      (input_poly original) (segment_poly input 0 384)
      (segment_poly output 128 128)).
    - exact Hstage224.
    - exact Hlocal224.
  split.
  + apply (factor_eqm_trans 128 416
      (input_poly original) (segment_poly input 0 384)
      (segment_poly output 256 128)).
    - exact Hstage416.
    - exact Hlocal416.
  split.
  + apply (factor_eqm_trans 128 160
      (input_poly original) (segment_poly input 384 384)
      (segment_poly output 384 128)).
    - exact Hstage160.
    - exact Hlocal160.
  split.
  + apply (factor_eqm_trans 128 352
      (input_poly original) (segment_poly input 384 384)
      (segment_poly output 512 128)).
    - exact Hstage352.
    - exact Hlocal352.
  apply (factor_eqm_trans 128 544
    (input_poly original) (segment_poly input 384 384)
    (segment_poly output 640 128)).
  + exact Hstage544.
  + exact Hlocal544.
qed.

lemma radix3_spec_semantics
    (original input : W16.t Array768.t) :
  stage1_semantics original input =>
  NTRUPlus768NTTRadix3Algebra.stage1_output_shape input =>
  radix3_semantics original (NTRUPlus768NTTRadix3Proof.radix3_spec input).
proof.
  move=> Hstage Hshape.
  apply (radix3_algebra_refines_stage1_semantics
    original input (NTRUPlus768NTTRadix3Proof.radix3_spec input)).
  + exact Hstage.
  + exact (NTRUPlus768NTTRadix3Algebra.radix3_spec_algebra input Hshape).
qed.

lemma ntt_radix3_semantics_functional
    (original rp0 : W16.t Array768.t) :
  stage1_semantics original rp0 =>
  NTRUPlus768NTTRadix3Algebra.stage1_output_shape rp0 =>
  hoare [NTRUPlus768NTTRadix3.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix3 :
    rp = rp0 ==> radix3_semantics original res].
proof.
  move=> Hstage Hshape.
  conseq
    (NTRUPlus768NTTRadix3Algebra.ntt_radix3_algebra_functional rp0 Hshape)
    => />.
  move=> result Halg.
  apply (radix3_algebra_refines_stage1_semantics original rp0 result).
  + exact Hstage.
  + exact Halg.
qed.

lemma ntt_radix3_correct_semantics
    (original rp0 : W16.t Array768.t) :
  stage1_semantics original rp0 =>
  NTRUPlus768NTTRadix3Algebra.stage1_output_shape rp0 =>
  phoare [NTRUPlus768NTTRadix3.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix3 :
    rp = rp0 ==> radix3_semantics original res] = 1%r.
proof.
  move=> Hstage Hshape.
  have Hfunctional :
      hoare [NTRUPlus768NTTRadix3.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix3 :
        rp = rp0 ==> radix3_semantics original res].
  + apply ntt_radix3_semantics_functional.
    - exact Hstage.
    - exact Hshape.
  by conseq NTRUPlus768NTTRadix3Proof.ntt_radix3_lossless Hfunctional.
qed.
