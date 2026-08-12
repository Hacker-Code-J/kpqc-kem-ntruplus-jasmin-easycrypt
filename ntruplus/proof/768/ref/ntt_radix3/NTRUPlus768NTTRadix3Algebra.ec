require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord JModel_x86.

require import W16extra.
require import Array768.
require import NTRUPlus768NTTRadix3Proof.
require import NTRUPlus768BasemulProof.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768NTTSchedule.

import Ring.IntID IntOrder.

op radix3_zeta2_root : int = (zeta_root ^ 32) %% q.
op radix3_zeta3_root : int = (zeta_root ^ 64) %% q.
op radix3_zeta4_root : int = (zeta_root ^ 160) %% q.
op radix3_zeta5_root : int = (zeta_root ^ 320) %% q.
op radix3_omega_root : int = (zeta_root ^ 192) %% q.

op stage1_output_shape (p : W16.t Array768.t) : bool =
  forall j, 0 <= j < 768 =>
    if j < second_base then -2 * q <= coeff p.[j] < 2 * q
    else -3 * q <= coeff p.[j] < 3 * q.

lemma stage1_output_shape_before
    (p : W16.t Array768.t) (j : int) :
  stage1_output_shape p =>
  0 <= j < second_base =>
  -2 * q <= coeff p.[j] < 2 * q.
proof.
  move=> Hshape Hj.
  rewrite /stage1_output_shape in Hshape.
  have Hjshape := Hshape j _; first smt().
  by move: Hjshape; smt().
qed.

lemma stage1_output_shape_after
    (p : W16.t Array768.t) (j : int) :
  stage1_output_shape p =>
  second_base <= j < 768 =>
  -3 * q <= coeff p.[j] < 3 * q.
proof.
  move=> Hshape Hj.
  rewrite /stage1_output_shape in Hshape.
  have Hjshape := Hshape j _; first smt().
  by move: Hjshape; smt().
qed.

op radix3_block_math
    (a0 a1 a2 root1 root2 : int) : int * int * int =
  ( a0 + a1 * root1 + a2 * root2
  , a0 - a2 * root2 + (a1 * root1 - a2 * root2) * radix3_omega_root
  , a0 - a1 * root1 - (a1 * root1 - a2 * root2) * radix3_omega_root).

op radix3_block_math_at
    (p : W16.t Array768.t) (base : int) (root1 root2 : int) (k : int)
    : int * int * int =
  radix3_block_math
    (coeff p.[base + k])
    (coeff p.[base + k + block])
    (coeff p.[base + k + double_block])
    root1 root2.

op radix3_math (p : W16.t Array768.t) (j : int) : int =
  if j < block then
    (radix3_block_math_at p 0 radix3_zeta2_root radix3_zeta3_root j).`1
  else if j < double_block then
    (radix3_block_math_at p 0 radix3_zeta2_root radix3_zeta3_root (j - block)).`2
  else if j < second_base then
    (radix3_block_math_at p 0 radix3_zeta2_root radix3_zeta3_root (j - double_block)).`3
  else if j < second_base + block then
    (radix3_block_math_at p second_base radix3_zeta4_root radix3_zeta5_root
      (j - second_base)).`1
  else if j < second_base + double_block then
    (radix3_block_math_at p second_base radix3_zeta4_root radix3_zeta5_root
      (j - second_base - block)).`2
  else
    (radix3_block_math_at p second_base radix3_zeta4_root radix3_zeta5_root
      (j - second_base - double_block)).`3.

op radix3_algebra
    (input output : W16.t Array768.t) : bool =
  forall j, 0 <= j < 768 =>
    (if j < second_base then -4 * q <= coeff output.[j] < 4 * q
     else -5 * q <= coeff output.[j] < 5 * q) /\
    coeff output.[j] %% q = radix3_math input j %% q.

lemma radix3_zeta_schedule_indices :
  coeff zeta2 = zetas192_coeff 2 /\ zetas192_exp 2 = 32 /\
  coeff zeta3 = zetas192_coeff 3 /\ zetas192_exp 3 = 64 /\
  coeff zeta4 = zetas192_coeff 4 /\ zetas192_exp 4 = 160 /\
  coeff zeta5 = zetas192_coeff 5 /\ zetas192_exp 5 = 320.
proof.
  rewrite /coeff /zeta2 /zeta3 /zeta4 /zeta5.
  rewrite /zetas192_coeff /zetas192_exp /zetas192_coeffs /zetas192_exponents /=.
  rewrite !W16.of_sintK !/W16.smod /=.
  done.
qed.

lemma radix3_omega_schedule :
  coeff omega = OMEGA_coeff /\ OMEGA_coeff = -886 /\ omega_exp = 192.
proof.
  rewrite /coeff /omega /OMEGA_coeff /omega_exp.
  rewrite W16.of_sintK /W16.smod /=.
  done.
qed.

lemma radix3_zeta2_in_qrange : in_qrange zeta2.
proof.
  rewrite /in_qrange /coeff /zeta2 W16.of_sintK /W16.smod /q /=.
  done.
qed.

lemma radix3_zeta3_in_qrange : in_qrange zeta3.
proof.
  rewrite /in_qrange /coeff /zeta3 W16.of_sintK /W16.smod /q /=.
  done.
qed.

lemma radix3_zeta4_in_qrange : in_qrange zeta4.
proof.
  rewrite /in_qrange /coeff /zeta4 W16.of_sintK /W16.smod /q /=.
  done.
qed.

lemma radix3_zeta5_in_qrange : in_qrange zeta5.
proof.
  rewrite /in_qrange /coeff /zeta5 W16.of_sintK /W16.smod /q /=.
  done.
qed.

lemma radix3_omega_in_qrange : in_qrange omega.
proof.
  rewrite /in_qrange /coeff /omega W16.of_sintK /W16.smod /q /=.
  done.
qed.

lemma radix3_zeta2_montgomery_meaning :
  (coeff zeta2 * Rinv) %% q = radix3_zeta2_root.
proof.
  have Hschedule := zetas192_relation 2 _; first smt().
  move: Hschedule.
  rewrite /decode_mont /radix3_zeta2_root /zetas192_coeff /zetas192_exp.
  rewrite /zetas192_coeffs /zetas192_exponents /coeff /zeta2 /=.
  rewrite W16.of_sintK /W16.smod /=.
  done.
qed.

lemma radix3_zeta3_montgomery_meaning :
  (coeff zeta3 * Rinv) %% q = radix3_zeta3_root.
proof.
  have Hschedule := zetas192_relation 3 _; first smt().
  move: Hschedule.
  rewrite /decode_mont /radix3_zeta3_root /zetas192_coeff /zetas192_exp.
  rewrite /zetas192_coeffs /zetas192_exponents /coeff /zeta3 /=.
  rewrite W16.of_sintK /W16.smod /=.
  done.
qed.

lemma radix3_zeta4_montgomery_meaning :
  (coeff zeta4 * Rinv) %% q = radix3_zeta4_root.
proof.
  have Hschedule := zetas192_relation 4 _; first smt().
  move: Hschedule.
  rewrite /decode_mont /radix3_zeta4_root /zetas192_coeff /zetas192_exp.
  rewrite /zetas192_coeffs /zetas192_exponents /coeff /zeta4 /=.
  rewrite W16.of_sintK /W16.smod /=.
  done.
qed.

lemma radix3_zeta5_montgomery_meaning :
  (coeff zeta5 * Rinv) %% q = radix3_zeta5_root.
proof.
  have Hschedule := zetas192_relation 5 _; first smt().
  move: Hschedule.
  rewrite /decode_mont /radix3_zeta5_root /zetas192_coeff /zetas192_exp.
  rewrite /zetas192_coeffs /zetas192_exponents /coeff /zeta5 /=.
  rewrite W16.of_sintK /W16.smod /=.
  done.
qed.

lemma radix3_omega_montgomery_meaning :
  (coeff omega * Rinv) %% q = radix3_omega_root.
proof.
  have [Hdecode _] := omega_montgomery_meaning.
  move: Hdecode.
  rewrite /decode_mont /radix3_omega_root /coeff /omega /OMEGA_coeff /omega_exp.
  rewrite W16.of_sintK /W16.smod /=.
  done.
qed.

lemma scaled_qrange_norm (m x : int) :
  0 <= m =>
  -m * q <= x < m * q =>
  `|x| <= m * q.
proof.
  move=> Hm Hx.
  rewrite ler_norml.
  smt().
qed.

lemma scaled_product_bound (m x y : int) :
  0 < m <= 4 =>
  -q <= x < q =>
  -m * q <= y < m * q =>
  -R %/ 2 * q <= x * y < R %/ 2 * q.
proof.
  move=> Hm Hx Hy.
  have Habsx : `|x| <= q by exact (qrange_norm x Hx).
  have Hm0 : 0 <= m by smt().
  have Habsy : `|y| <= m * q.
  + exact (scaled_qrange_norm m y Hm0 Hy).
  have Habsxy : `|x * y| <= q * (m * q).
  + rewrite normrM.
    apply ler_pmul.
    + exact (normr_ge0 x).
    + exact (normr_ge0 y).
    + exact Habsx.
    exact Habsy.
  have Hlim4 : q * (4 * q) < R %/ 2 * q.
  + rewrite R_halfE /q.
    smt().
  have Hscaled : q * (m * q) <= q * (4 * q).
  + rewrite /q.
    smt().
  have Habs : `|x * y| < R %/ 2 * q by smt().
  move: Habs; rewrite ltr_norml; smt().
qed.

lemma radix3_mul_algebra (z a : W16.t) (root m : int) :
  0 < m <= 4 =>
  in_qrange z =>
  -m * q <= coeff a < m * q =>
  (coeff z * Rinv) %% q = root =>
  -q <= coeff (radix3_mul z a) < q /\
  coeff (radix3_mul z a) %% q = (coeff a * root) %% q.
proof.
  move=> Hm Hz Ha Hroot.
  have Hproduct :=
    scaled_product_bound m (coeff z) (coeff a) Hm Hz Ha.
  have Hreduce :=
    montgomery_reduce_of_int (coeff z * coeff a) Hproduct.
  have Hmul : mul_i16 z a = W32.of_int (coeff z * coeff a)
    by apply mul_i16E.
  have Ht : radix3_mul z a = montgomery_reduce
      (W32.of_int (coeff z * coeff a))
    by rewrite /radix3_mul Hmul.
  have [Hrange Hcongr] := Hreduce.
  split; first by rewrite Ht.
  have Hcongr' :
      coeff (radix3_mul z a) %% q =
      (coeff z * coeff a * Rinv) %% q.
  + rewrite /radix3_mul Hmul.
    exact Hcongr.
  rewrite Hcongr'.
  rewrite (_ : coeff z * coeff a * Rinv = coeff a * (coeff z * Rinv)) 1:/#.
  rewrite -modzMmr Hroot.
  done.
qed.

lemma coeff_add_qbounded (m : int) (a b : W16.t) :
  0 < m <= 4 =>
  -m * q <= coeff a < m * q =>
  -q <= coeff b < q =>
  coeff (a + b) = coeff a + coeff b.
proof.
  move=> Hm Ha Hb.
  apply W16extra.to_sintD_small.
  move: Ha Hb.
  rewrite /coeff /q /=.
  smt().
qed.

lemma coeff_sub_qbounded (m : int) (a b : W16.t) :
  0 < m <= 4 =>
  -m * q <= coeff a < m * q =>
  -q <= coeff b < q =>
  coeff (a - b) = coeff a - coeff b.
proof.
  move=> Hm Ha Hb.
  apply W16extra.to_sintB_small.
  move: Ha Hb.
  rewrite /coeff /q /=.
  smt().
qed.

lemma int_add_qbounded (m x y : int) :
  0 < m =>
  -m * q <= x < m * q =>
  -q <= y < q =>
  -(m + 1) * q <= x + y < (m + 1) * q.
proof.
  rewrite /q.
  smt().
qed.

lemma int_sub_qbounded (m x y : int) :
  0 < m =>
  -m * q <= x < m * q =>
  -q <= y < q =>
  -(m + 1) * q <= x - y < (m + 1) * q.
proof.
  rewrite /q.
  smt().
qed.

lemma radix3_block_algebra
    (m : int)
    (z1 z2 a0 a1 a2 : W16.t)
    (root1 root2 : int) :
  0 < m <= 3 =>
  -m * q <= coeff a0 < m * q =>
  -m * q <= coeff a1 < m * q =>
  -m * q <= coeff a2 < m * q =>
  in_qrange z1 =>
  in_qrange z2 =>
  (coeff z1 * Rinv) %% q = root1 =>
  (coeff z2 * Rinv) %% q = root2 =>
  let out = radix3_block z1 z2 a0 a1 a2 in
    -(m + 2) * q <= coeff out.`1 < (m + 2) * q /\
    -(m + 2) * q <= coeff out.`2 < (m + 2) * q /\
    -(m + 2) * q <= coeff out.`3 < (m + 2) * q /\
    coeff out.`1 %% q =
      (coeff a0 + coeff a1 * root1 + coeff a2 * root2) %% q /\
    coeff out.`2 %% q =
      (coeff a0 - coeff a2 * root2 +
       (coeff a1 * root1 - coeff a2 * root2) * radix3_omega_root) %% q /\
    coeff out.`3 %% q =
      (coeff a0 - coeff a1 * root1 -
       (coeff a1 * root1 - coeff a2 * root2) * radix3_omega_root) %% q.
proof.
  move=> Hm Ha0 Ha1 Ha2 Hz1 Hz2 Hroot1 Hroot2 out.
  pose t1 := radix3_mul z1 a1.
  pose t2 := radix3_mul z2 a2.
  pose td := t1 - t2.
  pose t3 := radix3_mul omega td.
  have Hmpos : 0 < m by smt().
  have Hm4 : 0 < m <= 4 by smt().
  have Ht1 := radix3_mul_algebra z1 a1 root1 m Hm4 Hz1 Ha1 Hroot1.
  have Ht2 := radix3_mul_algebra z2 a2 root2 m Hm4 Hz2 Ha2 Hroot2.
  have Hm1 : 0 < 1 <= 4 by smt().
  have Hm2 : 0 < 2 <= 4 by smt().
  have Ht1range : -q <= coeff t1 < q by move: Ht1; smt().
  have Ht2range : -q <= coeff t2 < q by move: Ht2; smt().
  have Htd : coeff td = coeff t1 - coeff t2.
  + rewrite /td.
    exact (coeff_sub_qbounded 1 t1 t2 Hm1 Ht1range Ht2range).
  have Htdrange : -2 * q <= coeff td < 2 * q.
  + move: Htd Ht1range Ht2range; smt().
  have Ht3 :=
    radix3_mul_algebra omega td radix3_omega_root 2 Hm2
      radix3_omega_in_qrange Htdrange radix3_omega_montgomery_meaning.
  have Ht3range : -q <= coeff t3 < q by move: Ht3; smt().
  have Hout1a : coeff (a0 + t1) = coeff a0 + coeff t1.
  + exact (coeff_add_qbounded m a0 t1 Hm4 Ha0 Ht1range).
  have Hmnext : 0 < m + 1 <= 4 by smt().
  have Hmnextpos : 0 < m + 1 by smt().
  have Hsum01range :
      -(m + 1) * q <= coeff a0 + coeff t1 < (m + 1) * q.
  + exact (int_add_qbounded m (coeff a0) (coeff t1)
      Hmpos Ha0 Ht1range).
  have Hout1arange :
      -(m + 1) * q <= coeff (a0 + t1) < (m + 1) * q.
  + by rewrite Hout1a.
  have Hout1 : coeff out.`1 = coeff a0 + coeff t1 + coeff t2.
  + have -> : coeff out.`1 = coeff ((a0 + t1) + t2)
      by rewrite /out /radix3_block /t1 /t2.
    have Hsum1 : coeff ((a0 + t1) + t2) = coeff (a0 + t1) + coeff t2.
    + exact (coeff_add_qbounded (m + 1) (a0 + t1) t2
        Hmnext Hout1arange Ht2range).
    by rewrite Hsum1 Hout1a.
  have Hout2a : coeff (a0 - t2) = coeff a0 - coeff t2.
  + exact (coeff_sub_qbounded m a0 t2 Hm4 Ha0 Ht2range).
  have Hdiff02range :
      -(m + 1) * q <= coeff a0 - coeff t2 < (m + 1) * q.
  + exact (int_sub_qbounded m (coeff a0) (coeff t2)
      Hmpos Ha0 Ht2range).
  have Hout2arange :
      -(m + 1) * q <= coeff (a0 - t2) < (m + 1) * q.
  + by rewrite Hout2a.
  have Hout2 : coeff out.`2 = coeff a0 - coeff t2 + coeff t3.
  + have -> : coeff out.`2 = coeff ((a0 - t2) + t3)
      by rewrite /out /radix3_block /t2 /t3.
    have Hsum2 : coeff ((a0 - t2) + t3) = coeff (a0 - t2) + coeff t3.
    + exact (coeff_add_qbounded (m + 1) (a0 - t2) t3
        Hmnext Hout2arange Ht3range).
    by rewrite Hsum2 Hout2a.
  have Hout3a : coeff (a0 - t1) = coeff a0 - coeff t1.
  + exact (coeff_sub_qbounded m a0 t1 Hm4 Ha0 Ht1range).
  have Hdiff01range :
      -(m + 1) * q <= coeff a0 - coeff t1 < (m + 1) * q.
  + exact (int_sub_qbounded m (coeff a0) (coeff t1)
      Hmpos Ha0 Ht1range).
  have Hout3arange :
      -(m + 1) * q <= coeff (a0 - t1) < (m + 1) * q.
  + by rewrite Hout3a.
  have Hout3 : coeff out.`3 = coeff a0 - coeff t1 - coeff t3.
  + have -> : coeff out.`3 = coeff ((a0 - t1) - t3)
      by rewrite /out /radix3_block /t1 /t3.
    have Hsum3 : coeff ((a0 - t1) - t3) = coeff (a0 - t1) - coeff t3.
    + exact (coeff_sub_qbounded (m + 1) (a0 - t1) t3
        Hmnext Hout3arange Ht3range).
    by rewrite Hsum3 Hout3a.
  have Hout1range : -(m + 2) * q <= coeff out.`1 < (m + 2) * q.
  + rewrite Hout1.
    exact (int_add_qbounded (m + 1) (coeff a0 + coeff t1) (coeff t2)
      Hmnextpos Hsum01range Ht2range).
  have Hout2range : -(m + 2) * q <= coeff out.`2 < (m + 2) * q.
  + rewrite Hout2.
    exact (int_add_qbounded (m + 1) (coeff a0 - coeff t2) (coeff t3)
      Hmnextpos Hdiff02range Ht3range).
  have Hout3range : -(m + 2) * q <= coeff out.`3 < (m + 2) * q.
  + rewrite Hout3.
    exact (int_sub_qbounded (m + 1) (coeff a0 - coeff t1) (coeff t3)
      Hmnextpos Hdiff01range Ht3range).
  have Ht1congr : coeff t1 %% q = (coeff a1 * root1) %% q
    by move: Ht1; smt().
  have Ht2congr : coeff t2 %% q = (coeff a2 * root2) %% q
    by move: Ht2; smt().
  have Ht3congr :
      coeff t3 %% q =
        ((coeff a1 * root1 - coeff a2 * root2) * radix3_omega_root) %% q.
  + have Htdcongr :
        coeff td %% q =
        (coeff a1 * root1 - coeff a2 * root2) %% q.
    + rewrite Htd -modzBm Ht1congr Ht2congr modzBm.
      done.
    have Ht3base :
        coeff t3 %% q = (coeff td * radix3_omega_root) %% q
      by move: Ht3; smt().
    rewrite Ht3base.
    have -> :
        (coeff td * radix3_omega_root) %% q =
        ((coeff td %% q) * radix3_omega_root) %% q
      by rewrite modzMml.
    rewrite Htdcongr.
    by rewrite modzMml.
  have Hout1congr :
      coeff out.`1 %% q =
        (coeff a0 + coeff a1 * root1 + coeff a2 * root2) %% q.
  + have Hsum12 :
        (coeff t1 + coeff t2) %% q =
        (coeff a1 * root1 + coeff a2 * root2) %% q.
    + rewrite -modzDm Ht1congr Ht2congr modzDm.
      done.
    rewrite Hout1.
    rewrite (_ : coeff a0 + coeff t1 + coeff t2 =
                coeff a0 + (coeff t1 + coeff t2)) 1:/#.
    rewrite (_ : coeff a0 + coeff a1 * root1 + coeff a2 * root2 =
                coeff a0 + (coeff a1 * root1 + coeff a2 * root2)) 1:/#.
    rewrite -modzDmr Hsum12 modzDmr.
    done.
  have Hout2congr :
      coeff out.`2 %% q =
        (coeff a0 - coeff a2 * root2 +
         (coeff a1 * root1 - coeff a2 * root2) * radix3_omega_root) %% q.
  + have Hsub2 :
        (coeff a0 - coeff t2) %% q =
        (coeff a0 - coeff a2 * root2) %% q.
    + rewrite -modzBm Ht2congr modzBm.
      done.
    rewrite Hout2.
    rewrite (_ : coeff a0 - coeff t2 + coeff t3 =
                (coeff a0 - coeff t2) + coeff t3) 1:/#.
    rewrite -modzDm Hsub2 Ht3congr modzDm.
    done.
  have Hout3congr :
      coeff out.`3 %% q =
        (coeff a0 - coeff a1 * root1 -
         (coeff a1 * root1 - coeff a2 * root2) * radix3_omega_root) %% q.
  + have Hsub1 :
        (coeff a0 - coeff t1) %% q =
        (coeff a0 - coeff a1 * root1) %% q.
    + rewrite -modzBm Ht1congr modzBm.
      done.
    rewrite Hout3.
    rewrite (_ : coeff a0 - coeff t1 - coeff t3 =
                (coeff a0 - coeff t1) - coeff t3) 1:/#.
    rewrite -modzBm Hsub1 Ht3congr modzBm.
    done.
  split; first exact Hout1range.
  split; first exact Hout2range.
  split; first exact Hout3range.
  split; first exact Hout1congr.
  split; first exact Hout2congr.
  exact Hout3congr.
qed.

lemma radix3_first_spec_far (p : W16.t Array768.t) (j : int) :
  second_base <= j < 768 =>
  (radix3_first_spec p).[j] = p.[j].
proof.
  move=> Hj.
  rewrite /radix3_first_spec /radix3_prefix_spec Array768.initiE 1:/#.
  smt().
qed.

lemma radix3_second_spec_before
    (p : W16.t Array768.t) (j : int) :
  0 <= j < second_base =>
  (radix3_second_spec p).[j] = p.[j].
proof.
  move=> Hj.
  rewrite /radix3_second_spec /radix3_prefix_spec Array768.initiE 1:/#.
  smt().
qed.

lemma radix3_spec_algebra (p : W16.t Array768.t) :
  stage1_output_shape p =>
  radix3_algebra p (radix3_spec p).
proof.
  move=> Hinput j Hj.
  rewrite /radix3_algebra /radix3_math.
  case (j < block) => Hj0.
  + rewrite ifT 1:/#.
    have Ha0 : -2 * q <= coeff p.[j] < 2 * q
      by apply (stage1_output_shape_before p j Hinput); smt().
    have Ha1 : -2 * q <= coeff p.[j + block] < 2 * q
      by apply (stage1_output_shape_before p (j + block) Hinput); smt().
    have Ha2 : -2 * q <= coeff p.[j + double_block] < 2 * q
      by apply (stage1_output_shape_before p (j + double_block) Hinput); smt().
    have Hblk := radix3_block_algebra 2 zeta2 zeta3 p.[j] p.[j + block] p.[j + double_block]
      radix3_zeta2_root radix3_zeta3_root _ Ha0 Ha1 Ha2
      radix3_zeta2_in_qrange radix3_zeta3_in_qrange
      radix3_zeta2_montgomery_meaning radix3_zeta3_montgomery_meaning; first smt().
    move: Hblk.
    rewrite /radix3_spec /radix3_second_spec /radix3_prefix_spec Array768.initiE 1:/#.
    rewrite /= ifF 1:/# ifF 1:/# ifF 1:/#.
    rewrite /radix3_first_spec /radix3_prefix_spec Array768.initiE 1:/#.
    rewrite /= ifT 1:/#.
    rewrite /radix3_block_at /radix3_block_math_at /radix3_block_math /=.
    move=> [Hr0 [Hr1 [Hr2 [Hc0 [Hc1 Hc2]]]]].
    split; [exact Hr0 | exact Hc0].
  case (j < double_block) => Hj1.
  + rewrite ifT 1:/#.
    have Hk : 0 <= j - block < block by smt().
    have Ha0 : -2 * q <= coeff p.[j - block] < 2 * q
      by apply (stage1_output_shape_before p (j - block) Hinput); smt().
    have Ha1 : -2 * q <= coeff p.[j] < 2 * q
      by apply (stage1_output_shape_before p j Hinput); smt().
    have Ha2 : -2 * q <= coeff p.[j + block] < 2 * q
      by apply (stage1_output_shape_before p (j + block) Hinput); smt().
    have Hblk := radix3_block_algebra 2 zeta2 zeta3 p.[j - block] p.[j] p.[j + block]
      radix3_zeta2_root radix3_zeta3_root _ Ha0 Ha1 Ha2
      radix3_zeta2_in_qrange radix3_zeta3_in_qrange
      radix3_zeta2_montgomery_meaning radix3_zeta3_montgomery_meaning; first smt().
    move: Hblk.
    rewrite /radix3_spec /radix3_second_spec /radix3_prefix_spec Array768.initiE 1:/#.
    rewrite /= ifF 1:/# ifF 1:/# ifF 1:/#.
    rewrite /radix3_first_spec /radix3_prefix_spec Array768.initiE 1:/#.
    rewrite /= ifF 1:/# ifT 1:/#.
    rewrite /radix3_block_at /radix3_block_math_at /radix3_block_math /=.
    move=> [Hr0 [Hr1 [Hr2 [Hc0 [Hc1 Hc2]]]]].
    split; [exact Hr1 | exact Hc1].
  case (j < second_base) => Hj2.
  + have Hk : 0 <= j - double_block < block by smt().
    have Ha0 : -2 * q <= coeff p.[j - double_block] < 2 * q
      by apply (stage1_output_shape_before p (j - double_block) Hinput); smt().
    have Ha1 : -2 * q <= coeff p.[j - block] < 2 * q
      by apply (stage1_output_shape_before p (j - block) Hinput); smt().
    have Ha2 : -2 * q <= coeff p.[j] < 2 * q
      by apply (stage1_output_shape_before p j Hinput); smt().
    have Hblk := radix3_block_algebra 2 zeta2 zeta3 p.[j - double_block] p.[j - block] p.[j]
      radix3_zeta2_root radix3_zeta3_root _ Ha0 Ha1 Ha2
      radix3_zeta2_in_qrange radix3_zeta3_in_qrange
      radix3_zeta2_montgomery_meaning radix3_zeta3_montgomery_meaning; first smt().
    move: Hblk.
    rewrite /radix3_spec /radix3_second_spec /radix3_prefix_spec Array768.initiE 1:/#.
    rewrite /= ifF 1:/# ifF 1:/# ifF 1:/#.
    rewrite /radix3_first_spec /radix3_prefix_spec Array768.initiE 1:/#.
    rewrite /= ifF 1:/# ifF 1:/# ifT 1:/#.
    rewrite /radix3_block_at /radix3_block_math_at /radix3_block_math /=.
    move=> [Hr0 [Hr1 [Hr2 [Hc0 [Hc1 Hc2]]]]].
    split; [exact Hr2 | exact Hc2].
  case (j < second_base + block) => Hj3.
  + have Ha0 : -3 * q <= coeff p.[j] < 3 * q
      by apply (stage1_output_shape_after p j Hinput); smt().
    have Ha1 : -3 * q <= coeff p.[j + block] < 3 * q
      by apply (stage1_output_shape_after p (j + block) Hinput); smt().
    have Ha2 : -3 * q <= coeff p.[j + double_block] < 3 * q
      by apply (stage1_output_shape_after p (j + double_block) Hinput); smt().
    have Hblk := radix3_block_algebra 3 zeta4 zeta5 p.[j] p.[j + block] p.[j + double_block]
      radix3_zeta4_root radix3_zeta5_root _ Ha0 Ha1 Ha2
      radix3_zeta4_in_qrange radix3_zeta5_in_qrange
      radix3_zeta4_montgomery_meaning radix3_zeta5_montgomery_meaning; first smt().
    move: Hblk.
    rewrite /radix3_spec /radix3_second_spec /radix3_prefix_spec Array768.initiE 1:/#.
    rewrite /= ifT 1:/#.
    rewrite /radix3_block_at /=.
    rewrite (radix3_first_spec_far p j) 1:/#.
    rewrite (radix3_first_spec_far p (j + block)) 1:/#.
    rewrite (radix3_first_spec_far p (j + double_block)) 1:/#.
    rewrite /radix3_block_math_at /radix3_block_math /=.
    move=> [Hr0 [Hr1 [Hr2 [Hc0 [Hc1 Hc2]]]]].
    split; [exact Hr0 | exact Hc0].
  case (j < second_base + double_block) => Hj4.
  + have Hk : 0 <= j - second_base - block < block by smt().
    have Ha0 : -3 * q <= coeff p.[j - block] < 3 * q
      by apply (stage1_output_shape_after p (j - block) Hinput); smt().
    have Ha1 : -3 * q <= coeff p.[j] < 3 * q
      by apply (stage1_output_shape_after p j Hinput); smt().
    have Ha2 : -3 * q <= coeff p.[j + block] < 3 * q
      by apply (stage1_output_shape_after p (j + block) Hinput); smt().
    have Hblk := radix3_block_algebra 3 zeta4 zeta5 p.[j - block] p.[j] p.[j + block]
      radix3_zeta4_root radix3_zeta5_root _ Ha0 Ha1 Ha2
      radix3_zeta4_in_qrange radix3_zeta5_in_qrange
      radix3_zeta4_montgomery_meaning radix3_zeta5_montgomery_meaning; first smt().
    move: Hblk.
    rewrite /radix3_spec /radix3_second_spec /radix3_prefix_spec Array768.initiE 1:/#.
    rewrite /= ifF 1:/# ifT 1:/#.
    rewrite /radix3_block_at /=.
    rewrite (radix3_first_spec_far p (j - block)) 1:/#.
    rewrite (radix3_first_spec_far p j) 1:/#.
    rewrite (radix3_first_spec_far p (j + block)) 1:/#.
    rewrite /radix3_block_math_at /radix3_block_math /=.
    move=> [Hr0 [Hr1 [Hr2 [Hc0 [Hc1 Hc2]]]]].
    split; [exact Hr1 | exact Hc1].
  have Hk : 0 <= j - second_base - double_block < block by smt().
  have Ha0 : -3 * q <= coeff p.[j - double_block] < 3 * q
    by apply (stage1_output_shape_after p (j - double_block) Hinput); smt().
  have Ha1 : -3 * q <= coeff p.[j - block] < 3 * q
    by apply (stage1_output_shape_after p (j - block) Hinput); smt().
  have Ha2 : -3 * q <= coeff p.[j] < 3 * q
    by apply (stage1_output_shape_after p j Hinput); smt().
  have Hblk := radix3_block_algebra 3 zeta4 zeta5 p.[j - double_block] p.[j - block] p.[j]
    radix3_zeta4_root radix3_zeta5_root _ Ha0 Ha1 Ha2
    radix3_zeta4_in_qrange radix3_zeta5_in_qrange
    radix3_zeta4_montgomery_meaning radix3_zeta5_montgomery_meaning; first smt().
  move: Hblk.
  rewrite /radix3_spec /radix3_second_spec /radix3_prefix_spec Array768.initiE 1:/#.
  rewrite /= ifF 1:/# ifF 1:/# ifT 1:/#.
  rewrite /radix3_block_at /=.
  rewrite (radix3_first_spec_far p (j - double_block)) 1:/#.
  rewrite (radix3_first_spec_far p (j - block)) 1:/#.
  rewrite (radix3_first_spec_far p j) 1:/#.
  rewrite /radix3_block_math_at /radix3_block_math /=.
  move=> [Hr0 [Hr1 [Hr2 [Hc0 [Hc1 Hc2]]]]].
  split; [exact Hr2 | exact Hc2].
qed.

lemma ntt_radix3_algebra_functional
    (rp0 : W16.t Array768.t) :
  stage1_output_shape rp0 =>
  hoare [NTRUPlus768NTTRadix3.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix3 :
    rp = rp0 ==> radix3_algebra rp0 res].
proof.
  move=> Hinput.
  conseq (ntt_radix3_functional rp0) => />.
  exact (radix3_spec_algebra rp0 Hinput).
qed.

lemma ntt_radix3_correct_algebra
    (rp0 : W16.t Array768.t) :
  stage1_output_shape rp0 =>
  phoare [NTRUPlus768NTTRadix3.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix3 :
    rp = rp0 ==> radix3_algebra rp0 res] = 1%r.
proof.
  move=> Hinput.
  have Hfunctional := ntt_radix3_algebra_functional rp0 Hinput.
  by conseq ntt_radix3_lossless Hfunctional.
qed.
