require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord JModel_x86.

require import JWord_extra W16extra.
require import Array768.
require import NTRUPlus768NTTRadix2_32Proof.
require import NTRUPlus768BasemulProof.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768NTTSchedule.
require NTRUPlus768NTTRadix2_64Algebra.

import Ring.IntID IntOrder.

op second_base : int = 384.

op radix2_32_zeta1_root : int = (zeta_root ^ 8) %% q.
op radix2_32_zeta2_root : int = (zeta_root ^ 152) %% q.
op radix2_32_zeta3_root : int = (zeta_root ^ 56) %% q.
op radix2_32_zeta4_root : int = (zeta_root ^ 200) %% q.
op radix2_32_zeta5_root : int = (zeta_root ^ 104) %% q.
op radix2_32_zeta6_root : int = (zeta_root ^ 248) %% q.
op radix2_32_zeta7_root : int = (zeta_root ^ 40) %% q.
op radix2_32_zeta8_root : int = (zeta_root ^ 184) %% q.
op radix2_32_zeta9_root : int = (zeta_root ^ 88) %% q.
op radix2_32_zeta10_root : int = (zeta_root ^ 232) %% q.
op radix2_32_zeta11_root : int = (zeta_root ^ 136) %% q.
op radix2_32_zeta12_root : int = (zeta_root ^ 280) %% q.

op radix2_64_output_shape (p : W16.t Array768.t) : bool =
  forall j, 0 <= j < 768 => -1728 <= coeff p.[j] <= 1728.

lemma radix2_64_algebra_output_shape
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_64Algebra.radix2_64_algebra input output =>
  radix2_64_output_shape output.
proof.
  move=> Halg.
  rewrite /NTRUPlus768NTTRadix2_64Algebra.radix2_64_algebra in Halg.
  rewrite /radix2_64_output_shape.
  move=> j Hj.
  have Hjalg := Halg j Hj.
  by move: Hjalg => [Hrange _].
qed.

op radix2_32_pair_math (lo hi root : int) : int * int =
  (lo + hi * root, lo - hi * root).

op radix2_32_pair_math_at
    (p : W16.t Array768.t) (base : int) (root : int) (k : int)
    : int * int =
  radix2_32_pair_math
    (coeff p.[base + k])
    (coeff p.[base + k + block])
    root.

op radix2_32_math (p : W16.t Array768.t) (j : int) : int =
  if j < block then
    (radix2_32_pair_math_at p 0 radix2_32_zeta1_root j).`1
  else if j < double_block then
    (radix2_32_pair_math_at p 0 radix2_32_zeta1_root (j - block)).`2
  else if j < double_block + block then
    (radix2_32_pair_math_at p double_block radix2_32_zeta2_root (j - double_block)).`1
  else if j < double_block + double_block then
    (radix2_32_pair_math_at p double_block radix2_32_zeta2_root (j - double_block - block)).`2
  else if j < (2 * double_block) + block then
    (radix2_32_pair_math_at p (2 * double_block) radix2_32_zeta3_root (j - (2 * double_block))).`1
  else if j < (2 * double_block) + double_block then
    (radix2_32_pair_math_at p (2 * double_block) radix2_32_zeta3_root (j - (2 * double_block) - block)).`2
  else if j < (3 * double_block) + block then
    (radix2_32_pair_math_at p (3 * double_block) radix2_32_zeta4_root (j - (3 * double_block))).`1
  else if j < (3 * double_block) + double_block then
    (radix2_32_pair_math_at p (3 * double_block) radix2_32_zeta4_root (j - (3 * double_block) - block)).`2
  else if j < (4 * double_block) + block then
    (radix2_32_pair_math_at p (4 * double_block) radix2_32_zeta5_root (j - (4 * double_block))).`1
  else if j < (4 * double_block) + double_block then
    (radix2_32_pair_math_at p (4 * double_block) radix2_32_zeta5_root (j - (4 * double_block) - block)).`2
  else if j < (5 * double_block) + block then
    (radix2_32_pair_math_at p (5 * double_block) radix2_32_zeta6_root (j - (5 * double_block))).`1
  else if j < (5 * double_block) + double_block then
    (radix2_32_pair_math_at p (5 * double_block) radix2_32_zeta6_root (j - (5 * double_block) - block)).`2
  else if j < second_base + block then
    (radix2_32_pair_math_at p second_base radix2_32_zeta7_root (j - second_base)).`1
  else if j < second_base + double_block then
    (radix2_32_pair_math_at p second_base radix2_32_zeta7_root (j - second_base - block)).`2
  else if j < (second_base + double_block) + block then
    (radix2_32_pair_math_at p (second_base + double_block) radix2_32_zeta8_root (j - (second_base + double_block))).`1
  else if j < (second_base + double_block) + double_block then
    (radix2_32_pair_math_at p (second_base + double_block) radix2_32_zeta8_root (j - (second_base + double_block) - block)).`2
  else if j < (second_base + 2 * double_block) + block then
    (radix2_32_pair_math_at p (second_base + 2 * double_block) radix2_32_zeta9_root (j - (second_base + 2 * double_block))).`1
  else if j < (second_base + 2 * double_block) + double_block then
    (radix2_32_pair_math_at p (second_base + 2 * double_block) radix2_32_zeta9_root (j - (second_base + 2 * double_block) - block)).`2
  else if j < (second_base + 3 * double_block) + block then
    (radix2_32_pair_math_at p (second_base + 3 * double_block) radix2_32_zeta10_root (j - (second_base + 3 * double_block))).`1
  else if j < (second_base + 3 * double_block) + double_block then
    (radix2_32_pair_math_at p (second_base + 3 * double_block) radix2_32_zeta10_root (j - (second_base + 3 * double_block) - block)).`2
  else if j < (second_base + 4 * double_block) + block then
    (radix2_32_pair_math_at p (second_base + 4 * double_block) radix2_32_zeta11_root (j - (second_base + 4 * double_block))).`1
  else if j < (second_base + 4 * double_block) + double_block then
    (radix2_32_pair_math_at p (second_base + 4 * double_block) radix2_32_zeta11_root (j - (second_base + 4 * double_block) - block)).`2
  else if j < (second_base + 5 * double_block) + block then
    (radix2_32_pair_math_at p (second_base + 5 * double_block) radix2_32_zeta12_root (j - (second_base + 5 * double_block))).`1
  else if j < (second_base + 5 * double_block) + double_block then
    (radix2_32_pair_math_at p (second_base + 5 * double_block) radix2_32_zeta12_root (j - (second_base + 5 * double_block) - block)).`2
  else witness.

op radix2_32_algebra (input output : W16.t Array768.t) : bool =
  forall j, 0 <= j < 768 =>
    -1728 <= coeff output.[j] <= 1728 /\
    coeff output.[j] %% q = radix2_32_math input j %% q.

op barrett_v : int = 19412.
op barrett_shift : int = 2 ^ 26.
op barrett_bias : int = 2 ^ 25.
op qhalf : int = q %/ 2.

op centered_quot (x : int) : int = (x + qhalf) %/ q.
op centered_rem (x : int) : int = x - centered_quot x * q.
op barrett_quot (x : int) : int = (barrett_v * x + barrett_bias) %/ barrett_shift.

lemma radix2_64_output_shape_qrange
    (p : W16.t Array768.t) (j : int) :
  radix2_64_output_shape p =>
  0 <= j < 768 =>
  -q <= coeff p.[j] < q.
proof.
  move=> Hshape Hj.
  rewrite /radix2_64_output_shape in Hshape.
  have Hjshape := Hshape j _; first exact Hj.
  move: Hjshape; rewrite /q /=; smt().
qed.

lemma radix2_32_zeta_schedule_indices :
  coeff zeta1 = zetas192_coeff 12 /\ zetas192_exp 12 = 8 /\
  coeff zeta2 = zetas192_coeff 13 /\ zetas192_exp 13 = 152 /\
  coeff zeta3 = zetas192_coeff 14 /\ zetas192_exp 14 = 56 /\
  coeff zeta4 = zetas192_coeff 15 /\ zetas192_exp 15 = 200 /\
  coeff zeta5 = zetas192_coeff 16 /\ zetas192_exp 16 = 104 /\
  coeff zeta6 = zetas192_coeff 17 /\ zetas192_exp 17 = 248 /\
  coeff zeta7 = zetas192_coeff 18 /\ zetas192_exp 18 = 40 /\
  coeff zeta8 = zetas192_coeff 19 /\ zetas192_exp 19 = 184 /\
  coeff zeta9 = zetas192_coeff 20 /\ zetas192_exp 20 = 88 /\
  coeff zeta10 = zetas192_coeff 21 /\ zetas192_exp 21 = 232 /\
  coeff zeta11 = zetas192_coeff 22 /\ zetas192_exp 22 = 136 /\
  coeff zeta12 = zetas192_coeff 23 /\ zetas192_exp 23 = 280.
proof.
  rewrite /coeff /zeta1 /zeta2 /zeta3 /zeta4 /zeta5 /zeta6 /zeta7 /zeta8 /zeta9 /zeta10 /zeta11 /zeta12.
  rewrite /zetas192_coeff /zetas192_exp /zetas192_coeffs /zetas192_exponents /=.
  rewrite !W16.of_sintK !/W16.smod /=.
  done.
qed.

lemma radix2_32_zeta1_in_qrange : in_qrange zeta1.
proof.
  rewrite /in_qrange /coeff /zeta1 W16.of_sintK /W16.smod /q /=.
  done.
qed.

lemma radix2_32_zeta1_montgomery_meaning :
  (coeff zeta1 * Rinv) %% q = radix2_32_zeta1_root.
proof.
  have Hschedule := zetas192_relation 12 _; first smt().
  move: Hschedule.
  rewrite /decode_mont /radix2_32_zeta1_root /zetas192_coeff /zetas192_exp.
  rewrite /zetas192_coeffs /zetas192_exponents /coeff /zeta1 /=.
  rewrite W16.of_sintK /W16.smod /=.
  done.
qed.

lemma radix2_32_zeta2_in_qrange : in_qrange zeta2.
proof.
  rewrite /in_qrange /coeff /zeta2 W16.of_sintK /W16.smod /q /=.
  done.
qed.

lemma radix2_32_zeta2_montgomery_meaning :
  (coeff zeta2 * Rinv) %% q = radix2_32_zeta2_root.
proof.
  have Hschedule := zetas192_relation 13 _; first smt().
  move: Hschedule.
  rewrite /decode_mont /radix2_32_zeta2_root /zetas192_coeff /zetas192_exp.
  rewrite /zetas192_coeffs /zetas192_exponents /coeff /zeta2 /=.
  rewrite W16.of_sintK /W16.smod /=.
  done.
qed.

lemma radix2_32_zeta3_in_qrange : in_qrange zeta3.
proof.
  rewrite /in_qrange /coeff /zeta3 W16.of_sintK /W16.smod /q /=.
  done.
qed.

lemma radix2_32_zeta3_montgomery_meaning :
  (coeff zeta3 * Rinv) %% q = radix2_32_zeta3_root.
proof.
  have Hschedule := zetas192_relation 14 _; first smt().
  move: Hschedule.
  rewrite /decode_mont /radix2_32_zeta3_root /zetas192_coeff /zetas192_exp.
  rewrite /zetas192_coeffs /zetas192_exponents /coeff /zeta3 /=.
  rewrite W16.of_sintK /W16.smod /=.
  done.
qed.

lemma radix2_32_zeta4_in_qrange : in_qrange zeta4.
proof.
  rewrite /in_qrange /coeff /zeta4 W16.of_sintK /W16.smod /q /=.
  done.
qed.

lemma radix2_32_zeta4_montgomery_meaning :
  (coeff zeta4 * Rinv) %% q = radix2_32_zeta4_root.
proof.
  have Hschedule := zetas192_relation 15 _; first smt().
  move: Hschedule.
  rewrite /decode_mont /radix2_32_zeta4_root /zetas192_coeff /zetas192_exp.
  rewrite /zetas192_coeffs /zetas192_exponents /coeff /zeta4 /=.
  rewrite W16.of_sintK /W16.smod /=.
  done.
qed.

lemma radix2_32_zeta5_in_qrange : in_qrange zeta5.
proof.
  rewrite /in_qrange /coeff /zeta5 W16.of_sintK /W16.smod /q /=.
  done.
qed.

lemma radix2_32_zeta5_montgomery_meaning :
  (coeff zeta5 * Rinv) %% q = radix2_32_zeta5_root.
proof.
  have Hschedule := zetas192_relation 16 _; first smt().
  move: Hschedule.
  rewrite /decode_mont /radix2_32_zeta5_root /zetas192_coeff /zetas192_exp.
  rewrite /zetas192_coeffs /zetas192_exponents /coeff /zeta5 /=.
  rewrite W16.of_sintK /W16.smod /=.
  done.
qed.

lemma radix2_32_zeta6_in_qrange : in_qrange zeta6.
proof.
  rewrite /in_qrange /coeff /zeta6 W16.of_sintK /W16.smod /q /=.
  done.
qed.

lemma radix2_32_zeta6_montgomery_meaning :
  (coeff zeta6 * Rinv) %% q = radix2_32_zeta6_root.
proof.
  have Hschedule := zetas192_relation 17 _; first smt().
  move: Hschedule.
  rewrite /decode_mont /radix2_32_zeta6_root /zetas192_coeff /zetas192_exp.
  rewrite /zetas192_coeffs /zetas192_exponents /coeff /zeta6 /=.
  rewrite W16.of_sintK /W16.smod /=.
  done.
qed.

lemma radix2_32_zeta7_in_qrange : in_qrange zeta7.
proof.
  rewrite /in_qrange /coeff /zeta7 W16.of_sintK /W16.smod /q /=.
  done.
qed.

lemma radix2_32_zeta7_montgomery_meaning :
  (coeff zeta7 * Rinv) %% q = radix2_32_zeta7_root.
proof.
  have Hschedule := zetas192_relation 18 _; first smt().
  move: Hschedule.
  rewrite /decode_mont /radix2_32_zeta7_root /zetas192_coeff /zetas192_exp.
  rewrite /zetas192_coeffs /zetas192_exponents /coeff /zeta7 /=.
  rewrite W16.of_sintK /W16.smod /=.
  done.
qed.

lemma radix2_32_zeta8_in_qrange : in_qrange zeta8.
proof.
  rewrite /in_qrange /coeff /zeta8 W16.of_sintK /W16.smod /q /=.
  done.
qed.

lemma radix2_32_zeta8_montgomery_meaning :
  (coeff zeta8 * Rinv) %% q = radix2_32_zeta8_root.
proof.
  have Hschedule := zetas192_relation 19 _; first smt().
  move: Hschedule.
  rewrite /decode_mont /radix2_32_zeta8_root /zetas192_coeff /zetas192_exp.
  rewrite /zetas192_coeffs /zetas192_exponents /coeff /zeta8 /=.
  rewrite W16.of_sintK /W16.smod /=.
  done.
qed.

lemma radix2_32_zeta9_in_qrange : in_qrange zeta9.
proof.
  rewrite /in_qrange /coeff /zeta9 W16.of_sintK /W16.smod /q /=.
  done.
qed.

lemma radix2_32_zeta9_montgomery_meaning :
  (coeff zeta9 * Rinv) %% q = radix2_32_zeta9_root.
proof.
  have Hschedule := zetas192_relation 20 _; first smt().
  move: Hschedule.
  rewrite /decode_mont /radix2_32_zeta9_root /zetas192_coeff /zetas192_exp.
  rewrite /zetas192_coeffs /zetas192_exponents /coeff /zeta9 /=.
  rewrite W16.of_sintK /W16.smod /=.
  done.
qed.

lemma radix2_32_zeta10_in_qrange : in_qrange zeta10.
proof.
  rewrite /in_qrange /coeff /zeta10 W16.of_sintK /W16.smod /q /=.
  done.
qed.

lemma radix2_32_zeta10_montgomery_meaning :
  (coeff zeta10 * Rinv) %% q = radix2_32_zeta10_root.
proof.
  have Hschedule := zetas192_relation 21 _; first smt().
  move: Hschedule.
  rewrite /decode_mont /radix2_32_zeta10_root /zetas192_coeff /zetas192_exp.
  rewrite /zetas192_coeffs /zetas192_exponents /coeff /zeta10 /=.
  rewrite W16.of_sintK /W16.smod /=.
  done.
qed.

lemma radix2_32_zeta11_in_qrange : in_qrange zeta11.
proof.
  rewrite /in_qrange /coeff /zeta11 W16.of_sintK /W16.smod /q /=.
  done.
qed.

lemma radix2_32_zeta11_montgomery_meaning :
  (coeff zeta11 * Rinv) %% q = radix2_32_zeta11_root.
proof.
  have Hschedule := zetas192_relation 22 _; first smt().
  move: Hschedule.
  rewrite /decode_mont /radix2_32_zeta11_root /zetas192_coeff /zetas192_exp.
  rewrite /zetas192_coeffs /zetas192_exponents /coeff /zeta11 /=.
  rewrite W16.of_sintK /W16.smod /=.
  done.
qed.

lemma radix2_32_zeta12_in_qrange : in_qrange zeta12.
proof.
  rewrite /in_qrange /coeff /zeta12 W16.of_sintK /W16.smod /q /=.
  done.
qed.

lemma radix2_32_zeta12_montgomery_meaning :
  (coeff zeta12 * Rinv) %% q = radix2_32_zeta12_root.
proof.
  have Hschedule := zetas192_relation 23 _; first smt().
  move: Hschedule.
  rewrite /decode_mont /radix2_32_zeta12_root /zetas192_coeff /zetas192_exp.
  rewrite /zetas192_coeffs /zetas192_exponents /coeff /zeta12 /=.
  rewrite W16.of_sintK /W16.smod /=.
  done.
qed.

lemma barrett_qhalfE : qhalf = 1728.
proof. by rewrite /qhalf /q /=. qed.

lemma barrett_shiftE : barrett_shift = 67108864.
proof. by rewrite /barrett_shift /=. qed.

lemma barrett_biasE : barrett_bias = 33554432.
proof. by rewrite /barrett_bias /=. qed.

lemma barrett_mul_qE : barrett_v * q = barrett_shift - 1580.
proof. by rewrite /barrett_v /q barrett_shiftE /=. qed.

lemma centered_rem_bounds (x : int) :
  -qhalf <= centered_rem x <= qhalf.
proof.
  rewrite /centered_rem /centered_quot.
  have Hdiv := divz_eq (x + qhalf) q.
  have Hmod : 0 <= (x + qhalf) %% q < q by smt().
  have Hrepr : x - ((x + qhalf) %/ q) * q = (x + qhalf) %% q - qhalf.
  + move: Hdiv.
    smt().
  rewrite Hrepr.
  rewrite barrett_qhalfE /q.
  smt().
qed.

lemma centered_quot_bounds (x : int) :
  -6 * q <= x < 6 * q =>
  -6 <= centered_quot x <= 6.
proof.
  rewrite /centered_quot barrett_qhalfE /q.
  smt().
qed.

lemma SAR_sem26 (a : W32.t) :
  a `|>>` W8.of_int 26 = W32.of_int (W32.to_sint a %/ 2 ^ 26).
proof.
  apply W32_to_sint_inj.
  rewrite /W32.(`|>>`) W8.of_uintK.
  have Hmod : 26 %% W8.modulus = 26 by smt().
  rewrite Hmod W32_sar_div.
  + smt().
  rewrite W32.to_sintK_small.
  + have Ha' : -2147483648 <= W32.to_sint a <= 2147483647 by apply W32.to_sint_cmp.
    split.
    + have Hpow : 0 < 2 ^ 26 by smt(gt0_pow2).
      smt().
    move=> _.
    have Hpow : 0 < 2 ^ 26 by smt(gt0_pow2).
    rewrite -ltzS.
    smt().
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
  0 < m <= 5 =>
  -q <= x < q =>
  -m * q <= y < m * q =>
  -R %/ 2 * q <= x * y < R %/ 2 * q.
proof.
  move=> Hm Hx Hy.
  have Habsx : `|x| <= q by exact (qrange_norm x Hx).
  have Hm0 : 0 <= m by smt().
  have Habsy : `|y| <= m * q by exact (scaled_qrange_norm m y Hm0 Hy).
  have Habsxy : `|x * y| <= q * (m * q).
  + rewrite normrM.
    apply ler_pmul.
    + exact (normr_ge0 x).
    + exact (normr_ge0 y).
    + exact Habsx.
    exact Habsy.
  have Hlim5 : q * (5 * q) < R %/ 2 * q.
  + rewrite R_halfE /q.
    smt().
  have Hscaled : q * (m * q) <= q * (5 * q).
  + rewrite /q.
    smt().
  have Habs : `|x * y| < R %/ 2 * q by smt().
  move: Habs; rewrite ltr_norml; smt().
qed.

lemma radix2_32_mul_algebra (z a : W16.t) (root m : int) :
  0 < m <= 5 =>
  in_qrange z =>
  -m * q <= coeff a < m * q =>
  (coeff z * Rinv) %% q = root =>
  -q <= coeff (radix2_32_mul z a) < q /\
  coeff (radix2_32_mul z a) %% q = (coeff a * root) %% q.
proof.
  move=> Hm Hz Ha Hroot.
  have Hproduct := scaled_product_bound m (coeff z) (coeff a) Hm Hz Ha.
  have Hreduce := montgomery_reduce_of_int (coeff z * coeff a) Hproduct.
  have Hmul : mul_i16 z a = W32.of_int (coeff z * coeff a) by apply mul_i16E.
  have Ht : radix2_32_mul z a = montgomery_reduce
      (W32.of_int (coeff z * coeff a))
    by rewrite /radix2_32_mul Hmul.
  have [Hrange Hcongr] := Hreduce.
  split; first by rewrite Ht.
  have Hcongr' :
      coeff (radix2_32_mul z a) %% q =
      (coeff z * coeff a * Rinv) %% q.
  + rewrite /radix2_32_mul Hmul.
    exact Hcongr.
  rewrite Hcongr'.
  rewrite (_ : coeff z * coeff a * Rinv = coeff a * (coeff z * Rinv)) 1:/#.
  rewrite -modzMmr Hroot.
  done.
qed.

lemma coeff_add_qbounded (m : int) (a b : W16.t) :
  0 < m <= 5 =>
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
  0 < m <= 5 =>
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

lemma barrett_reduce_small (a : W16.t) :
  -6 * q <= coeff a < 6 * q =>
  coeff (barrett_reduce a) = centered_rem (coeff a) /\
  -1728 <= coeff (barrett_reduce a) <= 1728 /\
  coeff (barrett_reduce a) %% q = coeff a %% q.
proof.
  move=> Ha.
  pose x := coeff a.
  pose k := centered_quot x.
  pose r := centered_rem x.
  have Hk : -6 <= k <= 6 by exact (centered_quot_bounds x Ha).
  have Hr : -qhalf <= r <= qhalf by exact (centered_rem_bounds x).
  have HNsmall : -2147483648 <= barrett_v * x + barrett_bias < 2147483648.
  + rewrite /x /barrett_v barrett_biasE /q.
    smt().
  have Hsplit :
      barrett_v * x + barrett_bias =
      k * barrett_shift + (barrett_v * r + barrett_bias - 1580 * k).
  + rewrite /r /k /centered_rem /barrett_v /q
      /barrett_shift /barrett_bias /=.
    ring.
  have HS :
      0 <= barrett_v * r + barrett_bias - 1580 * k < barrett_shift.
  + rewrite /barrett_v barrett_shiftE barrett_biasE.
    rewrite barrett_qhalfE in Hr.
    smt().
  have Hquot : barrett_quot x = k.
  + rewrite /barrett_quot Hsplit.
    rewrite divzMDl 1:/#.
    have -> :
      (barrett_v * r + barrett_bias - 1580 * k) %/ barrett_shift = 0 by smt().
    ring.
  have Hshiftraw :
      truncateu16
        (((sigextu32 a * W32.of_int barrett_v) + W32.of_int barrett_bias)
          `|>>` W8.of_int 26) =
      W16.of_int k.
  + rewrite sigextu32E.
    have -> :
        W32.of_int x * W32.of_int barrett_v + W32.of_int barrett_bias =
        W32.of_int (barrett_v * x + barrett_bias).
    + rewrite W32.of_intM W32.of_intD'.
      congr; ring.
    rewrite SAR_sem26 truncateu16_of_int.
    have HNrange :
        W32.min_sint <= barrett_v * x + barrett_bias <= W32.max_sint.
    + move: HNsmall.
      smt().
    rewrite (W32.to_sintK_small
      (barrett_v * x + barrett_bias) HNrange).
    by rewrite -Hquot /barrett_quot /barrett_shift /=.
  have Hqword :
      truncateu16
        (sigextu32
          (truncateu16
            (((sigextu32 a * W32.of_int barrett_v) + W32.of_int barrett_bias)
              `|>>` W8.of_int 26)) * W32.of_int q) =
      W16.of_int (k * q).
  + rewrite Hshiftraw sigextu32E.
    have Hksmall : W16.min_sint <= k <= W16.max_sint by smt().
    rewrite /coeff (W16.to_sintK_small k Hksmall).
    by rewrite W32.of_intM truncateu16_of_int.
  have Hcoeffq :
      coeff
        (truncateu16
          (sigextu32
            (truncateu16
              (((sigextu32 a * W32.of_int barrett_v) + W32.of_int barrett_bias)
                `|>>` W8.of_int 26)) * W32.of_int q)) = k * q.
  + rewrite Hqword /coeff.
    have Hkqsmall : W16.min_sint <= k * q <= W16.max_sint.
    + rewrite /q.
      smt().
    exact (W16.to_sintK_small (k * q) Hkqsmall).
  have Hcoeff :
      coeff (barrett_reduce a) = x - k * q.
  + have Hcoeffq_num := Hcoeffq.
    rewrite /barrett_v barrett_biasE /q /coeff in Hcoeffq_num.
    rewrite /barrett_reduce /=.
    rewrite /x /q -Hcoeffq_num.
    apply W16extra.to_sintB_small.
    rewrite Hcoeffq_num.
    move: Hr.
    rewrite /r /x barrett_qhalfE /q.
    smt().
  have Hrange : -1728 <= coeff (barrett_reduce a) <= 1728.
  + rewrite Hcoeff /r.
    move: Hr.
    rewrite barrett_qhalfE.
    smt().
  split; first by rewrite Hcoeff /r.
  split; first exact Hrange.
  rewrite Hcoeff /x.
  apply radix2_32_modz_sub_dvd.
  apply/dvdzE.
  apply dvdz_mull.
  exact (dvdzz q).
qed.

lemma radix2_32_pair_algebra
    (m : int) (z lo hi : W16.t) (root : int) :
  0 < m <= 5 =>
  -m * q <= coeff lo < m * q =>
  -m * q <= coeff hi < m * q =>
  in_qrange z =>
  (coeff z * Rinv) %% q = root =>
  let out = radix2_32_pair z lo hi in
    -1728 <= coeff out.`1 <= 1728 /\
    -1728 <= coeff out.`2 <= 1728 /\
    coeff out.`1 %% q = (coeff lo + coeff hi * root) %% q /\
    coeff out.`2 %% q = (coeff lo - coeff hi * root) %% q.
proof.
  move=> Hm Hlo Hhi Hz Hroot out.
  pose t := radix2_32_mul z hi.
  have Ht := radix2_32_mul_algebra z hi root m Hm Hz Hhi Hroot.
  have Ht_range : -q <= coeff t < q by move: Ht; smt().
  have Ht_congr : coeff t %% q = (coeff hi * root) %% q by move: Ht; smt().
  have Hsum : coeff (lo + t) = coeff lo + coeff t.
  + exact (coeff_add_qbounded m lo t Hm Hlo Ht_range).
  have Hdiff : coeff (lo - t) = coeff lo - coeff t.
  + exact (coeff_sub_qbounded m lo t Hm Hlo Ht_range).
  have Hmpos : 0 < m by smt().
  have Hsum_range : -(m + 1) * q <= coeff (lo + t) < (m + 1) * q.
  + rewrite Hsum.
    exact (int_add_qbounded m (coeff lo) (coeff t) Hmpos Hlo Ht_range).
  have Hdiff_range : -(m + 1) * q <= coeff (lo - t) < (m + 1) * q.
  + rewrite Hdiff.
    exact (int_sub_qbounded m (coeff lo) (coeff t) Hmpos Hlo Ht_range).
  have Hsum_small : -6 * q <= coeff (lo + t) < 6 * q by move: Hsum_range Hm; smt().
  have Hdiff_small : -6 * q <= coeff (lo - t) < 6 * q by move: Hdiff_range Hm; smt().
  have Hbar_sum := barrett_reduce_small (lo + t) Hsum_small.
  have Hbar_diff := barrett_reduce_small (lo - t) Hdiff_small.
  have Hsum_congr :
      coeff (lo + t) %% q = (coeff lo + coeff hi * root) %% q.
  + rewrite Hsum -modzDmr Ht_congr modzDmr.
    done.
  have Hdiff_congr :
      coeff (lo - t) %% q = (coeff lo - coeff hi * root) %% q.
  + rewrite Hdiff -modzBm Ht_congr modzBm.
    done.
  move: Hbar_sum Hbar_diff.
  rewrite /out /radix2_32_pair /t /=.
  move=> [Hsum_eq [Hsum_rng Hsum_mod]] [Hdiff_eq [Hdiff_rng Hdiff_mod]].
  split; first exact Hsum_rng.
  split; first exact Hdiff_rng.
  split.
  + rewrite Hsum_mod Hsum_congr.
    done.
  rewrite Hdiff_mod Hdiff_congr.
  done.
qed.

lemma radix2_32_block_spec_far
    (p : W16.t Array768.t) (base j : int) (z : W16.t) :
  0 <= j < 768 =>
  j < base \/ base + double_block <= j =>
  (radix2_32_block_spec p base z).[j] = p.[j].
proof.
  move=> Hj Hfar.
  rewrite /radix2_32_block_spec /radix2_32_prefix_spec Array768.initiE 1:Hj.
  smt().
qed.

lemma radix2_32_block_spec_before
    (p : W16.t Array768.t) (base j : int) (z : W16.t) :
  0 <= j < 768 =>
  j < base =>
  (radix2_32_block_spec p base z).[j] = p.[j].
proof.
  move=> Hj Hbefore.
  apply radix2_32_block_spec_far.
  + exact Hj.
  by left.
qed.

lemma radix2_32_block_spec_get0
    (p : W16.t Array768.t) (base k : int) (z : W16.t) :
  0 <= base =>
  base + double_block <= 768 =>
  0 <= k < block =>
  (radix2_32_block_spec p base z).[base + k] =
    (radix2_32_pair_at p base z k).`1.
proof.
  move=> Hbase Hbound Hk.
  rewrite /radix2_32_block_spec /radix2_32_prefix_spec Array768.initiE 1:/#.
  by rewrite /radix2_32_pair_at; smt().
qed.

lemma radix2_32_block_spec_get1
    (p : W16.t Array768.t) (base k : int) (z : W16.t) :
  0 <= base =>
  base + double_block <= 768 =>
  0 <= k < block =>
  (radix2_32_block_spec p base z).[base + block + k] =
    (radix2_32_pair_at p base z k).`2.
proof.
  move=> Hbase Hbound Hk.
  rewrite /radix2_32_block_spec /radix2_32_prefix_spec Array768.initiE 1:/#.
  by rewrite /radix2_32_pair_at; smt().
qed.

lemma radix2_32_block_spec_get0_valid
    (p : W16.t Array768.t) (base k : int) (z : W16.t) :
  valid_base base =>
  0 <= k < block =>
  (radix2_32_block_spec p base z).[base + k] =
    (radix2_32_pair_at p base z k).`1.
proof.
  move=> Hvalid Hk.
  have [Hbase Hbound] := valid_base_bounds base Hvalid.
  exact (radix2_32_block_spec_get0 p base k z Hbase Hbound Hk).
qed.

lemma radix2_32_block_spec_get1_valid
    (p : W16.t Array768.t) (base k : int) (z : W16.t) :
  valid_base base =>
  0 <= k < block =>
  (radix2_32_block_spec p base z).[base + block + k] =
    (radix2_32_pair_at p base z k).`2.
proof.
  move=> Hvalid Hk.
  have [Hbase Hbound] := valid_base_bounds base Hvalid.
  exact (radix2_32_block_spec_get1 p base k z Hbase Hbound Hk).
qed.

lemma radix2_32_block_spec_far_pair_at
    (p : W16.t Array768.t) (base1 base2 k : int) (z1 z2 : W16.t) :
  0 <= base1 =>
  base1 + double_block <= 768 =>
  0 <= base2 =>
  base2 + double_block <= 768 =>
  (base1 + double_block <= base2 \/ base2 + double_block <= base1) =>
  0 <= k < block =>
  radix2_32_pair_at (radix2_32_block_spec p base1 z1) base2 z2 k =
  radix2_32_pair_at p base2 z2 k.
proof.
  move=> Hbase1 Hbound1 Hbase2 Hbound2 Hdisj Hk.
  rewrite /radix2_32_pair_at.
  congr.
  + apply radix2_32_block_spec_far.
    + smt().
    smt().
  apply radix2_32_block_spec_far.
  + smt().
  smt().
qed.


lemma radix2_32_spec_algebra (p : W16.t Array768.t) :
  radix2_64_output_shape p => radix2_32_algebra p (radix2_32_spec p).
proof.
  move=> Hshape j Hj_range.
  have Hvalid0 : valid_base 0.
  + rewrite /valid_base /double_block /nblocks.
    exists 0; smt().
  have Hvalid1 : valid_base double_block.
  + rewrite /valid_base /double_block /nblocks.
    exists 1; smt().
  have Hvalid2 : valid_base (2 * double_block).
  + rewrite /valid_base /double_block /nblocks.
    exists 2; smt().
  have Hvalid3 : valid_base (3 * double_block).
  + rewrite /valid_base /double_block /nblocks.
    exists 3; smt().
  have Hvalid4 : valid_base (4 * double_block).
  + rewrite /valid_base /double_block /nblocks.
    exists 4; smt().
  have Hvalid5 : valid_base (5 * double_block).
  + rewrite /valid_base /double_block /nblocks.
    exists 5; smt().
  have Hvalid6 : valid_base second_base.
  + rewrite /valid_base /double_block /nblocks.
    exists 6; smt().
  have Hvalid7 : valid_base (second_base + double_block).
  + rewrite /valid_base /double_block /nblocks.
    exists 7; smt().
  have Hvalid8 : valid_base (second_base + 2 * double_block).
  + rewrite /valid_base /double_block /nblocks.
    exists 8; smt().
  have Hvalid9 : valid_base (second_base + 3 * double_block).
  + rewrite /valid_base /double_block /nblocks.
    exists 9; smt().
  have Hvalid10 : valid_base (second_base + 4 * double_block).
  + rewrite /valid_base /double_block /nblocks.
    exists 10; smt().
  have Hvalid11 : valid_base (second_base + 5 * double_block).
  + rewrite /valid_base /double_block /nblocks.
    exists 11; smt().
  pose p0 := radix2_32_block_spec p 0 zeta1.
  pose p1 := radix2_32_block_spec p0 double_block zeta2.
  pose p2 := radix2_32_block_spec p1 (2 * double_block) zeta3.
  pose p3 := radix2_32_block_spec p2 (3 * double_block) zeta4.
  pose p4 := radix2_32_block_spec p3 (4 * double_block) zeta5.
  pose p5 := radix2_32_block_spec p4 (5 * double_block) zeta6.
  pose p6 := radix2_32_block_spec p5 second_base zeta7.
  pose p7 := radix2_32_block_spec p6 (second_base + double_block) zeta8.
  pose p8 := radix2_32_block_spec p7 (second_base + 2 * double_block) zeta9.
  pose p9 := radix2_32_block_spec p8 (second_base + 3 * double_block) zeta10.
  pose p10 := radix2_32_block_spec p9 (second_base + 4 * double_block) zeta11.
  rewrite /radix2_32_spec /radix2_32_algebra /radix2_32_math.
  case (j < block) => Hj0.
  + pose k := j.
    have Hk : 0 <= k < block by rewrite /k /block /double_block /second_base; smt().
    have Hlo : -q <= coeff p.[j] < q
      by apply (radix2_64_output_shape_qrange p j Hshape); smt().
    have Hhi : -q <= coeff p.[j + block] < q
      by apply (radix2_64_output_shape_qrange p (j + block) Hshape); smt().
    have Hpair := radix2_32_pair_algebra 1 zeta1 p.[j] p.[j + block]
      radix2_32_zeta1_root _ Hlo Hhi
      radix2_32_zeta1_in_qrange radix2_32_zeta1_montgomery_meaning; first smt().
    have Hout :
        (radix2_32_block_spec p10 (second_base + 5 * double_block) zeta12).[j] =
        (radix2_32_pair_at p 0 zeta1 k).`1.
    +
      rewrite (radix2_32_block_spec_before p10 (second_base + 5 * double_block) j zeta12 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p9 (second_base + 4 * double_block) j zeta11 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p8 (second_base + 3 * double_block) j zeta10 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p7 (second_base + 2 * double_block) j zeta9 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p6 (second_base + double_block) j zeta8 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p5 second_base j zeta7 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p4 (5 * double_block) j zeta6 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p3 (4 * double_block) j zeta5 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p2 (3 * double_block) j zeta4 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p1 (2 * double_block) j zeta3 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p0 double_block j zeta2 Hj_range) 1:/#.
      by rewrite (radix2_32_block_spec_get0 p 0 k zeta1) 1:/# 2:/#.
    move: Hpair.
    rewrite /k Hout /radix2_32_pair_at /radix2_32_pair_math_at /radix2_32_pair_math /=.
    move=> [Hr0 [Hr1 [Hc0 Hc1]]].
    split; first exact Hr0.
    exact Hc0.
  case (j < double_block) => Hj1.
  + pose k := j - block.
    have Hk : 0 <= k < block by rewrite /k /block /double_block /second_base; smt().
    have Hlo : -q <= coeff p.[j - block] < q
      by apply (radix2_64_output_shape_qrange p (j - block) Hshape); smt().
    have Hhi : -q <= coeff p.[j] < q
      by apply (radix2_64_output_shape_qrange p j Hshape); smt().
    have Hpair := radix2_32_pair_algebra 1 zeta1 p.[j - block] p.[j]
      radix2_32_zeta1_root _ Hlo Hhi
      radix2_32_zeta1_in_qrange radix2_32_zeta1_montgomery_meaning; first smt().
    have Hout :
        (radix2_32_block_spec p10 (second_base + 5 * double_block) zeta12).[j] =
        (radix2_32_pair_at p 0 zeta1 k).`2.
    +
      rewrite (radix2_32_block_spec_before p10 (second_base + 5 * double_block) j zeta12 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p9 (second_base + 4 * double_block) j zeta11 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p8 (second_base + 3 * double_block) j zeta10 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p7 (second_base + 2 * double_block) j zeta9 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p6 (second_base + double_block) j zeta8 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p5 second_base j zeta7 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p4 (5 * double_block) j zeta6 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p3 (4 * double_block) j zeta5 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p2 (3 * double_block) j zeta4 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p1 (2 * double_block) j zeta3 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p0 double_block j zeta2 Hj_range) 1:/#.
      by rewrite (radix2_32_block_spec_get1_valid p 0 k zeta1 Hvalid0 Hk).
    move: Hpair.
    rewrite /k Hout /radix2_32_pair_at /radix2_32_pair_math_at /radix2_32_pair_math /=.
    move=> [Hr0 [Hr1 [Hc0 Hc1]]].
    split; first exact Hr1.
    exact Hc1.
  case (j < double_block + block) => Hj2.
  + pose k := j - double_block.
    have Hk : 0 <= k < block by rewrite /k /block /double_block /second_base; smt().
    have Hlo : -q <= coeff p.[j] < q
      by apply (radix2_64_output_shape_qrange p j Hshape); smt().
    have Hhi : -q <= coeff p.[j + block] < q
      by apply (radix2_64_output_shape_qrange p (j + block) Hshape); smt().
    have Hpair := radix2_32_pair_algebra 1 zeta2 p.[j] p.[j + block]
      radix2_32_zeta2_root _ Hlo Hhi
      radix2_32_zeta2_in_qrange radix2_32_zeta2_montgomery_meaning; first smt().
    have Hpaireq1_0 :
        radix2_32_pair_at p0 double_block zeta2 k =
        radix2_32_pair_at p double_block zeta2 k.
    + rewrite /p0.
      by apply (radix2_32_block_spec_far_pair_at p 0 double_block k zeta1 zeta2); smt().
    have Hout :
        (radix2_32_block_spec p10 (second_base + 5 * double_block) zeta12).[j] =
        (radix2_32_pair_at p double_block zeta2 k).`1.
    +
      rewrite (radix2_32_block_spec_before p10 (second_base + 5 * double_block) j zeta12 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p9 (second_base + 4 * double_block) j zeta11 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p8 (second_base + 3 * double_block) j zeta10 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p7 (second_base + 2 * double_block) j zeta9 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p6 (second_base + double_block) j zeta8 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p5 second_base j zeta7 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p4 (5 * double_block) j zeta6 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p3 (4 * double_block) j zeta5 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p2 (3 * double_block) j zeta4 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p1 (2 * double_block) j zeta3 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_get0_valid p0 double_block k zeta2 Hvalid1 Hk).
      by rewrite Hpaireq1_0.
    move: Hpair.
    rewrite /k Hout /radix2_32_pair_at /radix2_32_pair_math_at /radix2_32_pair_math /=.
    move=> [Hr0 [Hr1 [Hc0 Hc1]]].
    split; first exact Hr0.
    exact Hc0.
  case (j < double_block + double_block) => Hj3.
  + pose k := j - double_block - block.
    have Hk : 0 <= k < block by rewrite /k /block /double_block /second_base; smt().
    have Hlo : -q <= coeff p.[j - block] < q
      by apply (radix2_64_output_shape_qrange p (j - block) Hshape); smt().
    have Hhi : -q <= coeff p.[j] < q
      by apply (radix2_64_output_shape_qrange p j Hshape); smt().
    have Hpair := radix2_32_pair_algebra 1 zeta2 p.[j - block] p.[j]
      radix2_32_zeta2_root _ Hlo Hhi
      radix2_32_zeta2_in_qrange radix2_32_zeta2_montgomery_meaning; first smt().
    have Hpaireq1_0 :
        radix2_32_pair_at p0 double_block zeta2 k =
        radix2_32_pair_at p double_block zeta2 k.
    + rewrite /p0.
      by apply (radix2_32_block_spec_far_pair_at p 0 double_block k zeta1 zeta2); smt().
    have Hout :
        (radix2_32_block_spec p10 (second_base + 5 * double_block) zeta12).[j] =
        (radix2_32_pair_at p double_block zeta2 k).`2.
    +
      rewrite (radix2_32_block_spec_before p10 (second_base + 5 * double_block) j zeta12 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p9 (second_base + 4 * double_block) j zeta11 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p8 (second_base + 3 * double_block) j zeta10 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p7 (second_base + 2 * double_block) j zeta9 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p6 (second_base + double_block) j zeta8 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p5 second_base j zeta7 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p4 (5 * double_block) j zeta6 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p3 (4 * double_block) j zeta5 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p2 (3 * double_block) j zeta4 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p1 (2 * double_block) j zeta3 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_get1_valid p0 double_block k zeta2 Hvalid1 Hk).
      by rewrite Hpaireq1_0.
    move: Hpair.
    rewrite /k Hout /radix2_32_pair_at /radix2_32_pair_math_at /radix2_32_pair_math /=.
    move=> [Hr0 [Hr1 [Hc0 Hc1]]].
    split; first exact Hr1.
    exact Hc1.
  case (j < (2 * double_block) + block) => Hj4.
  + pose k := j - (2 * double_block).
    have Hk : 0 <= k < block by rewrite /k /block /double_block /second_base; smt().
    have Hlo : -q <= coeff p.[j] < q
      by apply (radix2_64_output_shape_qrange p j Hshape); smt().
    have Hhi : -q <= coeff p.[j + block] < q
      by apply (radix2_64_output_shape_qrange p (j + block) Hshape); smt().
    have Hpair := radix2_32_pair_algebra 1 zeta3 p.[j] p.[j + block]
      radix2_32_zeta3_root _ Hlo Hhi
      radix2_32_zeta3_in_qrange radix2_32_zeta3_montgomery_meaning; first smt().
    have Hpaireq2_1 :
        radix2_32_pair_at p1 (2 * double_block) zeta3 k =
        radix2_32_pair_at p0 (2 * double_block) zeta3 k.
    + rewrite /p1.
      by apply (radix2_32_block_spec_far_pair_at p0 double_block (2 * double_block) k zeta2 zeta3); smt().
    have Hpaireq2_0 :
        radix2_32_pair_at p0 (2 * double_block) zeta3 k =
        radix2_32_pair_at p (2 * double_block) zeta3 k.
    + rewrite /p0.
      by apply (radix2_32_block_spec_far_pair_at p 0 (2 * double_block) k zeta1 zeta3); smt().
    have Hout :
        (radix2_32_block_spec p10 (second_base + 5 * double_block) zeta12).[j] =
        (radix2_32_pair_at p (2 * double_block) zeta3 k).`1.
    +
      rewrite (radix2_32_block_spec_before p10 (second_base + 5 * double_block) j zeta12 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p9 (second_base + 4 * double_block) j zeta11 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p8 (second_base + 3 * double_block) j zeta10 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p7 (second_base + 2 * double_block) j zeta9 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p6 (second_base + double_block) j zeta8 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p5 second_base j zeta7 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p4 (5 * double_block) j zeta6 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p3 (4 * double_block) j zeta5 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p2 (3 * double_block) j zeta4 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_get0_valid p1 (2 * double_block) k zeta3 Hvalid2 Hk).
      by rewrite Hpaireq2_1 Hpaireq2_0.
    move: Hpair.
    rewrite /k Hout /radix2_32_pair_at /radix2_32_pair_math_at /radix2_32_pair_math /=.
    move=> [Hr0 [Hr1 [Hc0 Hc1]]].
    split; first exact Hr0.
    exact Hc0.
  case (j < (2 * double_block) + double_block) => Hj5.
  + pose k := j - (2 * double_block) - block.
    have Hk : 0 <= k < block by rewrite /k /block /double_block /second_base; smt().
    have Hlo : -q <= coeff p.[j - block] < q
      by apply (radix2_64_output_shape_qrange p (j - block) Hshape); smt().
    have Hhi : -q <= coeff p.[j] < q
      by apply (radix2_64_output_shape_qrange p j Hshape); smt().
    have Hpair := radix2_32_pair_algebra 1 zeta3 p.[j - block] p.[j]
      radix2_32_zeta3_root _ Hlo Hhi
      radix2_32_zeta3_in_qrange radix2_32_zeta3_montgomery_meaning; first smt().
    have Hpaireq2_1 :
        radix2_32_pair_at p1 (2 * double_block) zeta3 k =
        radix2_32_pair_at p0 (2 * double_block) zeta3 k.
    + rewrite /p1.
      by apply (radix2_32_block_spec_far_pair_at p0 double_block (2 * double_block) k zeta2 zeta3); smt().
    have Hpaireq2_0 :
        radix2_32_pair_at p0 (2 * double_block) zeta3 k =
        radix2_32_pair_at p (2 * double_block) zeta3 k.
    + rewrite /p0.
      by apply (radix2_32_block_spec_far_pair_at p 0 (2 * double_block) k zeta1 zeta3); smt().
    have Hout :
        (radix2_32_block_spec p10 (second_base + 5 * double_block) zeta12).[j] =
        (radix2_32_pair_at p (2 * double_block) zeta3 k).`2.
    +
      rewrite (radix2_32_block_spec_before p10 (second_base + 5 * double_block) j zeta12 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p9 (second_base + 4 * double_block) j zeta11 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p8 (second_base + 3 * double_block) j zeta10 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p7 (second_base + 2 * double_block) j zeta9 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p6 (second_base + double_block) j zeta8 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p5 second_base j zeta7 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p4 (5 * double_block) j zeta6 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p3 (4 * double_block) j zeta5 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p2 (3 * double_block) j zeta4 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_get1_valid p1 (2 * double_block) k zeta3 Hvalid2 Hk).
      by rewrite Hpaireq2_1 Hpaireq2_0.
    move: Hpair.
    rewrite /k Hout /radix2_32_pair_at /radix2_32_pair_math_at /radix2_32_pair_math /=.
    move=> [Hr0 [Hr1 [Hc0 Hc1]]].
    split; first exact Hr1.
    exact Hc1.
  case (j < (3 * double_block) + block) => Hj6.
  + pose k := j - (3 * double_block).
    have Hk : 0 <= k < block by rewrite /k /block /double_block /second_base; smt().
    have Hlo : -q <= coeff p.[j] < q
      by apply (radix2_64_output_shape_qrange p j Hshape); smt().
    have Hhi : -q <= coeff p.[j + block] < q
      by apply (radix2_64_output_shape_qrange p (j + block) Hshape); smt().
    have Hpair := radix2_32_pair_algebra 1 zeta4 p.[j] p.[j + block]
      radix2_32_zeta4_root _ Hlo Hhi
      radix2_32_zeta4_in_qrange radix2_32_zeta4_montgomery_meaning; first smt().
    have Hpaireq3_2 :
        radix2_32_pair_at p2 (3 * double_block) zeta4 k =
        radix2_32_pair_at p1 (3 * double_block) zeta4 k.
    + rewrite /p2.
      by apply (radix2_32_block_spec_far_pair_at p1 (2 * double_block) (3 * double_block) k zeta3 zeta4); smt().
    have Hpaireq3_1 :
        radix2_32_pair_at p1 (3 * double_block) zeta4 k =
        radix2_32_pair_at p0 (3 * double_block) zeta4 k.
    + rewrite /p1.
      by apply (radix2_32_block_spec_far_pair_at p0 double_block (3 * double_block) k zeta2 zeta4); smt().
    have Hpaireq3_0 :
        radix2_32_pair_at p0 (3 * double_block) zeta4 k =
        radix2_32_pair_at p (3 * double_block) zeta4 k.
    + rewrite /p0.
      by apply (radix2_32_block_spec_far_pair_at p 0 (3 * double_block) k zeta1 zeta4); smt().
    have Hout :
        (radix2_32_block_spec p10 (second_base + 5 * double_block) zeta12).[j] =
        (radix2_32_pair_at p (3 * double_block) zeta4 k).`1.
    +
      rewrite (radix2_32_block_spec_before p10 (second_base + 5 * double_block) j zeta12 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p9 (second_base + 4 * double_block) j zeta11 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p8 (second_base + 3 * double_block) j zeta10 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p7 (second_base + 2 * double_block) j zeta9 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p6 (second_base + double_block) j zeta8 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p5 second_base j zeta7 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p4 (5 * double_block) j zeta6 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p3 (4 * double_block) j zeta5 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_get0_valid p2 (3 * double_block) k zeta4 Hvalid3 Hk).
      by rewrite Hpaireq3_2 Hpaireq3_1 Hpaireq3_0.
    move: Hpair.
    rewrite /k Hout /radix2_32_pair_at /radix2_32_pair_math_at /radix2_32_pair_math /=.
    move=> [Hr0 [Hr1 [Hc0 Hc1]]].
    split; first exact Hr0.
    exact Hc0.
  case (j < (3 * double_block) + double_block) => Hj7.
  + pose k := j - (3 * double_block) - block.
    have Hk : 0 <= k < block by rewrite /k /block /double_block /second_base; smt().
    have Hlo : -q <= coeff p.[j - block] < q
      by apply (radix2_64_output_shape_qrange p (j - block) Hshape); smt().
    have Hhi : -q <= coeff p.[j] < q
      by apply (radix2_64_output_shape_qrange p j Hshape); smt().
    have Hpair := radix2_32_pair_algebra 1 zeta4 p.[j - block] p.[j]
      radix2_32_zeta4_root _ Hlo Hhi
      radix2_32_zeta4_in_qrange radix2_32_zeta4_montgomery_meaning; first smt().
    have Hpaireq3_2 :
        radix2_32_pair_at p2 (3 * double_block) zeta4 k =
        radix2_32_pair_at p1 (3 * double_block) zeta4 k.
    + rewrite /p2.
      by apply (radix2_32_block_spec_far_pair_at p1 (2 * double_block) (3 * double_block) k zeta3 zeta4); smt().
    have Hpaireq3_1 :
        radix2_32_pair_at p1 (3 * double_block) zeta4 k =
        radix2_32_pair_at p0 (3 * double_block) zeta4 k.
    + rewrite /p1.
      by apply (radix2_32_block_spec_far_pair_at p0 double_block (3 * double_block) k zeta2 zeta4); smt().
    have Hpaireq3_0 :
        radix2_32_pair_at p0 (3 * double_block) zeta4 k =
        radix2_32_pair_at p (3 * double_block) zeta4 k.
    + rewrite /p0.
      by apply (radix2_32_block_spec_far_pair_at p 0 (3 * double_block) k zeta1 zeta4); smt().
    have Hout :
        (radix2_32_block_spec p10 (second_base + 5 * double_block) zeta12).[j] =
        (radix2_32_pair_at p (3 * double_block) zeta4 k).`2.
    +
      rewrite (radix2_32_block_spec_before p10 (second_base + 5 * double_block) j zeta12 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p9 (second_base + 4 * double_block) j zeta11 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p8 (second_base + 3 * double_block) j zeta10 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p7 (second_base + 2 * double_block) j zeta9 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p6 (second_base + double_block) j zeta8 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p5 second_base j zeta7 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p4 (5 * double_block) j zeta6 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p3 (4 * double_block) j zeta5 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_get1_valid p2 (3 * double_block) k zeta4 Hvalid3 Hk).
      by rewrite Hpaireq3_2 Hpaireq3_1 Hpaireq3_0.
    move: Hpair.
    rewrite /k Hout /radix2_32_pair_at /radix2_32_pair_math_at /radix2_32_pair_math /=.
    move=> [Hr0 [Hr1 [Hc0 Hc1]]].
    split; first exact Hr1.
    exact Hc1.
  case (j < (4 * double_block) + block) => Hj8.
  + pose k := j - (4 * double_block).
    have Hk : 0 <= k < block by rewrite /k /block /double_block /second_base; smt().
    have Hlo : -q <= coeff p.[j] < q
      by apply (radix2_64_output_shape_qrange p j Hshape); smt().
    have Hhi : -q <= coeff p.[j + block] < q
      by apply (radix2_64_output_shape_qrange p (j + block) Hshape); smt().
    have Hpair := radix2_32_pair_algebra 1 zeta5 p.[j] p.[j + block]
      radix2_32_zeta5_root _ Hlo Hhi
      radix2_32_zeta5_in_qrange radix2_32_zeta5_montgomery_meaning; first smt().
    have Hpaireq4_3 :
        radix2_32_pair_at p3 (4 * double_block) zeta5 k =
        radix2_32_pair_at p2 (4 * double_block) zeta5 k.
    + rewrite /p3.
      by apply (radix2_32_block_spec_far_pair_at p2 (3 * double_block) (4 * double_block) k zeta4 zeta5); smt().
    have Hpaireq4_2 :
        radix2_32_pair_at p2 (4 * double_block) zeta5 k =
        radix2_32_pair_at p1 (4 * double_block) zeta5 k.
    + rewrite /p2.
      by apply (radix2_32_block_spec_far_pair_at p1 (2 * double_block) (4 * double_block) k zeta3 zeta5); smt().
    have Hpaireq4_1 :
        radix2_32_pair_at p1 (4 * double_block) zeta5 k =
        radix2_32_pair_at p0 (4 * double_block) zeta5 k.
    + rewrite /p1.
      by apply (radix2_32_block_spec_far_pair_at p0 double_block (4 * double_block) k zeta2 zeta5); smt().
    have Hpaireq4_0 :
        radix2_32_pair_at p0 (4 * double_block) zeta5 k =
        radix2_32_pair_at p (4 * double_block) zeta5 k.
    + rewrite /p0.
      by apply (radix2_32_block_spec_far_pair_at p 0 (4 * double_block) k zeta1 zeta5); smt().
    have Hout :
        (radix2_32_block_spec p10 (second_base + 5 * double_block) zeta12).[j] =
        (radix2_32_pair_at p (4 * double_block) zeta5 k).`1.
    +
      rewrite (radix2_32_block_spec_before p10 (second_base + 5 * double_block) j zeta12 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p9 (second_base + 4 * double_block) j zeta11 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p8 (second_base + 3 * double_block) j zeta10 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p7 (second_base + 2 * double_block) j zeta9 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p6 (second_base + double_block) j zeta8 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p5 second_base j zeta7 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p4 (5 * double_block) j zeta6 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_get0_valid p3 (4 * double_block) k zeta5 Hvalid4 Hk).
      by rewrite Hpaireq4_3 Hpaireq4_2 Hpaireq4_1 Hpaireq4_0.
    move: Hpair.
    rewrite /k Hout /radix2_32_pair_at /radix2_32_pair_math_at /radix2_32_pair_math /=.
    move=> [Hr0 [Hr1 [Hc0 Hc1]]].
    split; first exact Hr0.
    exact Hc0.
  case (j < (4 * double_block) + double_block) => Hj9.
  + pose k := j - (4 * double_block) - block.
    have Hk : 0 <= k < block by rewrite /k /block /double_block /second_base; smt().
    have Hlo : -q <= coeff p.[j - block] < q
      by apply (radix2_64_output_shape_qrange p (j - block) Hshape); smt().
    have Hhi : -q <= coeff p.[j] < q
      by apply (radix2_64_output_shape_qrange p j Hshape); smt().
    have Hpair := radix2_32_pair_algebra 1 zeta5 p.[j - block] p.[j]
      radix2_32_zeta5_root _ Hlo Hhi
      radix2_32_zeta5_in_qrange radix2_32_zeta5_montgomery_meaning; first smt().
    have Hpaireq4_3 :
        radix2_32_pair_at p3 (4 * double_block) zeta5 k =
        radix2_32_pair_at p2 (4 * double_block) zeta5 k.
    + rewrite /p3.
      by apply (radix2_32_block_spec_far_pair_at p2 (3 * double_block) (4 * double_block) k zeta4 zeta5); smt().
    have Hpaireq4_2 :
        radix2_32_pair_at p2 (4 * double_block) zeta5 k =
        radix2_32_pair_at p1 (4 * double_block) zeta5 k.
    + rewrite /p2.
      by apply (radix2_32_block_spec_far_pair_at p1 (2 * double_block) (4 * double_block) k zeta3 zeta5); smt().
    have Hpaireq4_1 :
        radix2_32_pair_at p1 (4 * double_block) zeta5 k =
        radix2_32_pair_at p0 (4 * double_block) zeta5 k.
    + rewrite /p1.
      by apply (radix2_32_block_spec_far_pair_at p0 double_block (4 * double_block) k zeta2 zeta5); smt().
    have Hpaireq4_0 :
        radix2_32_pair_at p0 (4 * double_block) zeta5 k =
        radix2_32_pair_at p (4 * double_block) zeta5 k.
    + rewrite /p0.
      by apply (radix2_32_block_spec_far_pair_at p 0 (4 * double_block) k zeta1 zeta5); smt().
    have Hout :
        (radix2_32_block_spec p10 (second_base + 5 * double_block) zeta12).[j] =
        (radix2_32_pair_at p (4 * double_block) zeta5 k).`2.
    +
      rewrite (radix2_32_block_spec_before p10 (second_base + 5 * double_block) j zeta12 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p9 (second_base + 4 * double_block) j zeta11 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p8 (second_base + 3 * double_block) j zeta10 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p7 (second_base + 2 * double_block) j zeta9 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p6 (second_base + double_block) j zeta8 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p5 second_base j zeta7 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p4 (5 * double_block) j zeta6 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_get1_valid p3 (4 * double_block) k zeta5 Hvalid4 Hk).
      by rewrite Hpaireq4_3 Hpaireq4_2 Hpaireq4_1 Hpaireq4_0.
    move: Hpair.
    rewrite /k Hout /radix2_32_pair_at /radix2_32_pair_math_at /radix2_32_pair_math /=.
    move=> [Hr0 [Hr1 [Hc0 Hc1]]].
    split; first exact Hr1.
    exact Hc1.
  case (j < (5 * double_block) + block) => Hj10.
  + pose k := j - (5 * double_block).
    have Hk : 0 <= k < block by rewrite /k /block /double_block /second_base; smt().
    have Hlo : -q <= coeff p.[j] < q
      by apply (radix2_64_output_shape_qrange p j Hshape); smt().
    have Hhi : -q <= coeff p.[j + block] < q
      by apply (radix2_64_output_shape_qrange p (j + block) Hshape); smt().
    have Hpair := radix2_32_pair_algebra 1 zeta6 p.[j] p.[j + block]
      radix2_32_zeta6_root _ Hlo Hhi
      radix2_32_zeta6_in_qrange radix2_32_zeta6_montgomery_meaning; first smt().
    have Hpaireq5_4 :
        radix2_32_pair_at p4 (5 * double_block) zeta6 k =
        radix2_32_pair_at p3 (5 * double_block) zeta6 k.
    + rewrite /p4.
      by apply (radix2_32_block_spec_far_pair_at p3 (4 * double_block) (5 * double_block) k zeta5 zeta6); smt().
    have Hpaireq5_3 :
        radix2_32_pair_at p3 (5 * double_block) zeta6 k =
        radix2_32_pair_at p2 (5 * double_block) zeta6 k.
    + rewrite /p3.
      by apply (radix2_32_block_spec_far_pair_at p2 (3 * double_block) (5 * double_block) k zeta4 zeta6); smt().
    have Hpaireq5_2 :
        radix2_32_pair_at p2 (5 * double_block) zeta6 k =
        radix2_32_pair_at p1 (5 * double_block) zeta6 k.
    + rewrite /p2.
      by apply (radix2_32_block_spec_far_pair_at p1 (2 * double_block) (5 * double_block) k zeta3 zeta6); smt().
    have Hpaireq5_1 :
        radix2_32_pair_at p1 (5 * double_block) zeta6 k =
        radix2_32_pair_at p0 (5 * double_block) zeta6 k.
    + rewrite /p1.
      by apply (radix2_32_block_spec_far_pair_at p0 double_block (5 * double_block) k zeta2 zeta6); smt().
    have Hpaireq5_0 :
        radix2_32_pair_at p0 (5 * double_block) zeta6 k =
        radix2_32_pair_at p (5 * double_block) zeta6 k.
    + rewrite /p0.
      by apply (radix2_32_block_spec_far_pair_at p 0 (5 * double_block) k zeta1 zeta6); smt().
    have Hout :
        (radix2_32_block_spec p10 (second_base + 5 * double_block) zeta12).[j] =
        (radix2_32_pair_at p (5 * double_block) zeta6 k).`1.
    +
      rewrite (radix2_32_block_spec_before p10 (second_base + 5 * double_block) j zeta12 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p9 (second_base + 4 * double_block) j zeta11 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p8 (second_base + 3 * double_block) j zeta10 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p7 (second_base + 2 * double_block) j zeta9 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p6 (second_base + double_block) j zeta8 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p5 second_base j zeta7 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_get0_valid p4 (5 * double_block) k zeta6 Hvalid5 Hk).
      by rewrite Hpaireq5_4 Hpaireq5_3 Hpaireq5_2 Hpaireq5_1 Hpaireq5_0.
    move: Hpair.
    rewrite /k Hout /radix2_32_pair_at /radix2_32_pair_math_at /radix2_32_pair_math /=.
    move=> [Hr0 [Hr1 [Hc0 Hc1]]].
    split; first exact Hr0.
    exact Hc0.
  case (j < (5 * double_block) + double_block) => Hj11.
  + pose k := j - (5 * double_block) - block.
    have Hk : 0 <= k < block by rewrite /k /block /double_block /second_base; smt().
    have Hlo : -q <= coeff p.[j - block] < q
      by apply (radix2_64_output_shape_qrange p (j - block) Hshape); smt().
    have Hhi : -q <= coeff p.[j] < q
      by apply (radix2_64_output_shape_qrange p j Hshape); smt().
    have Hpair := radix2_32_pair_algebra 1 zeta6 p.[j - block] p.[j]
      radix2_32_zeta6_root _ Hlo Hhi
      radix2_32_zeta6_in_qrange radix2_32_zeta6_montgomery_meaning; first smt().
    have Hpaireq5_4 :
        radix2_32_pair_at p4 (5 * double_block) zeta6 k =
        radix2_32_pair_at p3 (5 * double_block) zeta6 k.
    + rewrite /p4.
      by apply (radix2_32_block_spec_far_pair_at p3 (4 * double_block) (5 * double_block) k zeta5 zeta6); smt().
    have Hpaireq5_3 :
        radix2_32_pair_at p3 (5 * double_block) zeta6 k =
        radix2_32_pair_at p2 (5 * double_block) zeta6 k.
    + rewrite /p3.
      by apply (radix2_32_block_spec_far_pair_at p2 (3 * double_block) (5 * double_block) k zeta4 zeta6); smt().
    have Hpaireq5_2 :
        radix2_32_pair_at p2 (5 * double_block) zeta6 k =
        radix2_32_pair_at p1 (5 * double_block) zeta6 k.
    + rewrite /p2.
      by apply (radix2_32_block_spec_far_pair_at p1 (2 * double_block) (5 * double_block) k zeta3 zeta6); smt().
    have Hpaireq5_1 :
        radix2_32_pair_at p1 (5 * double_block) zeta6 k =
        radix2_32_pair_at p0 (5 * double_block) zeta6 k.
    + rewrite /p1.
      by apply (radix2_32_block_spec_far_pair_at p0 double_block (5 * double_block) k zeta2 zeta6); smt().
    have Hpaireq5_0 :
        radix2_32_pair_at p0 (5 * double_block) zeta6 k =
        radix2_32_pair_at p (5 * double_block) zeta6 k.
    + rewrite /p0.
      by apply (radix2_32_block_spec_far_pair_at p 0 (5 * double_block) k zeta1 zeta6); smt().
    have Hout :
        (radix2_32_block_spec p10 (second_base + 5 * double_block) zeta12).[j] =
        (radix2_32_pair_at p (5 * double_block) zeta6 k).`2.
    +
      rewrite (radix2_32_block_spec_before p10 (second_base + 5 * double_block) j zeta12 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p9 (second_base + 4 * double_block) j zeta11 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p8 (second_base + 3 * double_block) j zeta10 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p7 (second_base + 2 * double_block) j zeta9 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p6 (second_base + double_block) j zeta8 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p5 second_base j zeta7 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_get1_valid p4 (5 * double_block) k zeta6 Hvalid5 Hk).
      by rewrite Hpaireq5_4 Hpaireq5_3 Hpaireq5_2 Hpaireq5_1 Hpaireq5_0.
    move: Hpair.
    rewrite /k Hout /radix2_32_pair_at /radix2_32_pair_math_at /radix2_32_pair_math /=.
    move=> [Hr0 [Hr1 [Hc0 Hc1]]].
    split; first exact Hr1.
    exact Hc1.
  case (j < second_base + block) => Hj12.
  + pose k := j - second_base.
    have Hk : 0 <= k < block by rewrite /k /block /double_block /second_base; smt().
    have Hlo : -q <= coeff p.[j] < q
      by apply (radix2_64_output_shape_qrange p j Hshape); smt().
    have Hhi : -q <= coeff p.[j + block] < q
      by apply (radix2_64_output_shape_qrange p (j + block) Hshape); smt().
    have Hpair := radix2_32_pair_algebra 1 zeta7 p.[j] p.[j + block]
      radix2_32_zeta7_root _ Hlo Hhi
      radix2_32_zeta7_in_qrange radix2_32_zeta7_montgomery_meaning; first smt().
    have Hpaireq6_5 :
        radix2_32_pair_at p5 second_base zeta7 k =
        radix2_32_pair_at p4 second_base zeta7 k.
    + rewrite /p5.
      by apply (radix2_32_block_spec_far_pair_at p4 (5 * double_block) second_base k zeta6 zeta7); smt().
    have Hpaireq6_4 :
        radix2_32_pair_at p4 second_base zeta7 k =
        radix2_32_pair_at p3 second_base zeta7 k.
    + rewrite /p4.
      by apply (radix2_32_block_spec_far_pair_at p3 (4 * double_block) second_base k zeta5 zeta7); smt().
    have Hpaireq6_3 :
        radix2_32_pair_at p3 second_base zeta7 k =
        radix2_32_pair_at p2 second_base zeta7 k.
    + rewrite /p3.
      by apply (radix2_32_block_spec_far_pair_at p2 (3 * double_block) second_base k zeta4 zeta7); smt().
    have Hpaireq6_2 :
        radix2_32_pair_at p2 second_base zeta7 k =
        radix2_32_pair_at p1 second_base zeta7 k.
    + rewrite /p2.
      by apply (radix2_32_block_spec_far_pair_at p1 (2 * double_block) second_base k zeta3 zeta7); smt().
    have Hpaireq6_1 :
        radix2_32_pair_at p1 second_base zeta7 k =
        radix2_32_pair_at p0 second_base zeta7 k.
    + rewrite /p1.
      by apply (radix2_32_block_spec_far_pair_at p0 double_block second_base k zeta2 zeta7); smt().
    have Hpaireq6_0 :
        radix2_32_pair_at p0 second_base zeta7 k =
        radix2_32_pair_at p second_base zeta7 k.
    + rewrite /p0.
      by apply (radix2_32_block_spec_far_pair_at p 0 second_base k zeta1 zeta7); smt().
    have Hout :
        (radix2_32_block_spec p10 (second_base + 5 * double_block) zeta12).[j] =
        (radix2_32_pair_at p second_base zeta7 k).`1.
    +
      rewrite (radix2_32_block_spec_before p10 (second_base + 5 * double_block) j zeta12 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p9 (second_base + 4 * double_block) j zeta11 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p8 (second_base + 3 * double_block) j zeta10 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p7 (second_base + 2 * double_block) j zeta9 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p6 (second_base + double_block) j zeta8 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_get0_valid p5 second_base k zeta7 Hvalid6 Hk).
      by rewrite Hpaireq6_5 Hpaireq6_4 Hpaireq6_3 Hpaireq6_2 Hpaireq6_1 Hpaireq6_0.
    move: Hpair.
    rewrite /k Hout /radix2_32_pair_at /radix2_32_pair_math_at /radix2_32_pair_math /=.
    move=> [Hr0 [Hr1 [Hc0 Hc1]]].
    split; first exact Hr0.
    exact Hc0.
  case (j < second_base + double_block) => Hj13.
  + pose k := j - second_base - block.
    have Hk : 0 <= k < block by rewrite /k /block /double_block /second_base; smt().
    have Hlo : -q <= coeff p.[j - block] < q
      by apply (radix2_64_output_shape_qrange p (j - block) Hshape); smt().
    have Hhi : -q <= coeff p.[j] < q
      by apply (radix2_64_output_shape_qrange p j Hshape); smt().
    have Hpair := radix2_32_pair_algebra 1 zeta7 p.[j - block] p.[j]
      radix2_32_zeta7_root _ Hlo Hhi
      radix2_32_zeta7_in_qrange radix2_32_zeta7_montgomery_meaning; first smt().
    have Hpaireq6_5 :
        radix2_32_pair_at p5 second_base zeta7 k =
        radix2_32_pair_at p4 second_base zeta7 k.
    + rewrite /p5.
      by apply (radix2_32_block_spec_far_pair_at p4 (5 * double_block) second_base k zeta6 zeta7); smt().
    have Hpaireq6_4 :
        radix2_32_pair_at p4 second_base zeta7 k =
        radix2_32_pair_at p3 second_base zeta7 k.
    + rewrite /p4.
      by apply (radix2_32_block_spec_far_pair_at p3 (4 * double_block) second_base k zeta5 zeta7); smt().
    have Hpaireq6_3 :
        radix2_32_pair_at p3 second_base zeta7 k =
        radix2_32_pair_at p2 second_base zeta7 k.
    + rewrite /p3.
      by apply (radix2_32_block_spec_far_pair_at p2 (3 * double_block) second_base k zeta4 zeta7); smt().
    have Hpaireq6_2 :
        radix2_32_pair_at p2 second_base zeta7 k =
        radix2_32_pair_at p1 second_base zeta7 k.
    + rewrite /p2.
      by apply (radix2_32_block_spec_far_pair_at p1 (2 * double_block) second_base k zeta3 zeta7); smt().
    have Hpaireq6_1 :
        radix2_32_pair_at p1 second_base zeta7 k =
        radix2_32_pair_at p0 second_base zeta7 k.
    + rewrite /p1.
      by apply (radix2_32_block_spec_far_pair_at p0 double_block second_base k zeta2 zeta7); smt().
    have Hpaireq6_0 :
        radix2_32_pair_at p0 second_base zeta7 k =
        radix2_32_pair_at p second_base zeta7 k.
    + rewrite /p0.
      by apply (radix2_32_block_spec_far_pair_at p 0 second_base k zeta1 zeta7); smt().
    have Hout :
        (radix2_32_block_spec p10 (second_base + 5 * double_block) zeta12).[j] =
        (radix2_32_pair_at p second_base zeta7 k).`2.
    +
      rewrite (radix2_32_block_spec_before p10 (second_base + 5 * double_block) j zeta12 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p9 (second_base + 4 * double_block) j zeta11 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p8 (second_base + 3 * double_block) j zeta10 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p7 (second_base + 2 * double_block) j zeta9 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p6 (second_base + double_block) j zeta8 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_get1_valid p5 second_base k zeta7 Hvalid6 Hk).
      by rewrite Hpaireq6_5 Hpaireq6_4 Hpaireq6_3 Hpaireq6_2 Hpaireq6_1 Hpaireq6_0.
    move: Hpair.
    rewrite /k Hout /radix2_32_pair_at /radix2_32_pair_math_at /radix2_32_pair_math /=.
    move=> [Hr0 [Hr1 [Hc0 Hc1]]].
    split; first exact Hr1.
    exact Hc1.
  case (j < (second_base + double_block) + block) => Hj14.
  + pose k := j - (second_base + double_block).
    have Hk : 0 <= k < block by rewrite /k /block /double_block /second_base; smt().
    have Hlo : -q <= coeff p.[j] < q
      by apply (radix2_64_output_shape_qrange p j Hshape); smt().
    have Hhi : -q <= coeff p.[j + block] < q
      by apply (radix2_64_output_shape_qrange p (j + block) Hshape); smt().
    have Hpair := radix2_32_pair_algebra 1 zeta8 p.[j] p.[j + block]
      radix2_32_zeta8_root _ Hlo Hhi
      radix2_32_zeta8_in_qrange radix2_32_zeta8_montgomery_meaning; first smt().
    have Hpaireq7_6 :
        radix2_32_pair_at p6 (second_base + double_block) zeta8 k =
        radix2_32_pair_at p5 (second_base + double_block) zeta8 k.
    + rewrite /p6.
      by apply (radix2_32_block_spec_far_pair_at p5 second_base (second_base + double_block) k zeta7 zeta8); smt().
    have Hpaireq7_5 :
        radix2_32_pair_at p5 (second_base + double_block) zeta8 k =
        radix2_32_pair_at p4 (second_base + double_block) zeta8 k.
    + rewrite /p5.
      by apply (radix2_32_block_spec_far_pair_at p4 (5 * double_block) (second_base + double_block) k zeta6 zeta8); smt().
    have Hpaireq7_4 :
        radix2_32_pair_at p4 (second_base + double_block) zeta8 k =
        radix2_32_pair_at p3 (second_base + double_block) zeta8 k.
    + rewrite /p4.
      by apply (radix2_32_block_spec_far_pair_at p3 (4 * double_block) (second_base + double_block) k zeta5 zeta8); smt().
    have Hpaireq7_3 :
        radix2_32_pair_at p3 (second_base + double_block) zeta8 k =
        radix2_32_pair_at p2 (second_base + double_block) zeta8 k.
    + rewrite /p3.
      by apply (radix2_32_block_spec_far_pair_at p2 (3 * double_block) (second_base + double_block) k zeta4 zeta8); smt().
    have Hpaireq7_2 :
        radix2_32_pair_at p2 (second_base + double_block) zeta8 k =
        radix2_32_pair_at p1 (second_base + double_block) zeta8 k.
    + rewrite /p2.
      by apply (radix2_32_block_spec_far_pair_at p1 (2 * double_block) (second_base + double_block) k zeta3 zeta8); smt().
    have Hpaireq7_1 :
        radix2_32_pair_at p1 (second_base + double_block) zeta8 k =
        radix2_32_pair_at p0 (second_base + double_block) zeta8 k.
    + rewrite /p1.
      by apply (radix2_32_block_spec_far_pair_at p0 double_block (second_base + double_block) k zeta2 zeta8); smt().
    have Hpaireq7_0 :
        radix2_32_pair_at p0 (second_base + double_block) zeta8 k =
        radix2_32_pair_at p (second_base + double_block) zeta8 k.
    + rewrite /p0.
      by apply (radix2_32_block_spec_far_pair_at p 0 (second_base + double_block) k zeta1 zeta8); smt().
    have Hout :
        (radix2_32_block_spec p10 (second_base + 5 * double_block) zeta12).[j] =
        (radix2_32_pair_at p (second_base + double_block) zeta8 k).`1.
    +
      rewrite (radix2_32_block_spec_before p10 (second_base + 5 * double_block) j zeta12 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p9 (second_base + 4 * double_block) j zeta11 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p8 (second_base + 3 * double_block) j zeta10 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p7 (second_base + 2 * double_block) j zeta9 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_get0_valid p6 (second_base + double_block) k zeta8 Hvalid7 Hk).
      by rewrite Hpaireq7_6 Hpaireq7_5 Hpaireq7_4 Hpaireq7_3 Hpaireq7_2 Hpaireq7_1 Hpaireq7_0.
    move: Hpair.
    rewrite /k Hout /radix2_32_pair_at /radix2_32_pair_math_at /radix2_32_pair_math /=.
    move=> [Hr0 [Hr1 [Hc0 Hc1]]].
    split; first exact Hr0.
    exact Hc0.
  case (j < (second_base + double_block) + double_block) => Hj15.
  + pose k := j - (second_base + double_block) - block.
    have Hk : 0 <= k < block by rewrite /k /block /double_block /second_base; smt().
    have Hlo : -q <= coeff p.[j - block] < q
      by apply (radix2_64_output_shape_qrange p (j - block) Hshape); smt().
    have Hhi : -q <= coeff p.[j] < q
      by apply (radix2_64_output_shape_qrange p j Hshape); smt().
    have Hpair := radix2_32_pair_algebra 1 zeta8 p.[j - block] p.[j]
      radix2_32_zeta8_root _ Hlo Hhi
      radix2_32_zeta8_in_qrange radix2_32_zeta8_montgomery_meaning; first smt().
    have Hpaireq7_6 :
        radix2_32_pair_at p6 (second_base + double_block) zeta8 k =
        radix2_32_pair_at p5 (second_base + double_block) zeta8 k.
    + rewrite /p6.
      by apply (radix2_32_block_spec_far_pair_at p5 second_base (second_base + double_block) k zeta7 zeta8); smt().
    have Hpaireq7_5 :
        radix2_32_pair_at p5 (second_base + double_block) zeta8 k =
        radix2_32_pair_at p4 (second_base + double_block) zeta8 k.
    + rewrite /p5.
      by apply (radix2_32_block_spec_far_pair_at p4 (5 * double_block) (second_base + double_block) k zeta6 zeta8); smt().
    have Hpaireq7_4 :
        radix2_32_pair_at p4 (second_base + double_block) zeta8 k =
        radix2_32_pair_at p3 (second_base + double_block) zeta8 k.
    + rewrite /p4.
      by apply (radix2_32_block_spec_far_pair_at p3 (4 * double_block) (second_base + double_block) k zeta5 zeta8); smt().
    have Hpaireq7_3 :
        radix2_32_pair_at p3 (second_base + double_block) zeta8 k =
        radix2_32_pair_at p2 (second_base + double_block) zeta8 k.
    + rewrite /p3.
      by apply (radix2_32_block_spec_far_pair_at p2 (3 * double_block) (second_base + double_block) k zeta4 zeta8); smt().
    have Hpaireq7_2 :
        radix2_32_pair_at p2 (second_base + double_block) zeta8 k =
        radix2_32_pair_at p1 (second_base + double_block) zeta8 k.
    + rewrite /p2.
      by apply (radix2_32_block_spec_far_pair_at p1 (2 * double_block) (second_base + double_block) k zeta3 zeta8); smt().
    have Hpaireq7_1 :
        radix2_32_pair_at p1 (second_base + double_block) zeta8 k =
        radix2_32_pair_at p0 (second_base + double_block) zeta8 k.
    + rewrite /p1.
      by apply (radix2_32_block_spec_far_pair_at p0 double_block (second_base + double_block) k zeta2 zeta8); smt().
    have Hpaireq7_0 :
        radix2_32_pair_at p0 (second_base + double_block) zeta8 k =
        radix2_32_pair_at p (second_base + double_block) zeta8 k.
    + rewrite /p0.
      by apply (radix2_32_block_spec_far_pair_at p 0 (second_base + double_block) k zeta1 zeta8); smt().
    have Hout :
        (radix2_32_block_spec p10 (second_base + 5 * double_block) zeta12).[j] =
        (radix2_32_pair_at p (second_base + double_block) zeta8 k).`2.
    +
      rewrite (radix2_32_block_spec_before p10 (second_base + 5 * double_block) j zeta12 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p9 (second_base + 4 * double_block) j zeta11 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p8 (second_base + 3 * double_block) j zeta10 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p7 (second_base + 2 * double_block) j zeta9 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_get1_valid p6 (second_base + double_block) k zeta8 Hvalid7 Hk).
      by rewrite Hpaireq7_6 Hpaireq7_5 Hpaireq7_4 Hpaireq7_3 Hpaireq7_2 Hpaireq7_1 Hpaireq7_0.
    move: Hpair.
    rewrite /k Hout /radix2_32_pair_at /radix2_32_pair_math_at /radix2_32_pair_math /=.
    move=> [Hr0 [Hr1 [Hc0 Hc1]]].
    split; first exact Hr1.
    exact Hc1.
  case (j < (second_base + 2 * double_block) + block) => Hj16.
  + pose k := j - (second_base + 2 * double_block).
    have Hk : 0 <= k < block by rewrite /k /block /double_block /second_base; smt().
    have Hlo : -q <= coeff p.[j] < q
      by apply (radix2_64_output_shape_qrange p j Hshape); smt().
    have Hhi : -q <= coeff p.[j + block] < q
      by apply (radix2_64_output_shape_qrange p (j + block) Hshape); smt().
    have Hpair := radix2_32_pair_algebra 1 zeta9 p.[j] p.[j + block]
      radix2_32_zeta9_root _ Hlo Hhi
      radix2_32_zeta9_in_qrange radix2_32_zeta9_montgomery_meaning; first smt().
    have Hpaireq8_7 :
        radix2_32_pair_at p7 (second_base + 2 * double_block) zeta9 k =
        radix2_32_pair_at p6 (second_base + 2 * double_block) zeta9 k.
    + rewrite /p7.
      by apply (radix2_32_block_spec_far_pair_at p6 (second_base + double_block) (second_base + 2 * double_block) k zeta8 zeta9); smt().
    have Hpaireq8_6 :
        radix2_32_pair_at p6 (second_base + 2 * double_block) zeta9 k =
        radix2_32_pair_at p5 (second_base + 2 * double_block) zeta9 k.
    + rewrite /p6.
      by apply (radix2_32_block_spec_far_pair_at p5 second_base (second_base + 2 * double_block) k zeta7 zeta9); smt().
    have Hpaireq8_5 :
        radix2_32_pair_at p5 (second_base + 2 * double_block) zeta9 k =
        radix2_32_pair_at p4 (second_base + 2 * double_block) zeta9 k.
    + rewrite /p5.
      by apply (radix2_32_block_spec_far_pair_at p4 (5 * double_block) (second_base + 2 * double_block) k zeta6 zeta9); smt().
    have Hpaireq8_4 :
        radix2_32_pair_at p4 (second_base + 2 * double_block) zeta9 k =
        radix2_32_pair_at p3 (second_base + 2 * double_block) zeta9 k.
    + rewrite /p4.
      by apply (radix2_32_block_spec_far_pair_at p3 (4 * double_block) (second_base + 2 * double_block) k zeta5 zeta9); smt().
    have Hpaireq8_3 :
        radix2_32_pair_at p3 (second_base + 2 * double_block) zeta9 k =
        radix2_32_pair_at p2 (second_base + 2 * double_block) zeta9 k.
    + rewrite /p3.
      by apply (radix2_32_block_spec_far_pair_at p2 (3 * double_block) (second_base + 2 * double_block) k zeta4 zeta9); smt().
    have Hpaireq8_2 :
        radix2_32_pair_at p2 (second_base + 2 * double_block) zeta9 k =
        radix2_32_pair_at p1 (second_base + 2 * double_block) zeta9 k.
    + rewrite /p2.
      by apply (radix2_32_block_spec_far_pair_at p1 (2 * double_block) (second_base + 2 * double_block) k zeta3 zeta9); smt().
    have Hpaireq8_1 :
        radix2_32_pair_at p1 (second_base + 2 * double_block) zeta9 k =
        radix2_32_pair_at p0 (second_base + 2 * double_block) zeta9 k.
    + rewrite /p1.
      by apply (radix2_32_block_spec_far_pair_at p0 double_block (second_base + 2 * double_block) k zeta2 zeta9); smt().
    have Hpaireq8_0 :
        radix2_32_pair_at p0 (second_base + 2 * double_block) zeta9 k =
        radix2_32_pair_at p (second_base + 2 * double_block) zeta9 k.
    + rewrite /p0.
      by apply (radix2_32_block_spec_far_pair_at p 0 (second_base + 2 * double_block) k zeta1 zeta9); smt().
    have Hout :
        (radix2_32_block_spec p10 (second_base + 5 * double_block) zeta12).[j] =
        (radix2_32_pair_at p (second_base + 2 * double_block) zeta9 k).`1.
    +
      rewrite (radix2_32_block_spec_before p10 (second_base + 5 * double_block) j zeta12 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p9 (second_base + 4 * double_block) j zeta11 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p8 (second_base + 3 * double_block) j zeta10 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_get0_valid p7 (second_base + 2 * double_block) k zeta9 Hvalid8 Hk).
      by rewrite Hpaireq8_7 Hpaireq8_6 Hpaireq8_5 Hpaireq8_4 Hpaireq8_3 Hpaireq8_2 Hpaireq8_1 Hpaireq8_0.
    move: Hpair.
    rewrite /k Hout /radix2_32_pair_at /radix2_32_pair_math_at /radix2_32_pair_math /=.
    move=> [Hr0 [Hr1 [Hc0 Hc1]]].
    split; first exact Hr0.
    exact Hc0.
  case (j < (second_base + 2 * double_block) + double_block) => Hj17.
  + pose k := j - (second_base + 2 * double_block) - block.
    have Hk : 0 <= k < block by rewrite /k /block /double_block /second_base; smt().
    have Hlo : -q <= coeff p.[j - block] < q
      by apply (radix2_64_output_shape_qrange p (j - block) Hshape); smt().
    have Hhi : -q <= coeff p.[j] < q
      by apply (radix2_64_output_shape_qrange p j Hshape); smt().
    have Hpair := radix2_32_pair_algebra 1 zeta9 p.[j - block] p.[j]
      radix2_32_zeta9_root _ Hlo Hhi
      radix2_32_zeta9_in_qrange radix2_32_zeta9_montgomery_meaning; first smt().
    have Hpaireq8_7 :
        radix2_32_pair_at p7 (second_base + 2 * double_block) zeta9 k =
        radix2_32_pair_at p6 (second_base + 2 * double_block) zeta9 k.
    + rewrite /p7.
      by apply (radix2_32_block_spec_far_pair_at p6 (second_base + double_block) (second_base + 2 * double_block) k zeta8 zeta9); smt().
    have Hpaireq8_6 :
        radix2_32_pair_at p6 (second_base + 2 * double_block) zeta9 k =
        radix2_32_pair_at p5 (second_base + 2 * double_block) zeta9 k.
    + rewrite /p6.
      by apply (radix2_32_block_spec_far_pair_at p5 second_base (second_base + 2 * double_block) k zeta7 zeta9); smt().
    have Hpaireq8_5 :
        radix2_32_pair_at p5 (second_base + 2 * double_block) zeta9 k =
        radix2_32_pair_at p4 (second_base + 2 * double_block) zeta9 k.
    + rewrite /p5.
      by apply (radix2_32_block_spec_far_pair_at p4 (5 * double_block) (second_base + 2 * double_block) k zeta6 zeta9); smt().
    have Hpaireq8_4 :
        radix2_32_pair_at p4 (second_base + 2 * double_block) zeta9 k =
        radix2_32_pair_at p3 (second_base + 2 * double_block) zeta9 k.
    + rewrite /p4.
      by apply (radix2_32_block_spec_far_pair_at p3 (4 * double_block) (second_base + 2 * double_block) k zeta5 zeta9); smt().
    have Hpaireq8_3 :
        radix2_32_pair_at p3 (second_base + 2 * double_block) zeta9 k =
        radix2_32_pair_at p2 (second_base + 2 * double_block) zeta9 k.
    + rewrite /p3.
      by apply (radix2_32_block_spec_far_pair_at p2 (3 * double_block) (second_base + 2 * double_block) k zeta4 zeta9); smt().
    have Hpaireq8_2 :
        radix2_32_pair_at p2 (second_base + 2 * double_block) zeta9 k =
        radix2_32_pair_at p1 (second_base + 2 * double_block) zeta9 k.
    + rewrite /p2.
      by apply (radix2_32_block_spec_far_pair_at p1 (2 * double_block) (second_base + 2 * double_block) k zeta3 zeta9); smt().
    have Hpaireq8_1 :
        radix2_32_pair_at p1 (second_base + 2 * double_block) zeta9 k =
        radix2_32_pair_at p0 (second_base + 2 * double_block) zeta9 k.
    + rewrite /p1.
      by apply (radix2_32_block_spec_far_pair_at p0 double_block (second_base + 2 * double_block) k zeta2 zeta9); smt().
    have Hpaireq8_0 :
        radix2_32_pair_at p0 (second_base + 2 * double_block) zeta9 k =
        radix2_32_pair_at p (second_base + 2 * double_block) zeta9 k.
    + rewrite /p0.
      by apply (radix2_32_block_spec_far_pair_at p 0 (second_base + 2 * double_block) k zeta1 zeta9); smt().
    have Hout :
        (radix2_32_block_spec p10 (second_base + 5 * double_block) zeta12).[j] =
        (radix2_32_pair_at p (second_base + 2 * double_block) zeta9 k).`2.
    +
      rewrite (radix2_32_block_spec_before p10 (second_base + 5 * double_block) j zeta12 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p9 (second_base + 4 * double_block) j zeta11 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p8 (second_base + 3 * double_block) j zeta10 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_get1_valid p7 (second_base + 2 * double_block) k zeta9 Hvalid8 Hk).
      by rewrite Hpaireq8_7 Hpaireq8_6 Hpaireq8_5 Hpaireq8_4 Hpaireq8_3 Hpaireq8_2 Hpaireq8_1 Hpaireq8_0.
    move: Hpair.
    rewrite /k Hout /radix2_32_pair_at /radix2_32_pair_math_at /radix2_32_pair_math /=.
    move=> [Hr0 [Hr1 [Hc0 Hc1]]].
    split; first exact Hr1.
    exact Hc1.
  case (j < (second_base + 3 * double_block) + block) => Hj18.
  + pose k := j - (second_base + 3 * double_block).
    have Hk : 0 <= k < block by rewrite /k /block /double_block /second_base; smt().
    have Hlo : -q <= coeff p.[j] < q
      by apply (radix2_64_output_shape_qrange p j Hshape); smt().
    have Hhi : -q <= coeff p.[j + block] < q
      by apply (radix2_64_output_shape_qrange p (j + block) Hshape); smt().
    have Hpair := radix2_32_pair_algebra 1 zeta10 p.[j] p.[j + block]
      radix2_32_zeta10_root _ Hlo Hhi
      radix2_32_zeta10_in_qrange radix2_32_zeta10_montgomery_meaning; first smt().
    have Hpaireq9_8 :
        radix2_32_pair_at p8 (second_base + 3 * double_block) zeta10 k =
        radix2_32_pair_at p7 (second_base + 3 * double_block) zeta10 k.
    + rewrite /p8.
      by apply (radix2_32_block_spec_far_pair_at p7 (second_base + 2 * double_block) (second_base + 3 * double_block) k zeta9 zeta10); smt().
    have Hpaireq9_7 :
        radix2_32_pair_at p7 (second_base + 3 * double_block) zeta10 k =
        radix2_32_pair_at p6 (second_base + 3 * double_block) zeta10 k.
    + rewrite /p7.
      by apply (radix2_32_block_spec_far_pair_at p6 (second_base + double_block) (second_base + 3 * double_block) k zeta8 zeta10); smt().
    have Hpaireq9_6 :
        radix2_32_pair_at p6 (second_base + 3 * double_block) zeta10 k =
        radix2_32_pair_at p5 (second_base + 3 * double_block) zeta10 k.
    + rewrite /p6.
      by apply (radix2_32_block_spec_far_pair_at p5 second_base (second_base + 3 * double_block) k zeta7 zeta10); smt().
    have Hpaireq9_5 :
        radix2_32_pair_at p5 (second_base + 3 * double_block) zeta10 k =
        radix2_32_pair_at p4 (second_base + 3 * double_block) zeta10 k.
    + rewrite /p5.
      by apply (radix2_32_block_spec_far_pair_at p4 (5 * double_block) (second_base + 3 * double_block) k zeta6 zeta10); smt().
    have Hpaireq9_4 :
        radix2_32_pair_at p4 (second_base + 3 * double_block) zeta10 k =
        radix2_32_pair_at p3 (second_base + 3 * double_block) zeta10 k.
    + rewrite /p4.
      by apply (radix2_32_block_spec_far_pair_at p3 (4 * double_block) (second_base + 3 * double_block) k zeta5 zeta10); smt().
    have Hpaireq9_3 :
        radix2_32_pair_at p3 (second_base + 3 * double_block) zeta10 k =
        radix2_32_pair_at p2 (second_base + 3 * double_block) zeta10 k.
    + rewrite /p3.
      by apply (radix2_32_block_spec_far_pair_at p2 (3 * double_block) (second_base + 3 * double_block) k zeta4 zeta10); smt().
    have Hpaireq9_2 :
        radix2_32_pair_at p2 (second_base + 3 * double_block) zeta10 k =
        radix2_32_pair_at p1 (second_base + 3 * double_block) zeta10 k.
    + rewrite /p2.
      by apply (radix2_32_block_spec_far_pair_at p1 (2 * double_block) (second_base + 3 * double_block) k zeta3 zeta10); smt().
    have Hpaireq9_1 :
        radix2_32_pair_at p1 (second_base + 3 * double_block) zeta10 k =
        radix2_32_pair_at p0 (second_base + 3 * double_block) zeta10 k.
    + rewrite /p1.
      by apply (radix2_32_block_spec_far_pair_at p0 double_block (second_base + 3 * double_block) k zeta2 zeta10); smt().
    have Hpaireq9_0 :
        radix2_32_pair_at p0 (second_base + 3 * double_block) zeta10 k =
        radix2_32_pair_at p (second_base + 3 * double_block) zeta10 k.
    + rewrite /p0.
      by apply (radix2_32_block_spec_far_pair_at p 0 (second_base + 3 * double_block) k zeta1 zeta10); smt().
    have Hout :
        (radix2_32_block_spec p10 (second_base + 5 * double_block) zeta12).[j] =
        (radix2_32_pair_at p (second_base + 3 * double_block) zeta10 k).`1.
    +
      rewrite (radix2_32_block_spec_before p10 (second_base + 5 * double_block) j zeta12 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p9 (second_base + 4 * double_block) j zeta11 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_get0_valid p8 (second_base + 3 * double_block) k zeta10 Hvalid9 Hk).
      by rewrite Hpaireq9_8 Hpaireq9_7 Hpaireq9_6 Hpaireq9_5 Hpaireq9_4 Hpaireq9_3 Hpaireq9_2 Hpaireq9_1 Hpaireq9_0.
    move: Hpair.
    rewrite /k Hout /radix2_32_pair_at /radix2_32_pair_math_at /radix2_32_pair_math /=.
    move=> [Hr0 [Hr1 [Hc0 Hc1]]].
    split; first exact Hr0.
    exact Hc0.
  case (j < (second_base + 3 * double_block) + double_block) => Hj19.
  + pose k := j - (second_base + 3 * double_block) - block.
    have Hk : 0 <= k < block by rewrite /k /block /double_block /second_base; smt().
    have Hlo : -q <= coeff p.[j - block] < q
      by apply (radix2_64_output_shape_qrange p (j - block) Hshape); smt().
    have Hhi : -q <= coeff p.[j] < q
      by apply (radix2_64_output_shape_qrange p j Hshape); smt().
    have Hpair := radix2_32_pair_algebra 1 zeta10 p.[j - block] p.[j]
      radix2_32_zeta10_root _ Hlo Hhi
      radix2_32_zeta10_in_qrange radix2_32_zeta10_montgomery_meaning; first smt().
    have Hpaireq9_8 :
        radix2_32_pair_at p8 (second_base + 3 * double_block) zeta10 k =
        radix2_32_pair_at p7 (second_base + 3 * double_block) zeta10 k.
    + rewrite /p8.
      by apply (radix2_32_block_spec_far_pair_at p7 (second_base + 2 * double_block) (second_base + 3 * double_block) k zeta9 zeta10); smt().
    have Hpaireq9_7 :
        radix2_32_pair_at p7 (second_base + 3 * double_block) zeta10 k =
        radix2_32_pair_at p6 (second_base + 3 * double_block) zeta10 k.
    + rewrite /p7.
      by apply (radix2_32_block_spec_far_pair_at p6 (second_base + double_block) (second_base + 3 * double_block) k zeta8 zeta10); smt().
    have Hpaireq9_6 :
        radix2_32_pair_at p6 (second_base + 3 * double_block) zeta10 k =
        radix2_32_pair_at p5 (second_base + 3 * double_block) zeta10 k.
    + rewrite /p6.
      by apply (radix2_32_block_spec_far_pair_at p5 second_base (second_base + 3 * double_block) k zeta7 zeta10); smt().
    have Hpaireq9_5 :
        radix2_32_pair_at p5 (second_base + 3 * double_block) zeta10 k =
        radix2_32_pair_at p4 (second_base + 3 * double_block) zeta10 k.
    + rewrite /p5.
      by apply (radix2_32_block_spec_far_pair_at p4 (5 * double_block) (second_base + 3 * double_block) k zeta6 zeta10); smt().
    have Hpaireq9_4 :
        radix2_32_pair_at p4 (second_base + 3 * double_block) zeta10 k =
        radix2_32_pair_at p3 (second_base + 3 * double_block) zeta10 k.
    + rewrite /p4.
      by apply (radix2_32_block_spec_far_pair_at p3 (4 * double_block) (second_base + 3 * double_block) k zeta5 zeta10); smt().
    have Hpaireq9_3 :
        radix2_32_pair_at p3 (second_base + 3 * double_block) zeta10 k =
        radix2_32_pair_at p2 (second_base + 3 * double_block) zeta10 k.
    + rewrite /p3.
      by apply (radix2_32_block_spec_far_pair_at p2 (3 * double_block) (second_base + 3 * double_block) k zeta4 zeta10); smt().
    have Hpaireq9_2 :
        radix2_32_pair_at p2 (second_base + 3 * double_block) zeta10 k =
        radix2_32_pair_at p1 (second_base + 3 * double_block) zeta10 k.
    + rewrite /p2.
      by apply (radix2_32_block_spec_far_pair_at p1 (2 * double_block) (second_base + 3 * double_block) k zeta3 zeta10); smt().
    have Hpaireq9_1 :
        radix2_32_pair_at p1 (second_base + 3 * double_block) zeta10 k =
        radix2_32_pair_at p0 (second_base + 3 * double_block) zeta10 k.
    + rewrite /p1.
      by apply (radix2_32_block_spec_far_pair_at p0 double_block (second_base + 3 * double_block) k zeta2 zeta10); smt().
    have Hpaireq9_0 :
        radix2_32_pair_at p0 (second_base + 3 * double_block) zeta10 k =
        radix2_32_pair_at p (second_base + 3 * double_block) zeta10 k.
    + rewrite /p0.
      by apply (radix2_32_block_spec_far_pair_at p 0 (second_base + 3 * double_block) k zeta1 zeta10); smt().
    have Hout :
        (radix2_32_block_spec p10 (second_base + 5 * double_block) zeta12).[j] =
        (radix2_32_pair_at p (second_base + 3 * double_block) zeta10 k).`2.
    +
      rewrite (radix2_32_block_spec_before p10 (second_base + 5 * double_block) j zeta12 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_before p9 (second_base + 4 * double_block) j zeta11 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_get1_valid p8 (second_base + 3 * double_block) k zeta10 Hvalid9 Hk).
      by rewrite Hpaireq9_8 Hpaireq9_7 Hpaireq9_6 Hpaireq9_5 Hpaireq9_4 Hpaireq9_3 Hpaireq9_2 Hpaireq9_1 Hpaireq9_0.
    move: Hpair.
    rewrite /k Hout /radix2_32_pair_at /radix2_32_pair_math_at /radix2_32_pair_math /=.
    move=> [Hr0 [Hr1 [Hc0 Hc1]]].
    split; first exact Hr1.
    exact Hc1.
  case (j < (second_base + 4 * double_block) + block) => Hj20.
  + pose k := j - (second_base + 4 * double_block).
    have Hk : 0 <= k < block by rewrite /k /block /double_block /second_base; smt().
    have Hlo : -q <= coeff p.[j] < q
      by apply (radix2_64_output_shape_qrange p j Hshape); smt().
    have Hhi : -q <= coeff p.[j + block] < q
      by apply (radix2_64_output_shape_qrange p (j + block) Hshape); smt().
    have Hpair := radix2_32_pair_algebra 1 zeta11 p.[j] p.[j + block]
      radix2_32_zeta11_root _ Hlo Hhi
      radix2_32_zeta11_in_qrange radix2_32_zeta11_montgomery_meaning; first smt().
    have Hpaireq10_9 :
        radix2_32_pair_at p9 (second_base + 4 * double_block) zeta11 k =
        radix2_32_pair_at p8 (second_base + 4 * double_block) zeta11 k.
    + rewrite /p9.
      by apply (radix2_32_block_spec_far_pair_at p8 (second_base + 3 * double_block) (second_base + 4 * double_block) k zeta10 zeta11); smt().
    have Hpaireq10_8 :
        radix2_32_pair_at p8 (second_base + 4 * double_block) zeta11 k =
        radix2_32_pair_at p7 (second_base + 4 * double_block) zeta11 k.
    + rewrite /p8.
      by apply (radix2_32_block_spec_far_pair_at p7 (second_base + 2 * double_block) (second_base + 4 * double_block) k zeta9 zeta11); smt().
    have Hpaireq10_7 :
        radix2_32_pair_at p7 (second_base + 4 * double_block) zeta11 k =
        radix2_32_pair_at p6 (second_base + 4 * double_block) zeta11 k.
    + rewrite /p7.
      by apply (radix2_32_block_spec_far_pair_at p6 (second_base + double_block) (second_base + 4 * double_block) k zeta8 zeta11); smt().
    have Hpaireq10_6 :
        radix2_32_pair_at p6 (second_base + 4 * double_block) zeta11 k =
        radix2_32_pair_at p5 (second_base + 4 * double_block) zeta11 k.
    + rewrite /p6.
      by apply (radix2_32_block_spec_far_pair_at p5 second_base (second_base + 4 * double_block) k zeta7 zeta11); smt().
    have Hpaireq10_5 :
        radix2_32_pair_at p5 (second_base + 4 * double_block) zeta11 k =
        radix2_32_pair_at p4 (second_base + 4 * double_block) zeta11 k.
    + rewrite /p5.
      by apply (radix2_32_block_spec_far_pair_at p4 (5 * double_block) (second_base + 4 * double_block) k zeta6 zeta11); smt().
    have Hpaireq10_4 :
        radix2_32_pair_at p4 (second_base + 4 * double_block) zeta11 k =
        radix2_32_pair_at p3 (second_base + 4 * double_block) zeta11 k.
    + rewrite /p4.
      by apply (radix2_32_block_spec_far_pair_at p3 (4 * double_block) (second_base + 4 * double_block) k zeta5 zeta11); smt().
    have Hpaireq10_3 :
        radix2_32_pair_at p3 (second_base + 4 * double_block) zeta11 k =
        radix2_32_pair_at p2 (second_base + 4 * double_block) zeta11 k.
    + rewrite /p3.
      by apply (radix2_32_block_spec_far_pair_at p2 (3 * double_block) (second_base + 4 * double_block) k zeta4 zeta11); smt().
    have Hpaireq10_2 :
        radix2_32_pair_at p2 (second_base + 4 * double_block) zeta11 k =
        radix2_32_pair_at p1 (second_base + 4 * double_block) zeta11 k.
    + rewrite /p2.
      by apply (radix2_32_block_spec_far_pair_at p1 (2 * double_block) (second_base + 4 * double_block) k zeta3 zeta11); smt().
    have Hpaireq10_1 :
        radix2_32_pair_at p1 (second_base + 4 * double_block) zeta11 k =
        radix2_32_pair_at p0 (second_base + 4 * double_block) zeta11 k.
    + rewrite /p1.
      by apply (radix2_32_block_spec_far_pair_at p0 double_block (second_base + 4 * double_block) k zeta2 zeta11); smt().
    have Hpaireq10_0 :
        radix2_32_pair_at p0 (second_base + 4 * double_block) zeta11 k =
        radix2_32_pair_at p (second_base + 4 * double_block) zeta11 k.
    + rewrite /p0.
      by apply (radix2_32_block_spec_far_pair_at p 0 (second_base + 4 * double_block) k zeta1 zeta11); smt().
    have Hout :
        (radix2_32_block_spec p10 (second_base + 5 * double_block) zeta12).[j] =
        (radix2_32_pair_at p (second_base + 4 * double_block) zeta11 k).`1.
    +
      rewrite (radix2_32_block_spec_before p10 (second_base + 5 * double_block) j zeta12 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_get0_valid p9 (second_base + 4 * double_block) k zeta11 Hvalid10 Hk).
      by rewrite Hpaireq10_9 Hpaireq10_8 Hpaireq10_7 Hpaireq10_6 Hpaireq10_5 Hpaireq10_4 Hpaireq10_3 Hpaireq10_2 Hpaireq10_1 Hpaireq10_0.
    move: Hpair.
    rewrite /k Hout /radix2_32_pair_at /radix2_32_pair_math_at /radix2_32_pair_math /=.
    move=> [Hr0 [Hr1 [Hc0 Hc1]]].
    split; first exact Hr0.
    exact Hc0.
  case (j < (second_base + 4 * double_block) + double_block) => Hj21.
  + pose k := j - (second_base + 4 * double_block) - block.
    have Hk : 0 <= k < block by rewrite /k /block /double_block /second_base; smt().
    have Hlo : -q <= coeff p.[j - block] < q
      by apply (radix2_64_output_shape_qrange p (j - block) Hshape); smt().
    have Hhi : -q <= coeff p.[j] < q
      by apply (radix2_64_output_shape_qrange p j Hshape); smt().
    have Hpair := radix2_32_pair_algebra 1 zeta11 p.[j - block] p.[j]
      radix2_32_zeta11_root _ Hlo Hhi
      radix2_32_zeta11_in_qrange radix2_32_zeta11_montgomery_meaning; first smt().
    have Hpaireq10_9 :
        radix2_32_pair_at p9 (second_base + 4 * double_block) zeta11 k =
        radix2_32_pair_at p8 (second_base + 4 * double_block) zeta11 k.
    + rewrite /p9.
      by apply (radix2_32_block_spec_far_pair_at p8 (second_base + 3 * double_block) (second_base + 4 * double_block) k zeta10 zeta11); smt().
    have Hpaireq10_8 :
        radix2_32_pair_at p8 (second_base + 4 * double_block) zeta11 k =
        radix2_32_pair_at p7 (second_base + 4 * double_block) zeta11 k.
    + rewrite /p8.
      by apply (radix2_32_block_spec_far_pair_at p7 (second_base + 2 * double_block) (second_base + 4 * double_block) k zeta9 zeta11); smt().
    have Hpaireq10_7 :
        radix2_32_pair_at p7 (second_base + 4 * double_block) zeta11 k =
        radix2_32_pair_at p6 (second_base + 4 * double_block) zeta11 k.
    + rewrite /p7.
      by apply (radix2_32_block_spec_far_pair_at p6 (second_base + double_block) (second_base + 4 * double_block) k zeta8 zeta11); smt().
    have Hpaireq10_6 :
        radix2_32_pair_at p6 (second_base + 4 * double_block) zeta11 k =
        radix2_32_pair_at p5 (second_base + 4 * double_block) zeta11 k.
    + rewrite /p6.
      by apply (radix2_32_block_spec_far_pair_at p5 second_base (second_base + 4 * double_block) k zeta7 zeta11); smt().
    have Hpaireq10_5 :
        radix2_32_pair_at p5 (second_base + 4 * double_block) zeta11 k =
        radix2_32_pair_at p4 (second_base + 4 * double_block) zeta11 k.
    + rewrite /p5.
      by apply (radix2_32_block_spec_far_pair_at p4 (5 * double_block) (second_base + 4 * double_block) k zeta6 zeta11); smt().
    have Hpaireq10_4 :
        radix2_32_pair_at p4 (second_base + 4 * double_block) zeta11 k =
        radix2_32_pair_at p3 (second_base + 4 * double_block) zeta11 k.
    + rewrite /p4.
      by apply (radix2_32_block_spec_far_pair_at p3 (4 * double_block) (second_base + 4 * double_block) k zeta5 zeta11); smt().
    have Hpaireq10_3 :
        radix2_32_pair_at p3 (second_base + 4 * double_block) zeta11 k =
        radix2_32_pair_at p2 (second_base + 4 * double_block) zeta11 k.
    + rewrite /p3.
      by apply (radix2_32_block_spec_far_pair_at p2 (3 * double_block) (second_base + 4 * double_block) k zeta4 zeta11); smt().
    have Hpaireq10_2 :
        radix2_32_pair_at p2 (second_base + 4 * double_block) zeta11 k =
        radix2_32_pair_at p1 (second_base + 4 * double_block) zeta11 k.
    + rewrite /p2.
      by apply (radix2_32_block_spec_far_pair_at p1 (2 * double_block) (second_base + 4 * double_block) k zeta3 zeta11); smt().
    have Hpaireq10_1 :
        radix2_32_pair_at p1 (second_base + 4 * double_block) zeta11 k =
        radix2_32_pair_at p0 (second_base + 4 * double_block) zeta11 k.
    + rewrite /p1.
      by apply (radix2_32_block_spec_far_pair_at p0 double_block (second_base + 4 * double_block) k zeta2 zeta11); smt().
    have Hpaireq10_0 :
        radix2_32_pair_at p0 (second_base + 4 * double_block) zeta11 k =
        radix2_32_pair_at p (second_base + 4 * double_block) zeta11 k.
    + rewrite /p0.
      by apply (radix2_32_block_spec_far_pair_at p 0 (second_base + 4 * double_block) k zeta1 zeta11); smt().
    have Hout :
        (radix2_32_block_spec p10 (second_base + 5 * double_block) zeta12).[j] =
        (radix2_32_pair_at p (second_base + 4 * double_block) zeta11 k).`2.
    +
      rewrite (radix2_32_block_spec_before p10 (second_base + 5 * double_block) j zeta12 Hj_range) 1:/#.
      rewrite (radix2_32_block_spec_get1_valid p9 (second_base + 4 * double_block) k zeta11 Hvalid10 Hk).
      by rewrite Hpaireq10_9 Hpaireq10_8 Hpaireq10_7 Hpaireq10_6 Hpaireq10_5 Hpaireq10_4 Hpaireq10_3 Hpaireq10_2 Hpaireq10_1 Hpaireq10_0.
    move: Hpair.
    rewrite /k Hout /radix2_32_pair_at /radix2_32_pair_math_at /radix2_32_pair_math /=.
    move=> [Hr0 [Hr1 [Hc0 Hc1]]].
    split; first exact Hr1.
    exact Hc1.
  case (j < (second_base + 5 * double_block) + block) => Hj22.
  + pose k := j - (second_base + 5 * double_block).
    have Hk : 0 <= k < block by rewrite /k /block /double_block /second_base; smt().
    have Hlo : -q <= coeff p.[j] < q
      by apply (radix2_64_output_shape_qrange p j Hshape); smt().
    have Hhi : -q <= coeff p.[j + block] < q
      by apply (radix2_64_output_shape_qrange p (j + block) Hshape); smt().
    have Hpair := radix2_32_pair_algebra 1 zeta12 p.[j] p.[j + block]
      radix2_32_zeta12_root _ Hlo Hhi
      radix2_32_zeta12_in_qrange radix2_32_zeta12_montgomery_meaning; first smt().
    have Hpaireq11_10 :
        radix2_32_pair_at p10 (second_base + 5 * double_block) zeta12 k =
        radix2_32_pair_at p9 (second_base + 5 * double_block) zeta12 k.
    + rewrite /p10.
      by apply (radix2_32_block_spec_far_pair_at p9 (second_base + 4 * double_block) (second_base + 5 * double_block) k zeta11 zeta12); smt().
    have Hpaireq11_9 :
        radix2_32_pair_at p9 (second_base + 5 * double_block) zeta12 k =
        radix2_32_pair_at p8 (second_base + 5 * double_block) zeta12 k.
    + rewrite /p9.
      by apply (radix2_32_block_spec_far_pair_at p8 (second_base + 3 * double_block) (second_base + 5 * double_block) k zeta10 zeta12); smt().
    have Hpaireq11_8 :
        radix2_32_pair_at p8 (second_base + 5 * double_block) zeta12 k =
        radix2_32_pair_at p7 (second_base + 5 * double_block) zeta12 k.
    + rewrite /p8.
      by apply (radix2_32_block_spec_far_pair_at p7 (second_base + 2 * double_block) (second_base + 5 * double_block) k zeta9 zeta12); smt().
    have Hpaireq11_7 :
        radix2_32_pair_at p7 (second_base + 5 * double_block) zeta12 k =
        radix2_32_pair_at p6 (second_base + 5 * double_block) zeta12 k.
    + rewrite /p7.
      by apply (radix2_32_block_spec_far_pair_at p6 (second_base + double_block) (second_base + 5 * double_block) k zeta8 zeta12); smt().
    have Hpaireq11_6 :
        radix2_32_pair_at p6 (second_base + 5 * double_block) zeta12 k =
        radix2_32_pair_at p5 (second_base + 5 * double_block) zeta12 k.
    + rewrite /p6.
      by apply (radix2_32_block_spec_far_pair_at p5 second_base (second_base + 5 * double_block) k zeta7 zeta12); smt().
    have Hpaireq11_5 :
        radix2_32_pair_at p5 (second_base + 5 * double_block) zeta12 k =
        radix2_32_pair_at p4 (second_base + 5 * double_block) zeta12 k.
    + rewrite /p5.
      by apply (radix2_32_block_spec_far_pair_at p4 (5 * double_block) (second_base + 5 * double_block) k zeta6 zeta12); smt().
    have Hpaireq11_4 :
        radix2_32_pair_at p4 (second_base + 5 * double_block) zeta12 k =
        radix2_32_pair_at p3 (second_base + 5 * double_block) zeta12 k.
    + rewrite /p4.
      by apply (radix2_32_block_spec_far_pair_at p3 (4 * double_block) (second_base + 5 * double_block) k zeta5 zeta12); smt().
    have Hpaireq11_3 :
        radix2_32_pair_at p3 (second_base + 5 * double_block) zeta12 k =
        radix2_32_pair_at p2 (second_base + 5 * double_block) zeta12 k.
    + rewrite /p3.
      by apply (radix2_32_block_spec_far_pair_at p2 (3 * double_block) (second_base + 5 * double_block) k zeta4 zeta12); smt().
    have Hpaireq11_2 :
        radix2_32_pair_at p2 (second_base + 5 * double_block) zeta12 k =
        radix2_32_pair_at p1 (second_base + 5 * double_block) zeta12 k.
    + rewrite /p2.
      by apply (radix2_32_block_spec_far_pair_at p1 (2 * double_block) (second_base + 5 * double_block) k zeta3 zeta12); smt().
    have Hpaireq11_1 :
        radix2_32_pair_at p1 (second_base + 5 * double_block) zeta12 k =
        radix2_32_pair_at p0 (second_base + 5 * double_block) zeta12 k.
    + rewrite /p1.
      by apply (radix2_32_block_spec_far_pair_at p0 double_block (second_base + 5 * double_block) k zeta2 zeta12); smt().
    have Hpaireq11_0 :
        radix2_32_pair_at p0 (second_base + 5 * double_block) zeta12 k =
        radix2_32_pair_at p (second_base + 5 * double_block) zeta12 k.
    + rewrite /p0.
      by apply (radix2_32_block_spec_far_pair_at p 0 (second_base + 5 * double_block) k zeta1 zeta12); smt().
    have Hout :
        (radix2_32_block_spec p10 (second_base + 5 * double_block) zeta12).[j] =
        (radix2_32_pair_at p (second_base + 5 * double_block) zeta12 k).`1.
    +
      rewrite (radix2_32_block_spec_get0_valid p10 (second_base + 5 * double_block) k zeta12 Hvalid11 Hk).
      by rewrite Hpaireq11_10 Hpaireq11_9 Hpaireq11_8 Hpaireq11_7 Hpaireq11_6 Hpaireq11_5 Hpaireq11_4 Hpaireq11_3 Hpaireq11_2 Hpaireq11_1 Hpaireq11_0.
    move: Hpair.
    rewrite /k Hout /radix2_32_pair_at /radix2_32_pair_math_at /radix2_32_pair_math /=.
    move=> [Hr0 [Hr1 [Hc0 Hc1]]].
    split; first exact Hr0.
    exact Hc0.
  case (j < (second_base + 5 * double_block) + double_block) => Hj23.
  + pose k := j - (second_base + 5 * double_block) - block.
    have Hk : 0 <= k < block by rewrite /k /block /double_block /second_base; smt().
    have Hlo : -q <= coeff p.[j - block] < q
      by apply (radix2_64_output_shape_qrange p (j - block) Hshape); smt().
    have Hhi : -q <= coeff p.[j] < q
      by apply (radix2_64_output_shape_qrange p j Hshape); smt().
    have Hpair := radix2_32_pair_algebra 1 zeta12 p.[j - block] p.[j]
      radix2_32_zeta12_root _ Hlo Hhi
      radix2_32_zeta12_in_qrange radix2_32_zeta12_montgomery_meaning; first smt().
    have Hpaireq11_10 :
        radix2_32_pair_at p10 (second_base + 5 * double_block) zeta12 k =
        radix2_32_pair_at p9 (second_base + 5 * double_block) zeta12 k.
    + rewrite /p10.
      by apply (radix2_32_block_spec_far_pair_at p9 (second_base + 4 * double_block) (second_base + 5 * double_block) k zeta11 zeta12); smt().
    have Hpaireq11_9 :
        radix2_32_pair_at p9 (second_base + 5 * double_block) zeta12 k =
        radix2_32_pair_at p8 (second_base + 5 * double_block) zeta12 k.
    + rewrite /p9.
      by apply (radix2_32_block_spec_far_pair_at p8 (second_base + 3 * double_block) (second_base + 5 * double_block) k zeta10 zeta12); smt().
    have Hpaireq11_8 :
        radix2_32_pair_at p8 (second_base + 5 * double_block) zeta12 k =
        radix2_32_pair_at p7 (second_base + 5 * double_block) zeta12 k.
    + rewrite /p8.
      by apply (radix2_32_block_spec_far_pair_at p7 (second_base + 2 * double_block) (second_base + 5 * double_block) k zeta9 zeta12); smt().
    have Hpaireq11_7 :
        radix2_32_pair_at p7 (second_base + 5 * double_block) zeta12 k =
        radix2_32_pair_at p6 (second_base + 5 * double_block) zeta12 k.
    + rewrite /p7.
      by apply (radix2_32_block_spec_far_pair_at p6 (second_base + double_block) (second_base + 5 * double_block) k zeta8 zeta12); smt().
    have Hpaireq11_6 :
        radix2_32_pair_at p6 (second_base + 5 * double_block) zeta12 k =
        radix2_32_pair_at p5 (second_base + 5 * double_block) zeta12 k.
    + rewrite /p6.
      by apply (radix2_32_block_spec_far_pair_at p5 second_base (second_base + 5 * double_block) k zeta7 zeta12); smt().
    have Hpaireq11_5 :
        radix2_32_pair_at p5 (second_base + 5 * double_block) zeta12 k =
        radix2_32_pair_at p4 (second_base + 5 * double_block) zeta12 k.
    + rewrite /p5.
      by apply (radix2_32_block_spec_far_pair_at p4 (5 * double_block) (second_base + 5 * double_block) k zeta6 zeta12); smt().
    have Hpaireq11_4 :
        radix2_32_pair_at p4 (second_base + 5 * double_block) zeta12 k =
        radix2_32_pair_at p3 (second_base + 5 * double_block) zeta12 k.
    + rewrite /p4.
      by apply (radix2_32_block_spec_far_pair_at p3 (4 * double_block) (second_base + 5 * double_block) k zeta5 zeta12); smt().
    have Hpaireq11_3 :
        radix2_32_pair_at p3 (second_base + 5 * double_block) zeta12 k =
        radix2_32_pair_at p2 (second_base + 5 * double_block) zeta12 k.
    + rewrite /p3.
      by apply (radix2_32_block_spec_far_pair_at p2 (3 * double_block) (second_base + 5 * double_block) k zeta4 zeta12); smt().
    have Hpaireq11_2 :
        radix2_32_pair_at p2 (second_base + 5 * double_block) zeta12 k =
        radix2_32_pair_at p1 (second_base + 5 * double_block) zeta12 k.
    + rewrite /p2.
      by apply (radix2_32_block_spec_far_pair_at p1 (2 * double_block) (second_base + 5 * double_block) k zeta3 zeta12); smt().
    have Hpaireq11_1 :
        radix2_32_pair_at p1 (second_base + 5 * double_block) zeta12 k =
        radix2_32_pair_at p0 (second_base + 5 * double_block) zeta12 k.
    + rewrite /p1.
      by apply (radix2_32_block_spec_far_pair_at p0 double_block (second_base + 5 * double_block) k zeta2 zeta12); smt().
    have Hpaireq11_0 :
        radix2_32_pair_at p0 (second_base + 5 * double_block) zeta12 k =
        radix2_32_pair_at p (second_base + 5 * double_block) zeta12 k.
    + rewrite /p0.
      by apply (radix2_32_block_spec_far_pair_at p 0 (second_base + 5 * double_block) k zeta1 zeta12); smt().
    have Hout :
        (radix2_32_block_spec p10 (second_base + 5 * double_block) zeta12).[j] =
        (radix2_32_pair_at p (second_base + 5 * double_block) zeta12 k).`2.
    +
      rewrite (radix2_32_block_spec_get1_valid p10 (second_base + 5 * double_block) k zeta12 Hvalid11 Hk).
      by rewrite Hpaireq11_10 Hpaireq11_9 Hpaireq11_8 Hpaireq11_7 Hpaireq11_6 Hpaireq11_5 Hpaireq11_4 Hpaireq11_3 Hpaireq11_2 Hpaireq11_1 Hpaireq11_0.
    move: Hpair.
    rewrite /k Hout /radix2_32_pair_at /radix2_32_pair_math_at /radix2_32_pair_math /=.
    move=> [Hr0 [Hr1 [Hc0 Hc1]]].
    split; first exact Hr1.
    exact Hc1.
  smt().
qed.

lemma ntt_radix2_32_algebra_functional
    (rp0 : W16.t Array768.t) :
  radix2_64_output_shape rp0 =>
  hoare [NTRUPlus768NTTRadix2_32.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_32 :
    rp = rp0 ==> radix2_32_algebra rp0 res].
proof.
  move=> Hshape.
  conseq (ntt_radix2_32_functional rp0) => />.
  exact (radix2_32_spec_algebra rp0 Hshape).
qed.

lemma ntt_radix2_32_correct_algebra
    (rp0 : W16.t Array768.t) :
  radix2_64_output_shape rp0 =>
  phoare [NTRUPlus768NTTRadix2_32.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_32 :
    rp = rp0 ==> radix2_32_algebra rp0 res] = 1%r.
proof.
  move=> Hshape.
  have Hfunctional := ntt_radix2_32_algebra_functional rp0 Hshape.
  by conseq ntt_radix2_32_lossless Hfunctional.
qed.
