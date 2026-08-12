require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord JModel_x86.

require import JWord_extra W16extra.
require import Array768.
require import NTRUPlus768NTTRadix2_64Proof.
require import NTRUPlus768BasemulProof.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768NTTSchedule.

import Ring.IntID IntOrder.

op second_base : int = 384.

op radix2_64_zeta1_root : int = (zeta_root ^ 16) %% q.
op radix2_64_zeta2_root : int = (zeta_root ^ 112) %% q.
op radix2_64_zeta3_root : int = (zeta_root ^ 208) %% q.
op radix2_64_zeta4_root : int = (zeta_root ^ 80) %% q.
op radix2_64_zeta5_root : int = (zeta_root ^ 176) %% q.
op radix2_64_zeta6_root : int = (zeta_root ^ 272) %% q.

op radix3_output_shape (p : W16.t Array768.t) : bool =
  forall j, 0 <= j < 768 =>
    if j < second_base then -4 * q <= coeff p.[j] < 4 * q
    else -5 * q <= coeff p.[j] < 5 * q.

op radix2_64_pair_math (lo hi root : int) : int * int =
  (lo + hi * root, lo - hi * root).

op radix2_64_pair_math_at
    (p : W16.t Array768.t) (base : int) (root : int) (k : int)
    : int * int =
  radix2_64_pair_math
    (coeff p.[base + k])
    (coeff p.[base + k + block])
    root.

op radix2_64_math (p : W16.t Array768.t) (j : int) : int =
  if j < block then
    (radix2_64_pair_math_at p 0 radix2_64_zeta1_root j).`1
  else if j < 2 * block then
    (radix2_64_pair_math_at p 0 radix2_64_zeta1_root (j - block)).`2
  else if j < 3 * block then
    (radix2_64_pair_math_at p double_block radix2_64_zeta2_root
      (j - double_block)).`1
  else if j < 4 * block then
    (radix2_64_pair_math_at p double_block radix2_64_zeta2_root
      (j - double_block - block)).`2
  else if j < 5 * block then
    (radix2_64_pair_math_at p (2 * double_block) radix2_64_zeta3_root
      (j - 2 * double_block)).`1
  else if j < 6 * block then
    (radix2_64_pair_math_at p (2 * double_block) radix2_64_zeta3_root
      (j - (2 * double_block + block))).`2
  else if j < second_base + block then
    (radix2_64_pair_math_at p second_base radix2_64_zeta4_root
      (j - second_base)).`1
  else if j < second_base + double_block then
    (radix2_64_pair_math_at p second_base radix2_64_zeta4_root
      (j - second_base - block)).`2
  else if j < second_base + 3 * block then
    (radix2_64_pair_math_at p (second_base + double_block)
      radix2_64_zeta5_root (j - second_base - double_block)).`1
  else if j < 10 * block then
    (radix2_64_pair_math_at p (second_base + double_block)
      radix2_64_zeta5_root
      (j - second_base - double_block - block)).`2
  else if j < 11 * block then
    (radix2_64_pair_math_at p (second_base + 2 * double_block)
      radix2_64_zeta6_root (j - second_base - 2 * double_block)).`1
  else
    (radix2_64_pair_math_at p (second_base + 2 * double_block)
      radix2_64_zeta6_root
      (j - second_base - 2 * double_block - block)).`2.

op radix2_64_algebra (input output : W16.t Array768.t) : bool =
  forall j, 0 <= j < 768 =>
    -1728 <= coeff output.[j] <= 1728 /\
    coeff output.[j] %% q = radix2_64_math input j %% q.

op barrett_v : int = 19412.
op barrett_shift : int = 2 ^ 26.
op barrett_bias : int = 2 ^ 25.
op qhalf : int = q %/ 2.

op centered_quot (x : int) : int = (x + qhalf) %/ q.
op centered_rem (x : int) : int = x - centered_quot x * q.
op barrett_quot (x : int) : int = (barrett_v * x + barrett_bias) %/ barrett_shift.

lemma radix3_output_shape_before
    (p : W16.t Array768.t) (j : int) :
  radix3_output_shape p =>
  0 <= j < second_base =>
  -4 * q <= coeff p.[j] < 4 * q.
proof.
  move=> Hshape Hj.
  rewrite /radix3_output_shape in Hshape.
  have Hjshape := Hshape j _; first smt().
  by move: Hjshape; smt().
qed.

lemma radix3_output_shape_after
    (p : W16.t Array768.t) (j : int) :
  radix3_output_shape p =>
  second_base <= j < 768 =>
  -5 * q <= coeff p.[j] < 5 * q.
proof.
  move=> Hshape Hj.
  rewrite /radix3_output_shape in Hshape.
  have Hjshape := Hshape j _; first smt().
  by move: Hjshape; smt().
qed.

lemma radix2_64_zeta_schedule_indices :
  coeff zeta1 = zetas192_coeff 6 /\ zetas192_exp 6 = 16 /\
  coeff zeta2 = zetas192_coeff 7 /\ zetas192_exp 7 = 112 /\
  coeff zeta3 = zetas192_coeff 8 /\ zetas192_exp 8 = 208 /\
  coeff zeta4 = zetas192_coeff 9 /\ zetas192_exp 9 = 80 /\
  coeff zeta5 = zetas192_coeff 10 /\ zetas192_exp 10 = 176 /\
  coeff zeta6 = zetas192_coeff 11 /\ zetas192_exp 11 = 272.
proof.
  rewrite /coeff /zeta1 /zeta2 /zeta3 /zeta4 /zeta5 /zeta6.
  rewrite /zetas192_coeff /zetas192_exp /zetas192_coeffs /zetas192_exponents /=.
  rewrite !W16.of_sintK !/W16.smod /=.
  done.
qed.

lemma radix2_64_zeta1_in_qrange : in_qrange zeta1.
proof.
  rewrite /in_qrange /coeff /zeta1 W16.of_sintK /W16.smod /q /=.
  done.
qed.

lemma radix2_64_zeta2_in_qrange : in_qrange zeta2.
proof.
  rewrite /in_qrange /coeff /zeta2 W16.of_sintK /W16.smod /q /=.
  done.
qed.

lemma radix2_64_zeta3_in_qrange : in_qrange zeta3.
proof.
  rewrite /in_qrange /coeff /zeta3 W16.of_sintK /W16.smod /q /=.
  done.
qed.

lemma radix2_64_zeta4_in_qrange : in_qrange zeta4.
proof.
  rewrite /in_qrange /coeff /zeta4 W16.of_sintK /W16.smod /q /=.
  done.
qed.

lemma radix2_64_zeta5_in_qrange : in_qrange zeta5.
proof.
  rewrite /in_qrange /coeff /zeta5 W16.of_sintK /W16.smod /q /=.
  done.
qed.

lemma radix2_64_zeta6_in_qrange : in_qrange zeta6.
proof.
  rewrite /in_qrange /coeff /zeta6 W16.of_sintK /W16.smod /q /=.
  done.
qed.

lemma radix2_64_zeta1_montgomery_meaning :
  (coeff zeta1 * Rinv) %% q = radix2_64_zeta1_root.
proof.
  have Hschedule := zetas192_relation 6 _; first smt().
  move: Hschedule.
  rewrite /decode_mont /radix2_64_zeta1_root /zetas192_coeff /zetas192_exp.
  rewrite /zetas192_coeffs /zetas192_exponents /coeff /zeta1 /=.
  rewrite W16.of_sintK /W16.smod /=.
  done.
qed.

lemma radix2_64_zeta2_montgomery_meaning :
  (coeff zeta2 * Rinv) %% q = radix2_64_zeta2_root.
proof.
  have Hschedule := zetas192_relation 7 _; first smt().
  move: Hschedule.
  rewrite /decode_mont /radix2_64_zeta2_root /zetas192_coeff /zetas192_exp.
  rewrite /zetas192_coeffs /zetas192_exponents /coeff /zeta2 /=.
  rewrite W16.of_sintK /W16.smod /=.
  done.
qed.

lemma radix2_64_zeta3_montgomery_meaning :
  (coeff zeta3 * Rinv) %% q = radix2_64_zeta3_root.
proof.
  have Hschedule := zetas192_relation 8 _; first smt().
  move: Hschedule.
  rewrite /decode_mont /radix2_64_zeta3_root /zetas192_coeff /zetas192_exp.
  rewrite /zetas192_coeffs /zetas192_exponents /coeff /zeta3 /=.
  rewrite W16.of_sintK /W16.smod /=.
  done.
qed.

lemma radix2_64_zeta4_montgomery_meaning :
  (coeff zeta4 * Rinv) %% q = radix2_64_zeta4_root.
proof.
  have Hschedule := zetas192_relation 9 _; first smt().
  move: Hschedule.
  rewrite /decode_mont /radix2_64_zeta4_root /zetas192_coeff /zetas192_exp.
  rewrite /zetas192_coeffs /zetas192_exponents /coeff /zeta4 /=.
  rewrite W16.of_sintK /W16.smod /=.
  done.
qed.

lemma radix2_64_zeta5_montgomery_meaning :
  (coeff zeta5 * Rinv) %% q = radix2_64_zeta5_root.
proof.
  have Hschedule := zetas192_relation 10 _; first smt().
  move: Hschedule.
  rewrite /decode_mont /radix2_64_zeta5_root /zetas192_coeff /zetas192_exp.
  rewrite /zetas192_coeffs /zetas192_exponents /coeff /zeta5 /=.
  rewrite W16.of_sintK /W16.smod /=.
  done.
qed.

lemma radix2_64_zeta6_montgomery_meaning :
  (coeff zeta6 * Rinv) %% q = radix2_64_zeta6_root.
proof.
  have Hschedule := zetas192_relation 11 _; first smt().
  move: Hschedule.
  rewrite /decode_mont /radix2_64_zeta6_root /zetas192_coeff /zetas192_exp.
  rewrite /zetas192_coeffs /zetas192_exponents /coeff /zeta6 /=.
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

lemma radix2_64_mul_algebra (z a : W16.t) (root m : int) :
  0 < m <= 5 =>
  in_qrange z =>
  -m * q <= coeff a < m * q =>
  (coeff z * Rinv) %% q = root =>
  -q <= coeff (radix2_64_mul z a) < q /\
  coeff (radix2_64_mul z a) %% q = (coeff a * root) %% q.
proof.
  move=> Hm Hz Ha Hroot.
  have Hproduct := scaled_product_bound m (coeff z) (coeff a) Hm Hz Ha.
  have Hreduce := montgomery_reduce_of_int (coeff z * coeff a) Hproduct.
  have Hmul : mul_i16 z a = W32.of_int (coeff z * coeff a) by apply mul_i16E.
  have Ht : radix2_64_mul z a = montgomery_reduce
      (W32.of_int (coeff z * coeff a))
    by rewrite /radix2_64_mul Hmul.
  have [Hrange Hcongr] := Hreduce.
  split; first by rewrite Ht.
  have Hcongr' :
      coeff (radix2_64_mul z a) %% q =
      (coeff z * coeff a * Rinv) %% q.
  + rewrite /radix2_64_mul Hmul.
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
  apply radix2_64_modz_sub_dvd.
  apply/dvdzE.
  apply dvdz_mull.
  exact (dvdzz q).
qed.

lemma radix2_64_pair_algebra
    (m : int) (z lo hi : W16.t) (root : int) :
  0 < m <= 5 =>
  -m * q <= coeff lo < m * q =>
  -m * q <= coeff hi < m * q =>
  in_qrange z =>
  (coeff z * Rinv) %% q = root =>
  let out = radix2_64_pair z lo hi in
    -1728 <= coeff out.`1 <= 1728 /\
    -1728 <= coeff out.`2 <= 1728 /\
    coeff out.`1 %% q = (coeff lo + coeff hi * root) %% q /\
    coeff out.`2 %% q = (coeff lo - coeff hi * root) %% q.
proof.
  move=> Hm Hlo Hhi Hz Hroot out.
  pose t := radix2_64_mul z hi.
  have Ht := radix2_64_mul_algebra z hi root m Hm Hz Hhi Hroot.
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
  rewrite /out /radix2_64_pair /t /=.
  move=> [Hsum_eq [Hsum_rng Hsum_mod]] [Hdiff_eq [Hdiff_rng Hdiff_mod]].
  split; first exact Hsum_rng.
  split; first exact Hdiff_rng.
  split.
  + rewrite Hsum_mod Hsum_congr.
    done.
  rewrite Hdiff_mod Hdiff_congr.
  done.
qed.

lemma radix2_64_block_spec_far
    (p : W16.t Array768.t) (base j : int) (z : W16.t) :
  0 <= j < 768 =>
  j < base \/ base + double_block <= j =>
  (radix2_64_block_spec p base z).[j] = p.[j].
proof.
  move=> Hj Hfar.
  rewrite /radix2_64_block_spec /radix2_64_prefix_spec Array768.initiE 1:Hj.
  smt().
qed.

lemma radix2_64_block_spec_before
    (p : W16.t Array768.t) (base j : int) (z : W16.t) :
  0 <= j < 768 =>
  j < base =>
  (radix2_64_block_spec p base z).[j] = p.[j].
proof.
  move=> Hj Hbefore.
  apply radix2_64_block_spec_far.
  + exact Hj.
  by left.
qed.

lemma radix2_64_block_spec_get0
    (p : W16.t Array768.t) (base k : int) (z : W16.t) :
  0 <= base =>
  base + double_block <= 768 =>
  0 <= k < block =>
  (radix2_64_block_spec p base z).[base + k] =
    (radix2_64_pair_at p base z k).`1.
proof.
  move=> Hbase Hbound Hk.
  rewrite /radix2_64_block_spec /radix2_64_prefix_spec Array768.initiE 1:/#.
  by rewrite /radix2_64_pair_at; smt().
qed.

lemma radix2_64_block_spec_get1
    (p : W16.t Array768.t) (base k : int) (z : W16.t) :
  0 <= base =>
  base + double_block <= 768 =>
  0 <= k < block =>
  (radix2_64_block_spec p base z).[base + block + k] =
    (radix2_64_pair_at p base z k).`2.
proof.
  move=> Hbase Hbound Hk.
  rewrite /radix2_64_block_spec /radix2_64_prefix_spec Array768.initiE 1:/#.
  by rewrite /radix2_64_pair_at; smt().
qed.

lemma radix2_64_block_spec_get0_valid
    (p : W16.t Array768.t) (base k : int) (z : W16.t) :
  valid_base base =>
  0 <= k < block =>
  (radix2_64_block_spec p base z).[base + k] =
    (radix2_64_pair_at p base z k).`1.
proof.
  move=> Hvalid Hk.
  have [Hbase Hbound] := valid_base_bounds base Hvalid.
  exact (radix2_64_block_spec_get0 p base k z Hbase Hbound Hk).
qed.

lemma radix2_64_block_spec_get1_valid
    (p : W16.t Array768.t) (base k : int) (z : W16.t) :
  valid_base base =>
  0 <= k < block =>
  (radix2_64_block_spec p base z).[base + block + k] =
    (radix2_64_pair_at p base z k).`2.
proof.
  move=> Hvalid Hk.
  have [Hbase Hbound] := valid_base_bounds base Hvalid.
  exact (radix2_64_block_spec_get1 p base k z Hbase Hbound Hk).
qed.

lemma radix2_64_block_spec_far_pair_at
    (p : W16.t Array768.t) (base1 base2 k : int) (z1 z2 : W16.t) :
  0 <= base1 =>
  base1 + double_block <= 768 =>
  0 <= base2 =>
  base2 + double_block <= 768 =>
  (base1 + double_block <= base2 \/ base2 + double_block <= base1) =>
  0 <= k < block =>
  radix2_64_pair_at (radix2_64_block_spec p base1 z1) base2 z2 k =
  radix2_64_pair_at p base2 z2 k.
proof.
  move=> Hbase1 Hbound1 Hbase2 Hbound2 Hdisj Hk.
  rewrite /radix2_64_pair_at.
  congr.
  + apply radix2_64_block_spec_far.
    + smt().
    smt().
  apply radix2_64_block_spec_far.
  + smt().
  smt().
qed.

lemma radix2_64_spec_algebra (p : W16.t Array768.t) :
  radix3_output_shape p => radix2_64_algebra p (radix2_64_spec p).
proof.
  move=> Hshape j Hj.
  have HblockE : block = 64 by rewrite /block.
  have Hdouble_blockE : double_block = 128 by rewrite /double_block /block.
  have Hsecond_baseE : second_base = 384 by rewrite /second_base.
  have Hvalid0 : valid_base 0.
  + rewrite /valid_base /double_block /nblocks.
    exists 0; smt().
  have Hvalid1 : valid_base double_block.
  + rewrite /valid_base /double_block /nblocks.
    exists 1; smt().
  have Hvalid2 : valid_base (2 * double_block).
  + rewrite /valid_base /double_block /nblocks.
    exists 2; smt().
  have Hvalid3 : valid_base second_base.
  + rewrite /valid_base /second_base /double_block /nblocks.
    exists 3; smt().
  have Hvalid4 : valid_base (second_base + double_block).
  + rewrite /valid_base /second_base /double_block /nblocks.
    exists 4; smt().
  have Hvalid5 : valid_base (second_base + 2 * double_block).
  + rewrite /valid_base /second_base /double_block /nblocks.
    exists 5; smt().
  pose p0 := radix2_64_block_spec p 0 zeta1.
  pose p1 := radix2_64_block_spec p0 128 zeta2.
  pose p2 := radix2_64_block_spec p1 256 zeta3.
  pose p3 := radix2_64_block_spec p2 384 zeta4.
  pose p4 := radix2_64_block_spec p3 512 zeta5.
  rewrite /radix2_64_spec /radix2_64_algebra /radix2_64_math.
  case (j < block) => Hj0.
  + rewrite HblockE in Hj0.
    have Hlo : -4 * q <= coeff p.[j] < 4 * q
      by apply (radix3_output_shape_before p j Hshape); smt().
    have Hhi : -4 * q <= coeff p.[j + block] < 4 * q
      by apply (radix3_output_shape_before p (j + block) Hshape); smt().
    have Hpair := radix2_64_pair_algebra 4 zeta1 p.[j] p.[j + block]
      radix2_64_zeta1_root _ Hlo Hhi
      radix2_64_zeta1_in_qrange radix2_64_zeta1_montgomery_meaning; first smt().
    have Hout :
        (radix2_64_block_spec p4 640 zeta6).[j] =
        (radix2_64_pair_at p 0 zeta1 j).`1.
    + have Hfar640 : j < 640 \/ 640 + double_block <= j.
      + left.
        move: Hj0.
        smt().
      rewrite (radix2_64_block_spec_far p4 640 j zeta6 Hj Hfar640).
      rewrite (radix2_64_block_spec_before p3 512 j zeta5 Hj) 1:/#.
      rewrite (radix2_64_block_spec_before p2 384 j zeta4 Hj) 1:/#.
      rewrite (radix2_64_block_spec_before p1 256 j zeta3 Hj) 1:/#.
      rewrite (radix2_64_block_spec_before p0 128 j zeta2 Hj) 1:/#.
      by rewrite (radix2_64_block_spec_get0 p 0 j zeta1) 1:/# 2:/#.
    move: Hpair.
    rewrite Hout /radix2_64_pair_at /radix2_64_pair_math_at /radix2_64_pair_math /=.
    move=> [Hr0 [Hr1 [Hc0 Hc1]]].
    split; first exact Hr0.
    exact Hc0.
  case (j < 2 * block) => Hj1.
  + pose k := j - block.
    have Hk : 0 <= k < block by rewrite /k /block; smt().
    have Hlo : -4 * q <= coeff p.[k] < 4 * q
      by apply (radix3_output_shape_before p k Hshape); smt().
    have Hhi : -4 * q <= coeff p.[j] < 4 * q
      by apply (radix3_output_shape_before p j Hshape); smt().
    have Hpair := radix2_64_pair_algebra 4 zeta1 p.[k] p.[j]
      radix2_64_zeta1_root _ Hlo Hhi
      radix2_64_zeta1_in_qrange radix2_64_zeta1_montgomery_meaning; first smt().
    have Hout :
        (radix2_64_block_spec p4 640 zeta6).[j] =
        (radix2_64_pair_at p 0 zeta1 k).`2.
    + rewrite (radix2_64_block_spec_before p4 640 j zeta6 Hj) 1:/#.
      rewrite (radix2_64_block_spec_before p3 512 j zeta5 Hj) 1:/#.
      rewrite (radix2_64_block_spec_before p2 384 j zeta4 Hj) 1:/#.
      rewrite (radix2_64_block_spec_before p1 256 j zeta3 Hj) 1:/#.
      rewrite (radix2_64_block_spec_before p0 128 j zeta2 Hj) 1:/#.
      by rewrite (radix2_64_block_spec_get1_valid p 0 k zeta1 Hvalid0 Hk).
    move: Hpair.
    rewrite /k Hout /radix2_64_pair_at /radix2_64_pair_math_at /radix2_64_pair_math /=.
    move=> [Hr0 [Hr1 [Hc0 Hc1]]].
    split; first exact Hr1.
    exact Hc1.
  case (j < 3 * block) => Hj2.
  + pose k := j - double_block.
    have Hk : 0 <= k < block by rewrite /k /double_block /block; smt().
    have Hlo : -4 * q <= coeff p.[j] < 4 * q
      by apply (radix3_output_shape_before p j Hshape); smt().
    have Hhi : -4 * q <= coeff p.[j + block] < 4 * q
      by apply (radix3_output_shape_before p (j + block) Hshape); smt().
    have Hpair := radix2_64_pair_algebra 4 zeta2 p.[j] p.[j + block]
      radix2_64_zeta2_root _ Hlo Hhi
      radix2_64_zeta2_in_qrange radix2_64_zeta2_montgomery_meaning; first smt().
    have Hpaireq :
        radix2_64_pair_at p0 double_block zeta2 k =
        radix2_64_pair_at p double_block zeta2 k.
    + rewrite /p0.
      by apply (radix2_64_block_spec_far_pair_at p 0 double_block k zeta1 zeta2); smt().
    have Hout :
        (radix2_64_block_spec p4 640 zeta6).[j] =
        (radix2_64_pair_at p double_block zeta2 k).`1.
    + rewrite (radix2_64_block_spec_before p4 640 j zeta6 Hj) 1:/#.
      rewrite (radix2_64_block_spec_before p3 512 j zeta5 Hj) 1:/#.
      rewrite (radix2_64_block_spec_before p2 384 j zeta4 Hj) 1:/#.
      rewrite (radix2_64_block_spec_before p1 256 j zeta3 Hj) 1:/#.
      rewrite (radix2_64_block_spec_get0_valid
        p0 double_block k zeta2 Hvalid1 Hk).
      by rewrite Hpaireq.
    move: Hpair.
    rewrite /k Hout /radix2_64_pair_at /radix2_64_pair_math_at /radix2_64_pair_math /=.
    move=> [Hr0 [Hr1 [Hc0 Hc1]]].
    split; first exact Hr0.
    exact Hc0.
  case (j < 4 * block) => Hj3.
  + pose k := j - double_block - block.
    have Hk : 0 <= k < block by rewrite /k /double_block /block; smt().
    have Hlo : -4 * q <= coeff p.[j - block] < 4 * q
      by apply (radix3_output_shape_before p (j - block) Hshape); smt().
    have Hhi : -4 * q <= coeff p.[j] < 4 * q
      by apply (radix3_output_shape_before p j Hshape); smt().
    have Hpair := radix2_64_pair_algebra 4 zeta2 p.[j - block] p.[j]
      radix2_64_zeta2_root _ Hlo Hhi
      radix2_64_zeta2_in_qrange radix2_64_zeta2_montgomery_meaning; first smt().
    have Hpaireq :
        radix2_64_pair_at p0 double_block zeta2 k =
        radix2_64_pair_at p double_block zeta2 k.
    + rewrite /p0.
      by apply (radix2_64_block_spec_far_pair_at p 0 double_block k zeta1 zeta2); smt().
    have Hout :
        (radix2_64_block_spec p4 640 zeta6).[j] =
        (radix2_64_pair_at p double_block zeta2 k).`2.
    + rewrite (radix2_64_block_spec_before p4 640 j zeta6 Hj) 1:/#.
      rewrite (radix2_64_block_spec_before p3 512 j zeta5 Hj) 1:/#.
      rewrite (radix2_64_block_spec_before p2 384 j zeta4 Hj) 1:/#.
      rewrite (radix2_64_block_spec_before p1 256 j zeta3 Hj) 1:/#.
      rewrite (radix2_64_block_spec_get1_valid
        p0 double_block k zeta2 Hvalid1 Hk).
      by rewrite Hpaireq.
    move: Hpair.
    rewrite /k Hout /radix2_64_pair_at /radix2_64_pair_math_at /radix2_64_pair_math /=.
    move=> [Hr0 [Hr1 [Hc0 Hc1]]].
    split; first exact Hr1.
    exact Hc1.
  case (j < 5 * block) => Hj4.
  + pose k := j - 2 * double_block.
    have Hk : 0 <= k < block by rewrite /k /double_block /block; smt().
    have Hlo : -4 * q <= coeff p.[j] < 4 * q
      by apply (radix3_output_shape_before p j Hshape); smt().
    have Hhi : -4 * q <= coeff p.[j + block] < 4 * q
      by apply (radix3_output_shape_before p (j + block) Hshape); smt().
    have Hpair := radix2_64_pair_algebra 4 zeta3 p.[j] p.[j + block]
      radix2_64_zeta3_root _ Hlo Hhi
      radix2_64_zeta3_in_qrange radix2_64_zeta3_montgomery_meaning; first smt().
    have Hpaireq1 :
        radix2_64_pair_at p1 (2 * double_block) zeta3 k =
        radix2_64_pair_at p0 (2 * double_block) zeta3 k.
    + rewrite /p1.
      by apply (radix2_64_block_spec_far_pair_at p0 double_block (2 * double_block) k zeta2 zeta3); smt().
    have Hpaireq2 :
        radix2_64_pair_at p0 (2 * double_block) zeta3 k =
        radix2_64_pair_at p (2 * double_block) zeta3 k.
    + rewrite /p0.
      by apply (radix2_64_block_spec_far_pair_at p 0 (2 * double_block) k zeta1 zeta3); smt().
    have Hout :
        (radix2_64_block_spec p4 640 zeta6).[j] =
        (radix2_64_pair_at p (2 * double_block) zeta3 k).`1.
    + rewrite (radix2_64_block_spec_before p4 640 j zeta6 Hj) 1:/#.
      rewrite (radix2_64_block_spec_before p3 512 j zeta5 Hj) 1:/#.
      rewrite (radix2_64_block_spec_before p2 384 j zeta4 Hj) 1:/#.
      rewrite (radix2_64_block_spec_get0_valid
        p1 (2 * double_block) k zeta3 Hvalid2 Hk).
      by rewrite Hpaireq1 Hpaireq2.
    move: Hpair.
    rewrite /k Hout /radix2_64_pair_at /radix2_64_pair_math_at /radix2_64_pair_math /=.
    move=> [Hr0 [Hr1 [Hc0 Hc1]]].
    split; first exact Hr0.
    exact Hc0.
  case (j < 6 * block) => Hj5.
  + pose k := j - (2 * double_block + block).
    have Hk : 0 <= k < block by rewrite /k /double_block /block; smt().
    have Hlo : -4 * q <= coeff p.[j - block] < 4 * q
      by apply (radix3_output_shape_before p (j - block) Hshape); smt().
    have Hhi : -4 * q <= coeff p.[j] < 4 * q
      by apply (radix3_output_shape_before p j Hshape); smt().
    have Hpair := radix2_64_pair_algebra 4 zeta3 p.[j - block] p.[j]
      radix2_64_zeta3_root _ Hlo Hhi
      radix2_64_zeta3_in_qrange radix2_64_zeta3_montgomery_meaning; first smt().
    have Hpaireq1 :
        radix2_64_pair_at p1 (2 * double_block) zeta3 k =
        radix2_64_pair_at p0 (2 * double_block) zeta3 k.
    + rewrite /p1.
      by apply (radix2_64_block_spec_far_pair_at p0 double_block (2 * double_block) k zeta2 zeta3); smt().
    have Hpaireq2 :
        radix2_64_pair_at p0 (2 * double_block) zeta3 k =
        radix2_64_pair_at p (2 * double_block) zeta3 k.
    + rewrite /p0.
      by apply (radix2_64_block_spec_far_pair_at p 0 (2 * double_block) k zeta1 zeta3); smt().
    have Hout :
        (radix2_64_block_spec p4 640 zeta6).[j] =
        (radix2_64_pair_at p (2 * double_block) zeta3 k).`2.
    + rewrite (radix2_64_block_spec_before p4 640 j zeta6 Hj) 1:/#.
      rewrite (radix2_64_block_spec_before p3 512 j zeta5 Hj) 1:/#.
      rewrite (radix2_64_block_spec_before p2 384 j zeta4 Hj) 1:/#.
      rewrite (radix2_64_block_spec_get1_valid
        p1 (2 * double_block) k zeta3 Hvalid2 Hk).
      by rewrite Hpaireq1 Hpaireq2.
    move: Hpair.
    rewrite /k Hout /radix2_64_pair_at /radix2_64_pair_math_at /radix2_64_pair_math /=.
    move=> [Hr0 [Hr1 [Hc0 Hc1]]].
    split; first exact Hr1.
    exact Hc1.
  case (j < second_base + block) => Hj6.
  + pose k := j - second_base.
    have Hk : 0 <= k < block by rewrite /k /second_base /block; smt().
    have Hlo : -5 * q <= coeff p.[j] < 5 * q
      by apply (radix3_output_shape_after p j Hshape); smt().
    have Hhi : -5 * q <= coeff p.[j + block] < 5 * q
      by apply (radix3_output_shape_after p (j + block) Hshape); smt().
    have Hpair := radix2_64_pair_algebra 5 zeta4 p.[j] p.[j + block]
      radix2_64_zeta4_root _ Hlo Hhi
      radix2_64_zeta4_in_qrange radix2_64_zeta4_montgomery_meaning; first smt().
    have Hpaireq1 :
        radix2_64_pair_at p2 second_base zeta4 k =
        radix2_64_pair_at p1 second_base zeta4 k.
    + rewrite /p2.
      by apply (radix2_64_block_spec_far_pair_at p1 (2 * double_block) second_base k zeta3 zeta4); smt().
    have Hpaireq2 :
        radix2_64_pair_at p1 second_base zeta4 k =
        radix2_64_pair_at p0 second_base zeta4 k.
    + rewrite /p1.
      by apply (radix2_64_block_spec_far_pair_at p0 double_block second_base k zeta2 zeta4); smt().
    have Hpaireq3 :
        radix2_64_pair_at p0 second_base zeta4 k =
        radix2_64_pair_at p second_base zeta4 k.
    + rewrite /p0.
      by apply (radix2_64_block_spec_far_pair_at p 0 second_base k zeta1 zeta4); smt().
    have Hout :
        (radix2_64_block_spec p4 640 zeta6).[j] =
        (radix2_64_pair_at p second_base zeta4 k).`1.
    + rewrite (radix2_64_block_spec_before p4 640 j zeta6 Hj) 1:/#.
      rewrite (radix2_64_block_spec_before p3 512 j zeta5 Hj) 1:/#.
      rewrite (radix2_64_block_spec_get0_valid
        p2 second_base k zeta4 Hvalid3 Hk).
      by rewrite Hpaireq1 Hpaireq2 Hpaireq3.
    move: Hpair.
    rewrite /k Hout /radix2_64_pair_at /radix2_64_pair_math_at /radix2_64_pair_math /=.
    move=> [Hr0 [Hr1 [Hc0 Hc1]]].
    split; first exact Hr0.
    exact Hc0.
  case (j < second_base + double_block) => Hj7.
  + pose k := j - second_base - block.
    have Hk : 0 <= k < block by rewrite /k /second_base /block; smt().
    have Hlo : -5 * q <= coeff p.[j - block] < 5 * q
      by apply (radix3_output_shape_after p (j - block) Hshape); smt().
    have Hhi : -5 * q <= coeff p.[j] < 5 * q
      by apply (radix3_output_shape_after p j Hshape); smt().
    have Hpair := radix2_64_pair_algebra 5 zeta4 p.[j - block] p.[j]
      radix2_64_zeta4_root _ Hlo Hhi
      radix2_64_zeta4_in_qrange radix2_64_zeta4_montgomery_meaning; first smt().
    have Hpaireq1 :
        radix2_64_pair_at p2 second_base zeta4 k =
        radix2_64_pair_at p1 second_base zeta4 k.
    + rewrite /p2.
      by apply (radix2_64_block_spec_far_pair_at p1 (2 * double_block) second_base k zeta3 zeta4); smt().
    have Hpaireq2 :
        radix2_64_pair_at p1 second_base zeta4 k =
        radix2_64_pair_at p0 second_base zeta4 k.
    + rewrite /p1.
      by apply (radix2_64_block_spec_far_pair_at p0 double_block second_base k zeta2 zeta4); smt().
    have Hpaireq3 :
        radix2_64_pair_at p0 second_base zeta4 k =
        radix2_64_pair_at p second_base zeta4 k.
    + rewrite /p0.
      by apply (radix2_64_block_spec_far_pair_at p 0 second_base k zeta1 zeta4); smt().
    have Hout :
        (radix2_64_block_spec p4 640 zeta6).[j] =
        (radix2_64_pair_at p second_base zeta4 k).`2.
    + rewrite (radix2_64_block_spec_before p4 640 j zeta6 Hj) 1:/#.
      rewrite (radix2_64_block_spec_before p3 512 j zeta5 Hj) 1:/#.
      rewrite (radix2_64_block_spec_get1_valid
        p2 second_base k zeta4 Hvalid3 Hk).
      by rewrite Hpaireq1 Hpaireq2 Hpaireq3.
    move: Hpair.
    rewrite /k Hout /radix2_64_pair_at /radix2_64_pair_math_at /radix2_64_pair_math /=.
    move=> [Hr0 [Hr1 [Hc0 Hc1]]].
    split; first exact Hr1.
    exact Hc1.
  case (j < second_base + 3 * block) => Hj8.
  + pose k := j - (second_base + double_block).
    have Hk : 0 <= k < block by rewrite /k /second_base /double_block /block; smt().
    have Hlo : -5 * q <= coeff p.[j] < 5 * q
      by apply (radix3_output_shape_after p j Hshape); smt().
    have Hhi : -5 * q <= coeff p.[j + block] < 5 * q
      by apply (radix3_output_shape_after p (j + block) Hshape); smt().
    have Hpair := radix2_64_pair_algebra 5 zeta5 p.[j] p.[j + block]
      radix2_64_zeta5_root _ Hlo Hhi
      radix2_64_zeta5_in_qrange radix2_64_zeta5_montgomery_meaning; first smt().
    have Hpaireq1 :
        radix2_64_pair_at p3 (second_base + double_block) zeta5 k =
        radix2_64_pair_at p2 (second_base + double_block) zeta5 k.
    + rewrite /p3.
      by apply (radix2_64_block_spec_far_pair_at p2 second_base (second_base + double_block) k zeta4 zeta5); smt().
    have Hpaireq2 :
        radix2_64_pair_at p2 (second_base + double_block) zeta5 k =
        radix2_64_pair_at p1 (second_base + double_block) zeta5 k.
    + rewrite /p2.
      by apply (radix2_64_block_spec_far_pair_at p1 (2 * double_block) (second_base + double_block) k zeta3 zeta5); smt().
    have Hpaireq3 :
        radix2_64_pair_at p1 (second_base + double_block) zeta5 k =
        radix2_64_pair_at p0 (second_base + double_block) zeta5 k.
    + rewrite /p1.
      by apply (radix2_64_block_spec_far_pair_at p0 double_block (second_base + double_block) k zeta2 zeta5); smt().
    have Hpaireq4 :
        radix2_64_pair_at p0 (second_base + double_block) zeta5 k =
        radix2_64_pair_at p (second_base + double_block) zeta5 k.
    + rewrite /p0.
      by apply (radix2_64_block_spec_far_pair_at p 0 (second_base + double_block) k zeta1 zeta5); smt().
    have Hout :
        (radix2_64_block_spec p4 640 zeta6).[j] =
        (radix2_64_pair_at p (second_base + double_block) zeta5 k).`1.
    + rewrite (radix2_64_block_spec_before p4 640 j zeta6 Hj) 1:/#.
      rewrite (radix2_64_block_spec_get0_valid
        p3 (second_base + double_block) k zeta5 Hvalid4 Hk).
      by rewrite Hpaireq1 Hpaireq2 Hpaireq3 Hpaireq4.
    move: Hpair.
    rewrite /k Hout /radix2_64_pair_at /radix2_64_pair_math_at /radix2_64_pair_math /=.
    move=> [Hr0 [Hr1 [Hc0 Hc1]]].
    split; first exact Hr0.
    exact Hc0.
  case (j < 10 * block) => Hj9.
  + pose k := j - (second_base + double_block + block).
    have Hk : 0 <= k < block by rewrite /k /second_base /double_block /block; smt().
    have Hlo : -5 * q <= coeff p.[j - block] < 5 * q
      by apply (radix3_output_shape_after p (j - block) Hshape); smt().
    have Hhi : -5 * q <= coeff p.[j] < 5 * q
      by apply (radix3_output_shape_after p j Hshape); smt().
    have Hpair := radix2_64_pair_algebra 5 zeta5 p.[j - block] p.[j]
      radix2_64_zeta5_root _ Hlo Hhi
      radix2_64_zeta5_in_qrange radix2_64_zeta5_montgomery_meaning; first smt().
    have Hpaireq1 :
        radix2_64_pair_at p3 (second_base + double_block) zeta5 k =
        radix2_64_pair_at p2 (second_base + double_block) zeta5 k.
    + rewrite /p3.
      by apply (radix2_64_block_spec_far_pair_at p2 second_base (second_base + double_block) k zeta4 zeta5); smt().
    have Hpaireq2 :
        radix2_64_pair_at p2 (second_base + double_block) zeta5 k =
        radix2_64_pair_at p1 (second_base + double_block) zeta5 k.
    + rewrite /p2.
      by apply (radix2_64_block_spec_far_pair_at p1 (2 * double_block) (second_base + double_block) k zeta3 zeta5); smt().
    have Hpaireq3 :
        radix2_64_pair_at p1 (second_base + double_block) zeta5 k =
        radix2_64_pair_at p0 (second_base + double_block) zeta5 k.
    + rewrite /p1.
      by apply (radix2_64_block_spec_far_pair_at p0 double_block (second_base + double_block) k zeta2 zeta5); smt().
    have Hpaireq4 :
        radix2_64_pair_at p0 (second_base + double_block) zeta5 k =
        radix2_64_pair_at p (second_base + double_block) zeta5 k.
    + rewrite /p0.
      by apply (radix2_64_block_spec_far_pair_at p 0 (second_base + double_block) k zeta1 zeta5); smt().
    have Hout :
        (radix2_64_block_spec p4 640 zeta6).[j] =
        (radix2_64_pair_at p (second_base + double_block) zeta5 k).`2.
    + rewrite (radix2_64_block_spec_before p4 640 j zeta6 Hj) 1:/#.
      rewrite (radix2_64_block_spec_get1_valid
        p3 (second_base + double_block) k zeta5 Hvalid4 Hk).
      by rewrite Hpaireq1 Hpaireq2 Hpaireq3 Hpaireq4.
    move: Hpair.
    rewrite /k Hout /radix2_64_pair_at /radix2_64_pair_math_at /radix2_64_pair_math /=.
    move=> [Hr0 [Hr1 [Hc0 Hc1]]].
    split; first exact Hr1.
    exact Hc1.
  case (j < 11 * block) => Hj10.
  + pose k := j - (second_base + 2 * double_block).
    have Hk : 0 <= k < block by rewrite /k /second_base /double_block /block; smt().
    have Hlo : -5 * q <= coeff p.[j] < 5 * q
      by apply (radix3_output_shape_after p j Hshape); smt().
    have Hhi : -5 * q <= coeff p.[j + block] < 5 * q
      by apply (radix3_output_shape_after p (j + block) Hshape); smt().
    have Hpair := radix2_64_pair_algebra 5 zeta6 p.[j] p.[j + block]
      radix2_64_zeta6_root _ Hlo Hhi
      radix2_64_zeta6_in_qrange radix2_64_zeta6_montgomery_meaning; first smt().
    have Hpaireq1 :
        radix2_64_pair_at p4 (second_base + 2 * double_block) zeta6 k =
        radix2_64_pair_at p3 (second_base + 2 * double_block) zeta6 k.
    + rewrite /p4.
      by apply (radix2_64_block_spec_far_pair_at p3 (second_base + double_block) (second_base + 2 * double_block) k zeta5 zeta6); smt().
    have Hpaireq2 :
        radix2_64_pair_at p3 (second_base + 2 * double_block) zeta6 k =
        radix2_64_pair_at p2 (second_base + 2 * double_block) zeta6 k.
    + rewrite /p3.
      by apply (radix2_64_block_spec_far_pair_at p2 second_base (second_base + 2 * double_block) k zeta4 zeta6); smt().
    have Hpaireq3 :
        radix2_64_pair_at p2 (second_base + 2 * double_block) zeta6 k =
        radix2_64_pair_at p1 (second_base + 2 * double_block) zeta6 k.
    + rewrite /p2.
      by apply (radix2_64_block_spec_far_pair_at p1 (2 * double_block) (second_base + 2 * double_block) k zeta3 zeta6); smt().
    have Hpaireq4 :
        radix2_64_pair_at p1 (second_base + 2 * double_block) zeta6 k =
        radix2_64_pair_at p0 (second_base + 2 * double_block) zeta6 k.
    + rewrite /p1.
      by apply (radix2_64_block_spec_far_pair_at p0 double_block (second_base + 2 * double_block) k zeta2 zeta6); smt().
    have Hpaireq5 :
        radix2_64_pair_at p0 (second_base + 2 * double_block) zeta6 k =
        radix2_64_pair_at p (second_base + 2 * double_block) zeta6 k.
    + rewrite /p0.
      by apply (radix2_64_block_spec_far_pair_at p 0 (second_base + 2 * double_block) k zeta1 zeta6); smt().
    have Hout :
        (radix2_64_block_spec p4 640 zeta6).[j] =
        (radix2_64_pair_at p (second_base + 2 * double_block) zeta6 k).`1.
    + rewrite (radix2_64_block_spec_get0_valid
        p4 (second_base + 2 * double_block) k zeta6 Hvalid5 Hk).
      by rewrite Hpaireq1 Hpaireq2 Hpaireq3 Hpaireq4 Hpaireq5.
    move: Hpair.
    rewrite /k Hout /radix2_64_pair_at /radix2_64_pair_math_at /radix2_64_pair_math /=.
    move=> [Hr0 [Hr1 [Hc0 Hc1]]].
    split; first exact Hr0.
    exact Hc0.
  pose k := j - (second_base + 2 * double_block + block).
  have Hk : 0 <= k < block by rewrite /k /second_base /double_block /block; smt().
  have Hlo : -5 * q <= coeff p.[j - block] < 5 * q
    by apply (radix3_output_shape_after p (j - block) Hshape); smt().
  have Hhi : -5 * q <= coeff p.[j] < 5 * q
    by apply (radix3_output_shape_after p j Hshape); smt().
  have Hpair := radix2_64_pair_algebra 5 zeta6 p.[j - block] p.[j]
    radix2_64_zeta6_root _ Hlo Hhi
    radix2_64_zeta6_in_qrange radix2_64_zeta6_montgomery_meaning; first smt().
  have Hpaireq1 :
      radix2_64_pair_at p4 (second_base + 2 * double_block) zeta6 k =
      radix2_64_pair_at p3 (second_base + 2 * double_block) zeta6 k.
  + rewrite /p4.
    by apply (radix2_64_block_spec_far_pair_at p3 (second_base + double_block) (second_base + 2 * double_block) k zeta5 zeta6); smt().
  have Hpaireq2 :
      radix2_64_pair_at p3 (second_base + 2 * double_block) zeta6 k =
      radix2_64_pair_at p2 (second_base + 2 * double_block) zeta6 k.
  + rewrite /p3.
    by apply (radix2_64_block_spec_far_pair_at p2 second_base (second_base + 2 * double_block) k zeta4 zeta6); smt().
  have Hpaireq3 :
      radix2_64_pair_at p2 (second_base + 2 * double_block) zeta6 k =
      radix2_64_pair_at p1 (second_base + 2 * double_block) zeta6 k.
  + rewrite /p2.
    by apply (radix2_64_block_spec_far_pair_at p1 (2 * double_block) (second_base + 2 * double_block) k zeta3 zeta6); smt().
  have Hpaireq4 :
      radix2_64_pair_at p1 (second_base + 2 * double_block) zeta6 k =
      radix2_64_pair_at p0 (second_base + 2 * double_block) zeta6 k.
  + rewrite /p1.
    by apply (radix2_64_block_spec_far_pair_at p0 double_block (second_base + 2 * double_block) k zeta2 zeta6); smt().
  have Hpaireq5 :
      radix2_64_pair_at p0 (second_base + 2 * double_block) zeta6 k =
      radix2_64_pair_at p (second_base + 2 * double_block) zeta6 k.
  + rewrite /p0.
    by apply (radix2_64_block_spec_far_pair_at p 0 (second_base + 2 * double_block) k zeta1 zeta6); smt().
  have Hout :
      (radix2_64_block_spec p4 640 zeta6).[j] =
      (radix2_64_pair_at p (second_base + 2 * double_block) zeta6 k).`2.
  + rewrite (radix2_64_block_spec_get1_valid
      p4 (second_base + 2 * double_block) k zeta6 Hvalid5 Hk).
    by rewrite Hpaireq1 Hpaireq2 Hpaireq3 Hpaireq4 Hpaireq5.
  move: Hpair.
  rewrite /k Hout /radix2_64_pair_at /radix2_64_pair_math_at /radix2_64_pair_math /=.
  move=> [Hr0 [Hr1 [Hc0 Hc1]]].
  split; first exact Hr1.
  exact Hc1.
qed.

lemma ntt_radix2_64_algebra_functional
    (rp0 : W16.t Array768.t) :
  radix3_output_shape rp0 =>
  hoare [NTRUPlus768NTTRadix2_64.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_64 :
    rp = rp0 ==> radix2_64_algebra rp0 res].
proof.
  move=> Hshape.
  conseq (ntt_radix2_64_functional rp0) => />.
  exact (radix2_64_spec_algebra rp0 Hshape).
qed.

lemma ntt_radix2_64_correct_algebra
    (rp0 : W16.t Array768.t) :
  radix3_output_shape rp0 =>
  phoare [NTRUPlus768NTTRadix2_64.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_64 :
    rp = rp0 ==> radix2_64_algebra rp0 res] = 1%r.
proof.
  move=> Hshape.
  have Hfunctional := ntt_radix2_64_algebra_functional rp0 Hshape.
  by conseq ntt_radix2_64_lossless Hfunctional.
qed.
