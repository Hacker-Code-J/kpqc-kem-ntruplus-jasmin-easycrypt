require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord JModel_x86.

require import W16extra.
require import Array768.
require import NTRUPlus768BasemulProof.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768NTTSchedule.
require import NTRUPlus768InvNTTFinalProof.
require import NTRUPlus768InvNTTRadix3Algebra.

import Ring.IntID IntOrder.

op zminusz5inv_root : int = 1634.
op ninv_root : int = 3439.
op twoninv_root : int = 3421.

op invntt_final_pair_math (a b : int) : int * int =
  let t1 = a + b in
  let t2 = (a - b) * zminusz5inv_root in
  ((t1 - t2) * ninv_root, t2 * twoninv_root).

op invntt_final_math (p : W16.t Array768.t) (j : int) : int =
  if j < NTRUPlus768InvNTTFinalProof.half then
    (invntt_final_pair_math
      (coeff p.[j]) (coeff p.[j + NTRUPlus768InvNTTFinalProof.half])).`1
  else
    (invntt_final_pair_math
      (coeff p.[j - NTRUPlus768InvNTTFinalProof.half]) (coeff p.[j])).`2.

op invntt_final_input_shape (p : W16.t Array768.t) : bool =
  forall j, 0 <= j < 768 =>
    (if j < 128 \/
        NTRUPlus768InvNTTFinalProof.half <= j <
        NTRUPlus768InvNTTFinalProof.half + 128
     then -3 * q <= coeff p.[j] < 3 * q
     else -q <= coeff p.[j] < q).

op invntt_final_algebra
    (input output : W16.t Array768.t) : bool =
  forall j, 0 <= j < 768 =>
    -q <= coeff output.[j] < q /\
    coeff output.[j] %% q = invntt_final_math input j %% q.

lemma coeff_of_word_small (x : int) :
  W16.min_sint <= x <= W16.max_sint =>
  coeff (W16.of_int x) = x.
proof.
  move=> Hx.
  rewrite /coeff.
  exact (W16.to_sintK_small x Hx).
qed.

lemma zminusz5inv_coeffE :
  coeff NTRUPlus768InvNTTFinalProof.zminusz5inv = ZMINUSZ5INV_coeff.
proof.
  rewrite /NTRUPlus768InvNTTFinalProof.zminusz5inv /ZMINUSZ5INV_coeff.
  apply coeff_of_word_small.
  smt().
qed.

lemma ninv_coeffE :
  coeff NTRUPlus768InvNTTFinalProof.ninv = NINV_coeff.
proof.
  rewrite /NTRUPlus768InvNTTFinalProof.ninv /NINV_coeff.
  apply coeff_of_word_small.
  smt().
qed.

lemma twoninv_coeffE :
  coeff NTRUPlus768InvNTTFinalProof.twoninv = TWONINV_coeff.
proof.
  rewrite /NTRUPlus768InvNTTFinalProof.twoninv /TWONINV_coeff.
  apply coeff_of_word_small.
  smt().
qed.

lemma zminusz5inv_in_qrange : in_qrange NTRUPlus768InvNTTFinalProof.zminusz5inv.
proof.
  rewrite /in_qrange zminusz5inv_coeffE /ZMINUSZ5INV_coeff /q.
  smt().
qed.

lemma ninv_in_qrange : in_qrange NTRUPlus768InvNTTFinalProof.ninv.
proof.
  rewrite /in_qrange ninv_coeffE /NINV_coeff /q.
  smt().
qed.

lemma twoninv_in_qrange : in_qrange NTRUPlus768InvNTTFinalProof.twoninv.
proof.
  rewrite /in_qrange twoninv_coeffE /TWONINV_coeff /q.
  smt().
qed.

lemma zminusz5inv_montgomery_meaning :
  (coeff NTRUPlus768InvNTTFinalProof.zminusz5inv * Rinv) %% q = zminusz5inv_root.
proof.
  have [Hdecode _] := zminusz5inv_true_montgomery_meaning.
  rewrite /zminusz5inv_root zminusz5inv_coeffE.
  rewrite /decode_mont in Hdecode.
  exact Hdecode.
qed.

lemma ninv_montgomery_meaning_root :
  (coeff NTRUPlus768InvNTTFinalProof.ninv * Rinv) %% q = ninv_root.
proof.
  have [Hdecode _] := ninv_montgomery_meaning.
  rewrite /ninv_root ninv_coeffE.
  rewrite /decode_mont in Hdecode.
  exact Hdecode.
qed.

lemma twoninv_montgomery_meaning_root :
  (coeff NTRUPlus768InvNTTFinalProof.twoninv * Rinv) %% q = twoninv_root.
proof.
  have [Hdecode _] := twoninv_montgomery_meaning.
  rewrite /twoninv_root twoninv_coeffE.
  rewrite /decode_mont in Hdecode.
  exact Hdecode.
qed.

lemma scaled_qrange_norm7 (m x : int) :
  0 <= m =>
  -m * q <= x < m * q =>
  `|x| <= m * q.
proof.
  move=> Hm Hx.
  rewrite ler_norml.
  smt().
qed.

lemma scaled_product_bound7 (m x y : int) :
  0 < m <= 7 =>
  -q <= x < q =>
  -m * q <= y < m * q =>
  -R %/ 2 * q <= x * y < R %/ 2 * q.
proof.
  move=> Hm Hx Hy.
  have Habsx : `|x| <= q by exact (qrange_norm x Hx).
  have Hm0 : 0 <= m by smt().
  have Habsy : `|y| <= m * q by exact (scaled_qrange_norm7 m y Hm0 Hy).
  have Habsxy : `|x * y| <= q * (m * q).
  + rewrite normrM.
    apply ler_pmul.
    + exact (normr_ge0 x).
    + exact (normr_ge0 y).
    + exact Habsx.
    exact Habsy.
  have Hlim7 : q * (7 * q) < R %/ 2 * q.
  + rewrite R_halfE /q.
    smt().
  have Hscaled : q * (m * q) <= q * (7 * q).
  + rewrite /q.
    smt().
  have Habs : `|x * y| < R %/ 2 * q by smt().
  move: Habs.
  rewrite ltr_norml.
  smt().
qed.

lemma invntt_final_mul_algebra (z a : W16.t) (root m : int) :
  0 < m <= 7 =>
  in_qrange z =>
  -m * q <= coeff a < m * q =>
  (coeff z * Rinv) %% q = root =>
  -q <= coeff (NTRUPlus768InvNTTFinalProof.invntt_final_mul z a) < q /\
  coeff (NTRUPlus768InvNTTFinalProof.invntt_final_mul z a) %% q =
    (coeff a * root) %% q.
proof.
  move=> Hm Hz Ha Hroot.
  have Hproduct := scaled_product_bound7 m (coeff z) (coeff a) Hm Hz Ha.
  have Hreduce := montgomery_reduce_of_int (coeff z * coeff a) Hproduct.
  have Hmul : mul_i16 z a = W32.of_int (coeff z * coeff a)
    by apply mul_i16E.
  have Ht :
      NTRUPlus768InvNTTFinalProof.invntt_final_mul z a =
      montgomery_reduce (W32.of_int (coeff z * coeff a))
    by rewrite /NTRUPlus768InvNTTFinalProof.invntt_final_mul Hmul.
  have [Hrange Hcongr] := Hreduce.
  split; first by rewrite Ht.
  have Hcongr' :
      coeff (NTRUPlus768InvNTTFinalProof.invntt_final_mul z a) %% q =
      (coeff z * coeff a * Rinv) %% q.
  + rewrite /NTRUPlus768InvNTTFinalProof.invntt_final_mul Hmul.
    exact Hcongr.
  rewrite Hcongr'.
  rewrite (_ : coeff z * coeff a * Rinv = coeff a * (coeff z * Rinv)) 1:/#.
  rewrite -modzMmr Hroot.
  done.
qed.

lemma coeff_add_qbounded7 (m : int) (a b : W16.t) :
  0 < m <= 7 =>
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

lemma coeff_sub_qbounded7 (m : int) (a b : W16.t) :
  0 < m <= 7 =>
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

lemma coeff_add_pair_qbounded (m : int) (a b : W16.t) :
  0 < m <= 3 =>
  -m * q <= coeff a < m * q =>
  -m * q <= coeff b < m * q =>
  coeff (a + b) = coeff a + coeff b.
proof.
  move=> Hm Ha Hb.
  apply W16extra.to_sintD_small.
  move: Ha Hb.
  rewrite /coeff /q /=.
  smt().
qed.

lemma coeff_sub_pair_qbounded (m : int) (a b : W16.t) :
  0 < m <= 3 =>
  -m * q <= coeff a < m * q =>
  -m * q <= coeff b < m * q =>
  coeff (a - b) = coeff a - coeff b.
proof.
  move=> Hm Ha Hb.
  apply W16extra.to_sintB_small.
  move: Ha Hb.
  rewrite /coeff /q /=.
  smt().
qed.

lemma invntt_final_pair_algebra (m : int) (a b : W16.t) :
  0 < m <= 3 =>
  -m * q <= coeff a < m * q =>
  -m * q <= coeff b < m * q =>
  let out = NTRUPlus768InvNTTFinalProof.invntt_final_pair a b in
    -q <= coeff out.`1 < q /\
    -q <= coeff out.`2 < q /\
    coeff out.`1 %% q = (invntt_final_pair_math (coeff a) (coeff b)).`1 %% q /\
    coeff out.`2 %% q = (invntt_final_pair_math (coeff a) (coeff b)).`2 %% q.
proof.
  move=> Hm Ha Hb out.
  pose t1 := a + b.
  pose d := a - b.
  pose t2 := NTRUPlus768InvNTTFinalProof.invntt_final_mul
    NTRUPlus768InvNTTFinalProof.zminusz5inv d.
  pose lowin := t1 - t2.
  have Hm2 : 0 < 2 * m <= 7 by smt().
  have Hm3 : 0 < 2 * m + 1 <= 7 by smt().
  have Hsum : coeff t1 = coeff a + coeff b.
  + rewrite /t1.
    exact (coeff_add_pair_qbounded m a b Hm Ha Hb).
  have Hsum_range : -(2 * m) * q <= coeff t1 < (2 * m) * q.
  + rewrite Hsum.
    smt().
  have Hdiff : coeff d = coeff a - coeff b.
  + rewrite /d.
    exact (coeff_sub_pair_qbounded m a b Hm Ha Hb).
  have Hdiff_range : -(2 * m) * q <= coeff d < (2 * m) * q.
  + rewrite Hdiff.
    smt().
  have Ht2 := invntt_final_mul_algebra
    NTRUPlus768InvNTTFinalProof.zminusz5inv d zminusz5inv_root (2 * m)
    Hm2 zminusz5inv_in_qrange Hdiff_range zminusz5inv_montgomery_meaning.
  have Ht2_range : -q <= coeff t2 < q by move: Ht2; rewrite /t2; smt().
  have Ht2_congr :
      coeff t2 %% q = ((coeff a - coeff b) * zminusz5inv_root) %% q.
  + move: Ht2.
    rewrite /t2 Hdiff.
    smt().
  have Hlowin : coeff lowin = coeff t1 - coeff t2.
  + rewrite /lowin.
    exact (coeff_sub_qbounded7 (2 * m) t1 t2 Hm2 Hsum_range Ht2_range).
  have Hm2pos : 0 < 2 * m by smt().
  have Hlowin_range : -(2 * m + 1) * q <= coeff lowin < (2 * m + 1) * q.
  + rewrite Hlowin.
    exact (NTRUPlus768NTTRadix2_64Algebra.int_sub_qbounded
      (2 * m) (coeff t1) (coeff t2) Hm2pos Hsum_range Ht2_range).
  have Hlow := invntt_final_mul_algebra
    NTRUPlus768InvNTTFinalProof.ninv lowin ninv_root (2 * m + 1)
    Hm3 ninv_in_qrange Hlowin_range ninv_montgomery_meaning_root.
  have Hone : 0 < 1 <= 7 by smt().
  have Hhigh := invntt_final_mul_algebra
    NTRUPlus768InvNTTFinalProof.twoninv t2 twoninv_root 1
    Hone twoninv_in_qrange Ht2_range twoninv_montgomery_meaning_root.
  have Hlow_congr :
      coeff lowin %% q =
      (coeff a + coeff b - (coeff a - coeff b) * zminusz5inv_root) %% q.
  + rewrite Hlowin Hsum.
    rewrite -modzBm Ht2_congr modzBm.
    done.
  have Hout0_congr :
      coeff out.`1 %% q =
      ((coeff a + coeff b - (coeff a - coeff b) * zminusz5inv_root) *
       ninv_root) %% q.
  + have Hbase : coeff out.`1 %% q = (coeff lowin * ninv_root) %% q.
    + move: Hlow.
      rewrite /out /NTRUPlus768InvNTTFinalProof.invntt_final_pair
              /NTRUPlus768InvNTTFinalProof.invntt_final_mul
              /t1 /t2 /d /lowin /=.
      smt().
    rewrite Hbase.
    have -> :
        (coeff lowin * ninv_root) %% q =
        ((coeff lowin %% q) * ninv_root) %% q
      by rewrite modzMml.
    rewrite Hlow_congr.
    by rewrite modzMml.
  have Hout1_congr :
      coeff out.`2 %% q =
      (((coeff a - coeff b) * zminusz5inv_root) * twoninv_root) %% q.
  + have Hbase : coeff out.`2 %% q = (coeff t2 * twoninv_root) %% q.
    + move: Hhigh.
      rewrite /out /NTRUPlus768InvNTTFinalProof.invntt_final_pair
              /NTRUPlus768InvNTTFinalProof.invntt_final_mul
              /t1 /t2 /d /=.
      smt().
    rewrite Hbase.
    have -> :
        (coeff t2 * twoninv_root) %% q =
        ((coeff t2 %% q) * twoninv_root) %% q
      by rewrite modzMml.
    rewrite Ht2_congr.
    by rewrite modzMml.
  split.
  + move: Hlow.
    rewrite /out /NTRUPlus768InvNTTFinalProof.invntt_final_pair
            /NTRUPlus768InvNTTFinalProof.invntt_final_mul
            /t1 /t2 /d /lowin /=.
    smt().
  split.
  + move: Hhigh.
    rewrite /out /NTRUPlus768InvNTTFinalProof.invntt_final_pair
            /NTRUPlus768InvNTTFinalProof.invntt_final_mul
            /t1 /t2 /d /=.
    smt().
  split.
  + rewrite /invntt_final_pair_math /=.
    exact Hout0_congr.
  rewrite /invntt_final_pair_math /=.
  exact Hout1_congr.
qed.

lemma invntt_final_input_shape_coeff
    (p : W16.t Array768.t) (j : int) :
  invntt_final_input_shape p =>
  0 <= j < 768 =>
  (if j < 128 \/
      NTRUPlus768InvNTTFinalProof.half <= j <
      NTRUPlus768InvNTTFinalProof.half + 128
   then -3 * q <= coeff p.[j] < 3 * q
   else -q <= coeff p.[j] < q).
proof.
  by move=> Hshape Hj; rewrite /invntt_final_input_shape in Hshape; exact (Hshape j Hj).
qed.

lemma invntt_final_spec_algebra (p : W16.t Array768.t) :
  invntt_final_input_shape p =>
  invntt_final_algebra p (NTRUPlus768InvNTTFinalProof.invntt_final_spec p).
proof.
  move=> Hshape j Hj.
  rewrite /invntt_final_algebra
          /NTRUPlus768InvNTTFinalProof.invntt_final_spec
          /NTRUPlus768InvNTTFinalProof.invntt_final_prefix_spec.
  rewrite Array768.initiE 1:Hj /invntt_final_math.
  case (j < NTRUPlus768InvNTTFinalProof.half) => Hjhalf.
  + rewrite ifT 1:/#.
    have Hjpair :
        0 <= j + NTRUPlus768InvNTTFinalProof.half < 768
      by rewrite /NTRUPlus768InvNTTFinalProof.half in Hjhalf; smt().
    have Ha :
        (if j < 128 \/ NTRUPlus768InvNTTFinalProof.half <= j <
            NTRUPlus768InvNTTFinalProof.half + 128
         then -3 * q <= coeff p.[j] < 3 * q
         else -q <= coeff p.[j] < q)
      by exact (invntt_final_input_shape_coeff p j Hshape Hj).
    have Hb :
        (if j + NTRUPlus768InvNTTFinalProof.half < 128 \/
            NTRUPlus768InvNTTFinalProof.half <=
              j + NTRUPlus768InvNTTFinalProof.half <
            NTRUPlus768InvNTTFinalProof.half + 128
         then -3 * q <=
              coeff p.[j + NTRUPlus768InvNTTFinalProof.half] <
              3 * q
         else -q <=
              coeff p.[j + NTRUPlus768InvNTTFinalProof.half] < q)
      by exact (invntt_final_input_shape_coeff p
           (j + NTRUPlus768InvNTTFinalProof.half) Hshape Hjpair).
    have Hm : 0 < (if j < 128 then 3 else 1) <= 3 by smt().
    have Hpair :
        let m = if j < 128 then 3 else 1 in
        -m * q <= coeff p.[j] < m * q /\
        -m * q <=
          coeff p.[j + NTRUPlus768InvNTTFinalProof.half] < m * q.
    + case (j < 128) => Hj128.
      + move: Ha Hb.
        rewrite /NTRUPlus768InvNTTFinalProof.half in Hj128.
        smt().
      move: Ha Hb.
      rewrite /NTRUPlus768InvNTTFinalProof.half in Hj128.
      smt().
    move: Hpair => [Ha' Hb'].
    have Halg := invntt_final_pair_algebra
      (if j < 128 then 3 else 1)
      p.[j] p.[j + NTRUPlus768InvNTTFinalProof.half] Hm Ha' Hb'.
    move: Halg.
    rewrite /NTRUPlus768InvNTTFinalProof.invntt_final_pair_at.
    move=> [Hrng0 [Hrng1 [Hcong0 Hcong1]]].
    split; first exact Hrng0.
    rewrite /invntt_final_pair_math /invntt_final_math /= in Hcong0.
    exact Hcong0.
  rewrite ifF 1:/# ifT 1:/#.
  have Hjlo :
      0 <= j - NTRUPlus768InvNTTFinalProof.half < 768
    by rewrite /NTRUPlus768InvNTTFinalProof.half in Hjhalf; smt().
  have Ha :
      (if j - NTRUPlus768InvNTTFinalProof.half < 128 \/
          NTRUPlus768InvNTTFinalProof.half <=
            j - NTRUPlus768InvNTTFinalProof.half <
          NTRUPlus768InvNTTFinalProof.half + 128
       then -3 * q <=
            coeff p.[j - NTRUPlus768InvNTTFinalProof.half] < 3 * q
       else -q <=
            coeff p.[j - NTRUPlus768InvNTTFinalProof.half] < q)
    by exact (invntt_final_input_shape_coeff p
         (j - NTRUPlus768InvNTTFinalProof.half) Hshape Hjlo).
  have Hb :
      (if j < 128 \/ NTRUPlus768InvNTTFinalProof.half <= j <
          NTRUPlus768InvNTTFinalProof.half + 128
       then -3 * q <= coeff p.[j] < 3 * q
       else -q <= coeff p.[j] < q)
    by exact (invntt_final_input_shape_coeff p j Hshape Hj).
  have Hm :
      0 < (if j - NTRUPlus768InvNTTFinalProof.half < 128 then 3 else 1) <= 3
    by rewrite /NTRUPlus768InvNTTFinalProof.half in Hjhalf; smt().
  have Hpair :
      let m = if j - NTRUPlus768InvNTTFinalProof.half < 128 then 3 else 1 in
      -m * q <=
        coeff p.[j - NTRUPlus768InvNTTFinalProof.half] < m * q /\
      -m * q <= coeff p.[j] < m * q.
  + case (j - NTRUPlus768InvNTTFinalProof.half < 128) => Hj128.
    + move: Ha Hb.
      rewrite /NTRUPlus768InvNTTFinalProof.half in Hj128.
      rewrite /NTRUPlus768InvNTTFinalProof.half in Hjhalf.
      smt().
    move: Ha Hb.
    rewrite /NTRUPlus768InvNTTFinalProof.half in Hj128.
    rewrite /NTRUPlus768InvNTTFinalProof.half in Hjhalf.
    smt().
  move: Hpair => [Ha' Hb'].
  have Halg := invntt_final_pair_algebra
    (if j - NTRUPlus768InvNTTFinalProof.half < 128 then 3 else 1)
    p.[j - NTRUPlus768InvNTTFinalProof.half] p.[j] Hm Ha' Hb'.
  move: Halg.
  rewrite /NTRUPlus768InvNTTFinalProof.invntt_final_pair_at.
  move=> [Hrng0 [Hrng1 [Hcong0 Hcong1]]].
  split; first exact Hrng1.
  rewrite /invntt_final_pair_math /invntt_final_math /= in Hcong1.
  exact Hcong1.
qed.

lemma invntt_radix3_algebra_implies_invntt_final_input_shape
    (input mid : W16.t Array768.t) :
  NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_algebra input mid =>
  invntt_final_input_shape mid.
proof.
  move=> Hradix3.
  rewrite /invntt_final_input_shape.
  move=> j Hj.
  have Hmid := Hradix3 j Hj.
  move: Hmid => [Hrange _].
  move: Hrange.
  rewrite /NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_algebra
          /NTRUPlus768InvNTTFinalProof.half.
  smt().
qed.

lemma invntt_final_from_invntt_radix3_algebra
    (input mid : W16.t Array768.t) :
  NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_algebra input mid =>
  invntt_final_algebra mid
    (NTRUPlus768InvNTTFinalProof.invntt_final_spec mid).
proof.
  move=> Hradix3.
  apply invntt_final_spec_algebra.
  exact (invntt_radix3_algebra_implies_invntt_final_input_shape input mid Hradix3).
qed.

lemma invntt_final_algebra_functional
    (rp0 : W16.t Array768.t) :
  invntt_final_input_shape rp0 =>
  hoare [NTRUPlus768InvNTTFinal.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_final :
    rp = rp0 ==> invntt_final_algebra rp0 res].
proof.
  move=> Hshape.
  conseq (NTRUPlus768InvNTTFinalProof.invntt_final_functional rp0) => />.
  exact (invntt_final_spec_algebra rp0 Hshape).
qed.

lemma invntt_final_correct_algebra
    (rp0 : W16.t Array768.t) :
  invntt_final_input_shape rp0 =>
  phoare [NTRUPlus768InvNTTFinal.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_final :
    rp = rp0 ==> invntt_final_algebra rp0 res] = 1%r.
proof.
  move=> Hshape.
  have Hfunctional := invntt_final_algebra_functional rp0 Hshape.
  by conseq NTRUPlus768InvNTTFinalProof.invntt_final_lossless Hfunctional.
qed.
