require import AllCore List IntDiv Ring StdOrder.
from Jasmin require import JWord JModel_x86.

require import JWord_extra W16extra.
require import Array768.
require import NTRUPlus768BasemulProof.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768NTTSchedule.
require NTRUPlus768NTTRadix2_4Proof.
require import NTRUPlus768NTTRadix2_8Proof.
require import NTRUPlus768NTTRadix2_8Algebra.
require import NTRUPlus768NTTRadix2_32Algebra.

import Ring.IntID IntOrder.

op block : int = 4.
op double_block : int = 8.
op nblocks : int = 96.

op centered_input_shape (p : W16.t Array768.t) : bool =
  forall j, 0 <= j < 768 => -1728 <= coeff p.[j] <= 1728.

lemma radix2_8_algebra_centered_input_shape
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_8Algebra.radix2_8_algebra input output =>
  centered_input_shape output.
proof.
  move=> Halg.
  rewrite /centered_input_shape.
  move=> j Hj.
  have Hjalg := Halg j Hj.
  by move: Hjalg => [Hrange _].
qed.

lemma centered_input_shape_qrange
    (p : W16.t Array768.t) (j : int) :
  centered_input_shape p =>
  0 <= j < 768 =>
  -q <= coeff p.[j] < q.
proof.
  move=> Hshape Hj.
  rewrite /centered_input_shape in Hshape.
  have Hjshape := Hshape j Hj.
  rewrite /q /=.
  smt().
qed.

op radix2_4_block_base (b : int) : int = double_block * b.
op radix2_4_schedule_index (b : int) : int = ntt_radix2_4_start + b.
op radix2_4_zeta (b : int) : W16.t =
  W16.of_int (zetas192_coeff (radix2_4_schedule_index b)).
op radix2_4_zeta_root (b : int) : int =
  (zeta_root ^ zetas192_exp (radix2_4_schedule_index b)) %% q.

op radix2_4_mul (z a : W16.t) : W16.t =
  montgomery_reduce (mul_i16 z a).

op radix2_4_pair (z lo hi : W16.t) : W16.t * W16.t =
  let t = radix2_4_mul z hi in
  (barrett_reduce (lo + t), barrett_reduce (lo - t)).

op radix2_4_pair_math (lo hi root : int) : int * int =
  (lo + hi * root, lo - hi * root).

op radix2_4_pair_at
    (p : W16.t Array768.t) (base : int) (z : W16.t) (k : int)
    : W16.t * W16.t =
  radix2_4_pair z p.[base + k] p.[base + k + block].

op radix2_4_pair_math_at
    (p : W16.t Array768.t) (base : int) (root : int) (k : int)
    : int * int =
  radix2_4_pair_math
    (coeff p.[base + k])
    (coeff p.[base + k + block])
    root.

op radix2_4_block_id (j : int) : int = j %/ double_block.
op radix2_4_block_offset (j : int) : int = j %% double_block.
op radix2_4_lane_index (j : int) : int =
  let r = radix2_4_block_offset j in if r < block then r else r - block.

op radix2_4_math (p : W16.t Array768.t) (j : int) : int =
  let b = radix2_4_block_id j in
  let base = radix2_4_block_base b in
  let root = radix2_4_zeta_root b in
  let k = radix2_4_lane_index j in
  if radix2_4_block_offset j < block then
    (radix2_4_pair_math_at p base root k).`1
  else
    (radix2_4_pair_math_at p base root k).`2.

op radix2_4_spec (p : W16.t Array768.t) : W16.t Array768.t =
  Array768.init (fun j =>
    let b = radix2_4_block_id j in
    let base = radix2_4_block_base b in
    let z = radix2_4_zeta b in
    let k = radix2_4_lane_index j in
    if radix2_4_block_offset j < block then
      (radix2_4_pair_at p base z k).`1
    else
      (radix2_4_pair_at p base z k).`2).

op radix2_4_algebra (input output : W16.t Array768.t) : bool =
  forall j, 0 <= j < 768 =>
    -1728 <= coeff output.[j] <= 1728 /\
    coeff output.[j] %% q = radix2_4_math input j %% q.

lemma radix2_4_schedule_index_range (b : int) :
  0 <= b < nblocks =>
  0 <= radix2_4_schedule_index b < 192.
proof.
  rewrite /radix2_4_schedule_index /ntt_radix2_4_start /nblocks.
  smt().
qed.

lemma radix2_4_block_id_range (j : int) :
  0 <= j < 768 =>
  0 <= radix2_4_block_id j < nblocks.
proof.
  rewrite /radix2_4_block_id /double_block /nblocks.
  smt().
qed.

lemma radix2_4_block_offset_range (j : int) :
  0 <= j < 768 =>
  0 <= radix2_4_block_offset j < double_block.
proof.
  rewrite /radix2_4_block_offset /double_block.
  smt().
qed.

lemma radix2_4_zeta_coeffE (b : int) :
  0 <= b < nblocks =>
  coeff (radix2_4_zeta b) = zetas192_coeff (radix2_4_schedule_index b).
proof.
  move=> Hb.
  have Hidx := radix2_4_schedule_index_range b Hb.
  have Hrange := zetas192_coeff_range (radix2_4_schedule_index b) Hidx.
  rewrite /radix2_4_zeta /coeff.
  have Hsmall : W16.min_sint <= zetas192_coeff (radix2_4_schedule_index b)
                               <= W16.max_sint.
  + move: Hrange.
    rewrite /q /=.
    smt().
  exact (W16.to_sintK_small _ Hsmall).
qed.

lemma radix2_4_zeta_in_qrange (b : int) :
  0 <= b < nblocks =>
  in_qrange (radix2_4_zeta b).
proof.
  move=> Hb.
  have Hidx := radix2_4_schedule_index_range b Hb.
  have Hrange := zetas192_coeff_range (radix2_4_schedule_index b) Hidx.
  rewrite /in_qrange (radix2_4_zeta_coeffE b Hb).
  move: Hrange.
  smt().
qed.

lemma radix2_4_zeta_montgomery_meaning (b : int) :
  0 <= b < nblocks =>
  (coeff (radix2_4_zeta b) * Rinv) %% q = radix2_4_zeta_root b.
proof.
  move=> Hb.
  have Hidx := radix2_4_schedule_index_range b Hb.
  have Hrel := zetas192_relation (radix2_4_schedule_index b) Hidx.
  rewrite /radix2_4_zeta_root.
  have -> : coeff (radix2_4_zeta b) = zetas192_coeff (radix2_4_schedule_index b)
    by exact (radix2_4_zeta_coeffE b Hb).
  exact Hrel.
qed.

lemma coeff_add_qrange (a b : W16.t) :
  -q <= coeff a < q =>
  -q <= coeff b < q =>
  coeff (a + b) = coeff a + coeff b.
proof.
  move=> Ha Hb.
  apply W16extra.to_sintD_small.
  move: Ha Hb.
  rewrite /coeff /q /=.
  smt().
qed.

lemma coeff_sub_qrange (a b : W16.t) :
  -q <= coeff a < q =>
  -q <= coeff b < q =>
  coeff (a - b) = coeff a - coeff b.
proof.
  move=> Ha Hb.
  apply W16extra.to_sintB_small.
  move: Ha Hb.
  rewrite /coeff /q /=.
  smt().
qed.

lemma radix2_4_mul_algebra (z a : W16.t) (root : int) :
  in_qrange z =>
  -q <= coeff a < q =>
  (coeff z * Rinv) %% q = root =>
  -q <= coeff (radix2_4_mul z a) < q /\
  coeff (radix2_4_mul z a) %% q = (coeff a * root) %% q.
proof.
  move=> Hz Ha Hroot.
  have Hproduct := product_bound (coeff z) (coeff a) Hz Ha.
  have Hreduce := montgomery_reduce_of_int (coeff z * coeff a) Hproduct.
  have Hmul : mul_i16 z a = W32.of_int (coeff z * coeff a) by apply mul_i16E.
  have Ht :
      radix2_4_mul z a = montgomery_reduce
        (W32.of_int (coeff z * coeff a))
    by rewrite /radix2_4_mul Hmul.
  move: Hreduce.
  rewrite Ht.
  move=> [Hrange Hcongr].
  split; first exact Hrange.
  rewrite Hcongr.
  rewrite (_ : coeff z * coeff a * Rinv = coeff a * (coeff z * Rinv)) 1:/#.
  rewrite -modzMmr Hroot.
  done.
qed.

lemma radix2_4_pair_algebra
    (z lo hi : W16.t) (root : int) :
  -q <= coeff lo < q =>
  -q <= coeff hi < q =>
  in_qrange z =>
  (coeff z * Rinv) %% q = root =>
  let out = radix2_4_pair z lo hi in
    -1728 <= coeff out.`1 <= 1728 /\
    -1728 <= coeff out.`2 <= 1728 /\
    coeff out.`1 %% q = (coeff lo + coeff hi * root) %% q /\
    coeff out.`2 %% q = (coeff lo - coeff hi * root) %% q.
proof.
  move=> Hlo Hhi Hz Hroot out.
  pose t := radix2_4_mul z hi.
  have Ht := radix2_4_mul_algebra z hi root Hz Hhi Hroot.
  have Ht_range : -q <= coeff t < q by move: Ht; smt().
  have Ht_congr : coeff t %% q = (coeff hi * root) %% q by move: Ht; smt().
  have Hsum : coeff (lo + t) = coeff lo + coeff t.
  + exact (coeff_add_qrange lo t Hlo Ht_range).
  have Hdiff : coeff (lo - t) = coeff lo - coeff t.
  + exact (coeff_sub_qrange lo t Hlo Ht_range).
  have Hsum_range : -2 * q <= coeff (lo + t) < 2 * q.
  + rewrite Hsum /q.
    smt().
  have Hdiff_range : -2 * q <= coeff (lo - t) < 2 * q.
  + rewrite Hdiff /q.
    smt().
  have Hsum_small : -6 * q <= coeff (lo + t) < 6 * q by move: Hsum_range; smt().
  have Hdiff_small : -6 * q <= coeff (lo - t) < 6 * q by move: Hdiff_range; smt().
  have Hbar_sum :=
    NTRUPlus768NTTRadix2_32Algebra.barrett_reduce_small (lo + t) Hsum_small.
  have Hbar_diff :=
    NTRUPlus768NTTRadix2_32Algebra.barrett_reduce_small (lo - t) Hdiff_small.
  have Hsum_congr :
      coeff (lo + t) %% q = (coeff lo + coeff hi * root) %% q.
  + rewrite Hsum -modzDmr Ht_congr modzDmr.
    done.
  have Hdiff_congr :
      coeff (lo - t) %% q = (coeff lo - coeff hi * root) %% q.
  + rewrite Hdiff -modzBm Ht_congr modzBm.
    done.
  move: Hbar_sum Hbar_diff.
  rewrite /out /radix2_4_pair /t /=.
  move=> [Hsum_eq [Hsum_rng Hsum_mod]] [Hdiff_eq [Hdiff_rng Hdiff_mod]].
  split; first exact Hsum_rng.
  split; first exact Hdiff_rng.
  split.
  + rewrite Hsum_mod Hsum_congr.
    done.
  rewrite Hdiff_mod Hdiff_congr.
  done.
qed.

lemma radix2_4_spec_algebra (p : W16.t Array768.t) :
  centered_input_shape p => radix2_4_algebra p (radix2_4_spec p).
proof.
  move=> Hshape j Hj.
  pose b := radix2_4_block_id j.
  pose r := radix2_4_block_offset j.
  pose base := radix2_4_block_base b.
  pose z := radix2_4_zeta b.
  pose root := radix2_4_zeta_root b.
  pose k := radix2_4_lane_index j.
  have Hb : 0 <= b < nblocks by rewrite /b; exact (radix2_4_block_id_range j Hj).
  have Hr : 0 <= r < double_block by rewrite /r; exact (radix2_4_block_offset_range j Hj).
  have Hdiv := divz_eq j double_block.
  rewrite /double_block in Hdiv.
  rewrite /radix2_4_algebra.
  rewrite /r /radix2_4_block_offset.
  case (j %% 8 < block) => Hrlo.
  + have Hk : 0 <= k < block.
    + move: Hr Hrlo.
      rewrite /k /radix2_4_lane_index /r /radix2_4_block_offset /double_block /block.
      smt().
    have Hbasek : base + k = j.
    + move: Hdiv Hr Hrlo.
      rewrite /base /b /k /radix2_4_block_base /radix2_4_block_id.
      rewrite /radix2_4_lane_index /radix2_4_block_offset /double_block /block.
      smt().
    have Hbasek_hi : base + k + block = j + block by rewrite Hbasek.
    have Hlo : -q <= coeff p.[j] < q
      by exact (centered_input_shape_qrange p j Hshape Hj).
    have Hj_hi : 0 <= j + block < 768.
    + move: Hr Hrlo.
      rewrite /r /radix2_4_block_offset /double_block /block.
      smt().
    have Hhi : -q <= coeff p.[j + block] < q
      by exact (centered_input_shape_qrange p (j + block) Hshape Hj_hi).
    have Hlo_base : -q <= coeff p.[base + k] < q by rewrite Hbasek.
    have Hhi_base : -q <= coeff p.[base + k + block] < q by rewrite Hbasek_hi.
    have Hpair :=
      radix2_4_pair_algebra z p.[base + k] p.[base + k + block] root
        Hlo_base Hhi_base
        (radix2_4_zeta_in_qrange b Hb)
        (radix2_4_zeta_montgomery_meaning b Hb).
    have Hspecj :
        (radix2_4_spec p).[j] = (radix2_4_pair_at p base z k).`1.
    + rewrite /radix2_4_spec Array768.initiE 1:Hj.
      rewrite /base /z /k /b.
      rewrite /radix2_4_block_base /radix2_4_lane_index.
      rewrite /radix2_4_block_id /radix2_4_block_offset.
      smt().
    have [Hrng0 [Hrng1 [Hcong0 Hcong1]]] := Hpair.
    rewrite Hspecj.
    split; first exact Hrng0.
    rewrite /radix2_4_math /radix2_4_block_id /radix2_4_block_base.
    rewrite /radix2_4_zeta_root /root /radix2_4_lane_index Hrlo.
    rewrite /radix2_4_pair_math_at /radix2_4_pair_math.
    exact Hcong0.
  have Hk : 0 <= k < block.
  + move: Hr Hrlo.
    rewrite /k /radix2_4_lane_index /r /radix2_4_block_offset /double_block /block.
    smt().
  have Hbasek : base + k = j - block.
  + move: Hdiv Hr Hrlo.
    rewrite /base /b /k /radix2_4_block_base /radix2_4_block_id.
    rewrite /radix2_4_lane_index /radix2_4_block_offset /double_block /block.
    smt().
  have Hbasek_hi : base + k + block = j by smt().
  have Hj_lo : 0 <= j - block < 768.
  + move: Hr Hrlo Hj.
    rewrite /r /radix2_4_block_offset /double_block /block.
    smt().
  have Hlo : -q <= coeff p.[j - block] < q
    by exact (centered_input_shape_qrange p (j - block) Hshape Hj_lo).
  have Hhi : -q <= coeff p.[j] < q
    by exact (centered_input_shape_qrange p j Hshape Hj).
  have Hlo_base : -q <= coeff p.[base + k] < q by rewrite Hbasek.
  have Hhi_base : -q <= coeff p.[base + k + block] < q by rewrite Hbasek_hi.
  have Hpair :=
    radix2_4_pair_algebra z p.[base + k] p.[base + k + block] root
      Hlo_base Hhi_base
      (radix2_4_zeta_in_qrange b Hb)
      (radix2_4_zeta_montgomery_meaning b Hb).
  have Hspecj :
      (radix2_4_spec p).[j] = (radix2_4_pair_at p base z k).`2.
  + rewrite /radix2_4_spec Array768.initiE 1:Hj.
    rewrite /base /z /k /b.
    rewrite /radix2_4_block_base /radix2_4_lane_index.
    rewrite /radix2_4_block_id /radix2_4_block_offset.
    smt().
  have [Hrng0 [Hrng1 [Hcong0 Hcong1]]] := Hpair.
  rewrite Hspecj.
  split; first exact Hrng1.
  rewrite /radix2_4_math /radix2_4_block_id /radix2_4_block_base.
  rewrite /radix2_4_zeta_root /root /radix2_4_lane_index Hrlo.
  rewrite /radix2_4_pair_math_at /radix2_4_pair_math.
  exact Hcong1.
qed.

lemma radix2_4_from_radix2_8_algebra
    (input mid : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_8Algebra.radix2_8_algebra input mid =>
  radix2_4_algebra mid (radix2_4_spec mid).
proof.
  move=> H8.
  apply radix2_4_spec_algebra.
  exact (radix2_8_algebra_centered_input_shape input mid H8).
qed.

op radix2_4_word_zeta (b : int) : W16.t =
  W16.of_int (zetas192_coeff (ntt_radix2_4_start + b)).

op radix2_4_word_indexed_spec
    (p : W16.t Array768.t) : W16.t Array768.t =
  Array768.init (fun j =>
    let b = j %/ double_block in
    let base = double_block * b in
    let k = if j %% double_block < block
            then j %% double_block
            else j %% double_block - block in
    if j %% double_block < block then
      (NTRUPlus768NTTRadix2_4Proof.radix2_4_pair_at
         p base (radix2_4_word_zeta b) k).`1
    else
      (NTRUPlus768NTTRadix2_4Proof.radix2_4_pair_at
         p base (radix2_4_word_zeta b) k).`2).

op radix2_4_word_apply_block
    (p : W16.t Array768.t) (b : int) : W16.t Array768.t =
  NTRUPlus768NTTRadix2_4Proof.radix2_4_block_spec
    p (double_block * b) (radix2_4_word_zeta b).

op radix2_4_word_fold
    (p : W16.t Array768.t) (n : int) : W16.t Array768.t =
  foldl radix2_4_word_apply_block p (range 0 n).

lemma radix2_4_word_spec_fold (p : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_4Proof.radix2_4_spec p =
  radix2_4_word_fold p nblocks.
proof.
  rewrite /NTRUPlus768NTTRadix2_4Proof.radix2_4_spec.
  rewrite /radix2_4_word_fold /nblocks.
  rewrite (rangeSr 0 95) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 94) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 93) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 92) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 91) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 90) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 89) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 88) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 87) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 86) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 85) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 84) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 83) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 82) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 81) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 80) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 79) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 78) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 77) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 76) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 75) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 74) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 73) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 72) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 71) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 70) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 69) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 68) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 67) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 66) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 65) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 64) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 63) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 62) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 61) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 60) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 59) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 58) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 57) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 56) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 55) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 54) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 53) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 52) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 51) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 50) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 49) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 48) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 47) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 46) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 45) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 44) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 43) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 42) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 41) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 40) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 39) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 38) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 37) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 36) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 35) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 34) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 33) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 32) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 31) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 30) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 29) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 28) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 27) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 26) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 25) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 24) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 23) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 22) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 21) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 20) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 19) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 18) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 17) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 16) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 15) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 14) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 13) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 12) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 11) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 10) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 9) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 8) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 7) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 6) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 5) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 4) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 3) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 2) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 1) 1:/# foldl_rcons /=.
  rewrite (rangeSr 0 0) 1:/# foldl_rcons /=.
  rewrite range_geq 1:/# /=.
  rewrite /radix2_4_word_apply_block /double_block /radix2_4_word_zeta.
  rewrite /ntt_radix2_4_start /zetas192_coeff /zetas192_coeffs.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta1.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta2.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta3.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta4.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta5.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta6.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta7.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta8.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta9.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta10.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta11.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta12.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta13.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta14.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta15.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta16.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta17.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta18.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta19.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta20.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta21.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta22.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta23.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta24.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta25.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta26.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta27.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta28.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta29.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta30.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta31.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta32.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta33.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta34.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta35.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta36.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta37.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta38.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta39.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta40.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta41.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta42.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta43.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta44.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta45.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta46.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta47.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta48.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta49.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta50.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta51.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta52.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta53.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta54.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta55.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta56.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta57.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta58.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta59.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta60.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta61.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta62.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta63.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta64.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta65.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta66.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta67.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta68.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta69.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta70.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta71.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta72.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta73.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta74.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta75.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta76.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta77.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta78.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta79.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta80.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta81.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta82.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta83.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta84.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta85.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta86.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta87.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta88.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta89.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta90.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta91.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta92.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta93.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta94.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta95.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta96.
  rewrite /NTRUPlus768NTTRadix2_4Proof.zeta96 /=.
  done.
qed.

lemma radix2_4_word_fold_get
    (p : W16.t Array768.t) (n : int) :
  forall j,
    0 <= n <= 96 =>
    0 <= j < 768 =>
    (radix2_4_word_fold p n).[j] =
      if j %/ double_block < n
      then (radix2_4_word_indexed_spec p).[j]
      else p.[j].
proof.
  elim/natind: n.
  + move=> n Hn j Hbound Hj.
    rewrite /radix2_4_word_fold range_geq 1:Hn /=.
    smt().
  + move=> m Hm IH j Hnext Hj.
    rewrite /radix2_4_word_fold rangeSr 1:Hm foldl_rcons /=.
    rewrite /radix2_4_word_apply_block.
    rewrite /NTRUPlus768NTTRadix2_4Proof.radix2_4_block_spec.
    rewrite /NTRUPlus768NTTRadix2_4Proof.radix2_4_prefix_spec.
    rewrite Array768.initiE 1:Hj.
    case (j %/ double_block = m) => Hblock.
    + have Hr := divz_eq j double_block.
      have Hrem : 0 <= j %% double_block < double_block.
      + rewrite /double_block; smt().
      rewrite /radix2_4_word_indexed_spec Array768.initiE 1:Hj.
      rewrite /double_block /block in Hblock.
      rewrite /double_block /block in Hr.
      rewrite /double_block /block in Hrem.
      rewrite /double_block /block.
      case (j %% 8 < 4) => Hlow.
      + have Hj0 : 0 <= 8 * m + (j - 8 * m) < 768 by smt().
        have Hj1 :
            0 <= 8 * m + (j - 8 * m) +
           NTRUPlus768NTTRadix2_4Proof.block < 768.
        + rewrite /NTRUPlus768NTTRadix2_4Proof.block; smt().
        rewrite /NTRUPlus768NTTRadix2_4Proof.radix2_4_pair_at.
        have Hprev0 := IH (8 * m + (j - 8 * m)) _ Hj0.
        + smt().
        have Hprev1 := IH
          (8 * m + (j - 8 * m) +
           NTRUPlus768NTTRadix2_4Proof.block) _ Hj1.
        + smt().
        rewrite /radix2_4_word_fold /radix2_4_word_apply_block
          /double_block in Hprev0.
        rewrite /radix2_4_word_fold /radix2_4_word_apply_block
          /double_block in Hprev1.
        rewrite (_ : 8 * m + (j - 8 * m) =
                     m * 8 + j %% 8) 1:/#
          divzMDl 1:/# divz_small 1:/# /= in Hprev0.
        rewrite /NTRUPlus768NTTRadix2_4Proof.block in Hprev1.
        rewrite (_ : 8 * m + (j - 8 * m) + 4 =
                     m * 8 + (j %% 8 + 4)) 1:/#
          divzMDl 1:/# divz_small 1:/# /= in Hprev1.
        rewrite (_ : m * 8 + (j %% 8 + 4) =
                     m * 8 + j %% 8 + 4) 1:/# in Hprev1.
        rewrite /NTRUPlus768NTTRadix2_4Proof.block.
        rewrite (_ : 8 * m + (j - 8 * m) =
                     m * 8 + j %% 8) 1:/#.
        rewrite Hprev0 Hprev1.
        rewrite Hblock Hlow /=.
        congr; smt().
      have Hj0 :
          0 <= 8 * m + (j - 8 * m -
               NTRUPlus768NTTRadix2_4Proof.block) < 768.
      + rewrite /NTRUPlus768NTTRadix2_4Proof.block; smt().
      have Hj1 :
          0 <= 8 * m + (j - 8 * m -
               NTRUPlus768NTTRadix2_4Proof.block) +
               NTRUPlus768NTTRadix2_4Proof.block < 768.
      + rewrite /NTRUPlus768NTTRadix2_4Proof.block; smt().
      rewrite /NTRUPlus768NTTRadix2_4Proof.radix2_4_pair_at.
      have Hprev0 := IH
        (8 * m + (j - 8 * m -
         NTRUPlus768NTTRadix2_4Proof.block)) _ Hj0.
      + smt().
      have Hprev1 := IH
        (8 * m + (j - 8 * m -
         NTRUPlus768NTTRadix2_4Proof.block) +
         NTRUPlus768NTTRadix2_4Proof.block) _ Hj1.
      + smt().
      rewrite /radix2_4_word_fold /radix2_4_word_apply_block
        /double_block in Hprev0.
      rewrite /radix2_4_word_fold /radix2_4_word_apply_block
        /double_block in Hprev1.
      rewrite /NTRUPlus768NTTRadix2_4Proof.block in Hprev0.
      rewrite (_ : 8 * m + (j - 8 * m - 4) =
                   m * 8 + (j %% 8 - 4)) 1:/#
        divzMDl 1:/# divz_small 1:/# /= in Hprev0.
      rewrite /NTRUPlus768NTTRadix2_4Proof.block in Hprev1.
      rewrite (_ : 8 * m + (j - 8 * m - 4) + 4 =
                   m * 8 + j %% 8) 1:/#
        divzMDl 1:/# divz_small 1:/# /= in Hprev1.
      rewrite /NTRUPlus768NTTRadix2_4Proof.block.
      rewrite (_ : 8 * m + (j - 8 * m - 4) =
                   m * 8 + (j %% 8 - 4)) 1:/#.
      rewrite (_ : m * 8 + (j %% 8 - 4) + 4 =
                   m * 8 + j %% 8) 1:/#.
      rewrite Hprev0.
      rewrite Hprev1.
      rewrite Hblock Hlow /=.
      clear Hprev0 Hprev1 IH.
      have Hfirst : ! (8 * m <= j < 8 * m + 4) by smt().
      have Hsecond : 8 * m + 4 <= j < 8 * m + 8 by smt().
      have Hsucc : m < m + 1 by smt().
      rewrite Hfirst Hsecond Hsucc /=.
      congr; smt().
    have Hprev := IH j _ Hj.
    + smt().
    rewrite /double_block in Hprev.
    rewrite Hprev.
    rewrite /double_block /NTRUPlus768NTTRadix2_4Proof.block.
    smt().
qed.

lemma radix2_4_word_spec_indexedE (p : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_4Proof.radix2_4_spec p =
  radix2_4_word_indexed_spec p.
proof.
  rewrite radix2_4_word_spec_fold /nblocks.
  apply Array768.tP => j Hj.
  have Hget := radix2_4_word_fold_get p 96 j _ Hj.
  + smt().
  rewrite Hget.
  rewrite /double_block.
  smt().
qed.

lemma radix2_4_word_pair_atE
    (p : W16.t Array768.t) (base : int) (z : W16.t) (k : int) :
  NTRUPlus768NTTRadix2_4Proof.radix2_4_pair_at p base z k =
  radix2_4_pair_at p base z k.
proof.
  rewrite /NTRUPlus768NTTRadix2_4Proof.radix2_4_pair_at
    /NTRUPlus768NTTRadix2_4Proof.radix2_4_pair
    /NTRUPlus768NTTRadix2_4Proof.radix2_4_mul
    /NTRUPlus768NTTRadix2_4Proof.barrett_reduce.
  rewrite /radix2_4_pair_at /radix2_4_pair /radix2_4_mul.
  rewrite /NTRUPlus768NTTRadix2_8Proof.barrett_reduce.
  done.
qed.

lemma radix2_4_word_indexed_specE (p : W16.t Array768.t) :
  radix2_4_word_indexed_spec p = radix2_4_spec p.
proof.
  apply Array768.tP => j Hj.
  rewrite /radix2_4_word_indexed_spec /radix2_4_spec.
  rewrite !Array768.initiE 1,2:Hj.
  rewrite /radix2_4_block_id /radix2_4_block_offset.
  rewrite /radix2_4_block_base /radix2_4_lane_index.
  rewrite /radix2_4_word_zeta /radix2_4_zeta
    /radix2_4_schedule_index.
  simplify.
  by rewrite !radix2_4_word_pair_atE.
qed.

lemma radix2_4_word_specE (p : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_4Proof.radix2_4_spec p = radix2_4_spec p.
proof.
  rewrite radix2_4_word_spec_indexedE radix2_4_word_indexed_specE.
  done.
qed.

lemma ntt_radix2_4_algebra_functional
    (rp0 : W16.t Array768.t) :
  centered_input_shape rp0 =>
  hoare [NTRUPlus768NTTRadix2_4.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_4 :
    rp = rp0 ==> radix2_4_algebra rp0 res].
proof.
  move=> Hshape.
  conseq (NTRUPlus768NTTRadix2_4Proof.ntt_radix2_4_functional rp0) => />.
  rewrite radix2_4_word_specE.
  exact (radix2_4_spec_algebra rp0 Hshape).
qed.

lemma ntt_radix2_4_correct_algebra
    (rp0 : W16.t Array768.t) :
  centered_input_shape rp0 =>
  phoare [NTRUPlus768NTTRadix2_4.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_4 :
    rp = rp0 ==> radix2_4_algebra rp0 res] = 1%r.
proof.
  move=> Hshape.
  have Hfunctional := ntt_radix2_4_algebra_functional rp0 Hshape.
  by conseq NTRUPlus768NTTRadix2_4Proof.ntt_radix2_4_lossless Hfunctional.
qed.
