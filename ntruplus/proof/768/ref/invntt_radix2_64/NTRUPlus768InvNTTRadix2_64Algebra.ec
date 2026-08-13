require import AllCore List IntDiv Ring StdOrder.
from Jasmin require import JWord JModel_x86.

require import JWord_extra W16extra.
require import Array768.
require import NTRUPlus768BasemulProof.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768NTTSchedule.
require import NTRUPlus768NTTRadix2_64Proof.
require import NTRUPlus768NTTRadix2_64Algebra.
require import NTRUPlus768InvNTTRadix2_4Proof.
require import NTRUPlus768InvNTTRadix2_4Algebra.
require import NTRUPlus768InvNTTRadix2_16Proof.
require import NTRUPlus768InvNTTRadix2_16Algebra.
require import NTRUPlus768InvNTTRadix2_32Proof.
require import NTRUPlus768InvNTTRadix2_32Algebra.
require import NTRUPlus768InvNTTRadix2_64Proof.

import Ring.IntID IntOrder.

op block : int = 64.
op double_block : int = 128.
op nblocks : int = 6.

lemma invntt_radix2_64_proof_blockE :
  NTRUPlus768InvNTTRadix2_64Proof.block = block.
proof.
  by rewrite /NTRUPlus768InvNTTRadix2_64Proof.block /block.
qed.

op invntt_radix2_64_input_shape (p : W16.t Array768.t) : bool =
  forall j, 0 <= j < 768 => -q <= coeff p.[j] < q.

lemma invntt_radix2_64_input_shape_coeff
    (p : W16.t Array768.t) (j : int) :
  invntt_radix2_64_input_shape p =>
  0 <= j < 768 =>
  -q <= coeff p.[j] < q.
proof.
  by move=> Hshape Hj; rewrite /invntt_radix2_64_input_shape in Hshape; exact (Hshape j Hj).
qed.

lemma invntt_radix2_32_algebra_output_qrange
    (input output : W16.t Array768.t) (j : int) :
  NTRUPlus768InvNTTRadix2_32Algebra.invntt_radix2_32_algebra input output =>
  0 <= j < 768 =>
  -q <= coeff output.[j] < q.
proof.
  move=> Halg Hj.
  have Hjalg := Halg j Hj.
  move: Hjalg => [Hrange _].
  case (NTRUPlus768InvNTTRadix2_32Proof.invntt_radix2_32_block_offset j <
        NTRUPlus768InvNTTRadix2_32Proof.block).
  + rewrite NTRUPlus768InvNTTRadix2_32Algebra.invntt_radix2_32_proof_blockE /q /=.
    smt().
  smt().
qed.

lemma invntt_radix2_32_algebra_implies_invntt_radix2_64_input_shape
    (input output : W16.t Array768.t) :
  NTRUPlus768InvNTTRadix2_32Algebra.invntt_radix2_32_algebra input output =>
  invntt_radix2_64_input_shape output.
proof.
  move=> Halg.
  rewrite /invntt_radix2_64_input_shape.
  by move=> j Hj; exact (invntt_radix2_32_algebra_output_qrange input output j Halg Hj).
qed.

op invntt_radix2_64_schedule_index (b : int) : int =
  ntt_radix2_64_start + (nblocks - 1 - b).

op invntt_radix2_64_schedule_zetas : W16.t list =
  rev (map (fun c => W16.of_int c)
       (take ntt_radix2_64_count (drop ntt_radix2_64_start zetas192_coeffs))).

lemma size_invntt_radix2_64_schedule_chunk :
  size (take ntt_radix2_64_count (drop ntt_radix2_64_start zetas192_coeffs)) = nblocks.
proof.
  rewrite /ntt_radix2_64_count /ntt_radix2_64_start /nblocks.
  smt(size_take size_drop size_zetas192_coeffs).
qed.

lemma size_invntt_radix2_64_schedule_zetas :
  size invntt_radix2_64_schedule_zetas = nblocks.
proof.
  by rewrite /invntt_radix2_64_schedule_zetas size_rev size_map size_invntt_radix2_64_schedule_chunk.
qed.

lemma invntt_radix2_64_schedule_zetasE :
  NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_zetas =
  invntt_radix2_64_schedule_zetas.
proof.
  rewrite /invntt_radix2_64_schedule_zetas.
  rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_zetas.
  rewrite /ntt_radix2_64_start /ntt_radix2_64_count /nblocks /zetas192_coeffs /=.
  done.
qed.

lemma invntt_radix2_64_schedule_index_range (b : int) :
  0 <= b < nblocks =>
  ntt_radix2_64_start <= invntt_radix2_64_schedule_index b < ntt_radix2_32_start.
proof.
  move=> Hb.
  rewrite /invntt_radix2_64_schedule_index.
  rewrite /ntt_radix2_64_start /ntt_radix2_32_start /nblocks.
  smt().
qed.

lemma invntt_radix2_64_word_zeta_scheduleE (b : int) :
  0 <= b < nblocks =>
  NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_word_zeta b =
    W16.of_int (zetas192_coeff (invntt_radix2_64_schedule_index b)).
proof.
  move=> Hb.
  rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_word_zeta.
  rewrite invntt_radix2_64_schedule_zetasE.
  rewrite /invntt_radix2_64_schedule_zetas.
  have Hrev :
      nth witness
        (rev (map (fun c => W16.of_int c)
             (take ntt_radix2_64_count
               (drop ntt_radix2_64_start zetas192_coeffs)))) b =
      nth witness
        (map (fun c => W16.of_int c)
          (take ntt_radix2_64_count
            (drop ntt_radix2_64_start zetas192_coeffs)))
        (size (map (fun c => W16.of_int c)
          (take ntt_radix2_64_count
            (drop ntt_radix2_64_start zetas192_coeffs))) - (b + 1)).
  + apply nth_rev.
    rewrite size_map size_invntt_radix2_64_schedule_chunk.
    smt().
  rewrite Hrev.
  rewrite size_map size_invntt_radix2_64_schedule_chunk.
  have Hmap :
      nth witness
        (map (fun c => W16.of_int c)
          (take ntt_radix2_64_count
            (drop ntt_radix2_64_start zetas192_coeffs)))
        (6 - (b + 1)) =
      W16.of_int
        (nth witness
          (take ntt_radix2_64_count
            (drop ntt_radix2_64_start zetas192_coeffs))
          (6 - (b + 1))).
  + have Hidx :
        0 <= 6 - (b + 1) <
        size (take ntt_radix2_64_count
              (drop ntt_radix2_64_start zetas192_coeffs)).
    + rewrite size_invntt_radix2_64_schedule_chunk.
      move: Hb => [Hb0 Hb1].
      split.
      + smt().
      smt().
    exact (nth_map witness witness (fun c => W16.of_int c)
      (6 - (b + 1))
      (take ntt_radix2_64_count (drop ntt_radix2_64_start zetas192_coeffs)) Hidx).
  rewrite Hmap.
  have Htakeidx : 0 <= 6 - (b + 1) < nblocks by move: Hb; rewrite /nblocks; smt().
  rewrite nth_take.
  + by rewrite /ntt_radix2_64_count.
  + move: Htakeidx.
    rewrite /nblocks /ntt_radix2_64_count.
    smt().
  have Hdropidx : 0 <= 6 - (b + 1) by move: Hb; smt().
  have Hdrop :=
    nth_drop witness ntt_radix2_64_start zetas192_coeffs (6 - (b + 1)) _ Hdropidx.
  + by rewrite /ntt_radix2_64_start.
  rewrite Hdrop.
  rewrite /invntt_radix2_64_schedule_index /zetas192_coeff.
  have -> : 6 + (6 - (b + 1)) = 6 + (5 - b) by smt().
  done.
qed.

lemma invntt_radix2_64_zeta_coeffE (b : int) :
  0 <= b < nblocks =>
  coeff (NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_word_zeta b) =
    zetas192_coeff (invntt_radix2_64_schedule_index b).
proof.
  move=> Hb.
  rewrite (invntt_radix2_64_word_zeta_scheduleE b Hb) /coeff.
  have Hidx' := invntt_radix2_64_schedule_index_range b Hb.
  have Hidx : 0 <= invntt_radix2_64_schedule_index b < 192 by smt().
  have Hrange := zetas192_coeff_range (invntt_radix2_64_schedule_index b) Hidx.
  have Hsmall :
      W16.min_sint <= zetas192_coeff (invntt_radix2_64_schedule_index b) <=
      W16.max_sint.
  + move: Hrange.
    rewrite /q /=.
    smt().
  exact (W16.to_sintK_small _ Hsmall).
qed.

lemma invntt_radix2_64_zeta_in_qrange (b : int) :
  0 <= b < nblocks =>
  in_qrange (NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_word_zeta b).
proof.
  move=> Hb.
  have Hidx' := invntt_radix2_64_schedule_index_range b Hb.
  have Hidx : 0 <= invntt_radix2_64_schedule_index b < 192 by smt().
  have Hrange := zetas192_coeff_range (invntt_radix2_64_schedule_index b) Hidx.
  rewrite /in_qrange (invntt_radix2_64_zeta_coeffE b Hb).
  move: Hrange.
  smt().
qed.

op invntt_radix2_64_zeta_root (b : int) : int =
  (zeta_root ^ zetas192_exp (invntt_radix2_64_schedule_index b)) %% q.

lemma invntt_radix2_64_zeta_montgomery_meaning (b : int) :
  0 <= b < nblocks =>
  (coeff (NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_word_zeta b) * Rinv) %% q =
    invntt_radix2_64_zeta_root b.
proof.
  move=> Hb.
  have Hidx' := invntt_radix2_64_schedule_index_range b Hb.
  have Hidx : 0 <= invntt_radix2_64_schedule_index b < 192 by smt().
  have Hrel := zetas192_relation (invntt_radix2_64_schedule_index b) Hidx.
  rewrite /invntt_radix2_64_zeta_root.
  have -> :
      coeff (NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_word_zeta b) =
      zetas192_coeff (invntt_radix2_64_schedule_index b)
    by exact (invntt_radix2_64_zeta_coeffE b Hb).
  exact Hrel.
qed.

op invntt_radix2_64_pair_math (lo hi root : int) : int * int =
  (lo + hi, (hi - lo) * root).

op invntt_radix2_64_pair_math_at
    (p : W16.t Array768.t) (base : int) (root : int) (k : int)
    : int * int =
  invntt_radix2_64_pair_math
    (coeff p.[base + k])
    (coeff p.[base + k + block])
    root.

op invntt_radix2_64_math (p : W16.t Array768.t) (j : int) : int =
  let b = NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_block_id j in
  let base = NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_block_base b in
  let root = invntt_radix2_64_zeta_root b in
  let k = NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_lane_index j in
  if NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_block_offset j < block then
    (invntt_radix2_64_pair_math_at p base root k).`1
  else
    (invntt_radix2_64_pair_math_at p base root k).`2.

op invntt_radix2_64_algebra
    (input output : W16.t Array768.t) : bool =
  forall j, 0 <= j < 768 =>
    (if NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_block_offset j < block
     then -1728 <= coeff output.[j] <= 1728
     else -q <= coeff output.[j] < q) /\
    coeff output.[j] %% q = invntt_radix2_64_math input j %% q.

lemma invntt_radix2_64_block_id_range (j : int) :
  0 <= j < 768 =>
  0 <= NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_block_id j < nblocks.
proof.
  rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_block_id.
  rewrite /double_block /nblocks.
  smt().
qed.

lemma invntt_radix2_64_block_offset_range (j : int) :
  0 <= j < 768 =>
  0 <= NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_block_offset j < double_block.
proof.
  rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_block_offset.
  rewrite /double_block.
  smt().
qed.

lemma invntt_radix2_64_pair_algebra
    (z lo hi : W16.t) (root : int) :
  -q <= coeff lo < q =>
  -q <= coeff hi < q =>
  in_qrange z =>
  (coeff z * Rinv) %% q = root =>
  let out = NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_pair z lo hi in
    -1728 <= coeff out.`1 <= 1728 /\
    -q <= coeff out.`2 < q /\
    coeff out.`1 %% q = (coeff lo + coeff hi) %% q /\
    coeff out.`2 %% q = ((coeff hi - coeff lo) * root) %% q.
proof.
  move=> Hlo Hhi Hz Hroot out.
  pose diffw := hi - lo.
  have Hdiffw : coeff diffw = coeff hi - coeff lo.
  + rewrite /diffw.
    exact (coeff_sub_qrange hi lo Hhi Hlo).
  have Hdiffw_range : -2 * q <= coeff diffw < 2 * q.
  + rewrite Hdiffw /q.
    smt().
  have Hm : 0 < 2 <= 5 by smt().
  have Hmul :=
    invntt_radix2_4_mul_algebra z diffw root 2 Hm Hz Hdiffw_range Hroot.
  have Hsum : coeff (lo + hi) = coeff lo + coeff hi.
  + exact (coeff_add_qrange lo hi Hlo Hhi).
  have Hsum_range : -2 * q <= coeff (lo + hi) < 2 * q.
  + rewrite Hsum /q.
    smt().
  have Hsum_small : -6 * q <= coeff (lo + hi) < 6 * q
    by move: Hsum_range; smt().
  have Hbar_sum :=
    invntt_radix2_4_barrett_reduce_small (lo + hi) Hsum_small.
  have Hsum_congr :
      coeff (lo + hi) %% q = (coeff lo + coeff hi) %% q.
  + rewrite Hsum.
    done.
  have Hmul_range :
      -q <= coeff (NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_mul z diffw) < q.
  + move: Hmul.
    rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_mul
            /NTRUPlus768InvNTTRadix2_4Proof.invntt_radix2_4_mul.
    smt().
  have Hmul_congr :
      coeff (NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_mul z diffw) %% q =
      ((coeff hi - coeff lo) * root) %% q.
  + move: Hmul.
    rewrite Hdiffw.
    rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_mul
            /NTRUPlus768InvNTTRadix2_4Proof.invntt_radix2_4_mul.
    smt().
  move: Hbar_sum Hmul_range Hmul_congr.
  rewrite /out /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_pair /=.
  move=> [Hsum_eq [Hsum_rng Hsum_mod]] Hout2_rng Hout2_mod.
  split; first exact Hsum_rng.
  split; first exact Hout2_rng.
  split.
  + rewrite Hsum_mod Hsum_congr.
    done.
  exact Hout2_mod.
qed.

lemma invntt_radix2_64_spec_algebra (p : W16.t Array768.t) :
  invntt_radix2_64_input_shape p =>
  invntt_radix2_64_algebra p (NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_spec p).
proof.
  move=> Hshape j Hj.
  pose b := NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_block_id j.
  pose r := NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_block_offset j.
  pose base := NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_block_base b.
  pose z := NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_word_zeta b.
  pose root := invntt_radix2_64_zeta_root b.
  pose k := NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_lane_index j.
  have Hb : 0 <= b < nblocks by rewrite /b; exact (invntt_radix2_64_block_id_range j Hj).
  have Hr : 0 <= r < double_block by rewrite /r; exact (invntt_radix2_64_block_offset_range j Hj).
  have Hdiv := divz_eq j double_block.
  rewrite /invntt_radix2_64_algebra.
  rewrite /r /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_block_offset.
  case (j %% 128 < block) => Hrlo.
  + have Hk : 0 <= k < block.
    + move: Hr Hrlo.
      rewrite /k /r /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_lane_index.
      rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_block_offset.
      rewrite /double_block /block.
      smt().
    have Hbasek : base + k = j.
    + move: Hdiv Hr Hrlo.
      rewrite /base /b /k.
      rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_block_base.
      rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_block_id.
      rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_lane_index.
      rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_block_offset.
      rewrite /double_block /block.
      smt().
    have Hbasek_hi : base + k + block = j + block by rewrite Hbasek.
    have Hlo : -q <= coeff p.[j] < q
      by exact (invntt_radix2_64_input_shape_coeff p j Hshape Hj).
    have Hj_hi : 0 <= j + block < 768.
    + move: Hr Hrlo.
      rewrite /r /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_block_offset.
      rewrite /double_block /block.
      smt().
    have Hhi : -q <= coeff p.[j + block] < q
      by exact (invntt_radix2_64_input_shape_coeff p (j + block) Hshape Hj_hi).
    have Hlo_base : -q <= coeff p.[base + k] < q by rewrite Hbasek.
    have Hhi_base : -q <= coeff p.[base + k + block] < q by rewrite Hbasek_hi.
    have Hpair :=
      invntt_radix2_64_pair_algebra z p.[base + k] p.[base + k + block] root
        Hlo_base Hhi_base
        (invntt_radix2_64_zeta_in_qrange b Hb)
        (invntt_radix2_64_zeta_montgomery_meaning b Hb).
    have Hspecj :
        (NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_spec p).[j] =
        (NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_pair_at p base z k).`1.
    + rewrite (NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_spec_get p j Hj).
      rewrite /base /z /k /b.
      rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_block_base.
      rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_lane_index.
      rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_block_id.
      rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_block_offset.
      smt().
    have [Hrng0 [Hrng1 [Hcong0 Hcong1]]] := Hpair.
    rewrite Hspecj.
    split.
    + move: Hrng0.
      rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_pair_at.
      rewrite invntt_radix2_64_proof_blockE.
      rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_pair.
      smt().
    rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_pair_at.
    rewrite invntt_radix2_64_proof_blockE.
    rewrite /invntt_radix2_64_math /root /k /base /b.
    rewrite /invntt_radix2_64_pair_math_at /invntt_radix2_64_pair_math.
    rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_block_id.
    rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_block_base.
    rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_lane_index Hrlo.
    move: Hcong0.
    rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_pair.
    done.
  have Hk : 0 <= k < block.
  + move: Hr Hrlo.
    rewrite /k /r /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_lane_index.
    rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_block_offset.
    rewrite /double_block /block.
    smt().
  have Hbasek : base + k = j - block.
  + move: Hdiv Hr Hrlo.
    rewrite /base /b /k.
    rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_block_base.
    rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_block_id.
    rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_lane_index.
    rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_block_offset.
    rewrite /double_block /block.
    smt().
  have Hbasek_hi : base + k + block = j by smt().
  have Hj_lo : 0 <= j - block < 768.
  + move: Hr Hrlo Hj.
    rewrite /r /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_block_offset.
    rewrite /double_block /block.
    smt().
  have Hlo : -q <= coeff p.[j - block] < q
    by exact (invntt_radix2_64_input_shape_coeff p (j - block) Hshape Hj_lo).
  have Hhi : -q <= coeff p.[j] < q
    by exact (invntt_radix2_64_input_shape_coeff p j Hshape Hj).
  have Hlo_base : -q <= coeff p.[base + k] < q by rewrite Hbasek.
  have Hhi_base : -q <= coeff p.[base + k + block] < q by rewrite Hbasek_hi.
  have Hpair :=
    invntt_radix2_64_pair_algebra z p.[base + k] p.[base + k + block] root
      Hlo_base Hhi_base
      (invntt_radix2_64_zeta_in_qrange b Hb)
      (invntt_radix2_64_zeta_montgomery_meaning b Hb).
  have Hspecj :
      (NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_spec p).[j] =
      (NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_pair_at p base z k).`2.
  + rewrite (NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_spec_get p j Hj).
    rewrite /base /z /k /b.
    rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_block_base.
    rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_lane_index.
    rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_block_id.
    rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_block_offset.
    smt().
  have [Hrng0 [Hrng1 [Hcong0 Hcong1]]] := Hpair.
  rewrite Hspecj.
  split.
  + move: Hrng1.
    rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_pair_at.
    rewrite invntt_radix2_64_proof_blockE.
    rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_pair.
    smt().
  rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_pair_at.
  rewrite invntt_radix2_64_proof_blockE.
  rewrite /invntt_radix2_64_math /root /k /base /b.
  rewrite /invntt_radix2_64_pair_math_at /invntt_radix2_64_pair_math.
  rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_block_id.
  rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_block_base.
  rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_lane_index Hrlo.
  move: Hcong1.
  rewrite /NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_pair.
  done.
qed.

lemma invntt_radix2_64_from_invntt_radix2_32_algebra
    (input mid : W16.t Array768.t) :
  NTRUPlus768InvNTTRadix2_32Algebra.invntt_radix2_32_algebra input mid =>
  invntt_radix2_64_algebra mid (NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_spec mid).
proof.
  move=> H32.
  apply invntt_radix2_64_spec_algebra.
  exact (invntt_radix2_32_algebra_implies_invntt_radix2_64_input_shape input mid H32).
qed.

lemma invntt_radix2_64_algebra_functional
    (rp0 : W16.t Array768.t) :
  invntt_radix2_64_input_shape rp0 =>
  hoare [NTRUPlus768InvNTTRadix2_64.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_64 :
    rp = rp0 ==> invntt_radix2_64_algebra rp0 res].
proof.
  move=> Hshape.
  conseq (NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_functional rp0) => />.
  exact (invntt_radix2_64_spec_algebra rp0 Hshape).
qed.

lemma invntt_radix2_64_correct_algebra
    (rp0 : W16.t Array768.t) :
  invntt_radix2_64_input_shape rp0 =>
  phoare [NTRUPlus768InvNTTRadix2_64.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_64 :
    rp = rp0 ==> invntt_radix2_64_algebra rp0 res] = 1%r.
proof.
  move=> Hshape.
  have Hfunctional := invntt_radix2_64_algebra_functional rp0 Hshape.
  by conseq NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_lossless Hfunctional.
qed.
