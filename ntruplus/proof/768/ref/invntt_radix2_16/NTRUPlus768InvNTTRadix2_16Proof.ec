require import AllCore IntDiv Ring StdOrder Distr List.
from Jasmin require import JWord JModel_x86.

require import Array768 WArray1536 NTRUPlus768InvNTTRadix2_16.
require import NTRUPlus768BasemulProof.

op block : int = 16.
op double_block : int = 32.
op nblocks : int = 24.

op invntt_radix2_16_zetas : W16.t list = [
  W16.of_int 1058; W16.of_int (-1105); W16.of_int 1713; W16.of_int (-603);
  W16.of_int 387; W16.of_int 893; W16.of_int 937; W16.of_int (-348);
  W16.of_int (-757); W16.of_int (-121); W16.of_int (-216); W16.of_int (-820);
  W16.of_int 39; W16.of_int (-44); W16.of_int 550; W16.of_int (-1241);
  W16.of_int (-1577); W16.of_int 95; W16.of_int 541; W16.of_int (-699);
  W16.of_int 655; W16.of_int 502; W16.of_int 639; W16.of_int (-455)
].

op valid_base (base : int) : bool =
  exists k, 0 <= k < nblocks /\ base = double_block * k.

op barrett_reduce (a : W16.t) : W16.t =
  let td = sigextu32 a * W32.of_int 19412 in
  let td = td + W32.of_int 33554432 in
  let t = truncateu16 (td `|>>` W8.of_int 26) in
  let td = sigextu32 t * W32.of_int 3457 in
  let t = truncateu16 td in
  a - t.

op invntt_radix2_16_mul (z a : W16.t) : W16.t =
  montgomery_reduce (mul_i16 z a).

op invntt_radix2_16_pair (z lo hi : W16.t) : W16.t * W16.t =
  (barrett_reduce (lo + hi), invntt_radix2_16_mul z (hi - lo)).

op invntt_radix2_16_word_zeta (b : int) : W16.t =
  nth witness invntt_radix2_16_zetas b.

op invntt_radix2_16_pair_at
    (p : W16.t Array768.t) (base : int) (z : W16.t) (k : int)
    : W16.t * W16.t =
  invntt_radix2_16_pair z p.[base + k] p.[base + k + block].

op invntt_radix2_16_prefix_spec
    (p : W16.t Array768.t) (base upto : int) (z : W16.t)
    : W16.t Array768.t =
  Array768.init (fun j =>
    if base <= j < base + upto then
      (invntt_radix2_16_pair_at p base z (j - base)).`1
    else if base + block <= j < base + block + upto then
      (invntt_radix2_16_pair_at p base z (j - base - block)).`2
    else p.[j]).

op invntt_radix2_16_block_spec
    (p : W16.t Array768.t) (base : int) (z : W16.t)
    : W16.t Array768.t =
  invntt_radix2_16_prefix_spec p base block z.

op invntt_radix2_16_block_id (j : int) : int = j %/ double_block.
op invntt_radix2_16_block_offset (j : int) : int = j %% double_block.
op invntt_radix2_16_block_base (b : int) : int = double_block * b.
op invntt_radix2_16_lane_index (j : int) : int =
  let r = invntt_radix2_16_block_offset j in if r < block then r else r - block.

op invntt_radix2_16_word_indexed_spec (p : W16.t Array768.t) : W16.t Array768.t =
  Array768.init (fun j =>
    let b = invntt_radix2_16_block_id j in
    let base = invntt_radix2_16_block_base b in
    let z = invntt_radix2_16_word_zeta b in
    let k = invntt_radix2_16_lane_index j in
    if invntt_radix2_16_block_offset j < block then
      (invntt_radix2_16_pair_at p base z k).`1
    else
      (invntt_radix2_16_pair_at p base z k).`2).

op invntt_radix2_16_word_apply_block
    (p : W16.t Array768.t) (b : int) : W16.t Array768.t =
  invntt_radix2_16_block_spec
    p (invntt_radix2_16_block_base b) (invntt_radix2_16_word_zeta b).

op invntt_radix2_16_word_fold (p : W16.t Array768.t) (n : int) : W16.t Array768.t =
  foldl invntt_radix2_16_word_apply_block p (range 0 n).

op invntt_radix2_16_spec (p : W16.t Array768.t) : W16.t Array768.t =
  invntt_radix2_16_word_indexed_spec p.

lemma invntt_radix2_16_mul_i16_functional (a0 b0 : W16.t) :
  hoare [NTRUPlus768InvNTTRadix2_16.M.__mul_i16 :
    a = a0 /\ b = b0 ==> res = mul_i16 a0 b0].
proof.
  proc; auto => />.
qed.

lemma invntt_radix2_16_montgomery_reduce_functional (a0 : W32.t) :
  hoare [NTRUPlus768InvNTTRadix2_16.M.__montgomery_reduce :
    a = a0 ==> res = montgomery_reduce a0].
proof.
  proc; auto => />.
qed.

lemma invntt_radix2_16_barrett_reduce_functional (a0 : W16.t) :
  hoare [NTRUPlus768InvNTTRadix2_16.M.__barrett_reduce :
    a = a0 ==> res = barrett_reduce a0].
proof.
  proc; auto => />.
qed.

lemma invntt_radix2_16_spec_get (p : W16.t Array768.t) (j : int) :
  0 <= j < 768 =>
  (invntt_radix2_16_spec p).[j] =
    let b = invntt_radix2_16_block_id j in
    let base = invntt_radix2_16_block_base b in
    let z = invntt_radix2_16_word_zeta b in
    let k = invntt_radix2_16_lane_index j in
    if invntt_radix2_16_block_offset j < block then
      (invntt_radix2_16_pair_at p base z k).`1
    else
      (invntt_radix2_16_pair_at p base z k).`2.
proof.
  move=> Hj.
  rewrite /invntt_radix2_16_spec /invntt_radix2_16_word_indexed_spec.
  by rewrite Array768.initiE.
qed.

lemma valid_base_bounds (base : int) :
  valid_base base => 0 <= base /\ base + double_block <= 768.
proof.
  rewrite /valid_base /double_block /nblocks.
  smt().
qed.

lemma valid_base_to_uint (base : int) :
  valid_base base => W64.to_uint (W64.of_int base) = base.
proof.
  move=> Hvalid.
  rewrite W64.to_uintK_small 1:/#.
  have [Hbase Hbound] := valid_base_bounds base Hvalid.
  rewrite /double_block in Hbound.
  smt(W64.to_uint_cmp).
qed.

lemma valid_base_stop_to_uint (base : int) :
  valid_base base =>
  W64.to_uint (W64.of_int base + W64.of_int block) = base + block.
proof.
  move=> Hvalid.
  rewrite W64.to_uintD (valid_base_to_uint base Hvalid) /block /=.
  have [Hbase Hbound] := valid_base_bounds base Hvalid.
  rewrite /double_block in Hbound.
  rewrite modz_small; smt(W64.to_uint_cmp).
qed.

lemma invntt_radix2_16_modz_sub_dvd (u m d : int) :
  m %% d = 0 => (u - m) %% d = u %% d.
proof.
  move=> Hmd.
  have Hneg : (-m) %% d = 0.
  + apply/dvdzE; apply dvdzN; apply/dvdzE; exact Hmd.
  rewrite (_ : u - m = u + (-m)) 1:/#.
  by rewrite -modzDmr Hneg /=.
qed.

lemma invntt_radix2_16_w16_of_sintK (w : W16.t) :
  W16.of_int (W16.to_sint w) = w.
proof.
  apply W16.to_uint_eq.
  rewrite W16.of_uintK W16.to_sintE /W16.smod.
  case (2 ^ (16 - 1) <= W16.to_uint w) => Hsign.
  + rewrite (invntt_radix2_16_modz_sub_dvd
      (W16.to_uint w) W16.modulus W16.modulus).
    - by rewrite modzz.
    by rewrite W16.to_uint_mod.
  by rewrite W16.to_uint_mod.
qed.

lemma invntt_radix2_16_truncateu16_of_int (x : int) :
  truncateu16 (W32.of_int x) = W16.of_int x.
proof.
  apply W16.to_uint_eq.
  rewrite /truncateu16 /= W16.of_uintK W32.of_uintK W16.of_uintK.
  rewrite modz_dvd.
  + apply/dvdzP; exists 65536; ring.
  done.
qed.

lemma invntt_radix2_16_truncate_sigext_add (x y : W16.t) :
  truncateu16 (sigextu32 x + sigextu32 y) = x + y.
proof.
  rewrite /sigextu32 /=.
  rewrite invntt_radix2_16_truncateu16_of_int W16.of_intD.
  by rewrite !invntt_radix2_16_w16_of_sintK.
qed.

lemma invntt_radix2_16_truncate_sigext_sub (x y : W16.t) :
  truncateu16 (sigextu32 x - sigextu32 y) = x - y.
proof.
  rewrite /sigextu32 /=.
  rewrite invntt_radix2_16_truncateu16_of_int W16.of_intS.
  by rewrite !invntt_radix2_16_w16_of_sintK.
qed.

lemma invntt_radix2_16_prefix_zero
    (p : W16.t Array768.t) (base : int) (z : W16.t) :
  0 <= base <= 768 =>
  invntt_radix2_16_prefix_spec p base 0 z = p.
proof.
  move=> Hbase.
  apply Array768.tP => j Hj.
  rewrite /invntt_radix2_16_prefix_spec Array768.initiE 1:Hj.
  smt().
qed.

lemma invntt_radix2_16_prefix_curr0
    (p : W16.t Array768.t) (base upto : int) (z : W16.t) :
  0 <= base =>
  0 <= upto < block =>
  base + block + upto < 768 =>
  (invntt_radix2_16_prefix_spec p base upto z).[base + upto] =
    p.[base + upto].
proof.
  move=> Hbase Hupto Hbound.
  rewrite /invntt_radix2_16_prefix_spec Array768.initiE 1:/#.
  smt().
qed.

lemma invntt_radix2_16_prefix_curr1
    (p : W16.t Array768.t) (base upto : int) (z : W16.t) :
  0 <= base =>
  0 <= upto < block =>
  base + block + upto < 768 =>
  (invntt_radix2_16_prefix_spec p base upto z).[base + block + upto] =
    p.[base + block + upto].
proof.
  move=> Hbase Hupto Hbound.
  rewrite /invntt_radix2_16_prefix_spec Array768.initiE 1:/#.
  smt().
qed.

lemma invntt_radix2_16_prefix_step
    (p : W16.t Array768.t) (base upto : int) (z : W16.t) :
  0 <= base =>
  0 <= upto < block =>
  base + block + upto < 768 =>
  (invntt_radix2_16_prefix_spec p base upto z)
    .[base + upto <- (invntt_radix2_16_pair_at p base z upto).`1]
    .[base + block + upto <- (invntt_radix2_16_pair_at p base z upto).`2] =
  invntt_radix2_16_prefix_spec p base (upto + 1) z.
proof.
  move=> Hbase Hupto Hbound.
  apply Array768.tP => j Hj.
  rewrite /invntt_radix2_16_prefix_spec.
  rewrite Array768.initiE 1:Hj.
  case (j = base + upto) => [-> | Hneq0].
  + by rewrite !Array768.get_setE; smt().
  case (j = base + block + upto) => [-> | Hneq1].
  + by rewrite !Array768.get_setE; smt().
  rewrite !Array768.get_setE.
  + smt().
  + smt().
  rewrite Array768.initiE 1:Hj.
  smt().
qed.

lemma invntt_radix2_16_block_functional
    (rp0 : W16.t Array768.t) (base0 : int) (z0 : W16.t) :
  valid_base base0 =>
  hoare [NTRUPlus768InvNTTRadix2_16.M.__invntt_radix2_16_block :
    rp = rp0 /\ base = W64.of_int base0 /\ zeta_0 = z0 ==>
    res = invntt_radix2_16_block_spec rp0 base0 z0].
proof.
  move=> Hvalid.
  have [Hbase Hbound] := valid_base_bounds base0 Hvalid.
  proc.
  seq 3 :
    (rp = invntt_radix2_16_prefix_spec rp0 base0 0 z0 /\
     i = W64.of_int base0 /\
     stop = W64.of_int base0 + W64.of_int block /\
     zeta_0 = z0).
  + auto => />.
    rewrite invntt_radix2_16_prefix_zero 1:/# /block.
    smt().
  while (base0 <= W64.to_uint i <= base0 + block /\
         stop = W64.of_int base0 + W64.of_int block /\
         zeta_0 = z0 /\
         rp = invntt_radix2_16_prefix_spec rp0 base0
                (W64.to_uint i - base0) z0); last first.
  + skip => &hr [Hrp [Hi [Hstop Hzeta]]].
    split.
    + split.
      - rewrite Hi W64.to_uintK_small 1:/#.
        smt(W64.to_uint_cmp).
      split; first exact Hstop.
      split; first exact Hzeta.
      rewrite Hrp.
      rewrite Hi W64.to_uintK_small 1:/#.
      smt().
    move=> i1 rp1 Hexit [Hi1 [_ [_ Hrp1]]].
    rewrite W64.ultE /= Hstop
      (valid_base_stop_to_uint base0 Hvalid) in Hexit.
    have Hiend : W64.to_uint i1 = base0 + block by smt().
    rewrite /invntt_radix2_16_block_spec.
    smt().
  inline NTRUPlus768InvNTTRadix2_16.M.__mul_i16
         NTRUPlus768InvNTTRadix2_16.M.__montgomery_reduce
         NTRUPlus768InvNTTRadix2_16.M.__barrett_reduce.
  auto => /> &hr Hi Hrp Hloop.
  rewrite W64.ultE /= in Hloop.
  rewrite (valid_base_stop_to_uint base0 Hvalid) in Hloop.
  have Hidx : 0 <= W64.to_uint i{hr} - base0 < block by smt().
  have Hcurri : W64.to_uint i{hr} = base0 + (W64.to_uint i{hr} - base0)
    by smt().
  have Hget0 :
      (invntt_radix2_16_prefix_spec rp0 base0
        (W64.to_uint i{hr} - base0) z0).[W64.to_uint i{hr}] =
      rp0.[W64.to_uint i{hr}].
  + have Hcurr := invntt_radix2_16_prefix_curr0 rp0 base0
        (W64.to_uint i{hr} - base0) z0 _ _ _; 1,2,3: smt().
    move: Hcurr.
    by rewrite -Hcurri.
  have Hget1 :
      (invntt_radix2_16_prefix_spec rp0 base0
        (W64.to_uint i{hr} - base0) z0).[W64.to_uint i{hr} + block] =
      rp0.[W64.to_uint i{hr} + block].
  + have Hcurr := invntt_radix2_16_prefix_curr1 rp0 base0
        (W64.to_uint i{hr} - base0) z0 _ _ _; 1,2,3: smt().
    have Hcurri1 :
        W64.to_uint i{hr} + block =
        base0 + block + (W64.to_uint i{hr} - base0) by smt().
    move: Hcurr.
    by rewrite -Hcurri1.
  have Hnext : W64.to_uint (i{hr} + W64.one) - base0 =
      (W64.to_uint i{hr} - base0) + 1.
  + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  have Haddr : W64.to_uint (i{hr} + W64.of_int block) =
      W64.to_uint i{hr} + block.
  + rewrite W64.to_uintD_small /= /block; smt(W64.to_uint_cmp).
  have Hspec_addr :
      base0 + block + (W64.to_uint i{hr} - base0) =
      W64.to_uint i{hr} + block by smt().
  have Hstep := invntt_radix2_16_prefix_step rp0 base0
      (W64.to_uint i{hr} - base0) z0 _ _ _; 1,2,3: smt().
  split.
  + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  rewrite Hnext.
  rewrite -Hstep.
  rewrite /invntt_radix2_16_pair_at /invntt_radix2_16_pair
    /invntt_radix2_16_mul /block.
  rewrite Hget0 Haddr Hget1.
  rewrite -Hcurri Hspec_addr.
  rewrite !invntt_radix2_16_truncate_sigext_add
          !invntt_radix2_16_truncate_sigext_sub.
  rewrite /barrett_reduce /mul_i16 /montgomery_reduce /=.
  done.
qed.

lemma invntt_radix2_16_block_lossless :
  islossless NTRUPlus768InvNTTRadix2_16.M.__invntt_radix2_16_block.
proof.
  proc.
  while (stop = base + W64.of_int block)
        (W64.to_uint stop - W64.to_uint i); last first.
  + auto => /> &hr i0 Hstop Hdone.
    rewrite W64.ultE /=.
    smt().
  move=> *.
  inline NTRUPlus768InvNTTRadix2_16.M.__mul_i16
         NTRUPlus768InvNTTRadix2_16.M.__montgomery_reduce
         NTRUPlus768InvNTTRadix2_16.M.__barrett_reduce.
  auto => /> &hr Hloop.
  rewrite W64.ultE /= in Hloop.
  have Hstop_bound :
      W64.to_uint (base{hr} + W64.of_int block) < W64.modulus.
  + have [_ Hbound] := W64.to_uint_cmp
      (base{hr} + W64.of_int block).
    exact Hbound.
  have Hsmall :
      W64.to_uint i{hr} + W64.to_uint W64.one < W64.modulus.
  + rewrite /=.
    rewrite /= in Hstop_bound.
    smt().
  have Hnext : W64.to_uint (i{hr} + W64.one) =
      W64.to_uint i{hr} + 1.
  + by rewrite (W64.to_uintD_small i{hr} W64.one Hsmall) /=.
  rewrite Hnext.
  smt().
qed.

lemma invntt_radix2_16_fold_predecessor_bound (m : int) :
  0 <= m => 0 <= m + 1 <= nblocks => 0 <= m <= nblocks.
proof.
  rewrite /nblocks.
  move=> Hm Hnext.
  smt().
qed.

lemma invntt_radix2_16_high_lane_bounds (j m : int) :
  0 <= j < 768 =>
  0 <= m + 1 <= nblocks =>
  j %/ double_block = m =>
  ! (j %% double_block < block) =>
  0 <= double_block * m +
         (j - double_block * m - block) < 768 /\
  0 <= double_block * m +
         (j - double_block * m - block) + block < 768.
proof.
  rewrite /nblocks /double_block /block.
  move=> [Hj0 Hj1] [Hm0 Hm1] Hblock Hhigh.
  have Hr := divz_eq j 32.
  have Hmnonneg : 0 <= m.
  + rewrite -Hblock (divz_ge0 j 32) 1:/#.
    exact Hj0.
  have Hr16 : 16 <= j %% 32.
  + by rewrite lezNgt.
  rewrite Hblock in Hr.
  have Hmul0 : 0 <= m * 32 by smt().
  have Hj16 : 16 <= j.
  + rewrite Hr.
    apply (lez_trans (j %% 32)).
    + exact Hr16.
    by rewrite lez_addr.
  have Heq0 : 32 * m + (j - 32 * m - 16) = j - 16 by ring.
  have Heq1 : j - 16 + 16 = j by ring.
  rewrite Heq0 Heq1.
  split.
  + split.
    + by rewrite subz_ge0.
    + smt().
  + smt().
qed.

lemma invntt_radix2_16_word_fold_get
    (p : W16.t Array768.t) (n : int) :
  forall j,
    0 <= n <= nblocks =>
    0 <= j < 768 =>
    (invntt_radix2_16_word_fold p n).[j] =
      if invntt_radix2_16_block_id j < n
      then (invntt_radix2_16_word_indexed_spec p).[j]
      else p.[j].
proof.
  elim/natind: n.
  + move=> n Hn j Hbound Hj.
    rewrite /invntt_radix2_16_word_fold range_geq 1:Hn /=.
    smt().
  + move=> m Hm IH j Hnext Hj.
    have Hm_bound := invntt_radix2_16_fold_predecessor_bound m Hm Hnext.
    rewrite /invntt_radix2_16_word_fold rangeSr 1:Hm foldl_rcons /=.
    rewrite /invntt_radix2_16_word_apply_block.
    rewrite /invntt_radix2_16_block_spec /invntt_radix2_16_prefix_spec.
    rewrite Array768.initiE 1:Hj.
    case (invntt_radix2_16_block_id j = m) => Hblock.
    + have Hr := divz_eq j double_block.
      have Hrem : 0 <= j %% double_block < double_block.
      + rewrite /double_block; smt().
      rewrite /invntt_radix2_16_word_indexed_spec Array768.initiE 1:Hj.
      rewrite /invntt_radix2_16_block_id /double_block /block in Hblock.
      rewrite /double_block /block in Hr.
      rewrite /double_block /block in Hrem.
      rewrite /invntt_radix2_16_block_base
        /invntt_radix2_16_block_id
        /invntt_radix2_16_block_offset
        /invntt_radix2_16_lane_index
        /double_block /block.
      case (j %% 32 < 16) => Hlow.
      + have Hj0 : 0 <= 32 * m + (j - 32 * m) < 768 by smt().
        have Hj1 : 0 <= 32 * m + (j - 32 * m) + block < 768.
        + rewrite /block; smt().
        rewrite /invntt_radix2_16_pair_at.
        have Hprev0 := IH (32 * m + (j - 32 * m)) Hm_bound Hj0.
        have Hprev1 := IH (32 * m + (j - 32 * m) + block) Hm_bound Hj1.
        rewrite /invntt_radix2_16_word_fold
          /invntt_radix2_16_word_apply_block
          /invntt_radix2_16_block_base /invntt_radix2_16_block_id
          /double_block in Hprev0.
        rewrite /invntt_radix2_16_word_fold
          /invntt_radix2_16_word_apply_block
          /invntt_radix2_16_block_base /invntt_radix2_16_block_id
          /double_block in Hprev1.
        rewrite (_ : 32 * m + (j - 32 * m) = m * 32 + j %% 32) 1:/#
          divzMDl 1:/# divz_small 1:/# /= in Hprev0.
        rewrite /block in Hprev1.
        rewrite (_ : 32 * m + (j - 32 * m) + 16 =
                     m * 32 + (j %% 32 + 16)) 1:/#
          divzMDl 1:/# divz_small 1:/# /= in Hprev1.
        rewrite (_ : m * 32 + (j %% 32 + 16) =
                     m * 32 + j %% 32 + 16) 1:/# in Hprev1.
        rewrite /block.
        rewrite (_ : 32 * m + (j - 32 * m) = m * 32 + j %% 32) 1:/#.
        rewrite Hprev0.
        rewrite Hprev1.
        rewrite Hblock Hlow /=.
        clear Hprev0 Hprev1 IH.
        have Hfirst : 32 * m <= j < 32 * m + 16 by smt().
        have Hsecond : ! (32 * m + 16 <= j < 32 * m + 32) by smt().
        have Hsucc : m < m + 1 by smt().
        rewrite Hfirst Hsecond Hsucc /=.
        congr.
        smt().
      have [Hj0 Hj1] := invntt_radix2_16_high_lane_bounds
        j m Hj Hnext Hblock Hlow.
      rewrite /invntt_radix2_16_pair_at.
      have Hprev0 := IH
        (32 * m + (j - 32 * m - block)) Hm_bound Hj0.
      have Hprev1 := IH
        (32 * m + (j - 32 * m - block) + block) Hm_bound Hj1.
      rewrite /invntt_radix2_16_word_fold
        /invntt_radix2_16_word_apply_block
        /invntt_radix2_16_block_base /invntt_radix2_16_block_id
        /double_block in Hprev0.
      rewrite /invntt_radix2_16_word_fold
        /invntt_radix2_16_word_apply_block
        /invntt_radix2_16_block_base /invntt_radix2_16_block_id
        /double_block in Hprev1.
      rewrite /block in Hprev0.
      rewrite /block in Hprev1.
      rewrite (_ : 32 * m + (j - 32 * m - 16) =
                   m * 32 + (j %% 32 - 16)) 1:/#
        divzMDl 1:/# divz_small 1:/# /= in Hprev0.
      rewrite (_ : 32 * m + (j - 32 * m - 16) + 16 =
                   m * 32 + j %% 32) 1:/#
        divzMDl 1:/# divz_small 1:/# /= in Hprev1.
      rewrite /block.
      rewrite (_ : 32 * m + (j - 32 * m - 16) =
                   m * 32 + (j %% 32 - 16)) 1:/#.
      rewrite (_ : m * 32 + (j %% 32 - 16) + 16 =
                   m * 32 + j %% 32) 1:/#.
      rewrite Hprev0.
      rewrite Hprev1.
      rewrite Hblock Hlow /=.
      clear Hprev0 Hprev1 IH.
      have Hfirst : ! (32 * m <= j < 32 * m + 16) by smt().
      have Hsecond : 32 * m + 16 <= j < 32 * m + 32 by smt().
      have Hsucc : m < m + 1 by smt().
      rewrite Hfirst Hsecond Hsucc /=.
      congr; smt().
    have Hprev := IH j Hm_bound Hj.
    rewrite /invntt_radix2_16_block_id /double_block in Hprev.
    rewrite Hprev /double_block /block.
    smt().
qed.

lemma invntt_radix2_16_word_fold_full (p : W16.t Array768.t) :
  invntt_radix2_16_word_fold p nblocks = invntt_radix2_16_spec p.
proof.
  apply Array768.tP => j Hj.
  have Hget := invntt_radix2_16_word_fold_get p nblocks j _ Hj.
  + by rewrite /nblocks.
  rewrite Hget /invntt_radix2_16_block_id /double_block /nblocks.
  smt().
qed.


lemma invntt_radix2_16_word_fold_step
    (p : W16.t Array768.t) (n : int) :
  0 <= n =>
  invntt_radix2_16_word_apply_block
    (invntt_radix2_16_word_fold p n) n =
  invntt_radix2_16_word_fold p (n + 1).
proof.
  move=> Hn.
  rewrite /invntt_radix2_16_word_fold rangeSr 1:Hn foldl_rcons /=.
  done.
qed.

lemma invntt_radix2_16_word_fold_zero (p : W16.t Array768.t) :
  invntt_radix2_16_word_fold p 0 = p.
proof.
  by rewrite /invntt_radix2_16_word_fold range_geq.
qed.

lemma invntt_radix2_16_fold_block_functional
    (p : W16.t Array768.t) (b base0 : int) (z0 : W16.t) :
  0 <= b < nblocks =>
  base0 = invntt_radix2_16_block_base b =>
  z0 = invntt_radix2_16_word_zeta b =>
  hoare [NTRUPlus768InvNTTRadix2_16.M.__invntt_radix2_16_block :
    rp = invntt_radix2_16_word_fold p b /\
    base = W64.of_int base0 /\
    zeta_0 = z0 ==>
    res = invntt_radix2_16_word_fold p (b + 1)].
proof.
  move=> Hb Hbase Hzeta.
  have Hvalid : valid_base base0.
  + rewrite /valid_base.
    exists b.
    rewrite Hbase /invntt_radix2_16_block_base.
    smt().
  conseq (invntt_radix2_16_block_functional
    (invntt_radix2_16_word_fold p b) base0 z0 Hvalid) => />.
  rewrite Hbase Hzeta.
  have Hstep := invntt_radix2_16_word_fold_step p b _.
  + smt().
  rewrite /invntt_radix2_16_word_apply_block in Hstep.
  smt().
qed.

lemma invntt_radix2_16_fold_functional
    (rp0 : W16.t Array768.t) :
  hoare [
    NTRUPlus768InvNTTRadix2_16.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_16 :
    rp = rp0 ==>
    res = invntt_radix2_16_word_fold rp0 nblocks].
proof.
  proc.
  call (invntt_radix2_16_fold_block_functional
    rp0 23 736 (W16.of_int (-455)) _ _ _).
  call (invntt_radix2_16_fold_block_functional
    rp0 22 704 (W16.of_int 639) _ _ _).
  call (invntt_radix2_16_fold_block_functional
    rp0 21 672 (W16.of_int 502) _ _ _).
  call (invntt_radix2_16_fold_block_functional
    rp0 20 640 (W16.of_int 655) _ _ _).
  call (invntt_radix2_16_fold_block_functional
    rp0 19 608 (W16.of_int (-699)) _ _ _).
  call (invntt_radix2_16_fold_block_functional
    rp0 18 576 (W16.of_int 541) _ _ _).
  call (invntt_radix2_16_fold_block_functional
    rp0 17 544 (W16.of_int 95) _ _ _).
  call (invntt_radix2_16_fold_block_functional
    rp0 16 512 (W16.of_int (-1577)) _ _ _).
  call (invntt_radix2_16_fold_block_functional
    rp0 15 480 (W16.of_int (-1241)) _ _ _).
  call (invntt_radix2_16_fold_block_functional
    rp0 14 448 (W16.of_int 550) _ _ _).
  call (invntt_radix2_16_fold_block_functional
    rp0 13 416 (W16.of_int (-44)) _ _ _).
  call (invntt_radix2_16_fold_block_functional
    rp0 12 384 (W16.of_int 39) _ _ _).
  call (invntt_radix2_16_fold_block_functional
    rp0 11 352 (W16.of_int (-820)) _ _ _).
  call (invntt_radix2_16_fold_block_functional
    rp0 10 320 (W16.of_int (-216)) _ _ _).
  call (invntt_radix2_16_fold_block_functional
    rp0 9 288 (W16.of_int (-121)) _ _ _).
  call (invntt_radix2_16_fold_block_functional
    rp0 8 256 (W16.of_int (-757)) _ _ _).
  call (invntt_radix2_16_fold_block_functional
    rp0 7 224 (W16.of_int (-348)) _ _ _).
  call (invntt_radix2_16_fold_block_functional
    rp0 6 192 (W16.of_int 937) _ _ _).
  call (invntt_radix2_16_fold_block_functional
    rp0 5 160 (W16.of_int 893) _ _ _).
  call (invntt_radix2_16_fold_block_functional
    rp0 4 128 (W16.of_int 387) _ _ _).
  call (invntt_radix2_16_fold_block_functional
    rp0 3 96 (W16.of_int (-603)) _ _ _).
  call (invntt_radix2_16_fold_block_functional
    rp0 2 64 (W16.of_int 1713) _ _ _).
  call (invntt_radix2_16_fold_block_functional
    rp0 1 32 (W16.of_int (-1105)) _ _ _).
  call (invntt_radix2_16_fold_block_functional
    rp0 0 0 (W16.of_int 1058) _ _ _).
  auto.
  rewrite invntt_radix2_16_word_fold_zero; done.
qed.

lemma invntt_radix2_16_functional
    (rp0 : W16.t Array768.t) :
  hoare [
    NTRUPlus768InvNTTRadix2_16.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_16 :
    rp = rp0 ==> res = invntt_radix2_16_spec rp0].
proof.
  conseq (invntt_radix2_16_fold_functional rp0) => />.
  exact (invntt_radix2_16_word_fold_full rp0).
qed.

lemma invntt_radix2_16_lossless :
  islossless
    NTRUPlus768InvNTTRadix2_16.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_16.
proof.
  proc.
  call invntt_radix2_16_block_lossless.
  call invntt_radix2_16_block_lossless.
  call invntt_radix2_16_block_lossless.
  call invntt_radix2_16_block_lossless.
  call invntt_radix2_16_block_lossless.
  call invntt_radix2_16_block_lossless.
  call invntt_radix2_16_block_lossless.
  call invntt_radix2_16_block_lossless.
  call invntt_radix2_16_block_lossless.
  call invntt_radix2_16_block_lossless.
  call invntt_radix2_16_block_lossless.
  call invntt_radix2_16_block_lossless.
  call invntt_radix2_16_block_lossless.
  call invntt_radix2_16_block_lossless.
  call invntt_radix2_16_block_lossless.
  call invntt_radix2_16_block_lossless.
  call invntt_radix2_16_block_lossless.
  call invntt_radix2_16_block_lossless.
  call invntt_radix2_16_block_lossless.
  call invntt_radix2_16_block_lossless.
  call invntt_radix2_16_block_lossless.
  call invntt_radix2_16_block_lossless.
  call invntt_radix2_16_block_lossless.
  call invntt_radix2_16_block_lossless.
  auto.
qed.

lemma invntt_radix2_16_correct
    (rp0 : W16.t Array768.t) :
  phoare [
    NTRUPlus768InvNTTRadix2_16.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_16 :
    rp = rp0 ==> res = invntt_radix2_16_spec rp0] = 1%r.
proof.
  by conseq invntt_radix2_16_lossless (invntt_radix2_16_functional rp0).
qed.
