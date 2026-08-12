require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.

require import Array768 WArray1536 NTRUPlus768NTTRadix3.
require import NTRUPlus768BasemulProof.

op block : int = 128.
op double_block : int = 256.
op second_base : int = 384.
op omega : W16.t = W16.of_int (-886).
op zeta2 : W16.t = W16.of_int (-682).
op zeta3 : W16.t = W16.of_int (-248).
op zeta4 : W16.t = W16.of_int (-708).
op zeta5 : W16.t = W16.of_int 682.

op radix3_mul (z a : W16.t) : W16.t =
  montgomery_reduce (mul_i16 z a).

op radix3_block
    (z1 z2 a0 a1 a2 : W16.t) : W16.t * W16.t * W16.t =
  let t1 = radix3_mul z1 a1 in
  let t2 = radix3_mul z2 a2 in
  let t3 = radix3_mul omega (t1 - t2) in
  (a0 + t1 + t2, a0 - t2 + t3, a0 - t1 - t3).

op radix3_block_at
    (p : W16.t Array768.t) (base : int) (z1 z2 : W16.t) (k : int)
    : W16.t * W16.t * W16.t =
  radix3_block z1 z2 p.[base + k] p.[base + k + block] p.[base + k + double_block].

op radix3_prefix_spec
    (p : W16.t Array768.t) (base upto : int) (z1 z2 : W16.t)
    : W16.t Array768.t =
  Array768.init (fun j =>
    if base <= j < base + upto then
      (radix3_block_at p base z1 z2 (j - base)).`1
    else if base + block <= j < base + block + upto then
      (radix3_block_at p base z1 z2 (j - base - block)).`2
    else if base + double_block <= j < base + double_block + upto then
      (radix3_block_at p base z1 z2 (j - base - double_block)).`3
    else p.[j]).

op radix3_first_spec (p : W16.t Array768.t) : W16.t Array768.t =
  radix3_prefix_spec p 0 block zeta2 zeta3.

op radix3_second_spec (p : W16.t Array768.t) : W16.t Array768.t =
  radix3_prefix_spec p second_base block zeta4 zeta5.

op radix3_spec (p : W16.t Array768.t) : W16.t Array768.t =
  radix3_second_spec (radix3_first_spec p).

lemma radix3_mul_i16_functional (a0 b0 : W16.t) :
  hoare [NTRUPlus768NTTRadix3.M.__mul_i16 :
    a = a0 /\ b = b0 ==> res = mul_i16 a0 b0].
proof.
  proc; auto => />.
qed.

lemma radix3_montgomery_reduce_functional (a0 : W32.t) :
  hoare [NTRUPlus768NTTRadix3.M.__montgomery_reduce :
    a = a0 ==> res = montgomery_reduce a0].
proof.
  proc; auto => />.
qed.

lemma radix3_prefix_zero
    (p : W16.t Array768.t) (base : int) (z1 z2 : W16.t) :
  0 <= base <= 768 =>
  radix3_prefix_spec p base 0 z1 z2 = p.
proof.
  move=> Hbase.
  apply Array768.tP => j Hj.
  rewrite /radix3_prefix_spec Array768.initiE 1:Hj.
  smt().
qed.

lemma radix3_prefix_curr0
    (p : W16.t Array768.t) (base upto : int) (z1 z2 : W16.t) :
  0 <= base =>
  0 <= upto < block =>
  base + double_block + upto < 768 =>
  (radix3_prefix_spec p base upto z1 z2).[base + upto] = p.[base + upto].
proof.
  move=> Hbase Hupto Hbound.
  rewrite /radix3_prefix_spec Array768.initiE 1:/#.
  smt().
qed.

lemma radix3_prefix_curr1
    (p : W16.t Array768.t) (base upto : int) (z1 z2 : W16.t) :
  0 <= base =>
  0 <= upto < block =>
  base + double_block + upto < 768 =>
  (radix3_prefix_spec p base upto z1 z2).[base + block + upto] =
    p.[base + block + upto].
proof.
  move=> Hbase Hupto Hbound.
  rewrite /radix3_prefix_spec Array768.initiE 1:/#.
  smt().
qed.

lemma radix3_prefix_curr2
    (p : W16.t Array768.t) (base upto : int) (z1 z2 : W16.t) :
  0 <= base =>
  0 <= upto < block =>
  base + double_block + upto < 768 =>
  (radix3_prefix_spec p base upto z1 z2).[base + double_block + upto] =
    p.[base + double_block + upto].
proof.
  move=> Hbase Hupto Hbound.
  rewrite /radix3_prefix_spec Array768.initiE 1:/#.
  smt().
qed.

lemma radix3_prefix_step
    (p : W16.t Array768.t) (base upto : int) (z1 z2 : W16.t) :
  0 <= base =>
  0 <= upto < block =>
  base + double_block + upto < 768 =>
  (radix3_prefix_spec p base upto z1 z2)
    .[base + upto <- (radix3_block_at p base z1 z2 upto).`1]
    .[base + block + upto <- (radix3_block_at p base z1 z2 upto).`2]
    .[base + double_block + upto <- (radix3_block_at p base z1 z2 upto).`3] =
  radix3_prefix_spec p base (upto + 1) z1 z2.
proof.
  move=> Hbase Hupto Hbound.
  apply Array768.tP => j Hj.
  rewrite /radix3_prefix_spec.
  rewrite Array768.initiE 1:Hj.
  case (j = base + upto) => [-> | Hneq0].
  + by rewrite !Array768.get_setE; smt().
  case (j = base + block + upto) => [-> | Hneq1].
  + by rewrite !Array768.get_setE; smt().
  case (j = base + double_block + upto) => [-> | Hneq2].
  + by rewrite !Array768.get_setE; smt().
  rewrite !Array768.get_setE.
  + smt().
  + smt().
  + smt().
  rewrite Array768.initiE 1:Hj.
  smt().
qed.

lemma ntt_radix3_functional
    (rp0 : W16.t Array768.t) :
  hoare [NTRUPlus768NTTRadix3.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix3 :
    rp = rp0 ==> res = radix3_spec rp0].
proof.
  proc.
  seq 3 : (rp = radix3_first_spec rp0).
  + seq 2 : (rp = radix3_prefix_spec rp0 0 0 zeta2 zeta3 /\ i = W64.of_int 0).
    + auto => />.
      by rewrite radix3_prefix_zero.
    while (0 <= W64.to_uint i <= block /\
           rp = radix3_prefix_spec rp0 0 (W64.to_uint i) zeta2 zeta3); last first.
    + skip => &hr [Hrp Hi].
      split.
      + split.
        - rewrite Hi W64.to_uint0; smt().
        by rewrite Hi W64.to_uint0; exact Hrp.
      move=> i1 rp1 Hexit [Hi1 Hrp1].
      rewrite W64.ultE /= in Hexit.
      have Hiend : W64.to_uint i1 = block by smt().
      rewrite /radix3_first_spec.
      smt().
    inline NTRUPlus768NTTRadix3.M.__mul_i16
           NTRUPlus768NTTRadix3.M.__montgomery_reduce.
    auto => /> &hr Hi Hrp Hloop.
    rewrite W64.ultE /= in Hloop.
    have Hidx : 0 <= W64.to_uint i{hr} < block by smt().
    have Hget0 :
        (radix3_prefix_spec rp0 0 (W64.to_uint i{hr}) zeta2 zeta3)
          .[W64.to_uint i{hr}] = rp0.[W64.to_uint i{hr}].
    + apply radix3_prefix_curr0; smt().
    have Hget1 :
        (radix3_prefix_spec rp0 0 (W64.to_uint i{hr}) zeta2 zeta3)
          .[W64.to_uint i{hr} + block] =
        rp0.[W64.to_uint i{hr} + block].
    + have -> : W64.to_uint i{hr} + block =
          0 + block + W64.to_uint i{hr} by smt().
      apply radix3_prefix_curr1; smt().
    have Hget2 :
        (radix3_prefix_spec rp0 0 (W64.to_uint i{hr}) zeta2 zeta3)
          .[W64.to_uint i{hr} + double_block] =
        rp0.[W64.to_uint i{hr} + double_block].
    + have -> : W64.to_uint i{hr} + double_block =
          0 + double_block + W64.to_uint i{hr} by smt().
      apply radix3_prefix_curr2; smt().
    have Hnext : W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
    + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
    have Haddr1 : W64.to_uint (i{hr} + W64.of_int 128) =
        W64.to_uint i{hr} + 128.
    + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
    have Haddr2 : W64.to_uint (i{hr} + W64.of_int 256) =
        W64.to_uint i{hr} + 256.
    + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
    have Hstep :
        (radix3_prefix_spec rp0 0 (W64.to_uint i{hr}) zeta2 zeta3)
          .[0 + W64.to_uint i{hr} <-
            (radix3_block_at rp0 0 zeta2 zeta3 (W64.to_uint i{hr})).`1]
          .[0 + block + W64.to_uint i{hr} <-
            (radix3_block_at rp0 0 zeta2 zeta3 (W64.to_uint i{hr})).`2]
          .[0 + double_block + W64.to_uint i{hr} <-
            (radix3_block_at rp0 0 zeta2 zeta3 (W64.to_uint i{hr})).`3] =
        radix3_prefix_spec rp0 0 (W64.to_uint i{hr} + 1) zeta2 zeta3.
    + apply radix3_prefix_step; smt().
    split.
    + rewrite Hnext; smt(W64.to_uint_cmp).
    rewrite Hnext.
    rewrite -Hstep.
    rewrite /radix3_block_at /radix3_block /radix3_mul /block /double_block.
    rewrite Hget0.
    rewrite Haddr1 Haddr2.
    rewrite /block in Hget1.
    rewrite /double_block in Hget2.
    rewrite Hget1 Hget2.
    rewrite /zeta2 /zeta3 /omega /mul_i16 /montgomery_reduce.
    rewrite /=.
    smt().
  seq 1 : (rp = radix3_first_spec rp0 /\ i = W64.of_int second_base).
  + auto => />.
  while (second_base <= W64.to_uint i <= second_base + block /\
         rp = radix3_prefix_spec (radix3_first_spec rp0) second_base
              (W64.to_uint i - second_base) zeta4 zeta5); last first.
  + skip => &hr [Hi Hrp].
    split.
    + split.
      - rewrite Hrp /second_base /block /=; smt().
      rewrite Hrp /second_base /=.
      rewrite radix3_prefix_zero 1:/#.
      exact Hi.
    move=> i1 rp1 Hexit [Hi1 Hrp1].
    rewrite W64.ultE /= in Hexit.
    have Hiend : W64.to_uint i1 = second_base + block by smt().
    rewrite /radix3_spec /radix3_second_spec.
    smt().
  inline NTRUPlus768NTTRadix3.M.__mul_i16
         NTRUPlus768NTTRadix3.M.__montgomery_reduce.
  auto => /> &hr Hi Hrp Hloop.
  rewrite W64.ultE /= in Hloop.
  have Hidx :
      0 <= W64.to_uint i{hr} - second_base < block by smt().
  have Hcurri : W64.to_uint i{hr} = second_base + (W64.to_uint i{hr} - second_base)
    by smt().
  have Hget0 :
      (radix3_prefix_spec (radix3_first_spec rp0) second_base
        (W64.to_uint i{hr} - second_base) zeta4 zeta5)
        .[W64.to_uint i{hr}] =
      (radix3_first_spec rp0).[W64.to_uint i{hr}].
  + rewrite Hcurri.
    apply radix3_prefix_curr0; smt().
  have Hget1 :
      (radix3_prefix_spec (radix3_first_spec rp0) second_base
        (W64.to_uint i{hr} - second_base) zeta4 zeta5)
        .[W64.to_uint i{hr} + block] =
      (radix3_first_spec rp0).[W64.to_uint i{hr} + block].
  + rewrite Hcurri.
    have -> : second_base + (W64.to_uint i{hr} - second_base) + block =
        second_base + block + (W64.to_uint i{hr} - second_base) by smt().
    apply radix3_prefix_curr1; smt().
  have Hget2 :
      (radix3_prefix_spec (radix3_first_spec rp0) second_base
        (W64.to_uint i{hr} - second_base) zeta4 zeta5)
        .[W64.to_uint i{hr} + double_block] =
      (radix3_first_spec rp0).[W64.to_uint i{hr} + double_block].
  + rewrite Hcurri.
    have -> : second_base + (W64.to_uint i{hr} - second_base) + double_block =
        second_base + double_block + (W64.to_uint i{hr} - second_base) by smt().
    apply radix3_prefix_curr2; smt().
  have Hnext : W64.to_uint (i{hr} + W64.one) - second_base =
      (W64.to_uint i{hr} - second_base) + 1.
  + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  have Haddr1 : W64.to_uint (i{hr} + W64.of_int 128) =
      W64.to_uint i{hr} + 128.
  + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  have Haddr2 : W64.to_uint (i{hr} + W64.of_int 256) =
      W64.to_uint i{hr} + 256.
  + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  have Hstep :
      (radix3_prefix_spec (radix3_first_spec rp0) second_base
        (W64.to_uint i{hr} - second_base) zeta4 zeta5)
        .[second_base + (W64.to_uint i{hr} - second_base) <-
          (radix3_block_at (radix3_first_spec rp0) second_base zeta4 zeta5
            (W64.to_uint i{hr} - second_base)).`1]
        .[second_base + block + (W64.to_uint i{hr} - second_base) <-
          (radix3_block_at (radix3_first_spec rp0) second_base zeta4 zeta5
            (W64.to_uint i{hr} - second_base)).`2]
        .[second_base + double_block + (W64.to_uint i{hr} - second_base) <-
          (radix3_block_at (radix3_first_spec rp0) second_base zeta4 zeta5
            (W64.to_uint i{hr} - second_base)).`3] =
      radix3_prefix_spec (radix3_first_spec rp0) second_base
        ((W64.to_uint i{hr} - second_base) + 1) zeta4 zeta5.
  + apply radix3_prefix_step; smt().
  split.
  + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  rewrite Hnext.
  rewrite -Hstep.
  rewrite /radix3_block_at /radix3_block /radix3_mul /block /double_block.
  rewrite Hget0.
  rewrite Haddr1 Haddr2.
  rewrite /block in Hget1.
  rewrite /double_block in Hget2.
  rewrite Hget1 Hget2.
  rewrite /zeta4 /zeta5 /omega /mul_i16 /montgomery_reduce.
  rewrite /second_base /=.
  smt().
qed.

lemma ntt_radix3_lossless :
  islossless
    NTRUPlus768NTTRadix3.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix3.
proof.
  proc.
  while (second_base <= W64.to_uint i <= second_base + block)
        (second_base + block - W64.to_uint i); last first.
  wp.
  while (0 <= W64.to_uint i <= block) (block - W64.to_uint i); last first.
  auto => />.
  move=> i; split.
  + move=> Hlo Hhi Hzero.
    rewrite W64.ultE /= /block.
    smt().
  move=> Hnot Hlo Hhi i0 Hbase Htop Hzero.
  rewrite W64.ultE /= /block /second_base.
  smt().
  move=> *.
  inline NTRUPlus768NTTRadix3.M.__mul_i16
         NTRUPlus768NTTRadix3.M.__montgomery_reduce.
  auto => /> &hr Hi Hhigh Hloop.
  rewrite W64.ultE /= in Hloop.
  rewrite W64.to_uintD_small /= /block; smt(W64.to_uint_cmp).
  move=> *.
  inline NTRUPlus768NTTRadix3.M.__mul_i16
         NTRUPlus768NTTRadix3.M.__montgomery_reduce.
  auto => /> &hr Hbase Hhigh Hloop.
  rewrite W64.ultE /= in Hloop.
  rewrite W64.to_uintD_small /= /block /second_base;
    smt(W64.to_uint_cmp).
qed.

lemma ntt_radix3_correct
    (rp0 : W16.t Array768.t) :
  phoare [NTRUPlus768NTTRadix3.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix3 :
    rp = rp0 ==> res = radix3_spec rp0] = 1%r.
proof.
  by conseq ntt_radix3_lossless (ntt_radix3_functional rp0).
qed.
