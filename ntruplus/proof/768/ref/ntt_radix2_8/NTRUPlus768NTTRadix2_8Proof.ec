require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.

require import Array768 WArray1536 NTRUPlus768NTTRadix2_8.
require import NTRUPlus768BasemulProof.

op block : int = 8.
op double_block : int = 16.
op nblocks : int = 48.

op zeta1  : W16.t = W16.of_int 1449.
op zeta2  : W16.t = W16.of_int 837.
op zeta3  : W16.t = W16.of_int 901.
op zeta4  : W16.t = W16.of_int 1637.
op zeta5  : W16.t = W16.of_int (-569).
op zeta6  : W16.t = W16.of_int (-1617).
op zeta7  : W16.t = W16.of_int (-1530).
op zeta8  : W16.t = W16.of_int 1199.
op zeta9  : W16.t = W16.of_int 50.
op zeta10 : W16.t = W16.of_int (-830).
op zeta11 : W16.t = W16.of_int (-625).
op zeta12 : W16.t = W16.of_int 4.
op zeta13 : W16.t = W16.of_int 176.
op zeta14 : W16.t = W16.of_int (-156).
op zeta15 : W16.t = W16.of_int 1257.
op zeta16 : W16.t = W16.of_int (-1507).
op zeta17 : W16.t = W16.of_int (-380).
op zeta18 : W16.t = W16.of_int (-606).
op zeta19 : W16.t = W16.of_int 1293.
op zeta20 : W16.t = W16.of_int 661.
op zeta21 : W16.t = W16.of_int 1428.
op zeta22 : W16.t = W16.of_int (-1580).
op zeta23 : W16.t = W16.of_int (-565).
op zeta24 : W16.t = W16.of_int (-992).
op zeta25 : W16.t = W16.of_int 548.
op zeta26 : W16.t = W16.of_int (-800).
op zeta27 : W16.t = W16.of_int 64.
op zeta28 : W16.t = W16.of_int (-371).
op zeta29 : W16.t = W16.of_int 961.
op zeta30 : W16.t = W16.of_int 641.
op zeta31 : W16.t = W16.of_int 87.
op zeta32 : W16.t = W16.of_int 630.
op zeta33 : W16.t = W16.of_int 675.
op zeta34 : W16.t = W16.of_int (-834).
op zeta35 : W16.t = W16.of_int 205.
op zeta36 : W16.t = W16.of_int 54.
op zeta37 : W16.t = W16.of_int (-1081).
op zeta38 : W16.t = W16.of_int 1351.
op zeta39 : W16.t = W16.of_int 1413.
op zeta40 : W16.t = W16.of_int (-1331).
op zeta41 : W16.t = W16.of_int (-1673).
op zeta42 : W16.t = W16.of_int (-1267).
op zeta43 : W16.t = W16.of_int (-1558).
op zeta44 : W16.t = W16.of_int 281.
op zeta45 : W16.t = W16.of_int (-1464).
op zeta46 : W16.t = W16.of_int (-588).
op zeta47 : W16.t = W16.of_int 1015.
op zeta48 : W16.t = W16.of_int 436.
op valid_base (base : int) : bool =
  exists k, 0 <= k < nblocks /\ base = double_block * k.

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

op barrett_reduce (a : W16.t) : W16.t =
  let td = sigextu32 a * W32.of_int 19412 in
  let td = td + W32.of_int 33554432 in
  let t = truncateu16 (td `|>>` W8.of_int 26) in
  let td = sigextu32 t * W32.of_int 3457 in
  let t = truncateu16 td in
  a - t.

lemma radix2_8_modz_sub_dvd (u m d : int) :
  m %% d = 0 => (u - m) %% d = u %% d.
proof.
  move=> Hmd.
  have Hneg : (-m) %% d = 0.
  + apply/dvdzE; apply dvdzN; apply/dvdzE; exact Hmd.
  rewrite (_ : u - m = u + (-m)) 1:/#.
  by rewrite -modzDmr Hneg /=.
qed.

lemma radix2_8_w16_of_sintK (w : W16.t) :
  W16.of_int (W16.to_sint w) = w.
proof.
  apply W16.to_uint_eq.
  rewrite W16.of_uintK W16.to_sintE /W16.smod.
  case (2 ^ (16 - 1) <= W16.to_uint w) => Hsign.
  + rewrite (radix2_8_modz_sub_dvd
      (W16.to_uint w) W16.modulus W16.modulus).
    - by rewrite modzz.
    by rewrite W16.to_uint_mod.
  by rewrite W16.to_uint_mod.
qed.

lemma radix2_8_truncateu16_of_int (x : int) :
  truncateu16 (W32.of_int x) = W16.of_int x.
proof.
  apply W16.to_uint_eq.
  rewrite /truncateu16 /= W16.of_uintK W32.of_uintK W16.of_uintK.
  rewrite modz_dvd.
  + apply/dvdzP; exists 65536; ring.
  done.
qed.

lemma radix2_8_truncate_sigext_add (x y : W16.t) :
  truncateu16 (sigextu32 x + sigextu32 y) = x + y.
proof.
  rewrite /sigextu32 /=.
  rewrite radix2_8_truncateu16_of_int W16.of_intD.
  by rewrite !radix2_8_w16_of_sintK.
qed.

lemma radix2_8_truncate_sigext_sub (x y : W16.t) :
  truncateu16 (sigextu32 x - sigextu32 y) = x - y.
proof.
  rewrite /sigextu32 /=.
  rewrite radix2_8_truncateu16_of_int W16.of_intS.
  by rewrite !radix2_8_w16_of_sintK.
qed.

op radix2_8_mul (z a : W16.t) : W16.t =
  montgomery_reduce (mul_i16 z a).

op radix2_8_pair (z lo hi : W16.t) : W16.t * W16.t =
  let t = radix2_8_mul z hi in
  (barrett_reduce (lo + t), barrett_reduce (lo - t)).

op radix2_8_pair_at
    (p : W16.t Array768.t) (base : int) (z : W16.t) (k : int)
    : W16.t * W16.t =
  radix2_8_pair z p.[base + k] p.[base + k + block].

op radix2_8_prefix_spec
    (p : W16.t Array768.t) (base upto : int) (z : W16.t)
    : W16.t Array768.t =
  Array768.init (fun j =>
    if base <= j < base + upto then
      (radix2_8_pair_at p base z (j - base)).`1
    else if base + block <= j < base + block + upto then
      (radix2_8_pair_at p base z (j - base - block)).`2
    else p.[j]).

op radix2_8_block_spec
    (p : W16.t Array768.t) (base : int) (z : W16.t)
    : W16.t Array768.t =
  radix2_8_prefix_spec p base block z.

op radix2_8_spec (p : W16.t Array768.t) : W16.t Array768.t =
(radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec
  (radix2_8_block_spec p 0 zeta1)
  16 zeta2)
  32 zeta3)
  48 zeta4)
  64 zeta5)
  80 zeta6)
  96 zeta7)
  112 zeta8)
  128 zeta9)
  144 zeta10)
  160 zeta11)
  176 zeta12)
  192 zeta13)
  208 zeta14)
  224 zeta15)
  240 zeta16)
  256 zeta17)
  272 zeta18)
  288 zeta19)
  304 zeta20)
  320 zeta21)
  336 zeta22)
  352 zeta23)
  368 zeta24)
  384 zeta25)
  400 zeta26)
  416 zeta27)
  432 zeta28)
  448 zeta29)
  464 zeta30)
  480 zeta31)
  496 zeta32)
  512 zeta33)
  528 zeta34)
  544 zeta35)
  560 zeta36)
  576 zeta37)
  592 zeta38)
  608 zeta39)
  624 zeta40)
  640 zeta41)
  656 zeta42)
  672 zeta43)
  688 zeta44)
  704 zeta45)
  720 zeta46)
  736 zeta47)
  752 zeta48).

lemma radix2_8_mul_i16_functional (a0 b0 : W16.t) :
  hoare [NTRUPlus768NTTRadix2_8.M.__mul_i16 :
    a = a0 /\ b = b0 ==> res = mul_i16 a0 b0].
proof.
  proc; auto => />.
qed.

lemma radix2_8_montgomery_reduce_functional (a0 : W32.t) :
  hoare [NTRUPlus768NTTRadix2_8.M.__montgomery_reduce :
    a = a0 ==> res = montgomery_reduce a0].
proof.
  proc; auto => />.
qed.

lemma radix2_8_barrett_reduce_functional (a0 : W16.t) :
  hoare [NTRUPlus768NTTRadix2_8.M.__barrett_reduce :
    a = a0 ==> res = barrett_reduce a0].
proof.
  proc; auto => />.
qed.

lemma radix2_8_prefix_zero
    (p : W16.t Array768.t) (base : int) (z : W16.t) :
  0 <= base <= 768 =>
  radix2_8_prefix_spec p base 0 z = p.
proof.
  move=> Hbase.
  apply Array768.tP => j Hj.
  rewrite /radix2_8_prefix_spec Array768.initiE 1:Hj.
  smt().
qed.

lemma radix2_8_prefix_curr0
    (p : W16.t Array768.t) (base upto : int) (z : W16.t) :
  0 <= base =>
  0 <= upto < block =>
  base + block + upto < 768 =>
  (radix2_8_prefix_spec p base upto z).[base + upto] = p.[base + upto].
proof.
  move=> Hbase Hupto Hbound.
  rewrite /radix2_8_prefix_spec Array768.initiE 1:/#.
  smt().
qed.

lemma radix2_8_prefix_curr1
    (p : W16.t Array768.t) (base upto : int) (z : W16.t) :
  0 <= base =>
  0 <= upto < block =>
  base + block + upto < 768 =>
  (radix2_8_prefix_spec p base upto z).[base + block + upto] =
    p.[base + block + upto].
proof.
  move=> Hbase Hupto Hbound.
  rewrite /radix2_8_prefix_spec Array768.initiE 1:/#.
  smt().
qed.

lemma radix2_8_prefix_step
    (p : W16.t Array768.t) (base upto : int) (z : W16.t) :
  0 <= base =>
  0 <= upto < block =>
  base + block + upto < 768 =>
  (radix2_8_prefix_spec p base upto z)
    .[base + upto <- (radix2_8_pair_at p base z upto).`1]
    .[base + block + upto <- (radix2_8_pair_at p base z upto).`2] =
  radix2_8_prefix_spec p base (upto + 1) z.
proof.
  move=> Hbase Hupto Hbound.
  apply Array768.tP => j Hj.
  rewrite /radix2_8_prefix_spec.
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

lemma radix2_8_block_functional
    (rp0 : W16.t Array768.t) (base0 : int) (z0 : W16.t) :
  valid_base base0 =>
  hoare [NTRUPlus768NTTRadix2_8.M.__radix2_8_block :
    rp = rp0 /\ base = W64.of_int base0 /\ zeta_0 = z0 ==>
    res = radix2_8_block_spec rp0 base0 z0].
proof.
  move=> Hvalid.
  have [Hbase Hbound] := valid_base_bounds base0 Hvalid.
  proc.
  seq 3 :
    (rp = radix2_8_prefix_spec rp0 base0 0 z0 /\
     i = W64.of_int base0 /\
     stop = W64.of_int base0 + W64.of_int block /\
     zeta_0 = z0).
  + auto => />.
    rewrite radix2_8_prefix_zero 1:/# /block.
    smt().
  while (base0 <= W64.to_uint i <= base0 + block /\
         stop = W64.of_int base0 + W64.of_int block /\
         zeta_0 = z0 /\
         rp = radix2_8_prefix_spec rp0 base0 (W64.to_uint i - base0) z0); last first.
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
    rewrite /radix2_8_block_spec.
    smt().
  inline NTRUPlus768NTTRadix2_8.M.__mul_i16
         NTRUPlus768NTTRadix2_8.M.__montgomery_reduce
         NTRUPlus768NTTRadix2_8.M.__barrett_reduce.
  auto => /> &hr Hi Hrp Hloop.
  rewrite W64.ultE /= in Hloop.
  rewrite (valid_base_stop_to_uint base0 Hvalid) in Hloop.
  have Hidx : 0 <= W64.to_uint i{hr} - base0 < block by smt().
  have Hcurri : W64.to_uint i{hr} = base0 + (W64.to_uint i{hr} - base0)
    by smt().
  have Hget0 :
      (radix2_8_prefix_spec rp0 base0 (W64.to_uint i{hr} - base0) z0)
        .[W64.to_uint i{hr}] = rp0.[W64.to_uint i{hr}].
  + have Hcurr :
        (radix2_8_prefix_spec rp0 base0 (W64.to_uint i{hr} - base0) z0)
          .[base0 + (W64.to_uint i{hr} - base0)] =
        rp0.[base0 + (W64.to_uint i{hr} - base0)].
    + apply radix2_8_prefix_curr0; smt().
    move: Hcurr.
    by rewrite -Hcurri.
  have Hget1 :
      (radix2_8_prefix_spec rp0 base0 (W64.to_uint i{hr} - base0) z0)
        .[W64.to_uint i{hr} + block] =
      rp0.[W64.to_uint i{hr} + block].
  + have Hcurr :
        (radix2_8_prefix_spec rp0 base0 (W64.to_uint i{hr} - base0) z0)
          .[base0 + block + (W64.to_uint i{hr} - base0)] =
        rp0.[base0 + block + (W64.to_uint i{hr} - base0)].
    + apply radix2_8_prefix_curr1; smt().
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
  have Hstep :
      (radix2_8_prefix_spec rp0 base0 (W64.to_uint i{hr} - base0) z0)
        .[base0 + (W64.to_uint i{hr} - base0) <-
          (radix2_8_pair_at rp0 base0 z0 (W64.to_uint i{hr} - base0)).`1]
        .[base0 + block + (W64.to_uint i{hr} - base0) <-
          (radix2_8_pair_at rp0 base0 z0 (W64.to_uint i{hr} - base0)).`2] =
      radix2_8_prefix_spec rp0 base0
        ((W64.to_uint i{hr} - base0) + 1) z0.
  + apply radix2_8_prefix_step; smt().
  split.
  + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  rewrite Hnext.
  rewrite -Hstep.
  rewrite /radix2_8_pair_at /radix2_8_pair /radix2_8_mul /block.
  rewrite Hget0 Haddr Hget1.
  rewrite -Hcurri Hspec_addr.
  rewrite !radix2_8_truncate_sigext_sub !radix2_8_truncate_sigext_add.
  rewrite /barrett_reduce /mul_i16 /montgomery_reduce.
  rewrite /=.
  apply Array768.set_set_swap.
  smt().
qed.

lemma radix2_8_block_lossless :
  islossless NTRUPlus768NTTRadix2_8.M.__radix2_8_block.
proof.
  proc.
  while (stop = base + W64.of_int block)
        (W64.to_uint stop - W64.to_uint i); last first.
  + auto => /> &hr i0 Hstop Hdone.
    rewrite W64.ultE /=.
    smt().
  move=> *.
  inline NTRUPlus768NTTRadix2_8.M.__mul_i16
         NTRUPlus768NTTRadix2_8.M.__montgomery_reduce
         NTRUPlus768NTTRadix2_8.M.__barrett_reduce.
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

lemma ntt_radix2_8_functional
    (rp0 : W16.t Array768.t) :
  hoare [NTRUPlus768NTTRadix2_8.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_8 :
    rp = rp0 ==> res = radix2_8_spec rp0].
proof.
  proc.
  seq 1 : (rp = rp0).
  + auto => />.
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12) 192 zeta13) 208 zeta14) 224 zeta15) 240 zeta16) 256 zeta17) 272 zeta18) 288 zeta19) 304 zeta20) 320 zeta21) 336 zeta22) 352 zeta23) 368 zeta24) 384 zeta25) 400 zeta26) 416 zeta27) 432 zeta28) 448 zeta29) 464 zeta30) 480 zeta31) 496 zeta32) 512 zeta33) 528 zeta34) 544 zeta35) 560 zeta36) 576 zeta37) 592 zeta38) 608 zeta39) 624 zeta40) 640 zeta41) 656 zeta42) 672 zeta43) 688 zeta44) 704 zeta45) 720 zeta46) 736 zeta47) 752 zeta48).
  + rewrite /valid_base /double_block /nblocks.
    exists 47; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12) 192 zeta13) 208 zeta14) 224 zeta15) 240 zeta16) 256 zeta17) 272 zeta18) 288 zeta19) 304 zeta20) 320 zeta21) 336 zeta22) 352 zeta23) 368 zeta24) 384 zeta25) 400 zeta26) 416 zeta27) 432 zeta28) 448 zeta29) 464 zeta30) 480 zeta31) 496 zeta32) 512 zeta33) 528 zeta34) 544 zeta35) 560 zeta36) 576 zeta37) 592 zeta38) 608 zeta39) 624 zeta40) 640 zeta41) 656 zeta42) 672 zeta43) 688 zeta44) 704 zeta45) 720 zeta46) 736 zeta47).
  + rewrite /valid_base /double_block /nblocks.
    exists 46; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12) 192 zeta13) 208 zeta14) 224 zeta15) 240 zeta16) 256 zeta17) 272 zeta18) 288 zeta19) 304 zeta20) 320 zeta21) 336 zeta22) 352 zeta23) 368 zeta24) 384 zeta25) 400 zeta26) 416 zeta27) 432 zeta28) 448 zeta29) 464 zeta30) 480 zeta31) 496 zeta32) 512 zeta33) 528 zeta34) 544 zeta35) 560 zeta36) 576 zeta37) 592 zeta38) 608 zeta39) 624 zeta40) 640 zeta41) 656 zeta42) 672 zeta43) 688 zeta44) 704 zeta45) 720 zeta46).
  + rewrite /valid_base /double_block /nblocks.
    exists 45; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12) 192 zeta13) 208 zeta14) 224 zeta15) 240 zeta16) 256 zeta17) 272 zeta18) 288 zeta19) 304 zeta20) 320 zeta21) 336 zeta22) 352 zeta23) 368 zeta24) 384 zeta25) 400 zeta26) 416 zeta27) 432 zeta28) 448 zeta29) 464 zeta30) 480 zeta31) 496 zeta32) 512 zeta33) 528 zeta34) 544 zeta35) 560 zeta36) 576 zeta37) 592 zeta38) 608 zeta39) 624 zeta40) 640 zeta41) 656 zeta42) 672 zeta43) 688 zeta44) 704 zeta45).
  + rewrite /valid_base /double_block /nblocks.
    exists 44; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12) 192 zeta13) 208 zeta14) 224 zeta15) 240 zeta16) 256 zeta17) 272 zeta18) 288 zeta19) 304 zeta20) 320 zeta21) 336 zeta22) 352 zeta23) 368 zeta24) 384 zeta25) 400 zeta26) 416 zeta27) 432 zeta28) 448 zeta29) 464 zeta30) 480 zeta31) 496 zeta32) 512 zeta33) 528 zeta34) 544 zeta35) 560 zeta36) 576 zeta37) 592 zeta38) 608 zeta39) 624 zeta40) 640 zeta41) 656 zeta42) 672 zeta43) 688 zeta44).
  + rewrite /valid_base /double_block /nblocks.
    exists 43; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12) 192 zeta13) 208 zeta14) 224 zeta15) 240 zeta16) 256 zeta17) 272 zeta18) 288 zeta19) 304 zeta20) 320 zeta21) 336 zeta22) 352 zeta23) 368 zeta24) 384 zeta25) 400 zeta26) 416 zeta27) 432 zeta28) 448 zeta29) 464 zeta30) 480 zeta31) 496 zeta32) 512 zeta33) 528 zeta34) 544 zeta35) 560 zeta36) 576 zeta37) 592 zeta38) 608 zeta39) 624 zeta40) 640 zeta41) 656 zeta42) 672 zeta43).
  + rewrite /valid_base /double_block /nblocks.
    exists 42; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12) 192 zeta13) 208 zeta14) 224 zeta15) 240 zeta16) 256 zeta17) 272 zeta18) 288 zeta19) 304 zeta20) 320 zeta21) 336 zeta22) 352 zeta23) 368 zeta24) 384 zeta25) 400 zeta26) 416 zeta27) 432 zeta28) 448 zeta29) 464 zeta30) 480 zeta31) 496 zeta32) 512 zeta33) 528 zeta34) 544 zeta35) 560 zeta36) 576 zeta37) 592 zeta38) 608 zeta39) 624 zeta40) 640 zeta41) 656 zeta42).
  + rewrite /valid_base /double_block /nblocks.
    exists 41; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12) 192 zeta13) 208 zeta14) 224 zeta15) 240 zeta16) 256 zeta17) 272 zeta18) 288 zeta19) 304 zeta20) 320 zeta21) 336 zeta22) 352 zeta23) 368 zeta24) 384 zeta25) 400 zeta26) 416 zeta27) 432 zeta28) 448 zeta29) 464 zeta30) 480 zeta31) 496 zeta32) 512 zeta33) 528 zeta34) 544 zeta35) 560 zeta36) 576 zeta37) 592 zeta38) 608 zeta39) 624 zeta40) 640 zeta41).
  + rewrite /valid_base /double_block /nblocks.
    exists 40; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12) 192 zeta13) 208 zeta14) 224 zeta15) 240 zeta16) 256 zeta17) 272 zeta18) 288 zeta19) 304 zeta20) 320 zeta21) 336 zeta22) 352 zeta23) 368 zeta24) 384 zeta25) 400 zeta26) 416 zeta27) 432 zeta28) 448 zeta29) 464 zeta30) 480 zeta31) 496 zeta32) 512 zeta33) 528 zeta34) 544 zeta35) 560 zeta36) 576 zeta37) 592 zeta38) 608 zeta39) 624 zeta40).
  + rewrite /valid_base /double_block /nblocks.
    exists 39; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12) 192 zeta13) 208 zeta14) 224 zeta15) 240 zeta16) 256 zeta17) 272 zeta18) 288 zeta19) 304 zeta20) 320 zeta21) 336 zeta22) 352 zeta23) 368 zeta24) 384 zeta25) 400 zeta26) 416 zeta27) 432 zeta28) 448 zeta29) 464 zeta30) 480 zeta31) 496 zeta32) 512 zeta33) 528 zeta34) 544 zeta35) 560 zeta36) 576 zeta37) 592 zeta38) 608 zeta39).
  + rewrite /valid_base /double_block /nblocks.
    exists 38; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12) 192 zeta13) 208 zeta14) 224 zeta15) 240 zeta16) 256 zeta17) 272 zeta18) 288 zeta19) 304 zeta20) 320 zeta21) 336 zeta22) 352 zeta23) 368 zeta24) 384 zeta25) 400 zeta26) 416 zeta27) 432 zeta28) 448 zeta29) 464 zeta30) 480 zeta31) 496 zeta32) 512 zeta33) 528 zeta34) 544 zeta35) 560 zeta36) 576 zeta37) 592 zeta38).
  + rewrite /valid_base /double_block /nblocks.
    exists 37; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12) 192 zeta13) 208 zeta14) 224 zeta15) 240 zeta16) 256 zeta17) 272 zeta18) 288 zeta19) 304 zeta20) 320 zeta21) 336 zeta22) 352 zeta23) 368 zeta24) 384 zeta25) 400 zeta26) 416 zeta27) 432 zeta28) 448 zeta29) 464 zeta30) 480 zeta31) 496 zeta32) 512 zeta33) 528 zeta34) 544 zeta35) 560 zeta36) 576 zeta37).
  + rewrite /valid_base /double_block /nblocks.
    exists 36; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12) 192 zeta13) 208 zeta14) 224 zeta15) 240 zeta16) 256 zeta17) 272 zeta18) 288 zeta19) 304 zeta20) 320 zeta21) 336 zeta22) 352 zeta23) 368 zeta24) 384 zeta25) 400 zeta26) 416 zeta27) 432 zeta28) 448 zeta29) 464 zeta30) 480 zeta31) 496 zeta32) 512 zeta33) 528 zeta34) 544 zeta35) 560 zeta36).
  + rewrite /valid_base /double_block /nblocks.
    exists 35; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12) 192 zeta13) 208 zeta14) 224 zeta15) 240 zeta16) 256 zeta17) 272 zeta18) 288 zeta19) 304 zeta20) 320 zeta21) 336 zeta22) 352 zeta23) 368 zeta24) 384 zeta25) 400 zeta26) 416 zeta27) 432 zeta28) 448 zeta29) 464 zeta30) 480 zeta31) 496 zeta32) 512 zeta33) 528 zeta34) 544 zeta35).
  + rewrite /valid_base /double_block /nblocks.
    exists 34; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12) 192 zeta13) 208 zeta14) 224 zeta15) 240 zeta16) 256 zeta17) 272 zeta18) 288 zeta19) 304 zeta20) 320 zeta21) 336 zeta22) 352 zeta23) 368 zeta24) 384 zeta25) 400 zeta26) 416 zeta27) 432 zeta28) 448 zeta29) 464 zeta30) 480 zeta31) 496 zeta32) 512 zeta33) 528 zeta34).
  + rewrite /valid_base /double_block /nblocks.
    exists 33; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12) 192 zeta13) 208 zeta14) 224 zeta15) 240 zeta16) 256 zeta17) 272 zeta18) 288 zeta19) 304 zeta20) 320 zeta21) 336 zeta22) 352 zeta23) 368 zeta24) 384 zeta25) 400 zeta26) 416 zeta27) 432 zeta28) 448 zeta29) 464 zeta30) 480 zeta31) 496 zeta32) 512 zeta33).
  + rewrite /valid_base /double_block /nblocks.
    exists 32; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12) 192 zeta13) 208 zeta14) 224 zeta15) 240 zeta16) 256 zeta17) 272 zeta18) 288 zeta19) 304 zeta20) 320 zeta21) 336 zeta22) 352 zeta23) 368 zeta24) 384 zeta25) 400 zeta26) 416 zeta27) 432 zeta28) 448 zeta29) 464 zeta30) 480 zeta31) 496 zeta32).
  + rewrite /valid_base /double_block /nblocks.
    exists 31; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12) 192 zeta13) 208 zeta14) 224 zeta15) 240 zeta16) 256 zeta17) 272 zeta18) 288 zeta19) 304 zeta20) 320 zeta21) 336 zeta22) 352 zeta23) 368 zeta24) 384 zeta25) 400 zeta26) 416 zeta27) 432 zeta28) 448 zeta29) 464 zeta30) 480 zeta31).
  + rewrite /valid_base /double_block /nblocks.
    exists 30; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12) 192 zeta13) 208 zeta14) 224 zeta15) 240 zeta16) 256 zeta17) 272 zeta18) 288 zeta19) 304 zeta20) 320 zeta21) 336 zeta22) 352 zeta23) 368 zeta24) 384 zeta25) 400 zeta26) 416 zeta27) 432 zeta28) 448 zeta29) 464 zeta30).
  + rewrite /valid_base /double_block /nblocks.
    exists 29; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12) 192 zeta13) 208 zeta14) 224 zeta15) 240 zeta16) 256 zeta17) 272 zeta18) 288 zeta19) 304 zeta20) 320 zeta21) 336 zeta22) 352 zeta23) 368 zeta24) 384 zeta25) 400 zeta26) 416 zeta27) 432 zeta28) 448 zeta29).
  + rewrite /valid_base /double_block /nblocks.
    exists 28; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12) 192 zeta13) 208 zeta14) 224 zeta15) 240 zeta16) 256 zeta17) 272 zeta18) 288 zeta19) 304 zeta20) 320 zeta21) 336 zeta22) 352 zeta23) 368 zeta24) 384 zeta25) 400 zeta26) 416 zeta27) 432 zeta28).
  + rewrite /valid_base /double_block /nblocks.
    exists 27; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12) 192 zeta13) 208 zeta14) 224 zeta15) 240 zeta16) 256 zeta17) 272 zeta18) 288 zeta19) 304 zeta20) 320 zeta21) 336 zeta22) 352 zeta23) 368 zeta24) 384 zeta25) 400 zeta26) 416 zeta27).
  + rewrite /valid_base /double_block /nblocks.
    exists 26; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12) 192 zeta13) 208 zeta14) 224 zeta15) 240 zeta16) 256 zeta17) 272 zeta18) 288 zeta19) 304 zeta20) 320 zeta21) 336 zeta22) 352 zeta23) 368 zeta24) 384 zeta25) 400 zeta26).
  + rewrite /valid_base /double_block /nblocks.
    exists 25; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12) 192 zeta13) 208 zeta14) 224 zeta15) 240 zeta16) 256 zeta17) 272 zeta18) 288 zeta19) 304 zeta20) 320 zeta21) 336 zeta22) 352 zeta23) 368 zeta24) 384 zeta25).
  + rewrite /valid_base /double_block /nblocks.
    exists 24; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12) 192 zeta13) 208 zeta14) 224 zeta15) 240 zeta16) 256 zeta17) 272 zeta18) 288 zeta19) 304 zeta20) 320 zeta21) 336 zeta22) 352 zeta23) 368 zeta24).
  + rewrite /valid_base /double_block /nblocks.
    exists 23; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12) 192 zeta13) 208 zeta14) 224 zeta15) 240 zeta16) 256 zeta17) 272 zeta18) 288 zeta19) 304 zeta20) 320 zeta21) 336 zeta22) 352 zeta23).
  + rewrite /valid_base /double_block /nblocks.
    exists 22; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12) 192 zeta13) 208 zeta14) 224 zeta15) 240 zeta16) 256 zeta17) 272 zeta18) 288 zeta19) 304 zeta20) 320 zeta21) 336 zeta22).
  + rewrite /valid_base /double_block /nblocks.
    exists 21; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12) 192 zeta13) 208 zeta14) 224 zeta15) 240 zeta16) 256 zeta17) 272 zeta18) 288 zeta19) 304 zeta20) 320 zeta21).
  + rewrite /valid_base /double_block /nblocks.
    exists 20; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12) 192 zeta13) 208 zeta14) 224 zeta15) 240 zeta16) 256 zeta17) 272 zeta18) 288 zeta19) 304 zeta20).
  + rewrite /valid_base /double_block /nblocks.
    exists 19; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12) 192 zeta13) 208 zeta14) 224 zeta15) 240 zeta16) 256 zeta17) 272 zeta18) 288 zeta19).
  + rewrite /valid_base /double_block /nblocks.
    exists 18; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12) 192 zeta13) 208 zeta14) 224 zeta15) 240 zeta16) 256 zeta17) 272 zeta18).
  + rewrite /valid_base /double_block /nblocks.
    exists 17; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12) 192 zeta13) 208 zeta14) 224 zeta15) 240 zeta16) 256 zeta17).
  + rewrite /valid_base /double_block /nblocks.
    exists 16; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12) 192 zeta13) 208 zeta14) 224 zeta15) 240 zeta16).
  + rewrite /valid_base /double_block /nblocks.
    exists 15; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12) 192 zeta13) 208 zeta14) 224 zeta15).
  + rewrite /valid_base /double_block /nblocks.
    exists 14; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12) 192 zeta13) 208 zeta14).
  + rewrite /valid_base /double_block /nblocks.
    exists 13; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12) 192 zeta13).
  + rewrite /valid_base /double_block /nblocks.
    exists 12; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11) 176 zeta12).
  + rewrite /valid_base /double_block /nblocks.
    exists 11; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10) 160 zeta11).
  + rewrite /valid_base /double_block /nblocks.
    exists 10; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9) 144 zeta10).
  + rewrite /valid_base /double_block /nblocks.
    exists 9; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8) 128 zeta9).
  + rewrite /valid_base /double_block /nblocks.
    exists 8; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7) 112 zeta8).
  + rewrite /valid_base /double_block /nblocks.
    exists 7; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6) 96 zeta7).
  + rewrite /valid_base /double_block /nblocks.
    exists 6; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5) 80 zeta6).
  + rewrite /valid_base /double_block /nblocks.
    exists 5; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4) 64 zeta5).
  + rewrite /valid_base /double_block /nblocks.
    exists 4; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3) 48 zeta4).
  + rewrite /valid_base /double_block /nblocks.
    exists 3; smt().
  call (radix2_8_block_functional (radix2_8_block_spec (radix2_8_block_spec rp0 0 zeta1) 16 zeta2) 32 zeta3).
  + rewrite /valid_base /double_block /nblocks.
    exists 2; smt().
  call (radix2_8_block_functional (radix2_8_block_spec rp0 0 zeta1) 16 zeta2).
  + rewrite /valid_base /double_block /nblocks.
    exists 1; smt().
  call (radix2_8_block_functional rp0 0 zeta1).
  + rewrite /valid_base /double_block /nblocks.
    exists 0; smt().
  auto => />.
qed.

lemma ntt_radix2_8_lossless :
  islossless
    NTRUPlus768NTTRadix2_8.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_8.
proof.
  proc.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  call radix2_8_block_lossless.
  auto.
qed.

lemma ntt_radix2_8_correct
    (rp0 : W16.t Array768.t) :
  phoare [NTRUPlus768NTTRadix2_8.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_8 :
    rp = rp0 ==> res = radix2_8_spec rp0] = 1%r.
proof.
  by conseq ntt_radix2_8_lossless (ntt_radix2_8_functional rp0).
qed.
