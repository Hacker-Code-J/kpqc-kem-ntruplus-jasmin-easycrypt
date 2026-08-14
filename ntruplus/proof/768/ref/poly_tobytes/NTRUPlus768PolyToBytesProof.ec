require import AllCore IntDiv Distr Ring StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array768 Array1152 NTRUPlus768PolyToBytes.
require import NTRUPlus768BasemulAlgebra.
require import JWord_extra.

import Ring.IntID IntOrder.

op poly_tobytes_input_qrange (ap : W16.t Array768.t) : bool =
  forall j, 0 <= j < 768 => -q <= coeff ap.[j] < q.

op canonical_coeff (w : W16.t) : int =
  if coeff w < 0 then coeff w + q else coeff w.

op poly_tobytes_byte0_int (ap : W16.t Array768.t) (i : int) : int =
  canonical_coeff ap.[2 * i] %% 256.

op poly_tobytes_byte1_int (ap : W16.t Array768.t) (i : int) : int =
  canonical_coeff ap.[2 * i] %/ 256 + 16 * (canonical_coeff ap.[2 * i + 1] %% 16).

op poly_tobytes_byte2_int (ap : W16.t Array768.t) (i : int) : int =
  canonical_coeff ap.[2 * i + 1] %/ 16.

op poly_tobytes_byte_at (ap : W16.t Array768.t) (j : int) : W8.t =
  if j %% 3 = 0 then
    W8.of_int (poly_tobytes_byte0_int ap (j %/ 3))
  else if j %% 3 = 1 then
    W8.of_int (poly_tobytes_byte1_int ap (j %/ 3))
  else
    W8.of_int (poly_tobytes_byte2_int ap (j %/ 3)).

op poly_tobytes_spec (ap : W16.t Array768.t) : W8.t Array1152.t =
  Array1152.init (fun j => poly_tobytes_byte_at ap j).

op poly_tobytes_canonical_word (w : W16.t) : W16.t =
  w + ((w `|>>` W8.of_int 15) `&` W16.of_int q).

op poly_tobytes_prefix
    (ap : W16.t Array768.t) (rp : W8.t Array1152.t) (upto : int) : bool =
  forall i, 0 <= i < upto =>
    rp.[3 * i] = W8.of_int (poly_tobytes_byte0_int ap i) /\
    rp.[3 * i + 1] = W8.of_int (poly_tobytes_byte1_int ap i) /\
    rp.[3 * i + 2] = W8.of_int (poly_tobytes_byte2_int ap i).

lemma canonical_coeff_range (w : W16.t) :
  -q <= coeff w < q =>
  0 <= canonical_coeff w < q.
proof.
  move=> Hw.
  rewrite /canonical_coeff.
  case (coeff w < 0).
  + move=> Hneg.
    rewrite /q /=.
    smt().
  move=> Hnonneg.
  rewrite /q /=.
  smt().
qed.

lemma poly_tobytes_W16_of_int_mone :
  W16.of_int (-1) = W16.onew.
proof.
  apply W16.to_uint_eq.
  rewrite W16.of_uintK W16.to_uint_onew /=.
  done.
qed.

lemma poly_tobytes_W16_of_sintK (w : W16.t) :
  W16.of_int (W16.to_sint w) = w.
proof.
  apply W16.to_uint_eq.
  rewrite W16.of_uintK W16.to_sintE /W16.smod.
  case (2 ^ (16 - 1) <= W16.to_uint w) => Hsign.
  + rewrite (modz_sub_dvd
      (W16.to_uint w) W16.modulus W16.modulus).
    - by rewrite modzz.
    by rewrite W16.to_uint_mod.
  by rewrite W16.to_uint_mod.
qed.

lemma poly_tobytes_word_from_coeff (w : W16.t) :
  w = W16.of_int (coeff w).
proof. by rewrite /coeff poly_tobytes_W16_of_sintK. qed.

lemma poly_tobytes_W16_min_sint_value : W16.min_sint = -32768 by done.
lemma poly_tobytes_W16_max_sint_value : W16.max_sint = 32767 by done.

lemma poly_tobytes_sign_mask_of_int (x : int) :
  W16.min_sint <= x <= W16.max_sint =>
  ((W16.of_int x `|>>` W8.of_int 15) `&` W16.of_int q) =
  W16.of_int (if x < 0 then q else 0).
proof.
  move=> Hx.
  rewrite poly_tobytes_W16_min_sint_value
    poly_tobytes_W16_max_sint_value in Hx.
  have Hcoeff :
      coeff (W16.of_int x `|>>` W8.of_int 15) = x %/ 2 ^ 15.
  + rewrite /coeff W16_sar_div 1:/#.
    rewrite (W16.to_sintK_small x Hx).
    done.
  case (x < 0) => Hsign.
  + rewrite (poly_tobytes_word_from_coeff
      (W16.of_int x `|>>` W8.of_int 15)).
    have Hdiv : x %/ 2 ^ 15 = -1.
    + have Hmin : -32768 <= x by smt().
      have Hmax : x <= 32767 by smt().
      have Hpos : 0 < -x by smt().
      have Hbound : -x <= 32768 by smt().
      rewrite (_ : x = -(-x)) 1:/#.
      rewrite divNz 1:Hpos 1:/#.
      rewrite divz_small; smt().
    rewrite Hcoeff Hdiv /=.
    by rewrite poly_tobytes_W16_of_int_mone W16.andwC W16.andw1.
  rewrite (poly_tobytes_word_from_coeff
      (W16.of_int x `|>>` W8.of_int 15)).
  have Hdiv : x %/ 2 ^ 15 = 0.
  + rewrite divz_small; smt().
  rewrite Hcoeff Hdiv /=.
  done.
qed.

lemma poly_tobytes_canonical_wordE (w : W16.t) :
  -q <= coeff w < q =>
  poly_tobytes_canonical_word w = W16.of_int (canonical_coeff w).
proof.
  move=> Hw.
  rewrite /poly_tobytes_canonical_word
    (poly_tobytes_word_from_coeff w).
  have Hword : W16.min_sint <= coeff w <= W16.max_sint.
  + rewrite /q /= in Hw.
    smt().
  rewrite (poly_tobytes_sign_mask_of_int (coeff w) Hword).
  have HcoeffK : coeff (W16.of_int (coeff w)) = coeff w.
  + rewrite /coeff W16.to_sintK_small 1:Hword.
    done.
  rewrite /canonical_coeff HcoeffK.
  case (coeff w < 0) => Hsign.
  + by rewrite W16.of_intD.
  done.
qed.

lemma poly_tobytes_byte0_wordE (w : W16.t) :
  -q <= coeff w < q =>
  truncateu8 (poly_tobytes_canonical_word w) =
  W8.of_int (canonical_coeff w %% 256).
proof.
  move=> Hw.
  rewrite (poly_tobytes_canonical_wordE w Hw).
  apply W8.to_uint_eq.
  rewrite /truncateu8 /= !of_uintK /=.
  have Hrange := canonical_coeff_range w Hw.
  rewrite /q /= in Hrange.
  smt().
qed.

lemma poly_tobytes_byte2_wordE (w : W16.t) :
  -q <= coeff w < q =>
  truncateu8 (poly_tobytes_canonical_word w `>>` W8.of_int 4) =
  W8.of_int (canonical_coeff w %/ 16).
proof.
  move=> Hw.
  rewrite (poly_tobytes_canonical_wordE w Hw).
  apply W8.to_uint_eq.
  rewrite /truncateu8 /= W16.to_uint_shr 1:/# !of_uintK /=.
  have Hrange := canonical_coeff_range w Hw.
  rewrite /q /= in Hrange.
  smt().
qed.

lemma poly_tobytes_byte1_wordE (w0 w1 : W16.t) :
  -q <= coeff w0 < q =>
  -q <= coeff w1 < q =>
  truncateu8
    ((poly_tobytes_canonical_word w0 `>>` W8.of_int 8) `|`
     (poly_tobytes_canonical_word w1 `<<` W8.of_int 4)) =
  W8.of_int
    (canonical_coeff w0 %/ 256 + 16 * (canonical_coeff w1 %% 16)).
proof.
  move=> Hw0 Hw1.
  rewrite (poly_tobytes_canonical_wordE w0 Hw0)
    (poly_tobytes_canonical_wordE w1 Hw1).
  have Hr0 := canonical_coeff_range w0 Hw0.
  have Hr1 := canonical_coeff_range w1 Hw1.
  rewrite /q /= in Hr0.
  rewrite /q /= in Hr1.
  rewrite W16.orw_disjoint.
  + rewrite /W16.(`&`).
    apply W16.ext_eq => k Hk.
    rewrite !map2iE // zerowE /(`>>`) /(`<<`) /=.
    case (k < 4).
    + smt(W16.get_out).
    move=> Hk4.
    rewrite !get_to_uint !of_uintK /=.
    have Hdiv : canonical_coeff w0 %/ 2 ^ (k + 8) = 0.
    + apply divz_small.
      rewrite /CoreInt.absz.
      have -> : 0 <= 2 ^ (k + 8) by smt(gt0_pow2).
      rewrite /=.
      have Hbase : 1 <= 2 by smt().
      move: (StdOrder.IntOrder.ler_weexpn2l 2 Hbase 12 (k + 8)).
      move=> Hmono.
      have Hpow : 2 ^ 12 <= 2 ^ (k + 8).
      + apply Hmono.
        smt().
      have HpowE : 4096 <= 2 ^ (k + 8).
      + move: Hpow.
        rewrite (_ : 2 ^ 12 = 4096) 1:/#.
        done.
      smt().
    have Hmod : canonical_coeff w0 %% 65536 = canonical_coeff w0.
    + rewrite modz_small; smt().
    rewrite Hmod Hdiv.
    done.
  apply W8.to_uint_eq.
  rewrite /truncateu8 /= W16.to_uintD_small.
  + rewrite W16.to_uint_shr 1:/# W16.to_uint_shl 1:/#
      !of_uintK /=.
    smt().
  rewrite W16.to_uint_shr 1:/# W16.to_uint_shl 1:/#
    !of_uintK /=.
  smt().
qed.

lemma poly_tobytes_index2E (i : W64.t) :
  W64.to_uint i < 384 =>
  W64.to_uint (W64.of_int 2 * i) = 2 * W64.to_uint i.
proof.
  move=> Hi.
  rewrite W64.to_uintM_small.
  + rewrite W64.of_uintK /=.
    smt(W64.to_uint_cmp).
  by rewrite W64.of_uintK /=.
qed.

lemma poly_tobytes_index2_add1E (i : W64.t) :
  W64.to_uint i < 384 =>
  W64.to_uint (W64.of_int 2 * i + W64.one) =
  2 * W64.to_uint i + 1.
proof.
  move=> Hi.
  rewrite W64.to_uintD_small.
  + rewrite poly_tobytes_index2E 1:Hi /=.
    smt(W64.to_uint_cmp).
  by rewrite poly_tobytes_index2E 1:Hi /=.
qed.

lemma poly_tobytes_offset3E (i : W64.t) :
  W64.to_uint i < 384 =>
  W64.to_uint ((i `<<` W8.one) + i) = 3 * W64.to_uint i.
proof.
  move=> Hi.
  rewrite W64.to_uintD_small.
  + rewrite /W64.(`<<`) W64.to_uint_shl 1:/# /=.
    smt(W64.to_uint_cmp).
  rewrite /W64.(`<<`) W64.to_uint_shl 1:/# /=.
  rewrite modz_small; first smt(W64.to_uint_cmp).
  smt().
qed.

lemma poly_tobytes_offset3_addE (i : W64.t) (d : int) :
  W64.to_uint i < 384 =>
  0 <= d <= 2 =>
  W64.to_uint ((i `<<` W8.one) + i + W64.of_int d) =
  3 * W64.to_uint i + d.
proof.
  move=> Hi Hd.
  rewrite W64.to_uintD_small.
  + rewrite poly_tobytes_offset3E 1:Hi W64.of_uintK.
    rewrite modz_small; smt(W64.to_uint_cmp).
  rewrite poly_tobytes_offset3E 1:Hi W64.of_uintK.
  rewrite modz_small; smt(W64.to_uint_cmp).
qed.

lemma poly_tobytes_byte0_range (ap : W16.t Array768.t) (i : int) :
  poly_tobytes_input_qrange ap =>
  0 <= i < 384 =>
  0 <= poly_tobytes_byte0_int ap i < 256.
proof.
  move=> Hap Hi.
  have Hcanon := canonical_coeff_range ap.[2 * i] _.
  + apply Hap.
    smt().
  rewrite /poly_tobytes_byte0_int.
  smt().
qed.

lemma poly_tobytes_byte1_range (ap : W16.t Array768.t) (i : int) :
  poly_tobytes_input_qrange ap =>
  0 <= i < 384 =>
  0 <= poly_tobytes_byte1_int ap i < 256.
proof.
  move=> Hap Hi.
  have Hc0 := canonical_coeff_range ap.[2 * i] _.
  + apply Hap.
    smt().
  have Hc1 := canonical_coeff_range ap.[2 * i + 1] _.
  + apply Hap.
    smt().
  rewrite /poly_tobytes_byte1_int.
  have Hdiv : 0 <= canonical_coeff ap.[2 * i] %/ 256 < 16 by smt().
  have Hmod : 0 <= canonical_coeff ap.[2 * i + 1] %% 16 < 16 by smt().
  smt().
qed.

lemma poly_tobytes_byte2_range (ap : W16.t Array768.t) (i : int) :
  poly_tobytes_input_qrange ap =>
  0 <= i < 384 =>
  0 <= poly_tobytes_byte2_int ap i < 256.
proof.
  move=> Hap Hi.
  have Hcanon := canonical_coeff_range ap.[2 * i + 1] _.
  + apply Hap.
    smt().
  rewrite /poly_tobytes_byte2_int.
  smt().
qed.

lemma poly_tobytes_prefix_extend
    (ap : W16.t Array768.t) (rp : W8.t Array1152.t) (i : int) :
  poly_tobytes_input_qrange ap =>
  0 <= i < 384 =>
  poly_tobytes_prefix ap rp i =>
  poly_tobytes_prefix ap
    (rp.[3 * i <- W8.of_int (poly_tobytes_byte0_int ap i)]
       .[3 * i + 1 <- W8.of_int (poly_tobytes_byte1_int ap i)]
       .[3 * i + 2 <- W8.of_int (poly_tobytes_byte2_int ap i)]) (i + 1).
proof.
  move=> Hap Hi Hprefix j Hj.
  case (j = i) => [-> | Hneq].
  + smt(Array1152.get_setE).
  have Hjold : 0 <= j < i by smt().
  have Hold := Hprefix j Hjold.
  move: Hold => [H0 [H1 H2]].
  smt(Array1152.get_setE).
qed.

lemma poly_tobytes_spec_byte0E (ap : W16.t Array768.t) (i : int) :
  0 <= i < 384 =>
  (poly_tobytes_spec ap).[3 * i] = W8.of_int (poly_tobytes_byte0_int ap i).
proof.
  move=> Hi.
  rewrite /poly_tobytes_spec Array1152.initiE 1:/# /poly_tobytes_byte_at.
  smt().
qed.

lemma poly_tobytes_spec_byte1E (ap : W16.t Array768.t) (i : int) :
  0 <= i < 384 =>
  (poly_tobytes_spec ap).[3 * i + 1] = W8.of_int (poly_tobytes_byte1_int ap i).
proof.
  move=> Hi.
  rewrite /poly_tobytes_spec Array1152.initiE 1:/# /poly_tobytes_byte_at.
  smt().
qed.

lemma poly_tobytes_spec_byte2E (ap : W16.t Array768.t) (i : int) :
  0 <= i < 384 =>
  (poly_tobytes_spec ap).[3 * i + 2] = W8.of_int (poly_tobytes_byte2_int ap i).
proof.
  move=> Hi.
  rewrite /poly_tobytes_spec Array1152.initiE 1:/# /poly_tobytes_byte_at.
  smt().
qed.

lemma poly_tobytes_prefix_full
    (ap : W16.t Array768.t) (rp : W8.t Array1152.t) :
  poly_tobytes_prefix ap rp 384 =>
  rp = poly_tobytes_spec ap.
proof.
  move=> Hprefix.
  apply Array1152.tP => j Hj.
  have Hjpair : 0 <= j %/ 3 < 384 by smt().
  move: (Hprefix (j %/ 3) Hjpair) => [H0 [H1 H2]].
  case (j %% 3 = 0).
  + move=> Hmod.
    have -> : j = 3 * (j %/ 3) by smt().
    rewrite H0.
    by rewrite (poly_tobytes_spec_byte0E ap (j %/ 3) Hjpair).
  case (j %% 3 = 1).
  + move=> Hmod0 Hmod1.
    have -> : j = 3 * (j %/ 3) + 1 by smt().
    rewrite H1.
    by rewrite (poly_tobytes_spec_byte1E ap (j %/ 3) Hjpair).
  move=> Hmod0 Hmod1.
  have -> : j = 3 * (j %/ 3) + 2 by smt().
  rewrite H2.
  by rewrite (poly_tobytes_spec_byte2E ap (j %/ 3) Hjpair).
qed.

lemma poly_tobytes_functional
    (rp0 : W8.t Array1152.t) (ap0 : W16.t Array768.t) :
  poly_tobytes_input_qrange ap0 =>
  hoare [NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes :
    rp = rp0 /\ ap = ap0 ==>
    res = poly_tobytes_spec ap0].
proof.
  move=> Hap0.
  proc.
  seq 2 :
    (ap = ap0 /\ i = W64.of_int 0 /\ poly_tobytes_prefix ap0 rp 0).
  + auto => />.
    rewrite /poly_tobytes_prefix.
    smt().
  while (0 <= W64.to_uint i <= 384 /\ ap = ap0 /\
         poly_tobytes_prefix ap0 rp (W64.to_uint i)); last first.
  + skip => &hr [Hap [Hi0 Hprefix0]].
    split.
    - split; first by rewrite Hi0 W64.to_uint0; smt().
      split; first exact Hap.
      by rewrite Hi0 W64.to_uint0.
    move=> i1 rp1 Hexit [Hi [Hap1 Hprefix1]].
    rewrite W64.ultE /= in Hexit.
    apply poly_tobytes_prefix_full.
    have Hiend : W64.to_uint i1 = 384 by smt().
    by rewrite -Hiend.
  auto => /> &hr HiLow HiHigh Hprefix Hloop.
  rewrite W64.ultE /= in Hloop.
  have Hi384 : 0 <= W64.to_uint i{hr} < 384 by smt().
  have HiLt : W64.to_uint i{hr} < 384 by smt().
  have Hnext :
      W64.to_uint (i{hr} + W64.one) =
      W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  split.
  + rewrite Hnext; smt(W64.to_uint_cmp).
  have Heven :
      -q <= coeff ap0.[2 * W64.to_uint i{hr}] < q.
  + apply Hap0.
    smt().
  have Hodd :
      -q <= coeff ap0.[2 * W64.to_uint i{hr} + 1] < q.
  + apply Hap0.
    smt().
  rewrite Hnext.
  rewrite (poly_tobytes_offset3E i{hr} HiLt).
  rewrite (poly_tobytes_offset3_addE i{hr} 1 HiLt _) 1:/#.
  rewrite (poly_tobytes_offset3_addE i{hr} 2 HiLt _) 1:/#.
  rewrite (poly_tobytes_index2E i{hr} HiLt).
  rewrite (poly_tobytes_index2_add1E i{hr} HiLt).
  rewrite -/poly_tobytes_canonical_word.
  rewrite (poly_tobytes_byte0_wordE
      ap0.[2 * W64.to_uint i{hr}] Heven).
  rewrite (poly_tobytes_byte1_wordE
      ap0.[2 * W64.to_uint i{hr}]
      ap0.[2 * W64.to_uint i{hr} + 1] Heven Hodd).
  rewrite (poly_tobytes_byte2_wordE
      ap0.[2 * W64.to_uint i{hr} + 1] Hodd).
  rewrite -/poly_tobytes_byte0_int -/poly_tobytes_byte1_int
    -/poly_tobytes_byte2_int.
  apply poly_tobytes_prefix_extend; first exact Hap0.
  + exact Hi384.
  exact Hprefix.
qed.

lemma poly_tobytes_lossless :
  islossless
    NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes.
proof.
  proc.
  while (0 <= W64.to_uint i <= 384) (384 - W64.to_uint i); last first.
  + auto => /> i0 Hi Hdone.
    rewrite W64.ultE /=.
    smt().
  auto => /> &hr Hi Hhigh Hloop.
  rewrite W64.ultE /= in Hloop.
  rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
qed.

lemma poly_tobytes_correct
    (rp0 : W8.t Array1152.t) (ap0 : W16.t Array768.t) :
  poly_tobytes_input_qrange ap0 =>
  phoare [NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes :
    rp = rp0 /\ ap = ap0 ==>
    res = poly_tobytes_spec ap0] = 1%r.
proof.
  move=> Hap0.
  by conseq poly_tobytes_lossless (poly_tobytes_functional rp0 ap0 Hap0).
qed.
