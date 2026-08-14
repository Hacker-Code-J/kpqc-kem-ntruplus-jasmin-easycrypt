require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord JModel_x86.

require import W16extra.
require import JWord_extra.
require import Array768.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768NTTStage1Algebra.
require import NTRUPlus768Crepmod3Proof.

import Ring.IntID IntOrder.

op qhalf_hi : int = (q + 1) %/ 2.
op qhalf_lo : int = (q - 1) %/ 2.
op crepmod3_v : int = 10923.
op crepmod3_bias : int = 16384.
op crepmod3_shift : int = 2 ^ 15.

op lift_nonneg (x : int) : int =
  if x < 0 then x + q else x.

op centered_q_input (x : int) : int =
  let x1 = lift_nonneg x in
  let x2 = x1 - qhalf_hi in
  let x3 = if x2 < 0 then x2 + q else x2 in
  x3 - qhalf_lo.

op crepmod3_quot (x : int) : int =
  (crepmod3_v * x + crepmod3_bias) %/ crepmod3_shift.

op crepmod3_int (x : int) : int =
  let centered = centered_q_input x in
  centered - 3 * crepmod3_quot centered.

op is_trit (x : int) : bool =
  x = -1 \/ x = 0 \/ x = 1.

op poly_crepmod3_algebra
    (input output : W16.t Array768.t) : bool =
  forall j, 0 <= j < 768 =>
    is_trit (coeff output.[j]) /\
    coeff output.[j] %% 3 = centered_q_input (coeff input.[j]) %% 3.

lemma qhalf_hiE : qhalf_hi = 1729.
proof. by rewrite /qhalf_hi /q /=. qed.

lemma qhalf_loE : qhalf_lo = 1728.
proof. by rewrite /qhalf_lo /q /=. qed.

lemma W16_min_sint_value : W16.min_sint = -32768 by done.
lemma W16_max_sint_value : W16.max_sint = 32767 by done.

lemma W16_of_int_mone : W16.of_int (-1) = W16.onew.
proof.
  apply W16.to_uint_eq.
  rewrite W16.of_uintK W16.to_uint_onew /=.
  done.
qed.

lemma crepmod3_modz_sub_dvd (u m d : int) :
  m %% d = 0 => (u - m) %% d = u %% d.
proof.
  move=> Hmd.
  have Hneg : (-m) %% d = 0.
  + apply/dvdzE; apply dvdzN; apply/dvdzE; exact Hmd.
  rewrite (_ : u - m = u + (-m)) 1:/#.
  by rewrite -modzDmr Hneg /=.
qed.

lemma crepmod3_w16_of_sintK (w : W16.t) :
  W16.of_int (W16.to_sint w) = w.
proof.
  apply W16.to_uint_eq.
  rewrite W16.of_uintK W16.to_sintE /W16.smod.
  case (2 ^ (16 - 1) <= W16.to_uint w) => Hsign.
  + rewrite (crepmod3_modz_sub_dvd
      (W16.to_uint w) W16.modulus W16.modulus).
    - by rewrite modzz.
    by rewrite W16.to_uint_mod.
  by rewrite W16.to_uint_mod.
qed.

lemma word_from_coeff (w : W16.t) :
  w = W16.of_int (coeff w).
proof. by rewrite /coeff crepmod3_w16_of_sintK. qed.

lemma coeff_of_word_small (x : int) :
  W16.min_sint <= x <= W16.max_sint =>
  coeff (W16.of_int x) = x.
proof.
  move=> Hx.
  rewrite /coeff.
  exact (W16.to_sintK_small x Hx).
qed.

lemma SAR_sem15 (a : W32.t) :
  a `|>>` W8.of_int 15 = W32.of_int (W32.to_sint a %/ 2 ^ 15).
proof.
  apply W32_to_sint_inj.
  rewrite /W32.(`|>>`) W8.of_uintK.
  have Hmod : 15 %% W8.modulus = 15 by smt().
  rewrite Hmod W32_sar_div.
  + smt().
  rewrite W32.to_sintK_small.
  + have Ha' : -2147483648 <= W32.to_sint a <= 2147483647 by apply W32.to_sint_cmp.
    split.
    + have Hpow : 0 < 2 ^ 15 by smt(gt0_pow2).
      smt().
    move=> _.
    have Hpow : 0 < 2 ^ 15 by smt(gt0_pow2).
    rewrite -ltzS.
    smt().
  done.
qed.

lemma sign_mask_of_int (x : int) :
  W16.min_sint <= x <= W16.max_sint =>
  ((W16.of_int x `|>>` W8.of_int 15) `&` W16.of_int q) =
  W16.of_int (if x < 0 then q else 0).
proof.
  move=> Hx.
  have Hcoeff :
      coeff (W16.of_int x `|>>` W8.of_int 15) = x %/ 2 ^ 15.
  + rewrite /coeff W16_sar_div 1:/#.
    rewrite (W16.to_sintK_small x Hx).
    done.
  case (x < 0) => Hsign.
  + rewrite (word_from_coeff (W16.of_int x `|>>` W8.of_int 15)).
    have Hdiv : x %/ 2 ^ 15 = -1.
    + have Hmin : -32768 <= x by smt(W16_min_sint_value).
      have Hmax : x <= 32767 by smt(W16_max_sint_value).
      have Hpos : 0 < -x by smt().
      have Hbound : -x <= 32768 by smt().
      rewrite (_ : x = -(-x)) 1:/#.
      rewrite divNz 1:Hpos 1:/#.
      rewrite divz_small; smt().
    rewrite Hcoeff Hdiv /=.
    by rewrite W16_of_int_mone W16.andwC W16.andw1.
  rewrite (word_from_coeff (W16.of_int x `|>>` W8.of_int 15)).
  have Hdiv : x %/ 2 ^ 15 = 0.
  + have Hmin : -32768 <= x by smt(W16_min_sint_value).
    have Hmax : x <= 32767 by smt(W16_max_sint_value).
    rewrite divz_small; smt().
  rewrite Hcoeff Hdiv /=.
  done.
qed.

lemma lift_nonneg_range (x : int) :
  -q <= x < q =>
  0 <= lift_nonneg x < q.
proof.
  move=> Hx.
  rewrite /lift_nonneg.
  case (x < 0); smt().
qed.

lemma centered_q_input_range (x : int) :
  -q <= x < q =>
  -1728 <= centered_q_input x <= 1728.
proof.
  move=> Hx.
  rewrite /centered_q_input /lift_nonneg qhalf_hiE qhalf_loE.
  have Hlift := lift_nonneg_range x Hx.
  case (x < 0); smt().
qed.

lemma centered_q_input_congr (x : int) :
  -q <= x < q =>
  centered_q_input x %% q = x %% q.
proof.
  move=> Hx.
  rewrite /centered_q_input /lift_nonneg qhalf_hiE qhalf_loE.
  case (x < 0) => Hneg; smt().
qed.

lemma centered_q_input_small (x : int) :
  -q <= x < q =>
  W16.min_sint <= centered_q_input x <= W16.max_sint.
proof.
  move=> Hx.
  have Hrange := centered_q_input_range x Hx.
  smt().
qed.

op centered_word (a : W16.t) : W16.t =
  let mask = (a `|>>` W8.of_int 15) `&` W16.of_int q in
  let a = a + mask in
  let a = a - W16.of_int qhalf_hi in
  let mask = (a `|>>` W8.of_int 15) `&` W16.of_int q in
  let a = a + mask in
  a - W16.of_int qhalf_lo.

lemma centered_word_qrangeE (a : W16.t) :
  in_qrange a =>
  centered_word a = W16.of_int (centered_q_input (coeff a)).
proof.
  move=> Ha.
  pose x := coeff a.
  have Hx : -q <= x < q by exact Ha.
  have Ha' : a = W16.of_int x.
  + rewrite /x.
    exact (word_from_coeff a).
  rewrite /centered_word Ha' /centered_q_input /lift_nonneg.
  have Hwx : W16.min_sint <= x <= W16.max_sint by rewrite /q; smt().
  rewrite (sign_mask_of_int x Hwx) qhalf_hiE qhalf_loE.
  case (x < 0) => Hnegx.
  + rewrite /= ?W16.of_intD' ?W16.of_intS'.
    have Hx2 : W16.min_sint <= x + q - 1729 <= W16.max_sint by rewrite /q; smt().
    rewrite (sign_mask_of_int (x + q - 1729) Hx2).
    case (x + q - 1729 < 0) => Hx2sign.
    + rewrite /= ?W16.of_intD' ?W16.of_intS'.
      done.
    rewrite /= ?W16.of_intD' ?W16.of_intS'.
    done.
  rewrite /= ?W16.of_intD' ?W16.of_intS'.
  have Hx2 : W16.min_sint <= x - 1729 <= W16.max_sint by rewrite /q; smt().
  rewrite (sign_mask_of_int (x - 1729) Hx2).
  case (x - 1729 < 0).
  + move=> Hx2neg.
    rewrite /= ?W16.of_intD' ?W16.of_intS'.
    done.
  move=> Hx2nonneg.
  rewrite /= ?W16.of_intD' ?W16.of_intS'.
  done.
qed.

lemma crepmod3_round_wordE (x : int) :
  -1728 <= x <= 1728 =>
  truncateu16
    (((sigextu32 (W16.of_int x) * W32.of_int crepmod3_v)
       + W32.of_int crepmod3_bias) `|>>` W8.of_int 15) =
  W16.of_int (crepmod3_quot x).
proof.
  move=> Hx.
  have Hx16 : W16.min_sint <= x <= W16.max_sint by smt().
  have Hword :
      sigextu32 (W16.of_int x) * W32.of_int crepmod3_v +
          W32.of_int crepmod3_bias =
      W32.of_int (crepmod3_v * x + crepmod3_bias).
  + rewrite sigextu32E (coeff_of_word_small x Hx16).
    rewrite W32.of_intM W32.of_intD'.
    ring.
  have Hsmall : W32.min_sint <= crepmod3_v * x + crepmod3_bias <= W32.max_sint.
  + smt().
  rewrite Hword SAR_sem15 truncateu16_of_int.
  rewrite (W32.to_sintK_small (crepmod3_v * x + crepmod3_bias) Hsmall).
  rewrite /crepmod3_quot /crepmod3_shift.
  done.
qed.

lemma crepmod3_word_centeredE (a : W16.t) :
  NTRUPlus768Crepmod3Proof.crepmod3_word a =
  let centered = centered_word a in
  let td = sigextu32 centered * W32.of_int crepmod3_v +
      W32.of_int crepmod3_bias in
  let t = truncateu16 (td `|>>` W8.of_int 15) in
  centered - t * W16.of_int 3.
proof.
  rewrite /NTRUPlus768Crepmod3Proof.crepmod3_word /centered_word.
  rewrite /NTRUPlus768Crepmod3Proof.qword
          /NTRUPlus768Crepmod3Proof.qhalf_hi_word
          /NTRUPlus768Crepmod3Proof.qhalf_lo_word
          /NTRUPlus768Crepmod3Proof.vword
          /NTRUPlus768Crepmod3Proof.biasword.
  rewrite /qhalf_hi /qhalf_lo /q /crepmod3_v /crepmod3_bias /=.
  done.
qed.

lemma crepmod3_word_qrangeE (a : W16.t) :
  in_qrange a =>
  NTRUPlus768Crepmod3Proof.crepmod3_word a =
  W16.of_int (crepmod3_int (coeff a)).
proof.
  move=> Ha.
  pose centered := centered_q_input (coeff a).
  have Hcentered : -1728 <= centered <= 1728.
  + exact (centered_q_input_range (coeff a) Ha).
  rewrite crepmod3_word_centeredE /=.
  rewrite (centered_word_qrangeE a Ha).
  rewrite (crepmod3_round_wordE centered Hcentered).
  rewrite ?W16.of_intM ?W16.of_intS'.
  rewrite (_ : crepmod3_quot centered * 3 =
               3 * crepmod3_quot centered) 1:/#.
  by rewrite /crepmod3_int /centered.
qed.

lemma crepmod3_quot_exact_m1 (k : int) :
  -575 <= k <= 576 =>
  crepmod3_quot (3 * k - 1) = k.
proof.
  move=> Hk.
  rewrite /crepmod3_quot /crepmod3_shift.
  have -> :
      crepmod3_v * (3 * k - 1) + crepmod3_bias =
      k * (2 ^ 15) + (k + 5461).
  + rewrite /crepmod3_v /crepmod3_bias.
    ring.
  rewrite divzMDl 1:/#.
  have -> : (k + 5461) %/ (2 ^ 15) = 0.
  + rewrite divz_small; smt().
  ring.
qed.

lemma crepmod3_quot_exact_0 (k : int) :
  -576 <= k <= 576 =>
  crepmod3_quot (3 * k) = k.
proof.
  move=> Hk.
  rewrite /crepmod3_quot /crepmod3_shift.
  have -> :
      crepmod3_v * (3 * k) + crepmod3_bias =
      k * (2 ^ 15) + (k + 16384).
  + rewrite /crepmod3_v /crepmod3_bias.
    ring.
  rewrite divzMDl 1:/#.
  have -> : (k + 16384) %/ (2 ^ 15) = 0.
  + rewrite divz_small; smt().
  ring.
qed.

lemma crepmod3_quot_exact_p1 (k : int) :
  -576 <= k <= 575 =>
  crepmod3_quot (3 * k + 1) = k.
proof.
  move=> Hk.
  rewrite /crepmod3_quot /crepmod3_shift.
  have -> :
      crepmod3_v * (3 * k + 1) + crepmod3_bias =
      k * (2 ^ 15) + (k + 27307).
  + rewrite /crepmod3_v /crepmod3_bias.
    ring.
  rewrite divzMDl 1:/#.
  have -> : (k + 27307) %/ (2 ^ 15) = 0.
  + rewrite divz_small; smt().
  ring.
qed.

lemma crepmod3_centered_trit (x : int) :
  -1728 <= x <= 1728 =>
  is_trit (x - 3 * crepmod3_quot x).
proof.
  move=> Hx.
  rewrite /is_trit.
  case (x %% 3 = 0) => Hmod0.
  + pose k := x %/ 3.
    have Hdiv : x = 3 * k by rewrite /k; smt(divz_eq).
    have Hk : -576 <= k <= 576 by smt().
    have Hquot : crepmod3_quot x = k.
    + rewrite Hdiv.
      exact (crepmod3_quot_exact_0 k Hk).
    rewrite Hquot.
    smt().
  case (x %% 3 = 1) => Hmod1.
  + pose k := x %/ 3.
    have Hdiv : x = 3 * k + 1 by rewrite /k; smt(divz_eq).
    have Hk : -576 <= k <= 575 by smt().
    have Hquot : crepmod3_quot x = k.
    + rewrite Hdiv.
      exact (crepmod3_quot_exact_p1 k Hk).
    rewrite Hquot.
    smt().
  have Hmod2 : x %% 3 = 2 by smt().
  pose k := (x + 1) %/ 3.
  have Hdiv : x = 3 * k - 1 by rewrite /k; smt(divz_eq).
  have Hk : -575 <= k <= 576 by smt().
  have Hquot : crepmod3_quot x = k.
  + rewrite Hdiv.
    exact (crepmod3_quot_exact_m1 k Hk).
  rewrite Hquot.
  smt().
qed.

lemma crepmod3_int_trit (x : int) :
  -q <= x < q =>
  is_trit (crepmod3_int x).
proof.
  move=> Hx.
  exact (crepmod3_centered_trit
    (centered_q_input x) (centered_q_input_range x Hx)).
qed.

lemma crepmod3_int_mod3 (x : int) :
  -q <= x < q =>
  crepmod3_int x %% 3 = centered_q_input x %% 3.
proof.
  move=> Hx.
  have Hmultiple :
      (3 * crepmod3_quot (centered_q_input x)) %% 3 = 0
    by rewrite mulzC modzMl.
  exact (crepmod3_modz_sub_dvd
    (centered_q_input x)
    (3 * crepmod3_quot (centered_q_input x))
    3 Hmultiple).
qed.

lemma poly_crepmod3_spec_algebra (p : W16.t Array768.t) :
  NTRUPlus768NTTStage1Algebra.input_qrange p =>
  poly_crepmod3_algebra p (NTRUPlus768Crepmod3Proof.poly_crepmod3_spec p).
proof.
  move=> Hinput j Hj.
  have Hq : in_qrange p.[j] by exact (Hinput j Hj).
  rewrite /poly_crepmod3_algebra /NTRUPlus768Crepmod3Proof.poly_crepmod3_spec.
  rewrite Array768.initiE 1:Hj.
  change (is_trit
      (coeff (NTRUPlus768Crepmod3Proof.crepmod3_word p.[j])) /\
    coeff (NTRUPlus768Crepmod3Proof.crepmod3_word p.[j]) %% 3 =
      centered_q_input (coeff p.[j]) %% 3).
  have Hword := crepmod3_word_qrangeE p.[j] Hq.
  rewrite Hword.
  have Htrit := crepmod3_int_trit (coeff p.[j]) Hq.
  have Hsmall :
      W16.min_sint <= crepmod3_int (coeff p.[j]) <= W16.max_sint.
  + have Htrit' := Htrit.
    move: Htrit'.
    rewrite /is_trit.
    move=> [Hminus | [Hzero | Hone]].
    - rewrite Hminus W16_min_sint_value W16_max_sint_value; done.
    - rewrite Hzero W16_min_sint_value W16_max_sint_value; done.
    rewrite Hone W16_min_sint_value W16_max_sint_value; done.
  rewrite (coeff_of_word_small (crepmod3_int (coeff p.[j])) Hsmall).
  split.
  + exact Htrit.
  exact (crepmod3_int_mod3 (coeff p.[j]) Hq).
qed.

lemma poly_crepmod3_spec_input_qrange (p : W16.t Array768.t) :
  NTRUPlus768NTTStage1Algebra.input_qrange p =>
  NTRUPlus768NTTStage1Algebra.input_qrange
    (NTRUPlus768Crepmod3Proof.poly_crepmod3_spec p).
proof.
  move=> Hinput j Hj.
  have Halg := poly_crepmod3_spec_algebra p Hinput j Hj.
  move: Halg => [Htrit _].
  rewrite /in_qrange.
  move: Htrit.
  rewrite /is_trit.
  move=> [Hminus | [Hzero | Hone]].
  + rewrite Hminus /q; done.
  + rewrite Hzero /q; done.
  rewrite Hone /q; done.
qed.

lemma poly_crepmod3_algebra_functional
    (rp0 ap0 : W16.t Array768.t) :
  NTRUPlus768NTTStage1Algebra.input_qrange ap0 =>
  hoare [NTRUPlus768Crepmod3.M.jade_ntruplus_ntruplus768_amd64_ref_poly_crepmod3 :
    rp = rp0 /\ ap = ap0 ==> poly_crepmod3_algebra ap0 res].
proof.
  move=> Hinput.
  conseq (NTRUPlus768Crepmod3Proof.poly_crepmod3_functional rp0 ap0) => /> &hr Hap j.
  rewrite Hap.
  move=> Hj.
  exact (poly_crepmod3_spec_algebra ap0 Hinput j Hj).
qed.

lemma poly_crepmod3_correct_algebra
    (rp0 ap0 : W16.t Array768.t) :
  NTRUPlus768NTTStage1Algebra.input_qrange ap0 =>
  phoare [NTRUPlus768Crepmod3.M.jade_ntruplus_ntruplus768_amd64_ref_poly_crepmod3 :
    rp = rp0 /\ ap = ap0 ==> poly_crepmod3_algebra ap0 res] = 1%r.
proof.
  move=> Hinput.
  have Hfunctional := poly_crepmod3_algebra_functional rp0 ap0 Hinput.
  by conseq NTRUPlus768Crepmod3Proof.poly_crepmod3_lossless Hfunctional.
qed.
