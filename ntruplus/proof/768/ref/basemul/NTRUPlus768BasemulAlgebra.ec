require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array4 NTRUPlus768Basemul.
require import Montgomery JWord_extra.
require import NTRUPlus768BasemulProof.

import Ring.IntID IntOrder.

op q : int = 3457.
op qinv : int = 12929.
op R : int = 2^16.
op Rinv : int = 2775.

clone import SignedReductions as NTRUPlusMontgomery with
  op k <- 16,
  op q <- q,
  op qinv <- qinv,
  op Rinv <- Rinv
  proof q_bnd by (rewrite /R => />)
  proof q_odd1 by (rewrite /R => />)
  proof qqinv by (rewrite /R => />)
  proof qinv_bnd by (rewrite /R => />)
  proof Rinv_gt0 by (rewrite /R => />)
  proof RRinv by (rewrite /R => />).

op coeff (w : W16.t) : int = W16.to_sint w.

op in_qrange (w : W16.t) : bool = -q <= coeff w < q.

op in_qrange4 (a : W16.t Array4.t) : bool =
  in_qrange a.[0] /\ in_qrange a.[1] /\ in_qrange a.[2] /\ in_qrange a.[3].

op zeta_mont_relation (z : W16.t) (zeta_math : int) : bool =
  -q <= zeta_math < q /\
  coeff z %% q = (zeta_math * (R %% q)) %% q.

op coeff0 (a b : W16.t Array4.t) (zeta_math : int) : int =
  coeff a.[0] * coeff b.[0] +
  zeta_math *
    (coeff a.[1] * coeff b.[3] +
     coeff a.[2] * coeff b.[2] +
     coeff a.[3] * coeff b.[1]).

op coeff1 (a b : W16.t Array4.t) (zeta_math : int) : int =
  coeff a.[0] * coeff b.[1] +
  coeff a.[1] * coeff b.[0] +
  zeta_math *
    (coeff a.[2] * coeff b.[3] +
     coeff a.[3] * coeff b.[2]).

op coeff2 (a b : W16.t Array4.t) (zeta_math : int) : int =
  coeff a.[0] * coeff b.[2] +
  coeff a.[1] * coeff b.[1] +
  coeff a.[2] * coeff b.[0] +
  zeta_math * (coeff a.[3] * coeff b.[3]).

op coeff3 (a b : W16.t Array4.t) (_zeta_math : int) : int =
  coeff a.[0] * coeff b.[3] +
  coeff a.[1] * coeff b.[2] +
  coeff a.[2] * coeff b.[1] +
  coeff a.[3] * coeff b.[0].

op t0_expr (a b : W16.t Array4.t) : int =
  coeff a.[1] * coeff b.[3] +
  coeff a.[2] * coeff b.[2] +
  coeff a.[3] * coeff b.[1].

op t1_expr (a b : W16.t Array4.t) : int =
  coeff a.[2] * coeff b.[3] +
  coeff a.[3] * coeff b.[2].

op t2_expr (a b : W16.t Array4.t) : int =
  coeff a.[3] * coeff b.[3].

op r0_expr (t0 z : W16.t) (a b : W16.t Array4.t) : int =
  coeff t0 * coeff z + coeff a.[0] * coeff b.[0].

op r1_expr (t1 z : W16.t) (a b : W16.t Array4.t) : int =
  coeff t1 * coeff z +
  coeff a.[0] * coeff b.[1] +
  coeff a.[1] * coeff b.[0].

op r2_expr (t2 z : W16.t) (a b : W16.t Array4.t) : int =
  coeff t2 * coeff z +
  coeff a.[0] * coeff b.[2] +
  coeff a.[1] * coeff b.[1] +
  coeff a.[2] * coeff b.[0].

op r3_expr (a b : W16.t Array4.t) : int =
  coeff a.[0] * coeff b.[3] +
  coeff a.[1] * coeff b.[2] +
  coeff a.[2] * coeff b.[1] +
  coeff a.[3] * coeff b.[0].

lemma smod_W16 (a : int) :
  NTRUPlusMontgomery.smod a W16.modulus =
  W16.smod (a %% W16.modulus).
proof. rewrite NTRUPlusMontgomery.smodE /W16.smod /=; smt(). qed.

lemma smod_W32 (a : int) :
  NTRUPlusMontgomery.smod a W32.modulus =
  W32.smod (a %% W32.modulus).
proof. rewrite NTRUPlusMontgomery.smodE /W32.smod /=; smt(). qed.

lemma W32_to_sint_inj (x y : W32.t) :
  W32.to_sint x = W32.to_sint y => x = y.
proof.
  rewrite W32.to_uint_eq !W32.to_sintE /W32.smod.
  have := W32.to_uint_cmp x.
  have := W32.to_uint_cmp y.
  smt().
qed.

lemma SAR_sem16 (a : W32.t) :
  a `|>>` W8.of_int 16 = W32.of_int (W32.to_sint a %/ 2^16).
proof.
  apply W32_to_sint_inj.
  rewrite /W32.(`|>>`) W8.of_uintK.
  have Hmod : 16 %% W8.modulus = 16.
  + smt().
  rewrite Hmod W32_sar_div.
  + smt().
  rewrite W32.to_sintK_small.
  + have Ha := W32.to_sint_cmp a.
    split.
    - apply lez_divRL.
      + smt(gt0_pow2).
      change (-2147483648 * 65536 <= W32.to_sint a).
      have Ha' : -2147483648 <= W32.to_sint a <= 2147483647.
      + apply W32.to_sint_cmp.
      smt().
    move=> _.
    have Hlt :
      W32.to_sint a %/ W16.modulus < W32.max_sint + 1.
    - rewrite ltz_divLR.
      + smt(gt0_pow2).
      change (W32.to_sint a < (2147483647 + 1) * 65536).
      have Ha' : -2147483648 <= W32.to_sint a <= 2147483647.
      + apply W32.to_sint_cmp.
      smt().
    rewrite -ltzS.
    assumption.
  done.
qed.

lemma modz_sub_dvd (u M d : int) :
  M %% d = 0 => (u - M) %% d = u %% d.
proof.
  move=> Hz.
  have Hn : (-M) %% d = 0.
  + apply/dvdzE; apply dvdzN; apply/dvdzE; exact Hz.
  rewrite (_ : u - M = u + (-M)).
  + ring.
  rewrite -modzDmr Hn /=.
  done.
qed.

lemma W32_of_sintK (w : W32.t) :
  W32.of_int (W32.to_sint w) = w.
proof.
  apply W32.to_uint_eq.
  rewrite W32.of_uintK W32.to_sintE /W32.smod.
  case (2 ^ (32 - 1) <= W32.to_uint w) => H.
  + rewrite (modz_sub_dvd (W32.to_uint w) W32.modulus W32.modulus).
    - by rewrite modzz.
    by rewrite W32.to_uint_mod.
  by rewrite W32.to_uint_mod.
qed.

lemma truncateu16_of_int (x : int) :
  truncateu16 (W32.of_int x) = W16.of_int x.
proof.
  apply W16.to_uint_eq.
  rewrite /truncateu16 /= W16.of_uintK W32.of_uintK W16.of_uintK.
  rewrite modz_dvd.
  + apply/dvdzP; exists 65536; ring.
  done.
qed.

lemma sigextu32E (w : W16.t) :
  sigextu32 w = W32.of_int (coeff w).
proof. by rewrite /coeff /sigextu32 /=. qed.

lemma truncateu16_mul_sint (a : W32.t) (x : int) :
  W16.to_sint (truncateu16 (a * W32.of_int x)) =
  NTRUPlusMontgomery.smod (W32.to_sint a * x) R.
proof.
  have Ha : a = W32.of_int (W32.to_sint a) by rewrite W32_of_sintK.
  rewrite {1}Ha W32.of_intM truncateu16_of_int W16.of_sintK.
  rewrite /R smod_W16.
  done.
qed.

lemma truncate_sar16 (a : W32.t) :
  W16.to_sint (truncateu16 (a `|>>` W8.of_int 16)) =
  NTRUPlusMontgomery.smod (W32.to_sint a %/ R) R.
proof.
  rewrite SAR_sem16 truncateu16_of_int W16.of_sintK.
  rewrite /R smod_W16.
  done.
qed.

lemma W32_sub_mul_sint (a : W32.t) (t : W16.t) :
  W32.to_sint (a - sigextu32 t * W32.of_int q) =
  NTRUPlusMontgomery.smod
    (W32.to_sint a - coeff t * q) (R * R).
proof.
  have Ha : a = W32.of_int (W32.to_sint a) by rewrite W32_of_sintK.
  rewrite {1}Ha sigextu32E W32.of_intM W32.of_intS'.
  rewrite W32.of_sintK /R smod_W32.
  rewrite /q /=.
  done.
qed.

lemma q_bounds :
  0 < q /\ q < R %/ 2.
proof. exact NTRUPlusMontgomery.q_bnd. qed.

lemma R_halfE : R %/ 2 = 32768.
proof.
  rewrite /R (_ : 2^16 = 65536).
  + ring.
  done.
qed.

lemma qrange_norm (x : int) :
  -q <= x < q => `|x| <= q.
proof.
  move=> Hx; rewrite ler_norml; smt().
qed.

lemma qrange_product_norm (x y : int) :
  -q <= x < q => -q <= y < q => `|x * y| <= q * q.
proof.
  move=> Hx Hy; rewrite normrM.
  apply ler_pmul.
  + exact (normr_ge0 x).
  + exact (normr_ge0 y).
  + exact (qrange_norm x Hx).
  exact (qrange_norm y Hy).
qed.

lemma product_bound x y :
  -q <= x < q => -q <= y < q =>
  -R %/ 2 * q <= x * y < R %/ 2 * q.
proof.
  move=> Hx Hy.
  have Hp := qrange_product_norm x y Hx Hy.
  have Hlim : q * q < R %/ 2 * q.
  + rewrite (ltr_pmul2r q).
    + by rewrite /q.
    rewrite R_halfE /q.
    smt().
  have Habs : `|x * y| < R %/ 2 * q by smt().
  move: Habs; rewrite ltr_norml; smt().
qed.

lemma product_sum2_bound x0 x1 y0 y1 :
  -q <= x0 < q => -q <= x1 < q =>
  -q <= y0 < q => -q <= y1 < q =>
  -R %/ 2 * q <= x0 * y0 + x1 * y1 < R %/ 2 * q.
proof.
  move=> Hx0 Hx1 Hy0 Hy1.
  have Hp0 := qrange_product_norm x0 y0 Hx0 Hy0.
  have Hp1 := qrange_product_norm x1 y1 Hx1 Hy1.
  have Htri := lez_norm_add (x0 * y0) (x1 * y1).
  have Hsum : `|x0 * y0 + x1 * y1| <= 2 * q * q by smt().
  have Hlim : 2 * q * q < R %/ 2 * q.
  + rewrite (ltr_pmul2r q).
    + by rewrite /q.
    rewrite R_halfE /q.
    smt().
  have Habs : `|x0 * y0 + x1 * y1| < R %/ 2 * q by smt().
  move: Habs; rewrite ltr_norml; smt().
qed.

lemma product_sum3_bound x0 x1 x2 y0 y1 y2 :
  -q <= x0 < q => -q <= x1 < q => -q <= x2 < q =>
  -q <= y0 < q => -q <= y1 < q => -q <= y2 < q =>
  -R %/ 2 * q <= x0 * y0 + x1 * y1 + x2 * y2 < R %/ 2 * q.
proof.
  move=> Hx0 Hx1 Hx2 Hy0 Hy1 Hy2.
  have Hp0 := qrange_product_norm x0 y0 Hx0 Hy0.
  have Hp1 := qrange_product_norm x1 y1 Hx1 Hy1.
  have Hp2 := qrange_product_norm x2 y2 Hx2 Hy2.
  have Htri0 := lez_norm_add (x0 * y0) (x1 * y1).
  have Htri1 := lez_norm_add (x0 * y0 + x1 * y1) (x2 * y2).
  have Hsum : `|x0 * y0 + x1 * y1 + x2 * y2| <= 3 * q * q by smt().
  have Hlim : 3 * q * q < R %/ 2 * q.
  + rewrite (ltr_pmul2r q).
    + by rewrite /q.
    rewrite R_halfE /q.
    smt().
  have Habs : `|x0 * y0 + x1 * y1 + x2 * y2| < R %/ 2 * q by smt().
  move: Habs; rewrite ltr_norml; smt().
qed.

lemma product_sum4_bound x0 x1 x2 x3 y0 y1 y2 y3 :
  -q <= x0 < q => -q <= x1 < q => -q <= x2 < q => -q <= x3 < q =>
  -q <= y0 < q => -q <= y1 < q => -q <= y2 < q => -q <= y3 < q =>
  -R %/ 2 * q <=
    x0 * y0 + x1 * y1 + x2 * y2 + x3 * y3 < R %/ 2 * q.
proof.
  move=> Hx0 Hx1 Hx2 Hx3 Hy0 Hy1 Hy2 Hy3.
  have Hp0 := qrange_product_norm x0 y0 Hx0 Hy0.
  have Hp1 := qrange_product_norm x1 y1 Hx1 Hy1.
  have Hp2 := qrange_product_norm x2 y2 Hx2 Hy2.
  have Hp3 := qrange_product_norm x3 y3 Hx3 Hy3.
  have Htri0 := lez_norm_add (x0 * y0) (x1 * y1).
  have Htri1 := lez_norm_add (x0 * y0 + x1 * y1) (x2 * y2).
  have Htri2 := lez_norm_add
    (x0 * y0 + x1 * y1 + x2 * y2) (x3 * y3).
  have Hsum :
    `|x0 * y0 + x1 * y1 + x2 * y2 + x3 * y3| <= 4 * q * q by smt().
  have Hlim : 4 * q * q < R %/ 2 * q.
  + rewrite (ltr_pmul2r q).
    + by rewrite /q.
    rewrite R_halfE /q.
    smt().
  have Habs :
    `|x0 * y0 + x1 * y1 + x2 * y2 + x3 * y3| < R %/ 2 * q by smt().
  move: Habs; rewrite ltr_norml; smt().
qed.

lemma RsqE :
  867 %% q = (R * R) %% q.
proof. by rewrite /R /q /=. qed.

lemma scaleE : (Rinv * 867 * Rinv) %% q = 1 %% q.
proof. by rewrite /Rinv /q /=. qed.

lemma double_montgomery_congr (o r e : int) :
  o %% q = (r * 867 * Rinv) %% q =>
  r %% q = (e * Rinv) %% q =>
  o %% q = e %% q.
proof.
  move=> Ho Hr.
  rewrite Ho (_ : r * 867 * Rinv = r * (867 * Rinv)).
  + ring.
  rewrite -modzMml Hr modzMml.
  rewrite (_ : e * Rinv * (867 * Rinv) = e * (Rinv * 867 * Rinv)).
  + ring.
  rewrite -modzMmr scaleE /=.
  done.
qed.

lemma montgomery_zeta_congr (t s z zm : int) :
  t %% q = (s * Rinv) %% q =>
  (z * Rinv) %% q = zm %% q =>
  (t * z) %% q = (s * zm) %% q.
proof.
  move=> Ht Hz.
  rewrite -modzMml Ht modzMml.
  rewrite (_ : s * Rinv * z = s * (z * Rinv)).
  + ring.
  rewrite -modzMmr Hz modzMmr.
  done.
qed.

lemma mul_i16E (a b : W16.t) :
  mul_i16 a b = W32.of_int (coeff a * coeff b).
proof. by rewrite /mul_i16 sigextu32E sigextu32E W32.of_intM. qed.

lemma montgomery_reduce_exact (a : W32.t) :
  W16.to_sint (montgomery_reduce a) =
  NTRUPlusMontgomery.SREDC (W32.to_sint a).
proof.
  rewrite /montgomery_reduce /=.
  rewrite truncate_sar16 W32_sub_mul_sint /coeff truncateu16_mul_sint.
  rewrite /NTRUPlusMontgomery.SREDC /=.
  rewrite NTRUPlusMontgomery.smod_div NTRUPlusMontgomery.smod_sq.
  rewrite /R /qinv /NTRUPlusMontgomery.R /q /=.
  done.
qed.

lemma montgomery_reduce_of_int (a : int) :
  -R %/ 2 * q <= a < R %/ 2 * q =>
  -q <= coeff (montgomery_reduce (W32.of_int a)) < q /\
  coeff (montgomery_reduce (W32.of_int a)) %% q = (a * Rinv) %% q.
proof.
  move=> Ha.
  have Hsmall : W32.to_sint (W32.of_int a) = a.
  + apply W32.to_sintK_small.
    move: Ha.
    rewrite /R /q /=.
    smt().
  have [Hbnd Hcongr] := NTRUPlusMontgomery.SREDCp_corr a (q_bounds) Ha.
  rewrite /coeff montgomery_reduce_exact Hsmall.
  by split.
qed.

lemma zeta_mont_Rinv (z : W16.t) (zeta_math : int) :
  zeta_mont_relation z zeta_math =>
  (coeff z * Rinv) %% q = zeta_math %% q.
proof.
  move=> [Hzb Hz].
  have HRR : ((R %% q) * Rinv) %% q = 1 %% q by smt(NTRUPlusMontgomery.RRinv).
  rewrite -modzMml Hz modzMml.
  rewrite (_ : zeta_math * (R %% q) * Rinv =
               zeta_math * ((R %% q) * Rinv)).
  + ring.
  rewrite -modzMmr HRR /=.
  done.
qed.

lemma basemul_spec_algebra
  (out a b : W16.t Array4.t) (z : W16.t) (zeta_math : int) :
  in_qrange4 a =>
  in_qrange4 b =>
  in_qrange z =>
  zeta_mont_relation z zeta_math =>
  let c = basemul_spec out a b z in
    in_qrange c.[0] /\ in_qrange c.[1] /\
    in_qrange c.[2] /\ in_qrange c.[3] /\
    coeff c.[0] %% q = coeff0 a b zeta_math %% q /\
    coeff c.[1] %% q = coeff1 a b zeta_math %% q /\
    coeff c.[2] %% q = coeff2 a b zeta_math %% q /\
    coeff c.[3] %% q = coeff3 a b zeta_math %% q.
proof.
  move=> Ha Hb Hz Hzeta.
  move: Ha Hb => [Ha0 [Ha1 [Ha2 Ha3]]] [Hb0 [Hb1 [Hb2 Hb3]]].
  have Ht0 :
    -q <= coeff (montgomery_reduce (W32.of_int (t0_expr a b))) < q /\
    coeff (montgomery_reduce (W32.of_int (t0_expr a b))) %% q =
      (t0_expr a b * Rinv) %% q.
  + apply montgomery_reduce_of_int.
    rewrite /t0_expr.
    exact (product_sum3_bound
      (coeff a.[1]) (coeff a.[2]) (coeff a.[3])
      (coeff b.[3]) (coeff b.[2]) (coeff b.[1])
      Ha1 Ha2 Ha3 Hb3 Hb2 Hb1).
  have Ht1 :
    -q <= coeff (montgomery_reduce (W32.of_int (t1_expr a b))) < q /\
    coeff (montgomery_reduce (W32.of_int (t1_expr a b))) %% q =
      (t1_expr a b * Rinv) %% q.
  + apply montgomery_reduce_of_int.
    rewrite /t1_expr.
    exact (product_sum2_bound
      (coeff a.[2]) (coeff a.[3])
      (coeff b.[3]) (coeff b.[2])
      Ha2 Ha3 Hb3 Hb2).
  have Ht2 :
    -q <= coeff (montgomery_reduce (W32.of_int (t2_expr a b))) < q /\
    coeff (montgomery_reduce (W32.of_int (t2_expr a b))) %% q =
      (t2_expr a b * Rinv) %% q.
  + apply montgomery_reduce_of_int.
    rewrite /t2_expr.
    exact (product_bound (coeff a.[3]) (coeff b.[3]) Ha3 Hb3).
  have [Ht0b Ht0c] := Ht0.
  have [Ht1b Ht1c] := Ht1.
  have [Ht2b Ht2c] := Ht2.
  pose t0w := montgomery_reduce (W32.of_int (t0_expr a b)).
  pose t1w := montgomery_reduce (W32.of_int (t1_expr a b)).
  pose t2w := montgomery_reduce (W32.of_int (t2_expr a b)).
  have Ht0wb : -q <= coeff t0w < q by rewrite /t0w; exact Ht0b.
  have Ht1wb : -q <= coeff t1w < q by rewrite /t1w; exact Ht1b.
  have Ht2wb : -q <= coeff t2w < q by rewrite /t2w; exact Ht2b.
  have Ht0wc : coeff t0w %% q = (t0_expr a b * Rinv) %% q
    by rewrite /t0w; exact Ht0c.
  have Ht1wc : coeff t1w %% q = (t1_expr a b * Rinv) %% q
    by rewrite /t1w; exact Ht1c.
  have Ht2wc : coeff t2w %% q = (t2_expr a b * Rinv) %% q
    by rewrite /t2w; exact Ht2c.
  have T0eq :
    montgomery_reduce
      (mul_i16 a.[1] b.[3] + mul_i16 a.[2] b.[2] + mul_i16 a.[3] b.[1]) = t0w.
    by rewrite /t0w /t0_expr !mul_i16E !W32.of_intD'.
  have T1eq :
    montgomery_reduce
      (mul_i16 a.[2] b.[3] + mul_i16 a.[3] b.[2]) = t1w.
    by rewrite /t1w /t1_expr !mul_i16E !W32.of_intD'.
  have T2eq :
    montgomery_reduce (mul_i16 a.[3] b.[3]) = t2w.
    by rewrite /t2w /t2_expr mul_i16E.
  have Hr0 :
    -q <= coeff (montgomery_reduce (W32.of_int (r0_expr t0w z a b))) < q /\
    coeff (montgomery_reduce (W32.of_int (r0_expr t0w z a b))) %% q =
      (r0_expr t0w z a b * Rinv) %% q.
  + apply montgomery_reduce_of_int.
    rewrite /r0_expr.
    exact (product_sum2_bound
      (coeff t0w) (coeff a.[0]) (coeff z) (coeff b.[0])
      Ht0wb Ha0 Hz Hb0).
  have Hr1 :
    -q <= coeff (montgomery_reduce (W32.of_int (r1_expr t1w z a b))) < q /\
    coeff (montgomery_reduce (W32.of_int (r1_expr t1w z a b))) %% q =
      (r1_expr t1w z a b * Rinv) %% q.
  + apply montgomery_reduce_of_int.
    rewrite /r1_expr.
    exact (product_sum3_bound
      (coeff t1w) (coeff a.[0]) (coeff a.[1])
      (coeff z) (coeff b.[1]) (coeff b.[0])
      Ht1wb Ha0 Ha1 Hz Hb1 Hb0).
  have Hr2 :
    -q <= coeff (montgomery_reduce (W32.of_int (r2_expr t2w z a b))) < q /\
    coeff (montgomery_reduce (W32.of_int (r2_expr t2w z a b))) %% q =
      (r2_expr t2w z a b * Rinv) %% q.
  + apply montgomery_reduce_of_int.
    rewrite /r2_expr.
    exact (product_sum4_bound
      (coeff t2w) (coeff a.[0]) (coeff a.[1]) (coeff a.[2])
      (coeff z) (coeff b.[2]) (coeff b.[1]) (coeff b.[0])
      Ht2wb Ha0 Ha1 Ha2 Hz Hb2 Hb1 Hb0).
  have Hr3 :
    -q <= coeff (montgomery_reduce (W32.of_int (r3_expr a b))) < q /\
    coeff (montgomery_reduce (W32.of_int (r3_expr a b))) %% q =
      (r3_expr a b * Rinv) %% q.
  + apply montgomery_reduce_of_int.
    rewrite /r3_expr.
    exact (product_sum4_bound
      (coeff a.[0]) (coeff a.[1]) (coeff a.[2]) (coeff a.[3])
      (coeff b.[3]) (coeff b.[2]) (coeff b.[1]) (coeff b.[0])
      Ha0 Ha1 Ha2 Ha3 Hb3 Hb2 Hb1 Hb0).
  have [Hr0b Hr0c] := Hr0.
  have [Hr1b Hr1c] := Hr1.
  have [Hr2b Hr2c] := Hr2.
  have [Hr3b Hr3c] := Hr3.
  pose r0w := montgomery_reduce (W32.of_int (r0_expr t0w z a b)).
  pose r1w := montgomery_reduce (W32.of_int (r1_expr t1w z a b)).
  pose r2w := montgomery_reduce (W32.of_int (r2_expr t2w z a b)).
  pose r3w := montgomery_reduce (W32.of_int (r3_expr a b)).
  have Hr0wb : -q <= coeff r0w < q by rewrite /r0w; exact Hr0b.
  have Hr1wb : -q <= coeff r1w < q by rewrite /r1w; exact Hr1b.
  have Hr2wb : -q <= coeff r2w < q by rewrite /r2w; exact Hr2b.
  have Hr3wb : -q <= coeff r3w < q by rewrite /r3w; exact Hr3b.
  have Hr0wc : coeff r0w %% q = (r0_expr t0w z a b * Rinv) %% q
    by rewrite /r0w; exact Hr0c.
  have Hr1wc : coeff r1w %% q = (r1_expr t1w z a b * Rinv) %% q
    by rewrite /r1w; exact Hr1c.
  have Hr2wc : coeff r2w %% q = (r2_expr t2w z a b * Rinv) %% q
    by rewrite /r2w; exact Hr2c.
  have Hr3wc : coeff r3w %% q = (r3_expr a b * Rinv) %% q
    by rewrite /r3w; exact Hr3c.
  have R0eq :
    montgomery_reduce
      (mul_i16 t0w z + mul_i16 a.[0] b.[0]) = r0w.
    by rewrite /r0w /r0_expr !mul_i16E !W32.of_intD'.
  have R1eq :
    montgomery_reduce
      (mul_i16 t1w z + mul_i16 a.[0] b.[1] + mul_i16 a.[1] b.[0]) = r1w.
    by rewrite /r1w /r1_expr !mul_i16E !W32.of_intD'.
  have R2eq :
    montgomery_reduce
      (mul_i16 t2w z + mul_i16 a.[0] b.[2] + mul_i16 a.[1] b.[1] +
       mul_i16 a.[2] b.[0]) = r2w.
    by rewrite /r2w /r2_expr !mul_i16E !W32.of_intD'.
  have R3eq :
    montgomery_reduce
      (mul_i16 a.[0] b.[3] + mul_i16 a.[1] b.[2] +
       mul_i16 a.[2] b.[1] + mul_i16 a.[3] b.[0]) = r3w.
    by rewrite /r3w /r3_expr !mul_i16E !W32.of_intD'.
  have H867 : -q <= 867 < q by rewrite /q.
  have Ho0 :
    -q <= coeff (montgomery_reduce (W32.of_int (coeff r0w * 867))) < q /\
    coeff (montgomery_reduce (W32.of_int (coeff r0w * 867))) %% q =
      (coeff r0w * 867 * Rinv) %% q.
  + apply montgomery_reduce_of_int.
    exact (product_bound (coeff r0w) 867 Hr0wb H867).
  have Ho1 :
    -q <= coeff (montgomery_reduce (W32.of_int (coeff r1w * 867))) < q /\
    coeff (montgomery_reduce (W32.of_int (coeff r1w * 867))) %% q =
      (coeff r1w * 867 * Rinv) %% q.
  + apply montgomery_reduce_of_int.
    exact (product_bound (coeff r1w) 867 Hr1wb H867).
  have Ho2 :
    -q <= coeff (montgomery_reduce (W32.of_int (coeff r2w * 867))) < q /\
    coeff (montgomery_reduce (W32.of_int (coeff r2w * 867))) %% q =
      (coeff r2w * 867 * Rinv) %% q.
  + apply montgomery_reduce_of_int.
    exact (product_bound (coeff r2w) 867 Hr2wb H867).
  have Ho3 :
    -q <= coeff (montgomery_reduce (W32.of_int (coeff r3w * 867))) < q /\
    coeff (montgomery_reduce (W32.of_int (coeff r3w * 867))) %% q =
      (coeff r3w * 867 * Rinv) %% q.
  + apply montgomery_reduce_of_int.
    exact (product_bound (coeff r3w) 867 Hr3wb H867).
  pose o0w := montgomery_reduce (W32.of_int (coeff r0w * 867)).
  pose o1w := montgomery_reduce (W32.of_int (coeff r1w * 867)).
  pose o2w := montgomery_reduce (W32.of_int (coeff r2w * 867)).
  pose o3w := montgomery_reduce (W32.of_int (coeff r3w * 867)).
  have [Ho0b Ho0c] := Ho0.
  have [Ho1b Ho1c] := Ho1.
  have [Ho2b Ho2c] := Ho2.
  have [Ho3b Ho3c] := Ho3.
  have Ho0wb : in_qrange o0w by rewrite /in_qrange /o0w; exact Ho0b.
  have Ho1wb : in_qrange o1w by rewrite /in_qrange /o1w; exact Ho1b.
  have Ho2wb : in_qrange o2w by rewrite /in_qrange /o2w; exact Ho2b.
  have Ho3wb : in_qrange o3w by rewrite /in_qrange /o3w; exact Ho3b.
  have Ho0wc : coeff o0w %% q = (coeff r0w * 867 * Rinv) %% q
    by rewrite /o0w; exact Ho0c.
  have Ho1wc : coeff o1w %% q = (coeff r1w * 867 * Rinv) %% q
    by rewrite /o1w; exact Ho1c.
  have Ho2wc : coeff o2w %% q = (coeff r2w * 867 * Rinv) %% q
    by rewrite /o2w; exact Ho2c.
  have Ho3wc : coeff o3w %% q = (coeff r3w * 867 * Rinv) %% q
    by rewrite /o3w; exact Ho3c.
  have O0eq :
    montgomery_reduce (mul_i16 r0w (W16.of_int 867)) = o0w.
    by rewrite /o0w mul_i16E /coeff W16.of_sintK /W16.smod /=.
  have O1eq :
    montgomery_reduce (mul_i16 r1w (W16.of_int 867)) = o1w.
    by rewrite /o1w mul_i16E /coeff W16.of_sintK /W16.smod /=.
  have O2eq :
    montgomery_reduce (mul_i16 r2w (W16.of_int 867)) = o2w.
    by rewrite /o2w mul_i16E /coeff W16.of_sintK /W16.smod /=.
  have O3eq :
    montgomery_reduce (mul_i16 r3w (W16.of_int 867)) = o3w.
    by rewrite /o3w mul_i16E /coeff W16.of_sintK /W16.smod /=.
  have HzR := zeta_mont_Rinv z zeta_math Hzeta.
  have Hout0 := double_montgomery_congr
    (coeff o0w) (coeff r0w) (r0_expr t0w z a b) Ho0wc Hr0wc.
  have Hout1 := double_montgomery_congr
    (coeff o1w) (coeff r1w) (r1_expr t1w z a b) Ho1wc Hr1wc.
  have Hout2 := double_montgomery_congr
    (coeff o2w) (coeff r2w) (r2_expr t2w z a b) Ho2wc Hr2wc.
  have Hout3 := double_montgomery_congr
    (coeff o3w) (coeff r3w) (r3_expr a b) Ho3wc Hr3wc.
  have Htz0 := montgomery_zeta_congr
    (coeff t0w) (t0_expr a b) (coeff z) zeta_math Ht0wc HzR.
  have Htz1 := montgomery_zeta_congr
    (coeff t1w) (t1_expr a b) (coeff z) zeta_math Ht1wc HzR.
  have Htz2 := montgomery_zeta_congr
    (coeff t2w) (t2_expr a b) (coeff z) zeta_math Ht2wc HzR.
  have Hpoly0 :
    r0_expr t0w z a b %% q = coeff0 a b zeta_math %% q.
  + rewrite /r0_expr /coeff0.
    rewrite -modzDml Htz0 modzDml /t0_expr.
    have Hring0 :
      (coeff a.[1] * coeff b.[3] + coeff a.[2] * coeff b.[2] +
       coeff a.[3] * coeff b.[1]) * zeta_math +
        coeff a.[0] * coeff b.[0] =
      coeff a.[0] * coeff b.[0] +
        zeta_math *
          (coeff a.[1] * coeff b.[3] + coeff a.[2] * coeff b.[2] +
           coeff a.[3] * coeff b.[1])
      by ring.
    rewrite Hring0.
    done.
  have Hpoly1 :
    r1_expr t1w z a b %% q = coeff1 a b zeta_math %% q.
  + rewrite /r1_expr /coeff1.
    rewrite (_ :
      coeff t1w * coeff z + coeff a.[0] * coeff b.[1] +
        coeff a.[1] * coeff b.[0] =
      coeff t1w * coeff z +
        (coeff a.[0] * coeff b.[1] + coeff a.[1] * coeff b.[0])).
    + ring.
    rewrite -modzDml Htz1 modzDml /t1_expr.
    have Hring1 :
      (coeff a.[2] * coeff b.[3] + coeff a.[3] * coeff b.[2]) *
          zeta_math +
        (coeff a.[0] * coeff b.[1] + coeff a.[1] * coeff b.[0]) =
      coeff a.[0] * coeff b.[1] + coeff a.[1] * coeff b.[0] +
        zeta_math *
          (coeff a.[2] * coeff b.[3] + coeff a.[3] * coeff b.[2])
      by ring.
    rewrite Hring1.
    done.
  have Hpoly2 :
    r2_expr t2w z a b %% q = coeff2 a b zeta_math %% q.
  + rewrite /r2_expr /coeff2.
    rewrite (_ :
      coeff t2w * coeff z + coeff a.[0] * coeff b.[2] +
        coeff a.[1] * coeff b.[1] + coeff a.[2] * coeff b.[0] =
      coeff t2w * coeff z +
        (coeff a.[0] * coeff b.[2] + coeff a.[1] * coeff b.[1] +
         coeff a.[2] * coeff b.[0])).
    + ring.
    rewrite -modzDml Htz2 modzDml /t2_expr.
    have Hring2 :
      coeff a.[3] * coeff b.[3] * zeta_math +
        (coeff a.[0] * coeff b.[2] + coeff a.[1] * coeff b.[1] +
         coeff a.[2] * coeff b.[0]) =
      coeff a.[0] * coeff b.[2] + coeff a.[1] * coeff b.[1] +
        coeff a.[2] * coeff b.[0] +
        zeta_math * (coeff a.[3] * coeff b.[3])
      by ring.
    rewrite Hring2.
    done.
  have Hpoly3 :
    r3_expr a b %% q = coeff3 a b zeta_math %% q
    by rewrite /r3_expr /coeff3.
  have Hmod1 :
    coeff o1w %% q = coeff1 a b zeta_math %% q
    by rewrite Hout1 Hpoly1.
  have Hmod0 :
    coeff o0w %% q = coeff0 a b zeta_math %% q
    by rewrite Hout0 Hpoly0.
  have Hmod2 :
    coeff o2w %% q = coeff2 a b zeta_math %% q
    by rewrite Hout2 Hpoly2.
  have Hmod3 :
    coeff o3w %% q = coeff3 a b zeta_math %% q
    by rewrite Hout3 Hpoly3.
  rewrite /basemul_spec /=.
  rewrite T0eq T1eq T2eq R0eq R1eq R2eq R3eq O0eq O1eq O2eq O3eq.
  split; first exact Ho0wb.
  split; first exact Ho1wb.
  split; first exact Ho2wb.
  split; first exact Ho3wb.
  split; first exact Hmod0.
  split; first exact Hmod1.
  split; first exact Hmod2.
  exact Hmod3.
qed.
