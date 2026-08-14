require import AllCore IntDiv List Ring StdOrder.
from Jasmin require import JWord.

require import Array4 Array96 Array768.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768NTTSchedule.
require import NTRUPlus768PolyBasemul.
require import NTRUPlus768PolyBasemulProof.
require import W16extra.

import IntOrder.

op zetas96_words : W16.t list = map W16.of_int (drop 96 zetas192_coeffs).

op zeta_coeff (i : int) : int = zetas192_coeff (96 + i).

op in_qrange768 (p : W16.t Array768.t) : bool =
  forall k, 0 <= k < 192 => in_qrange4 (block4 p k).

op in_s12range768 (p : W16.t Array768.t) : bool =
  forall k, 0 <= k < 192 => in_s12range4 (block4 p k).

op zeta_decode (z : W16.t) : int =
  (coeff z * Rinv) %% q.

op block_zeta_math (k : int) : int =
  zeta_decode (block_zeta k).

op poly_basemul_qring
    (ap bp rp : W16.t Array768.t) (upto : int) : bool =
  forall k, 0 <= k < upto =>
    let ak = block4 ap k in
    let bk = block4 bp k in
    let rk = block4 rp k in
      in_qrange4 rk /\
      coeff rk.[0] %% q = coeff0 ak bk (terminal_value k) %% q /\
      coeff rk.[1] %% q = coeff1 ak bk (terminal_value k) %% q /\
      coeff rk.[2] %% q = coeff2 ak bk (terminal_value k) %% q /\
      coeff rk.[3] %% q = coeff3 ak bk (terminal_value k) %% q.

lemma zeta_coeff_range (i : int) :
  0 <= i < 96 => -q <= zeta_coeff i < q.
proof.
  move=> Hi.
  have Hi192 : 0 <= 96 + i < 192 by smt().
  have := zetas192_coeff_range (96 + i) Hi192.
  rewrite /zeta_coeff.
  smt().
qed.

lemma zeta_coeff_range_strict (i : int) :
  0 <= i < 96 => -q < zeta_coeff i < q.
proof.
  move=> Hi.
  have Hi192 : 0 <= 96 + i < 192 by smt().
  have := zetas192_coeff_range (96 + i) Hi192.
  rewrite /zeta_coeff.
  smt().
qed.

lemma size_zetas96_words :
  size zetas96_words = 96.
proof.
  by rewrite /zetas96_words /zetas192_coeffs /=.
qed.

lemma zeta96E (i : int) :
  0 <= i < 96 =>
  nTRUPLUS_ZETAS96.[i] = W16.of_int (zeta_coeff i).
proof.
  move=> Hi.
  have -> : nTRUPLUS_ZETAS96 = Array96.of_list witness zetas96_words.
  + by rewrite /nTRUPLUS_ZETAS96 /zetas96_words /zetas192_coeffs /=.
  rewrite Array96.get_of_list 1:/# /zetas96_words.
  rewrite (nth_map witness).
  + by rewrite size_zetas96_words.
  by rewrite nth_drop 1:// 1:/# /zeta_coeff.
qed.

lemma zeta96_in_qrange (i : int) :
  0 <= i < 96 => in_qrange nTRUPLUS_ZETAS96.[i].
proof.
  move=> Hi.
  have Hz := zeta_coeff_range_strict i Hi.
  rewrite zeta96E 1:/# /in_qrange /coeff.
  rewrite W16.of_sintK /W16.smod /=.
  by smt().
qed.

lemma zeta96_strict_range (i : int) :
  0 <= i < 96 => -q < coeff nTRUPLUS_ZETAS96.[i] < q.
proof.
  move=> Hi.
  have Hz := zeta_coeff_range_strict i Hi.
  rewrite zeta96E 1:/# /coeff.
  rewrite W16.of_sintK /W16.smod /=.
  by smt().
qed.

lemma zeta96_coeffE (i : int) :
  0 <= i < 96 => coeff nTRUPLUS_ZETAS96.[i] = zeta_coeff i.
proof.
  move=> Hi.
  have Hz := zeta_coeff_range_strict i Hi.
  rewrite zeta96E 1:// /coeff W16.of_sintK /W16.smod /=.
  move: Hz; rewrite /q; smt().
qed.

lemma zeta96_neg_coeffE (i : int) :
  0 <= i < 96 =>
  coeff (-nTRUPLUS_ZETAS96.[i]) = - zeta_coeff i.
proof.
  move=> Hi.
  have Hz := zeta96_strict_range i Hi.
  have Hword :
      -W16.modulus %/ 2 < W16.to_sint nTRUPLUS_ZETAS96.[i] <
      W16.modulus %/ 2.
  + move: Hz; rewrite /q /coeff; smt().
  have Hcoeff := zeta96_coeffE i Hi.
  rewrite /coeff in Hcoeff.
  rewrite /coeff (to_sintN nTRUPLUS_ZETAS96.[i] Hword).
  by rewrite Hcoeff.
qed.

lemma in_qrangeN_strict (w : W16.t) :
  -q < coeff w < q => in_qrange (-w).
proof.
  move=> Hw.
  rewrite /in_qrange /coeff.
  have Hhalf : -W16.modulus %/ 2 < W16.to_sint w < W16.modulus %/ 2.
  + move: Hw; rewrite /q; smt().
  rewrite (to_sintN w Hhalf).
  move: Hw; smt().
qed.

lemma block_zeta_in_qrange (k : int) :
  0 <= k < 192 => in_qrange (block_zeta k).
proof.
  move=> Hk.
  rewrite /block_zeta.
  case (k %% 2 = 0) => Heven.
  + have Hhalf : 0 <= k %/ 2 < 96 by smt().
    by rewrite zeta96_in_qrange 1:/#.
  have Hhalf : 0 <= k %/ 2 < 96 by smt().
  apply in_qrangeN_strict.
  by rewrite zeta96_strict_range 1:/#.
qed.

lemma terminal_exp_nonneg (i : int) :
  0 <= i < 96 => 0 <= terminal_exp i.
proof.
  move=> Hi.
  have Hk : 0 <= 2 * i < 192 by smt().
  have Hfig := figure22_index_relation (2 * i) Hk.
  have Hrange := figure22_index_range (2 * i) Hk.
  rewrite /terminal_exp in Hfig.
  smt().
qed.

lemma zeta_root_shift_288 (e : int) :
  0 <= e =>
  (-(zeta_root ^ e %% q)) %% q = (zeta_root ^ (e + 288)) %% q.
proof.
  move=> He.
  rewrite exprD_nneg 1:/# 1:/#.
  rewrite -modzMmr zeta_order_288_value.
  smt().
qed.

lemma block_zeta_math_terminal_value (k : int) :
  0 <= k < 192 => block_zeta_math k = terminal_value k.
proof.
  move=> Hk.
  have Hhalf : 0 <= k %/ 2 < 96 by smt().
  have Hidx : 0 <= 96 + k %/ 2 < 192 by smt().
  have Hdecode := zetas192_relation (96 + k %/ 2) Hidx.
  rewrite -(terminal_exponents_suffix (k %/ 2) Hhalf) in Hdecode.
  rewrite /decode_mont in Hdecode.
  case (k %% 2 = 0) => Hpar.
  + have Hfig : figure22_index k = terminal_exp (k %/ 2).
    + have H := figure22_index_relation k Hk.
      rewrite Hpar in H.
      exact H.
    rewrite /block_zeta_math /zeta_decode /block_zeta Hpar.
    rewrite (zeta96_coeffE (k %/ 2) Hhalf) /zeta_coeff.
    rewrite /terminal_value.
    rewrite Hdecode.
    by rewrite Hfig.
  have Hfig : figure22_index k = terminal_exp (k %/ 2) + 288.
  + have H := figure22_index_relation k Hk.
    rewrite Hpar in H.
    exact H.
  rewrite /block_zeta_math /zeta_decode /block_zeta Hpar.
  rewrite (zeta96_neg_coeffE (k %/ 2) Hhalf) /zeta_coeff.
  have -> :
      ((- zetas192_coeff (96 + k %/ 2)) * Rinv) %% q =
      (- ((zetas192_coeff (96 + k %/ 2) * Rinv) %% q)) %% q.
  + have Hmul :
        (- zetas192_coeff (96 + k %/ 2)) * Rinv =
        - (zetas192_coeff (96 + k %/ 2) * Rinv) by ring.
    rewrite Hmul modzNm.
    done.
  rewrite /terminal_value.
  rewrite Hdecode.
  have Hnonneg := terminal_exp_nonneg (k %/ 2) Hhalf.
  rewrite (zeta_root_shift_288 (terminal_exp (k %/ 2)) Hnonneg).
  by rewrite Hfig.
qed.

lemma zeta_decode_relation (z : W16.t) :
  in_qrange z => zeta_mont_relation z (zeta_decode z).
proof.
  move=> Hz.
  split.
  + rewrite /zeta_decode.
    by smt(edivzP).
  rewrite /zeta_mont_relation /zeta_decode.
  have HRR : ((R %% q) * Rinv) %% q = 1 %% q by smt(NTRUPlusMontgomery.RRinv).
  rewrite modzMml.
  rewrite (_ : coeff z * Rinv * (R %% q) =
               coeff z * ((R %% q) * Rinv)).
  + ring.
  rewrite -modzMmr HRR /=.
  done.
qed.

lemma in_qrange768_block4 (p : W16.t Array768.t) (k : int) :
  in_qrange768 p => 0 <= k < 192 => in_qrange4 (block4 p k).
proof.
  move=> Hp Hk.
  exact (Hp k Hk).
qed.

lemma in_qrange768_in_s12range768 (p : W16.t Array768.t) :
  in_qrange768 p => in_s12range768 p.
proof.
  move=> Hp k Hk.
  exact (qrange4_in_s12range4 (block4 p k) (Hp k Hk)).
qed.

lemma in_s12range768_block4 (p : W16.t Array768.t) (k : int) :
  in_s12range768 p => 0 <= k < 192 => in_s12range4 (block4 p k).
proof.
  move=> Hp Hk.
  exact (Hp k Hk).
qed.

lemma poly_basemul_word_to_qring_s12
    (ap bp rp : W16.t Array768.t) :
  in_s12range768 ap =>
  in_s12range768 bp =>
  is_poly_basemul ap bp rp 192 =>
  poly_basemul_qring ap bp rp 192.
proof.
  move=> Hap Hbp Hword k Hk.
  have Hak : in_s12range4 (block4 ap k).
  + exact (in_s12range768_block4 ap k Hap Hk).
  have Hbk : in_s12range4 (block4 bp k).
  + exact (in_s12range768_block4 bp k Hbp Hk).
  have Hzk : in_qrange (block_zeta k).
  + exact (block_zeta_in_qrange k Hk).
  have Hspec := Hword k Hk.
  rewrite Hspec.
  rewrite /basemul_block_spec /in_qrange4.
  rewrite -(block_zeta_math_terminal_value k Hk).
  have Halg := basemul_spec_algebra_s12 witness (block4 ap k) (block4 bp k)
    (block_zeta k) (block_zeta_math k) Hak Hbk Hzk
    (zeta_decode_relation (block_zeta k) Hzk).
  move: Halg; smt().
qed.

lemma poly_basemul_word_to_qring
    (ap bp rp : W16.t Array768.t) :
  in_qrange768 ap =>
  in_qrange768 bp =>
  is_poly_basemul ap bp rp 192 =>
  poly_basemul_qring ap bp rp 192.
proof.
  move=> Hap Hbp Hword.
  exact (poly_basemul_word_to_qring_s12 ap bp rp
    (in_qrange768_in_s12range768 ap Hap)
    (in_qrange768_in_s12range768 bp Hbp)
    Hword).
qed.

lemma poly_basemul_correct_qring_s12
    (rp0 ap0 bp0 : W16.t Array768.t) :
  in_s12range768 ap0 =>
  in_s12range768 bp0 =>
  phoare [NTRUPlus768PolyBasemul.M.jade_ntruplus_ntruplus768_amd64_ref_poly_basemul :
    rp = rp0 /\ ap = ap0 /\ bp = bp0 ==>
    poly_basemul_qring ap0 bp0 res 192] = 1%r.
proof.
  move=> Hap Hbp.
  conseq poly_basemul_lossless (poly_basemul_functional rp0 ap0 bp0).
  move=> &hr _ result; split.
  + move=> [_ Hword].
    split.
    + trivial.
    exact Hword.
  move=> [_ Hword]; split.
  + exact (poly_basemul_word_to_qring_s12 ap0 bp0 result Hap Hbp Hword).
  exact Hword.
qed.

lemma poly_basemul_correct_qring
    (rp0 ap0 bp0 : W16.t Array768.t) :
  in_qrange768 ap0 =>
  in_qrange768 bp0 =>
  phoare [NTRUPlus768PolyBasemul.M.jade_ntruplus_ntruplus768_amd64_ref_poly_basemul :
    rp = rp0 /\ ap = ap0 /\ bp = bp0 ==>
    poly_basemul_qring ap0 bp0 res 192] = 1%r.
proof.
  move=> Hap Hbp.
  exact (poly_basemul_correct_qring_s12 rp0 ap0 bp0
    (in_qrange768_in_s12range768 ap0 Hap)
    (in_qrange768_in_s12range768 bp0 Hbp)).
qed.
