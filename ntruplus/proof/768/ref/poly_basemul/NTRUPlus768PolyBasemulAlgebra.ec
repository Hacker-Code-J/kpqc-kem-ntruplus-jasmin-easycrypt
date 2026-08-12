require import AllCore IntDiv List Ring StdOrder.
from Jasmin require import JWord.

require import Array4 Array96 Array768.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768PolyBasemul.
require import NTRUPlus768PolyBasemulProof.
require import W16extra.

import IntOrder.

op zetas96_coeffs : int list =
  [223; 1138; -1059; -397; -183; 1655; 559; -1674;
   277; 933; 1723; 437; -1514; 242; 1640; 432;
   -1583; 696; 774; 1671; 927; 514; 512; 489;
   297; 601; 1473; 1130; 1322; 871; 760; 1212;
   -312; -352; 443; 943; 8; 1250; -100; 1660;
   -31; 1206; -1341; -1247; 444; 235; 1364; -1209;
   361; 230; 673; 582; 1409; 1501; 1401; 251;
   1022; -1063; 1053; 1188; 417; -1391; -27; -1626;
   1685; -315; 1408; -1248; 400; 274; -1543; 32;
   -1550; 1531; -1367; -124; 1458; 1379; -940; -1681;
   22; 1709; -275; 1108; 354; -1728; -968; 858;
   1221; -218; 294; -732; -1095; 892; 1588; -779].

op zetas96_words : W16.t list = map W16.of_int zetas96_coeffs.

op zeta_coeff (i : int) : int = nth witness zetas96_coeffs i.

op in_qrange768 (p : W16.t Array768.t) : bool =
  forall k, 0 <= k < 192 => in_qrange4 (block4 p k).

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
      coeff rk.[0] %% q = coeff0 ak bk (block_zeta_math k) %% q /\
      coeff rk.[1] %% q = coeff1 ak bk (block_zeta_math k) %% q /\
      coeff rk.[2] %% q = coeff2 ak bk (block_zeta_math k) %% q /\
      coeff rk.[3] %% q = coeff3 ak bk (block_zeta_math k) %% q.

lemma zeta_coeff_range (i : int) :
  0 <= i < 96 => -q <= zeta_coeff i < q.
proof.
  move=> Hi.
  rewrite /zeta_coeff /zetas96_coeffs /q /=.
  smt().
qed.

lemma zeta_coeff_range_strict (i : int) :
  0 <= i < 96 => -q < zeta_coeff i < q.
proof.
  move=> Hi.
  rewrite /zeta_coeff /zetas96_coeffs /q /=.
  smt().
qed.

lemma size_zetas96_coeffs :
  size zetas96_coeffs = 96.
proof.
  by rewrite /zetas96_coeffs /=.
qed.

lemma zeta96E (i : int) :
  0 <= i < 96 =>
  nTRUPLUS_ZETAS96.[i] = W16.of_int (zeta_coeff i).
proof.
  move=> Hi.
  have -> : nTRUPLUS_ZETAS96 = Array96.of_list witness zetas96_words.
  + by rewrite /nTRUPLUS_ZETAS96 /zetas96_words /=.
  rewrite Array96.get_of_list 1:/# /zetas96_words.
  rewrite (nth_map witness).
  + by rewrite size_zetas96_coeffs.
  by rewrite /zeta_coeff.
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

lemma poly_basemul_word_to_qring
    (ap bp rp : W16.t Array768.t) :
  in_qrange768 ap =>
  in_qrange768 bp =>
  is_poly_basemul ap bp rp 192 =>
  poly_basemul_qring ap bp rp 192.
proof.
  move=> Hap Hbp Hword k Hk.
  have Hak : in_qrange4 (block4 ap k).
  + exact (in_qrange768_block4 ap k Hap Hk).
  have Hbk : in_qrange4 (block4 bp k).
  + exact (in_qrange768_block4 bp k Hbp Hk).
  have Hzk : in_qrange (block_zeta k).
  + exact (block_zeta_in_qrange k Hk).
  have Hspec := Hword k Hk.
  rewrite Hspec.
  rewrite /basemul_block_spec /in_qrange4.
  have Halg := basemul_spec_algebra witness (block4 ap k) (block4 bp k)
    (block_zeta k) (block_zeta_math k) Hak Hbk Hzk
    (zeta_decode_relation (block_zeta k) Hzk).
  move: Halg; smt().
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
  conseq poly_basemul_lossless (poly_basemul_functional rp0 ap0 bp0).
  move=> &hr _ result; split.
  + move=> [_ Hword].
    split.
    + trivial.
    exact Hword.
  move=> [_ Hword]; split.
  + exact (poly_basemul_word_to_qring ap0 bp0 result Hap Hbp Hword).
  exact Hword.
qed.
