require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord JModel_x86.

require import W16extra.
require import Array768.
require import NTRUPlus768InvNTTRadix3Proof.
require import NTRUPlus768BasemulProof.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768NTTSchedule.
require import NTRUPlus768NTTRadix2_64Proof.
require import NTRUPlus768NTTRadix2_64Algebra.
require import NTRUPlus768InvNTTRadix2_64Proof.
require import NTRUPlus768InvNTTRadix2_64Algebra.

import Ring.IntID IntOrder.

op invntt_radix3_zeta2_root : int = (zeta_root ^ 32) %% q.
op invntt_radix3_zeta3_root : int = (zeta_root ^ 64) %% q.
op invntt_radix3_zeta4_root : int = (zeta_root ^ 160) %% q.
op invntt_radix3_zeta5_root : int = (zeta_root ^ 320) %% q.
op invntt_radix3_omega_root : int = (zeta_root ^ 192) %% q.

op invntt_radix3_input_shape (p : W16.t Array768.t) : bool =
  forall j, 0 <= j < 768 => -q <= coeff p.[j] < q.

lemma invntt_radix3_input_shape_coeff
    (p : W16.t Array768.t) (j : int) :
  invntt_radix3_input_shape p =>
  0 <= j < 768 =>
  -q <= coeff p.[j] < q.
proof.
  by move=> Hshape Hj; rewrite /invntt_radix3_input_shape in Hshape; exact (Hshape j Hj).
qed.

lemma invntt_radix2_64_algebra_output_qrange
    (input output : W16.t Array768.t) (j : int) :
  NTRUPlus768InvNTTRadix2_64Algebra.invntt_radix2_64_algebra input output =>
  0 <= j < 768 =>
  -q <= coeff output.[j] < q.
proof.
  move=> Halg Hj.
  have Hjalg := Halg j Hj.
  move: Hjalg => [Hrange _].
  case (NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_block_offset j <
        NTRUPlus768InvNTTRadix2_64Algebra.block).
  + move: Hrange; rewrite /q /=; smt().
  move: Hrange; smt().
qed.

lemma invntt_radix2_64_algebra_implies_invntt_radix3_input_shape
    (input output : W16.t Array768.t) :
  NTRUPlus768InvNTTRadix2_64Algebra.invntt_radix2_64_algebra input output =>
  invntt_radix3_input_shape output.
proof.
  move=> Halg.
  rewrite /invntt_radix3_input_shape.
  by move=> j Hj; exact (invntt_radix2_64_algebra_output_qrange input output j Halg Hj).
qed.

lemma invntt_radix3_reverse_schedule :
  coeff NTRUPlus768InvNTTRadix3Proof.zeta5 = zetas192_coeff 5 /\
  coeff NTRUPlus768InvNTTRadix3Proof.zeta4 = zetas192_coeff 4 /\
  coeff NTRUPlus768InvNTTRadix3Proof.zeta3 = zetas192_coeff 3 /\
  coeff NTRUPlus768InvNTTRadix3Proof.zeta2 = zetas192_coeff 2 /\
  zetas192_exp 5 = 320 /\ zetas192_exp 4 = 160 /\
  zetas192_exp 3 = 64 /\ zetas192_exp 2 = 32 /\
  5 - 4 = 1.
proof.
  rewrite /coeff
          /NTRUPlus768InvNTTRadix3Proof.zeta2
          /NTRUPlus768InvNTTRadix3Proof.zeta3
          /NTRUPlus768InvNTTRadix3Proof.zeta4
          /NTRUPlus768InvNTTRadix3Proof.zeta5.
  rewrite /zetas192_coeff /zetas192_exp /zetas192_coeffs /zetas192_exponents /=.
  rewrite !W16.of_sintK !/W16.smod /=.
  done.
qed.

lemma invntt_radix3_omega_schedule :
  coeff NTRUPlus768InvNTTRadix3Proof.omega = OMEGA_coeff /\
  OMEGA_coeff = -886 /\ omega_exp = 192.
proof.
  rewrite /coeff /NTRUPlus768InvNTTRadix3Proof.omega /OMEGA_coeff /omega_exp.
  rewrite W16.of_sintK /W16.smod /=.
  done.
qed.

lemma invntt_radix3_zeta2_in_qrange :
  in_qrange NTRUPlus768InvNTTRadix3Proof.zeta2.
proof.
  rewrite /in_qrange /coeff /NTRUPlus768InvNTTRadix3Proof.zeta2.
  rewrite W16.of_sintK /W16.smod /q /=.
  done.
qed.

lemma invntt_radix3_zeta3_in_qrange :
  in_qrange NTRUPlus768InvNTTRadix3Proof.zeta3.
proof.
  rewrite /in_qrange /coeff /NTRUPlus768InvNTTRadix3Proof.zeta3.
  rewrite W16.of_sintK /W16.smod /q /=.
  done.
qed.

lemma invntt_radix3_zeta4_in_qrange :
  in_qrange NTRUPlus768InvNTTRadix3Proof.zeta4.
proof.
  rewrite /in_qrange /coeff /NTRUPlus768InvNTTRadix3Proof.zeta4.
  rewrite W16.of_sintK /W16.smod /q /=.
  done.
qed.

lemma invntt_radix3_zeta5_in_qrange :
  in_qrange NTRUPlus768InvNTTRadix3Proof.zeta5.
proof.
  rewrite /in_qrange /coeff /NTRUPlus768InvNTTRadix3Proof.zeta5.
  rewrite W16.of_sintK /W16.smod /q /=.
  done.
qed.

lemma invntt_radix3_omega_in_qrange :
  in_qrange NTRUPlus768InvNTTRadix3Proof.omega.
proof.
  rewrite /in_qrange /coeff /NTRUPlus768InvNTTRadix3Proof.omega.
  rewrite W16.of_sintK /W16.smod /q /=.
  done.
qed.

lemma invntt_radix3_zeta2_montgomery_meaning :
  (coeff NTRUPlus768InvNTTRadix3Proof.zeta2 * Rinv) %% q =
  invntt_radix3_zeta2_root.
proof.
  have Hschedule := zetas192_relation 2 _; first smt().
  move: Hschedule.
  rewrite /decode_mont /invntt_radix3_zeta2_root /zetas192_coeff /zetas192_exp.
  rewrite /zetas192_coeffs /zetas192_exponents /coeff
          /NTRUPlus768InvNTTRadix3Proof.zeta2 /=.
  rewrite W16.of_sintK /W16.smod /=.
  done.
qed.

lemma invntt_radix3_zeta3_montgomery_meaning :
  (coeff NTRUPlus768InvNTTRadix3Proof.zeta3 * Rinv) %% q =
  invntt_radix3_zeta3_root.
proof.
  have Hschedule := zetas192_relation 3 _; first smt().
  move: Hschedule.
  rewrite /decode_mont /invntt_radix3_zeta3_root /zetas192_coeff /zetas192_exp.
  rewrite /zetas192_coeffs /zetas192_exponents /coeff
          /NTRUPlus768InvNTTRadix3Proof.zeta3 /=.
  rewrite W16.of_sintK /W16.smod /=.
  done.
qed.

lemma invntt_radix3_zeta4_montgomery_meaning :
  (coeff NTRUPlus768InvNTTRadix3Proof.zeta4 * Rinv) %% q =
  invntt_radix3_zeta4_root.
proof.
  have Hschedule := zetas192_relation 4 _; first smt().
  move: Hschedule.
  rewrite /decode_mont /invntt_radix3_zeta4_root /zetas192_coeff /zetas192_exp.
  rewrite /zetas192_coeffs /zetas192_exponents /coeff
          /NTRUPlus768InvNTTRadix3Proof.zeta4 /=.
  rewrite W16.of_sintK /W16.smod /=.
  done.
qed.

lemma invntt_radix3_zeta5_montgomery_meaning :
  (coeff NTRUPlus768InvNTTRadix3Proof.zeta5 * Rinv) %% q =
  invntt_radix3_zeta5_root.
proof.
  have Hschedule := zetas192_relation 5 _; first smt().
  move: Hschedule.
  rewrite /decode_mont /invntt_radix3_zeta5_root /zetas192_coeff /zetas192_exp.
  rewrite /zetas192_coeffs /zetas192_exponents /coeff
          /NTRUPlus768InvNTTRadix3Proof.zeta5 /=.
  rewrite W16.of_sintK /W16.smod /=.
  done.
qed.

lemma invntt_radix3_omega_montgomery_meaning :
  (coeff NTRUPlus768InvNTTRadix3Proof.omega * Rinv) %% q =
  invntt_radix3_omega_root.
proof.
  have [Hdecode _] := omega_montgomery_meaning.
  move: Hdecode.
  rewrite /decode_mont /invntt_radix3_omega_root /coeff
          /NTRUPlus768InvNTTRadix3Proof.omega /OMEGA_coeff /omega_exp.
  rewrite W16.of_sintK /W16.smod /=.
  done.
qed.

op invntt_radix3_block_math
    (a0 a1 a2 root1 root2 : int) : int * int * int =
  let t1 = (a1 - a0) * invntt_radix3_omega_root in
  (a0 + a1 + a2,
   (a2 - a0 + t1) * root1,
   (a2 - a1 - t1) * root2).

op invntt_radix3_block_math_at
    (p : W16.t Array768.t) (base : int) (root1 root2 : int) (k : int)
    : int * int * int =
  invntt_radix3_block_math
    (coeff p.[base + k])
    (coeff p.[base + k + NTRUPlus768InvNTTRadix3Proof.block])
    (coeff p.[base + k + NTRUPlus768InvNTTRadix3Proof.double_block])
    root1 root2.

op invntt_radix3_math (p : W16.t Array768.t) (j : int) : int =
  if j < NTRUPlus768InvNTTRadix3Proof.block then
    (invntt_radix3_block_math_at p 0
      invntt_radix3_zeta4_root invntt_radix3_zeta5_root j).`1
  else if j < NTRUPlus768InvNTTRadix3Proof.double_block then
    (invntt_radix3_block_math_at p 0
      invntt_radix3_zeta4_root invntt_radix3_zeta5_root
      (j - NTRUPlus768InvNTTRadix3Proof.block)).`2
  else if j < NTRUPlus768InvNTTRadix3Proof.second_base then
    (invntt_radix3_block_math_at p 0
      invntt_radix3_zeta4_root invntt_radix3_zeta5_root
      (j - NTRUPlus768InvNTTRadix3Proof.double_block)).`3
  else if j < NTRUPlus768InvNTTRadix3Proof.second_base +
                    NTRUPlus768InvNTTRadix3Proof.block then
    (invntt_radix3_block_math_at p NTRUPlus768InvNTTRadix3Proof.second_base
      invntt_radix3_zeta2_root invntt_radix3_zeta3_root
      (j - NTRUPlus768InvNTTRadix3Proof.second_base)).`1
  else if j < NTRUPlus768InvNTTRadix3Proof.second_base +
                    NTRUPlus768InvNTTRadix3Proof.double_block then
    (invntt_radix3_block_math_at p NTRUPlus768InvNTTRadix3Proof.second_base
      invntt_radix3_zeta2_root invntt_radix3_zeta3_root
      (j - NTRUPlus768InvNTTRadix3Proof.second_base -
       NTRUPlus768InvNTTRadix3Proof.block)).`2
  else
    (invntt_radix3_block_math_at p NTRUPlus768InvNTTRadix3Proof.second_base
      invntt_radix3_zeta2_root invntt_radix3_zeta3_root
      (j - NTRUPlus768InvNTTRadix3Proof.second_base -
       NTRUPlus768InvNTTRadix3Proof.double_block)).`3.

op invntt_radix3_algebra
    (input output : W16.t Array768.t) : bool =
  forall j, 0 <= j < 768 =>
    (if j < NTRUPlus768InvNTTRadix3Proof.block \/
        NTRUPlus768InvNTTRadix3Proof.second_base <= j <
          NTRUPlus768InvNTTRadix3Proof.second_base +
          NTRUPlus768InvNTTRadix3Proof.block
     then -3 * q <= coeff output.[j] < 3 * q
     else -q <= coeff output.[j] < q) /\
    coeff output.[j] %% q = invntt_radix3_math input j %% q.

lemma invntt_radix3_mul_algebra
    (z a : W16.t) (root m : int) :
  0 < m <= 5 =>
  in_qrange z =>
  -m * q <= coeff a < m * q =>
  (coeff z * Rinv) %% q = root =>
  -q <= coeff (NTRUPlus768InvNTTRadix3Proof.invntt_radix3_mul z a) < q /\
  coeff (NTRUPlus768InvNTTRadix3Proof.invntt_radix3_mul z a) %% q =
    (coeff a * root) %% q.
proof.
  move=> Hm Hz Ha Hroot.
  have H := NTRUPlus768NTTRadix2_64Algebra.radix2_64_mul_algebra
    z a root m Hm Hz Ha Hroot.
  move: H.
  by rewrite /NTRUPlus768NTTRadix2_64Proof.radix2_64_mul
             /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_mul.
qed.

lemma invntt_radix3_block_algebra
    (z1 z2 a0 a1 a2 : W16.t) (root1 root2 : int) :
  -q <= coeff a0 < q =>
  -q <= coeff a1 < q =>
  -q <= coeff a2 < q =>
  in_qrange z1 =>
  in_qrange z2 =>
  (coeff z1 * Rinv) %% q = root1 =>
  (coeff z2 * Rinv) %% q = root2 =>
  let out = NTRUPlus768InvNTTRadix3Proof.invntt_radix3_block
              z1 z2 a0 a1 a2 in
    -3 * q <= coeff out.`1 < 3 * q /\
    -q <= coeff out.`2 < q /\
    -q <= coeff out.`3 < q /\
    coeff out.`1 %% q =
      (invntt_radix3_block_math (coeff a0) (coeff a1) (coeff a2)
        root1 root2).`1 %% q /\
    coeff out.`2 %% q =
      (invntt_radix3_block_math (coeff a0) (coeff a1) (coeff a2)
        root1 root2).`2 %% q /\
    coeff out.`3 %% q =
      (invntt_radix3_block_math (coeff a0) (coeff a1) (coeff a2)
        root1 root2).`3 %% q.
proof.
  move=> Ha0 Ha1 Ha2 Hz1 Hz2 Hroot1 Hroot2 out.
  pose d10 := a1 - a0.
  pose t1 := NTRUPlus768InvNTTRadix3Proof.invntt_radix3_mul
               NTRUPlus768InvNTTRadix3Proof.omega d10.
  pose d20 := a2 - a0.
  pose td2 := d20 + t1.
  pose t2 := NTRUPlus768InvNTTRadix3Proof.invntt_radix3_mul z1 td2.
  pose d21 := a2 - a1.
  pose td3 := d21 - t1.
  pose t3 := NTRUPlus768InvNTTRadix3Proof.invntt_radix3_mul z2 td3.
  have Hm1 : 0 < 1 <= 5 by smt().
  have Hm2 : 0 < 2 <= 5 by smt().
  have Hm3 : 0 < 3 <= 5 by smt().
  have Hd10 : coeff d10 = coeff a1 - coeff a0.
  + rewrite /d10.
    exact (NTRUPlus768NTTRadix2_64Algebra.coeff_sub_qbounded
      1 a1 a0 Hm1 Ha1 Ha0).
  have Hd10range : -2 * q <= coeff d10 < 2 * q
    by rewrite Hd10; smt().
  have Ht1 := invntt_radix3_mul_algebra
    NTRUPlus768InvNTTRadix3Proof.omega d10
    invntt_radix3_omega_root 2 Hm2
    invntt_radix3_omega_in_qrange Hd10range
    invntt_radix3_omega_montgomery_meaning.
  have Ht1range : -q <= coeff t1 < q by move: Ht1; rewrite /t1; smt().
  have Ht1congr :
      coeff t1 %% q =
      ((coeff a1 - coeff a0) * invntt_radix3_omega_root) %% q.
  + move: Ht1.
    rewrite /t1 Hd10.
    smt().
  have Hd20 : coeff d20 = coeff a2 - coeff a0.
  + rewrite /d20.
    exact (NTRUPlus768NTTRadix2_64Algebra.coeff_sub_qbounded
      1 a2 a0 Hm1 Ha2 Ha0).
  have Hd20range : -2 * q <= coeff d20 < 2 * q
    by rewrite Hd20; smt().
  have Htd2 : coeff td2 = coeff a2 - coeff a0 + coeff t1.
  + rewrite /td2.
    have H := NTRUPlus768NTTRadix2_64Algebra.coeff_add_qbounded
      2 d20 t1 Hm2 Hd20range Ht1range.
    by rewrite H Hd20.
  have Htd2range : -3 * q <= coeff td2 < 3 * q
    by rewrite Htd2; smt().
  have Ht2 := invntt_radix3_mul_algebra z1 td2 root1 3 Hm3
    Hz1 Htd2range Hroot1.
  have Ht2range : -q <= coeff t2 < q by move: Ht2; rewrite /t2; smt().
  have Htd2congr :
      coeff td2 %% q =
      (coeff a2 - coeff a0 +
       (coeff a1 - coeff a0) * invntt_radix3_omega_root) %% q.
  + rewrite Htd2.
    rewrite -modzDm Ht1congr modzDm.
    done.
  have Ht2congr :
      coeff t2 %% q =
      ((coeff a2 - coeff a0 +
        (coeff a1 - coeff a0) * invntt_radix3_omega_root) * root1) %% q.
  + have Hbase : coeff t2 %% q = (coeff td2 * root1) %% q
      by move: Ht2; rewrite /t2; smt().
    rewrite Hbase.
    have -> : (coeff td2 * root1) %% q = ((coeff td2 %% q) * root1) %% q
      by rewrite modzMml.
    rewrite Htd2congr.
    by rewrite modzMml.
  have Hd21 : coeff d21 = coeff a2 - coeff a1.
  + rewrite /d21.
    exact (NTRUPlus768NTTRadix2_64Algebra.coeff_sub_qbounded
      1 a2 a1 Hm1 Ha2 Ha1).
  have Hd21range : -2 * q <= coeff d21 < 2 * q
    by rewrite Hd21; smt().
  have Htd3 : coeff td3 = coeff a2 - coeff a1 - coeff t1.
  + rewrite /td3.
    have H := NTRUPlus768NTTRadix2_64Algebra.coeff_sub_qbounded
      2 d21 t1 Hm2 Hd21range Ht1range.
    by rewrite H Hd21.
  have Htd3range : -3 * q <= coeff td3 < 3 * q
    by rewrite Htd3; smt().
  have Ht3 := invntt_radix3_mul_algebra z2 td3 root2 3 Hm3
    Hz2 Htd3range Hroot2.
  have Ht3range : -q <= coeff t3 < q by move: Ht3; rewrite /t3; smt().
  have Htd3congr :
      coeff td3 %% q =
      (coeff a2 - coeff a1 -
       (coeff a1 - coeff a0) * invntt_radix3_omega_root) %% q.
  + rewrite Htd3.
    rewrite -modzBm Ht1congr modzBm.
    done.
  have Ht3congr :
      coeff t3 %% q =
      ((coeff a2 - coeff a1 -
        (coeff a1 - coeff a0) * invntt_radix3_omega_root) * root2) %% q.
  + have Hbase : coeff t3 %% q = (coeff td3 * root2) %% q
      by move: Ht3; rewrite /t3; smt().
    rewrite Hbase.
    have -> : (coeff td3 * root2) %% q = ((coeff td3 %% q) * root2) %% q
      by rewrite modzMml.
    rewrite Htd3congr.
    by rewrite modzMml.
  pose s01 := a0 + a1.
  have Hs01 : coeff s01 = coeff a0 + coeff a1.
  + rewrite /s01.
    exact (NTRUPlus768NTTRadix2_64Algebra.coeff_add_qbounded
      1 a0 a1 Hm1 Ha0 Ha1).
  have Hs01range : -2 * q <= coeff s01 < 2 * q
    by rewrite Hs01; smt().
  have Hsum := NTRUPlus768NTTRadix2_64Algebra.coeff_add_qbounded
    2 s01 a2 Hm2 Hs01range Ha2.
  have Hout0raw : coeff out.`1 = coeff s01 + coeff a2.
  + move: Hsum.
    rewrite /out /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_block
            /s01 /t1 /t2 /t3 /=.
    done.
  have Hout0 : coeff out.`1 = coeff a0 + coeff a1 + coeff a2
    by rewrite Hout0raw Hs01.
  have Hout0range : -3 * q <= coeff out.`1 < 3 * q
    by rewrite Hout0; smt().
  have Hout1range : -q <= coeff out.`2 < q.
  + move: Ht2range.
    rewrite /out /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_block
            /t1 /t2 /d10 /d20 /td2 /=.
    done.
  have Hout2range : -q <= coeff out.`3 < q.
  + move: Ht3range.
    rewrite /out /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_block
            /t1 /t3 /d10 /d21 /td3 /=.
    done.
  have Hout1congr :
      coeff out.`2 %% q =
      ((coeff a2 - coeff a0 +
        (coeff a1 - coeff a0) * invntt_radix3_omega_root) * root1) %% q.
  + move: Ht2congr.
    rewrite /out /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_block
            /t1 /t2 /d10 /d20 /td2 /=.
    done.
  have Hout2congr :
      coeff out.`3 %% q =
      ((coeff a2 - coeff a1 -
        (coeff a1 - coeff a0) * invntt_radix3_omega_root) * root2) %% q.
  + move: Ht3congr.
    rewrite /out /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_block
            /t1 /t3 /d10 /d21 /td3 /=.
    done.
  split; first exact Hout0range.
  split; first exact Hout1range.
  split; first exact Hout2range.
  rewrite /invntt_radix3_block_math /=.
  split; first by rewrite Hout0.
  split; first exact Hout1congr.
  exact Hout2congr.
qed.

lemma invntt_radix3_first_spec_far (p : W16.t Array768.t) (j : int) :
  NTRUPlus768InvNTTRadix3Proof.second_base <= j < 768 =>
  (NTRUPlus768InvNTTRadix3Proof.invntt_radix3_first_spec p).[j] = p.[j].
proof.
  move=> Hj.
  rewrite /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_first_spec
          /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_prefix_spec.
  rewrite Array768.initiE 1:/#.
  smt().
qed.

lemma invntt_radix3_spec_algebra (p : W16.t Array768.t) :
  invntt_radix3_input_shape p =>
  invntt_radix3_algebra p
    (NTRUPlus768InvNTTRadix3Proof.invntt_radix3_spec p).
proof.
  move=> Hinput j Hj.
  rewrite /invntt_radix3_algebra /invntt_radix3_math.
  case (j < NTRUPlus768InvNTTRadix3Proof.block) => Hj0.
  + rewrite ifT 1:/#.
    have Ha0 := invntt_radix3_input_shape_coeff p j Hinput _; first smt().
    have Ha1 := invntt_radix3_input_shape_coeff p
      (j + NTRUPlus768InvNTTRadix3Proof.block) Hinput _; first smt().
    have Ha2 := invntt_radix3_input_shape_coeff p
      (j + NTRUPlus768InvNTTRadix3Proof.double_block) Hinput _; first smt().
    have Hblk := invntt_radix3_block_algebra
      NTRUPlus768InvNTTRadix3Proof.zeta4
      NTRUPlus768InvNTTRadix3Proof.zeta5
      p.[j] p.[j + NTRUPlus768InvNTTRadix3Proof.block]
      p.[j + NTRUPlus768InvNTTRadix3Proof.double_block]
      invntt_radix3_zeta4_root invntt_radix3_zeta5_root
      Ha0 Ha1 Ha2 invntt_radix3_zeta4_in_qrange
      invntt_radix3_zeta5_in_qrange invntt_radix3_zeta4_montgomery_meaning
      invntt_radix3_zeta5_montgomery_meaning.
    move: Hblk.
    rewrite /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_spec
            /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_second_spec
            /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_prefix_spec.
    rewrite Array768.initiE 1:/# /= ifF 1:/# ifF 1:/# ifF 1:/#.
    rewrite /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_first_spec
            /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_prefix_spec.
    rewrite Array768.initiE 1:/# /= ifT 1:/#.
    rewrite /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_block_at
            /invntt_radix3_block_math_at /=.
    move=> [Hr0 [Hr1 [Hr2 [Hc0 [Hc1 Hc2]]]]].
    split; [exact Hr0 | exact Hc0].
  case (j < NTRUPlus768InvNTTRadix3Proof.double_block) => Hj1.
  + rewrite ifF 1:/#.
    have Ha0 := invntt_radix3_input_shape_coeff p
      (j - NTRUPlus768InvNTTRadix3Proof.block) Hinput _; first smt().
    have Ha1 := invntt_radix3_input_shape_coeff p j Hinput _; first smt().
    have Ha2 := invntt_radix3_input_shape_coeff p
      (j + NTRUPlus768InvNTTRadix3Proof.block) Hinput _; first smt().
    have Hblk := invntt_radix3_block_algebra
      NTRUPlus768InvNTTRadix3Proof.zeta4
      NTRUPlus768InvNTTRadix3Proof.zeta5
      p.[j - NTRUPlus768InvNTTRadix3Proof.block] p.[j]
      p.[j + NTRUPlus768InvNTTRadix3Proof.block]
      invntt_radix3_zeta4_root invntt_radix3_zeta5_root
      Ha0 Ha1 Ha2 invntt_radix3_zeta4_in_qrange
      invntt_radix3_zeta5_in_qrange invntt_radix3_zeta4_montgomery_meaning
      invntt_radix3_zeta5_montgomery_meaning.
    move: Hblk.
    rewrite /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_spec
            /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_second_spec
            /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_prefix_spec.
    rewrite Array768.initiE 1:/# /= ifF 1:/# ifF 1:/# ifF 1:/#.
    rewrite /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_first_spec
            /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_prefix_spec.
    rewrite Array768.initiE 1:/# /= ifF 1:/# ifT 1:/#.
    rewrite /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_block_at
            /invntt_radix3_block_math_at /=.
    move=> [Hr0 [Hr1 [Hr2 [Hc0 [Hc1 Hc2]]]]].
    split; [exact Hr1 | exact Hc1].
  case (j < NTRUPlus768InvNTTRadix3Proof.second_base) => Hj2.
  + rewrite ifF 1:/#.
    have Ha0 := invntt_radix3_input_shape_coeff p
      (j - NTRUPlus768InvNTTRadix3Proof.double_block) Hinput _; first smt().
    have Ha1 := invntt_radix3_input_shape_coeff p
      (j - NTRUPlus768InvNTTRadix3Proof.block) Hinput _; first smt().
    have Ha2 := invntt_radix3_input_shape_coeff p j Hinput _; first smt().
    have Hblk := invntt_radix3_block_algebra
      NTRUPlus768InvNTTRadix3Proof.zeta4
      NTRUPlus768InvNTTRadix3Proof.zeta5
      p.[j - NTRUPlus768InvNTTRadix3Proof.double_block]
      p.[j - NTRUPlus768InvNTTRadix3Proof.block] p.[j]
      invntt_radix3_zeta4_root invntt_radix3_zeta5_root
      Ha0 Ha1 Ha2 invntt_radix3_zeta4_in_qrange
      invntt_radix3_zeta5_in_qrange invntt_radix3_zeta4_montgomery_meaning
      invntt_radix3_zeta5_montgomery_meaning.
    move: Hblk.
    rewrite /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_spec
            /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_second_spec
            /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_prefix_spec.
    rewrite Array768.initiE 1:/# /= ifF 1:/# ifF 1:/# ifF 1:/#.
    rewrite /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_first_spec
            /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_prefix_spec.
    rewrite Array768.initiE 1:/# /= ifF 1:/# ifF 1:/# ifT 1:/#.
    rewrite /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_block_at
            /invntt_radix3_block_math_at /=.
    move=> [Hr0 [Hr1 [Hr2 [Hc0 [Hc1 Hc2]]]]].
    split; [exact Hr2 | exact Hc2].
  case (j < NTRUPlus768InvNTTRadix3Proof.second_base +
            NTRUPlus768InvNTTRadix3Proof.block) => Hj3.
  + rewrite ifT 1:/#.
    have Ha0 := invntt_radix3_input_shape_coeff p j Hinput _; first smt().
    have Ha1 := invntt_radix3_input_shape_coeff p
      (j + NTRUPlus768InvNTTRadix3Proof.block) Hinput _; first smt().
    have Ha2 := invntt_radix3_input_shape_coeff p
      (j + NTRUPlus768InvNTTRadix3Proof.double_block) Hinput _; first smt().
    have Hblk := invntt_radix3_block_algebra
      NTRUPlus768InvNTTRadix3Proof.zeta2
      NTRUPlus768InvNTTRadix3Proof.zeta3
      p.[j] p.[j + NTRUPlus768InvNTTRadix3Proof.block]
      p.[j + NTRUPlus768InvNTTRadix3Proof.double_block]
      invntt_radix3_zeta2_root invntt_radix3_zeta3_root
      Ha0 Ha1 Ha2 invntt_radix3_zeta2_in_qrange
      invntt_radix3_zeta3_in_qrange invntt_radix3_zeta2_montgomery_meaning
      invntt_radix3_zeta3_montgomery_meaning.
    move: Hblk.
    rewrite /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_spec
            /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_second_spec
            /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_prefix_spec.
    rewrite Array768.initiE 1:/# /= ifT 1:/#.
    rewrite /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_block_at /=.
    rewrite (invntt_radix3_first_spec_far p j) 1:/#.
    rewrite (invntt_radix3_first_spec_far p
      (j + NTRUPlus768InvNTTRadix3Proof.block)) 1:/#.
    rewrite (invntt_radix3_first_spec_far p
      (j + NTRUPlus768InvNTTRadix3Proof.double_block)) 1:/#.
    rewrite /invntt_radix3_block_math_at /=.
    move=> [Hr0 [Hr1 [Hr2 [Hc0 [Hc1 Hc2]]]]].
    split; [exact Hr0 | exact Hc0].
  case (j < NTRUPlus768InvNTTRadix3Proof.second_base +
            NTRUPlus768InvNTTRadix3Proof.double_block) => Hj4.
  + rewrite ifF 1:/#.
    have Ha0 := invntt_radix3_input_shape_coeff p
      (j - NTRUPlus768InvNTTRadix3Proof.block) Hinput _; first smt().
    have Ha1 := invntt_radix3_input_shape_coeff p j Hinput _; first smt().
    have Ha2 := invntt_radix3_input_shape_coeff p
      (j + NTRUPlus768InvNTTRadix3Proof.block) Hinput _; first smt().
    have Hblk := invntt_radix3_block_algebra
      NTRUPlus768InvNTTRadix3Proof.zeta2
      NTRUPlus768InvNTTRadix3Proof.zeta3
      p.[j - NTRUPlus768InvNTTRadix3Proof.block] p.[j]
      p.[j + NTRUPlus768InvNTTRadix3Proof.block]
      invntt_radix3_zeta2_root invntt_radix3_zeta3_root
      Ha0 Ha1 Ha2 invntt_radix3_zeta2_in_qrange
      invntt_radix3_zeta3_in_qrange invntt_radix3_zeta2_montgomery_meaning
      invntt_radix3_zeta3_montgomery_meaning.
    move: Hblk.
    rewrite /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_spec
            /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_second_spec
            /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_prefix_spec.
    rewrite Array768.initiE 1:/# /= ifF 1:/# ifT 1:/#.
    rewrite /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_block_at /=.
    rewrite (invntt_radix3_first_spec_far p
      (j - NTRUPlus768InvNTTRadix3Proof.block)) 1:/#.
    rewrite (invntt_radix3_first_spec_far p j) 1:/#.
    rewrite (invntt_radix3_first_spec_far p
      (j + NTRUPlus768InvNTTRadix3Proof.block)) 1:/#.
    rewrite /invntt_radix3_block_math_at /=.
    move=> [Hr0 [Hr1 [Hr2 [Hc0 [Hc1 Hc2]]]]].
    split; [exact Hr1 | exact Hc1].
  rewrite ifF 1:/#.
  have Ha0 := invntt_radix3_input_shape_coeff p
    (j - NTRUPlus768InvNTTRadix3Proof.double_block) Hinput _; first smt().
  have Ha1 := invntt_radix3_input_shape_coeff p
    (j - NTRUPlus768InvNTTRadix3Proof.block) Hinput _; first smt().
  have Ha2 := invntt_radix3_input_shape_coeff p j Hinput _; first smt().
  have Hblk := invntt_radix3_block_algebra
    NTRUPlus768InvNTTRadix3Proof.zeta2
    NTRUPlus768InvNTTRadix3Proof.zeta3
    p.[j - NTRUPlus768InvNTTRadix3Proof.double_block]
    p.[j - NTRUPlus768InvNTTRadix3Proof.block] p.[j]
    invntt_radix3_zeta2_root invntt_radix3_zeta3_root
    Ha0 Ha1 Ha2 invntt_radix3_zeta2_in_qrange
    invntt_radix3_zeta3_in_qrange invntt_radix3_zeta2_montgomery_meaning
    invntt_radix3_zeta3_montgomery_meaning.
  move: Hblk.
  rewrite /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_spec
          /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_second_spec
          /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_prefix_spec.
  rewrite Array768.initiE 1:/# /= ifF 1:/# ifF 1:/# ifT 1:/#.
  rewrite /NTRUPlus768InvNTTRadix3Proof.invntt_radix3_block_at /=.
  rewrite (invntt_radix3_first_spec_far p
    (j - NTRUPlus768InvNTTRadix3Proof.double_block)) 1:/#.
  rewrite (invntt_radix3_first_spec_far p
    (j - NTRUPlus768InvNTTRadix3Proof.block)) 1:/#.
  rewrite (invntt_radix3_first_spec_far p j) 1:/#.
  rewrite /invntt_radix3_block_math_at /=.
  move=> [Hr0 [Hr1 [Hr2 [Hc0 [Hc1 Hc2]]]]].
  split; [exact Hr2 | exact Hc2].
qed.

lemma invntt_radix3_from_invntt_radix2_64_algebra
    (input mid : W16.t Array768.t) :
  NTRUPlus768InvNTTRadix2_64Algebra.invntt_radix2_64_algebra input mid =>
  invntt_radix3_algebra mid
    (NTRUPlus768InvNTTRadix3Proof.invntt_radix3_spec mid).
proof.
  move=> H64.
  apply invntt_radix3_spec_algebra.
  exact (invntt_radix2_64_algebra_implies_invntt_radix3_input_shape
    input mid H64).
qed.

lemma invntt_radix3_algebra_functional
    (rp0 : W16.t Array768.t) :
  invntt_radix3_input_shape rp0 =>
  hoare [NTRUPlus768InvNTTRadix3.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_radix3 :
    rp = rp0 ==> invntt_radix3_algebra rp0 res].
proof.
  move=> Hinput.
  conseq (NTRUPlus768InvNTTRadix3Proof.invntt_radix3_functional rp0) => />.
  exact (invntt_radix3_spec_algebra rp0 Hinput).
qed.

lemma invntt_radix3_correct_algebra
    (rp0 : W16.t Array768.t) :
  invntt_radix3_input_shape rp0 =>
  phoare [NTRUPlus768InvNTTRadix3.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_radix3 :
    rp = rp0 ==> invntt_radix3_algebra rp0 res] = 1%r.
proof.
  move=> Hinput.
  have Hfunctional := invntt_radix3_algebra_functional rp0 Hinput.
  by conseq NTRUPlus768InvNTTRadix3Proof.invntt_radix3_lossless Hfunctional.
qed.
