require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.
require import Array768 NTRUPlus768PolyCenteredAdd.
require import NTRUPlus768BasemulAlgebra NTRUPlus768PolyBasemulAlgebra.
require import NTRUPlus768NTTRadix2_4Algebra.
require import NTRUPlus768EncapPolyBasemulAddAlgebra.

op centered_add_word32 (p a : W16.t) : W16.t =
  let s = sigextu32 p + sigextu32 a in
  let s = if s \slt W32.of_int (-3457) then s + W32.of_int 3457 else s in
  truncateu16 (if W32.of_int 3457 \sle s then s - W32.of_int 3457 else s).

lemma centered_add_word32_correct p a :
  in_qrange p => -1728 <= coeff a <= 1728 =>
  centered_add_word32 p a = centered_add_word p a.
proof.
  move=> hp ha.
  have hs : -5185 <= coeff p + coeff a <= 5184 by move: hp; rewrite /in_qrange /q; smt().
  rewrite /centered_add_word32 !sigextu32E /=.
  have hn : W32.to_sint (W32.of_int 4294963839) = -3457.
  + by rewrite /W32.to_sint W32.of_uintK /=.
  rewrite !W32.sltE hn.
  rewrite W32.to_sintK_small 1:/#.
  rewrite /centered_add_word /centered_sum_int /q /=.
  case (coeff p + coeff a < -3457) => hlow.
  + rewrite W32.sleE W32.to_sintK_small 1:/# W32.to_sintK_small 1:/#.
    have -> : !(3457 <= coeff p + coeff a + 3457) by smt().
    by rewrite /= truncateu16_of_int.
  rewrite W32.sleE W32.to_sintK_small 1:/# W32.to_sintK_small 1:/#.
  case (3457 <= coeff p + coeff a) => hhigh /=.
  + by rewrite truncateu16_of_int.
  by rewrite /= truncateu16_of_int.
qed.

lemma poly_centered_add_functional out0 product0 add0 :
  in_qrange768 product0 => centered_input_shape add0 =>
  hoare [NTRUPlus768PolyCenteredAdd.M.jade_ntruplus_ntruplus768_amd64_ref_poly_centered_add :
    arg = (out0,product0,add0) ==> res = poly_centered_add_spec product0 add0].
proof.
  move=> hp ha; proc.
  while (product = product0 /\ add = add0 /\ 0 <= W64.to_uint i <= 768 /\
    forall j, 0 <= j < W64.to_uint i =>
      output.[j] = centered_add_word product0.[j] add0.[j]); last first.
  + auto => />; split; first smt().
    move=> i1 out1 hd hlo hhi hprefix.
    rewrite W64.ultE /= in hd.
    have hi : W64.to_uint i1 = 768 by smt().
    apply Array768.tP => j hj.
    rewrite /poly_centered_add_spec Array768.initiE //.
    by apply hprefix; smt().
  auto => /> &hr hlo hhi hprefix hloop.
  rewrite W64.ultE /= in hloop.
  have hn : W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  rewrite hn.
  split; first smt().
  move=> j hjlo hjhi.
  rewrite Array768.get_setE 1:/# /=.
  case (j = W64.to_uint i{hr}) => heq.
  + rewrite heq.
    have hj : 0 <= W64.to_uint i{hr} < 768 by smt().
    have hw := centered_add_word32_correct product0.[W64.to_uint i{hr}] add0.[W64.to_uint i{hr}]
      (in_qrange768_coeff product0 (W64.to_uint i{hr}) hp hj)
      (centered_input_shape_add_bound add0 (W64.to_uint i{hr}) ha hj).
    by move: hw; rewrite /centered_add_word32 /=.
  by apply hprefix; smt().
qed.

lemma poly_centered_add_lossless : islossless
  NTRUPlus768PolyCenteredAdd.M.jade_ntruplus_ntruplus768_amd64_ref_poly_centered_add.
proof.
  proc.
  while (0 <= W64.to_uint i <= 768) (768 - W64.to_uint i).
  + auto => /> &hr hlo hhi hloop.
    rewrite W64.ultE /= in hloop.
    rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  auto => /> i hlo hhi hd; rewrite W64.ultE /=; smt().
qed.

lemma poly_centered_add_correct out0 product0 add0 :
  in_qrange768 product0 => centered_input_shape add0 =>
  phoare [NTRUPlus768PolyCenteredAdd.M.jade_ntruplus_ntruplus768_amd64_ref_poly_centered_add :
    arg = (out0,product0,add0) ==> res = poly_centered_add_spec product0 add0] = 1%r.
proof.
  move=> hp ha; by conseq poly_centered_add_lossless (poly_centered_add_functional out0 product0 add0 hp ha).
qed.

lemma poly_centered_add_qring_correct out0 product0 add0 :
  in_qrange768 product0 => centered_input_shape add0 =>
  phoare [NTRUPlus768PolyCenteredAdd.M.jade_ntruplus_ntruplus768_amd64_ref_poly_centered_add :
    arg = (out0,product0,add0) ==> poly_centered_add_qring product0 add0 res] = 1%r.
proof.
  move=> hp ha; conseq poly_centered_add_lossless (poly_centered_add_functional out0 product0 add0 hp ha) => />.
  have hh := poly_centered_add_spec_qring product0 add0 hp ha.
  by move: hh; rewrite /poly_centered_add_qring; smt().
qed.

lemma poly_centered_add_basemul_qring_correct out0 ap bp product0 add0 :
  poly_basemul_qring ap bp product0 192 => centered_input_shape add0 =>
  phoare [NTRUPlus768PolyCenteredAdd.M.jade_ntruplus_ntruplus768_amd64_ref_poly_centered_add :
    arg = (out0,product0,add0) ==> poly_basemul_add_qring ap bp add0 res 192] = 1%r.
proof.
  move=> hp ha.
  have hrange := poly_basemul_qring_product_in_qrange768 ap bp product0 hp.
  conseq poly_centered_add_lossless (poly_centered_add_functional out0 product0 add0 hrange ha) => />.
  have hh := poly_basemul_add_spec_qring ap bp product0 add0 hp ha.
  by move: hh; rewrite /poly_basemul_add_qring; smt().
qed.
