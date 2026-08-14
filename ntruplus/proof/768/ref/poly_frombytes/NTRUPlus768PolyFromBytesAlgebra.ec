require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array4 Array768 Array1152.
require import NTRUPlus768PolyBasemul.
require import NTRUPlus768PolyBasemulAlgebra.
require import NTRUPlus768PolyBasemulInvNTTAlgebra.

import Ring.IntID IntOrder.

(* This arithmetic spec mirrors the parser-pinned C expressions exactly,
   but it is not a theorem about C-AST equivalence. *)
op poly_frombytes_even_int (a : W8.t Array1152.t) (i : int) : int =
  W8.to_uint a.[3 * i] + 256 * (W8.to_uint a.[3 * i + 1] %% 16).

op poly_frombytes_odd_int (a : W8.t Array1152.t) (i : int) : int =
  W8.to_uint a.[3 * i + 1] %/ 16 + 16 * W8.to_uint a.[3 * i + 2].

op poly_frombytes_int (a : W8.t Array1152.t) (j : int) : int =
  if j %% 2 = 0 then
    poly_frombytes_even_int a (j %/ 2)
  else
    poly_frombytes_odd_int a (j %/ 2).

op poly_frombytes_spec (a : W8.t Array1152.t) : W16.t Array768.t =
  Array768.init (fun j => W16.of_int (poly_frombytes_int a j)).

op coeff_lt_4096 (p : W16.t Array768.t) : bool =
  forall i, 0 <= i < 768 => 0 <= W16.to_uint p.[i] < 4096.

lemma byte_bound (a : W8.t Array1152.t) (i : int) :
  0 <= i < 1152 =>
  0 <= W8.to_uint a.[i] < 256.
proof.
  move=> Hi.
  have := W8.to_uint_cmp a.[i].
  smt().
qed.

lemma poly_frombytes_even_int_range (a : W8.t Array1152.t) (i : int) :
  0 <= i < 384 =>
  0 <= poly_frombytes_even_int a i < 4096.
proof.
  move=> Hi.
  have Hb0 := byte_bound a (3 * i) _.
  + smt().
  have Hb1 := byte_bound a (3 * i + 1) _.
  + smt().
  rewrite /poly_frombytes_even_int.
  have Hmod : 0 <= W8.to_uint a.[3 * i + 1] %% 16 < 16 by smt().
  smt().
qed.

lemma poly_frombytes_odd_int_range (a : W8.t Array1152.t) (i : int) :
  0 <= i < 384 =>
  0 <= poly_frombytes_odd_int a i < 4096.
proof.
  move=> Hi.
  have Hb1 := byte_bound a (3 * i + 1) _.
  + smt().
  have Hb2 := byte_bound a (3 * i + 2) _.
  + smt().
  rewrite /poly_frombytes_odd_int.
  have Hdiv : 0 <= W8.to_uint a.[3 * i + 1] %/ 16 < 16 by smt().
  smt().
qed.

lemma poly_frombytes_int_range (a : W8.t Array1152.t) (j : int) :
  0 <= j < 768 =>
  0 <= poly_frombytes_int a j < 4096.
proof.
  move=> Hj.
  rewrite /poly_frombytes_int.
  case (j %% 2 = 0).
  + move=> _.
    apply poly_frombytes_even_int_range.
    smt().
  move=> _.
  apply poly_frombytes_odd_int_range.
  smt().
qed.

lemma poly_frombytes_spec_coeff_uint (a : W8.t Array1152.t) (j : int) :
  0 <= j < 768 =>
  W16.to_uint (poly_frombytes_spec a).[j] = poly_frombytes_int a j.
proof.
  move=> Hj.
  rewrite /poly_frombytes_spec Array768.initiE 1:/# W16.of_uintK.
  have Hrange := poly_frombytes_int_range a j Hj.
  smt().
qed.

lemma poly_frombytes_spec_coeff_range (a : W8.t Array1152.t) (j : int) :
  0 <= j < 768 =>
  0 <= W16.to_uint (poly_frombytes_spec a).[j] < 4096.
proof.
  move=> Hj.
  rewrite poly_frombytes_spec_coeff_uint 1:/#.
  exact (poly_frombytes_int_range a j Hj).
qed.

lemma poly_frombytes_spec_coeff_lt_4096 (a : W8.t Array1152.t) :
  coeff_lt_4096 (poly_frombytes_spec a).
proof.
  move=> j Hj.
  exact (poly_frombytes_spec_coeff_range a j Hj).
qed.

lemma coeff_uint_small (w : W16.t) :
  0 <= W16.to_uint w < 2^15 =>
  W16.to_sint w = W16.to_uint w.
proof.
  move=> Hw.
  apply W16.to_sint_unsigned.
  rewrite W16.to_sintE /W16.smod ifF.
  + smt().
  smt(W16.to_uint_cmp).
qed.

lemma coeff_lt_4096_in_s12range768 (p : W16.t Array768.t) :
  coeff_lt_4096 p => in_s12range768 p.
proof.
  move=> Hp k Hk.
  rewrite /in_s12range4 /block4.
  split.
  + rewrite /in_s12range /s12_bound /coeff Array4.initiE 1:/#.
    have H := Hp (4 * k) _.
    + smt().
    have Hcoeff : W16.to_sint p.[4 * k] = W16.to_uint p.[4 * k].
    + apply coeff_uint_small.
      move: H; smt().
    rewrite Hcoeff.
    move: H; smt().
  split.
  + rewrite /in_s12range /s12_bound /coeff Array4.initiE 1:/#.
    have H := Hp (4 * k + 1) _.
    + smt().
    have Hcoeff : W16.to_sint p.[4 * k + 1] = W16.to_uint p.[4 * k + 1].
    + apply coeff_uint_small.
      move: H; smt().
    rewrite Hcoeff.
    move: H; smt().
  split.
  + rewrite /in_s12range /s12_bound /coeff Array4.initiE 1:/#.
    have H := Hp (4 * k + 2) _.
    + smt().
    have Hcoeff : W16.to_sint p.[4 * k + 2] = W16.to_uint p.[4 * k + 2].
    + apply coeff_uint_small.
      move: H; smt().
    rewrite Hcoeff.
    move: H; smt().
  rewrite /in_s12range /s12_bound /coeff Array4.initiE 1:/#.
  have H := Hp (4 * k + 3) _.
  + smt().
  have Hcoeff : W16.to_sint p.[4 * k + 3] = W16.to_uint p.[4 * k + 3].
  + apply coeff_uint_small.
    move: H; smt().
  rewrite Hcoeff.
  move: H; smt().
qed.

lemma poly_frombytes_spec_in_s12range768 (a : W8.t Array1152.t) :
  in_s12range768 (poly_frombytes_spec a).
proof.
  exact (coeff_lt_4096_in_s12range768 (poly_frombytes_spec a)
    (poly_frombytes_spec_coeff_lt_4096 a)).
qed.

lemma poly_frombytes_two_decoder_specs_invntt_ready
    (a b : W8.t Array1152.t) (rp0 : W16.t Array768.t) :
  phoare [NTRUPlus768PolyBasemul.M.jade_ntruplus_ntruplus768_amd64_ref_poly_basemul :
    rp = rp0 /\
    ap = poly_frombytes_spec a /\
    bp = poly_frombytes_spec b ==>
    poly_basemul_invntt_ready (poly_frombytes_spec a) (poly_frombytes_spec b) res] = 1%r.
proof.
  have Ha : in_s12range768 (poly_frombytes_spec a)
    by exact (poly_frombytes_spec_in_s12range768 a).
  have Hb : in_s12range768 (poly_frombytes_spec b)
    by exact (poly_frombytes_spec_in_s12range768 b).
  exact
    (poly_basemul_correct_invntt_ready rp0
      (poly_frombytes_spec a) (poly_frombytes_spec b) Ha Hb).
qed.
