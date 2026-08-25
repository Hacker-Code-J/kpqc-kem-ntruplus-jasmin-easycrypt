require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord.

require import Array4.
require import NTRUPlus768BasemulProof.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768BaseInvAlgebra.
require import NTRUPlus768FqInvAlgebra.

import Ring.IntID IntOrder.

(* Scope: pure relational word specification for the scalar baseinv trace,
   matching the seam-checked C arithmetic schedule.  This file has no formal C/Jasmin procedure equivalence
   and no current return-code theorem;
   proves the raw trace5 zero criterion exactly at the word state and derives
   the final output q-range internally. *)

op mred_word_spec (x : int) : W16.t =
  NTRUPlus768BasemulProof.montgomery_reduce (W32.of_int x).

op baseinv_trace_expr
    (a : W16.t Array4.t) (zeta_word : W16.t) (state : int -> W16.t) (i : int)
    : int =
  if i = 0 then
    coeff a.[2] * coeff a.[2] - 2 * coeff a.[1] * coeff a.[3]
  else if i = 1 then
    coeff a.[3] * coeff a.[3]
  else if i = 2 then
    coeff a.[0] * coeff a.[0] + coeff (state 0) * coeff zeta_word
  else if i = 3 then
    coeff a.[1] * coeff a.[1] + coeff (state 1) * coeff zeta_word -
    2 * coeff a.[0] * coeff a.[2]
  else if i = 4 then
    coeff (state 3) * coeff zeta_word
  else if i = 5 then
    coeff (state 2) * coeff (state 2) -
    coeff (state 3) * coeff (state 4)
  else if i = 6 then
    coeff a.[0] * coeff (state 2) +
    coeff a.[2] * coeff (state 4)
  else if i = 7 then
    coeff a.[3] * coeff (state 4) +
    coeff a.[1] * coeff (state 2)
  else if i = 8 then
    coeff a.[2] * coeff (state 2) +
    coeff a.[0] * coeff (state 3)
  else if i = 9 then
    coeff a.[1] * coeff (state 3) +
    coeff a.[3] * coeff (state 2)
  else 0.

op baseinv_final_mul_expr
    (state : int -> W16.t) (invword : W16.t) (i : int) : int =
  coeff (state (6 + i)) * coeff invword.

op signed_word (w : W16.t) : W16.t = W16.of_int (-coeff w).

op baseinv_full_trace_expr
    (a : W16.t Array4.t) (zeta_word invword : W16.t)
    (state : int -> W16.t) (i : int) : int =
  if 0 <= i < 10 then baseinv_trace_expr a zeta_word state i
  else if i = 10 then baseinv_final_mul_expr state invword 0
  else if i = 11 then baseinv_final_mul_expr state invword 1
  else if i = 12 then baseinv_final_mul_expr state invword 2
  else if i = 13 then baseinv_final_mul_expr state invword 3
  else 0.

op baseinv_signed_output (state : int -> W16.t) : W16.t Array4.t =
  Array4.init (fun i =>
    if i = 0 then state 10 else
    if i = 1 then signed_word (state 11) else
    if i = 2 then state 12 else
    signed_word (state 13)).

lemma mred_word_spec_algebra (x : int) :
  -R %/ 2 * q <= x < R %/ 2 * q =>
  in_qrange (mred_word_spec x) /\
  coeff (mred_word_spec x) %% q = (x * Rinv) %% q.
proof.
  by rewrite /mred_word_spec; apply montgomery_reduce_of_int.
qed.

lemma mred_word_spec_strict_range (x : int) :
  -R %/ 2 * q <= x < R %/ 2 * q =>
  -q < coeff (mred_word_spec x) < q.
proof.
  by rewrite /mred_word_spec; apply montgomery_reduce_of_int_strict.
qed.

lemma mred_word_spec_zero_mod_iff_zero (x : int) :
  -R %/ 2 * q <= x < R %/ 2 * q =>
  (coeff (mred_word_spec x) %% q = 0) <=> mred_word_spec x = W16.zero.
proof.
  by rewrite /mred_word_spec; apply montgomery_reduce_of_int_zero_iff.
qed.

lemma add_mod_q_congr (x y x' y' : int) :
  x %% q = x' %% q =>
  y %% q = y' %% q =>
  (x + y) %% q = (x' + y') %% q.
proof.
  by move=> Hx Hy;
    rewrite -modzDml Hx modzDml -modzDmr Hy modzDmr.
qed.

lemma mul_left_mod_q_congr (k x x' : int) :
  x %% q = x' %% q =>
  (k * x) %% q = (k * x') %% q.
proof.
  move=> Hx.
  apply (mul_mod_q_congr k x k x').
  + done.
  exact Hx.
qed.

lemma square_minus_double_product_bound (x y z : int) :
  -q <= x < q =>
  -q <= y < q =>
  -q <= z < q =>
  -R %/ 2 * q <= x * x - 2 * y * z < R %/ 2 * q.
proof.
  move=> Hx Hy Hz.
  have Hx2 := qrange_product_norm x x Hx Hx.
  have Hyz := qrange_product_norm y z Hy Hz.
  have Hsum : `|x * x - 2 * y * z| <= 3 * q * q by smt().
  have Hlim : 3 * q * q < R %/ 2 * q.
  + rewrite (ltr_pmul2r q).
    + by rewrite /q.
    rewrite R_halfE /q.
    smt().
  have Habs : `|x * x - 2 * y * z| < R %/ 2 * q by smt().
  move: Habs; rewrite ltr_norml; smt().
qed.

lemma square_plus_product_bound (x y z : int) :
  -q <= x < q =>
  -q <= y < q =>
  -q <= z < q =>
  -R %/ 2 * q <= x * x + y * z < R %/ 2 * q.
proof.
  move=> Hx Hy Hz.
  have Hx2 := qrange_product_norm x x Hx Hx.
  have Hyz := qrange_product_norm y z Hy Hz.
  have Hsum : `|x * x + y * z| <= 2 * q * q by smt().
  have Hlim : 2 * q * q < R %/ 2 * q.
  + rewrite (ltr_pmul2r q).
    + by rewrite /q.
    rewrite R_halfE /q.
    smt().
  have Habs : `|x * x + y * z| < R %/ 2 * q by smt().
  move: Habs; rewrite ltr_norml; smt().
qed.

lemma square_plus_product_minus_double_product_bound
    (x y z u v : int) :
  -q <= x < q =>
  -q <= y < q =>
  -q <= z < q =>
  -q <= u < q =>
  -q <= v < q =>
  -R %/ 2 * q <= x * x + y * z - 2 * u * v < R %/ 2 * q.
proof.
  move=> Hx Hy Hz Hu Hv.
  have Hx2 := qrange_product_norm x x Hx Hx.
  have Hyz := qrange_product_norm y z Hy Hz.
  have Huv := qrange_product_norm u v Hu Hv.
  have Hsum : `|x * x + y * z - 2 * u * v| <= 4 * q * q by smt().
  have Hlim : 4 * q * q < R %/ 2 * q.
  + rewrite (ltr_pmul2r q).
    + by rewrite /q.
    rewrite R_halfE /q.
    smt().
  have Habs : `|x * x + y * z - 2 * u * v| < R %/ 2 * q by smt().
  move: Habs; rewrite ltr_norml; smt().
qed.

lemma square_minus_product_bound (x y z : int) :
  -q <= x < q =>
  -q <= y < q =>
  -q <= z < q =>
  -R %/ 2 * q <= x * x - y * z < R %/ 2 * q.
proof.
  move=> Hx Hy Hz.
  have Hx2 := qrange_product_norm x x Hx Hx.
  have Hyz := qrange_product_norm y z Hy Hz.
  have Hsum : `|x * x - y * z| <= 2 * q * q by smt().
  have Hlim : 2 * q * q < R %/ 2 * q.
  + rewrite (ltr_pmul2r q).
    + by rewrite /q.
    rewrite R_halfE /q.
    smt().
  have Habs : `|x * x - y * z| < R %/ 2 * q by smt().
  move: Habs; rewrite ltr_norml; smt().
qed.

lemma signed_word_coeff (w : W16.t) :
  in_qrange w =>
  coeff (signed_word w) = -coeff w.
proof.
  move=> Hw.
  have Hsmall : W16.min_sint <= -coeff w <= W16.max_sint.
  + rewrite /in_qrange in Hw.
    move: Hw; rewrite /q; smt().
  rewrite /signed_word /coeff.
  exact (W16.to_sintK_small (-coeff w) Hsmall).
qed.

lemma signed_word_in_qrange_strict (w : W16.t) :
  -q < coeff w < q => in_qrange (signed_word w).
proof.
  move=> Hw.
  have Hrange : in_qrange w by move: Hw; smt().
  rewrite /in_qrange (signed_word_coeff w Hrange).
  move: Hw; smt().
qed.

lemma baseinv_trace0
    (a : W16.t Array4.t) (zeta_word : W16.t) (state : int -> W16.t) :
  in_qrange4 a =>
  (forall i, 0 <= i < 10 =>
    state i = mred_word_spec (baseinv_trace_expr a zeta_word state i)) =>
  in_qrange (state 0) /\
  coeff (state 0) %% q =
    ((coeff a.[2] * coeff a.[2] - 2 * coeff a.[1] * coeff a.[3]) * Rinv) %% q.
proof.
  move=> Ha Hstate.
  move: Ha => [Ha0 [Ha1 [Ha2 Ha3]]].
  have H0 := Hstate 0.
  have -> :
    state 0 = mred_word_spec
      (coeff a.[2] * coeff a.[2] - 2 * coeff a.[1] * coeff a.[3])
    by apply H0; smt().
  exact (mred_word_spec_algebra
    (coeff a.[2] * coeff a.[2] - 2 * coeff a.[1] * coeff a.[3])
    (square_minus_double_product_bound
      (coeff a.[2]) (coeff a.[1]) (coeff a.[3]) Ha2 Ha1 Ha3)).
qed.

lemma baseinv_trace1
    (a : W16.t Array4.t) (zeta_word : W16.t) (state : int -> W16.t) :
  in_qrange4 a =>
  (forall i, 0 <= i < 10 =>
    state i = mred_word_spec (baseinv_trace_expr a zeta_word state i)) =>
  in_qrange (state 1) /\
  coeff (state 1) %% q = (coeff a.[3] * coeff a.[3] * Rinv) %% q.
proof.
  move=> Ha Hstate.
  move: Ha => [_ [_ [_ Ha3]]].
  have H1 := Hstate 1.
  have -> :
    state 1 = mred_word_spec (coeff a.[3] * coeff a.[3])
    by apply H1; smt().
  exact (mred_word_spec_algebra
    (coeff a.[3] * coeff a.[3])
    (product_bound (coeff a.[3]) (coeff a.[3]) Ha3 Ha3)).
qed.

lemma baseinv_trace2
    (a : W16.t Array4.t) (zeta_word : W16.t) (z : int) (state : int -> W16.t) :
  in_qrange4 a =>
  in_qrange zeta_word =>
  zeta_mont_relation zeta_word z =>
  (forall i, 0 <= i < 10 =>
    state i = mred_word_spec (baseinv_trace_expr a zeta_word state i)) =>
  in_qrange (state 2) /\
  coeff (state 2) %% q = (inverse_u a z * Rinv) %% q.
proof.
  move=> Ha Hzeta_w Hzeta Hstate.
  have [Ha0 [_ [Ha2 Ha3]]] := Ha.
  have Hs0 := baseinv_trace0 a zeta_word state Ha Hstate.
  move: Hs0 => [Hs0b Hs0c].
  have Hstate2 := Hstate 2.
  have -> :
    state 2 = mred_word_spec
      (coeff a.[0] * coeff a.[0] + coeff (state 0) * coeff zeta_word)
    by apply Hstate2; smt().
  have Hs0range : -q <= coeff (state 0) < q by rewrite /in_qrange in Hs0b.
  have Hbound := square_plus_product_bound
    (coeff a.[0]) (coeff (state 0)) (coeff zeta_word) Ha0 Hs0range Hzeta_w.
  have [Hrange Hcongr] :=
    mred_word_spec_algebra
      (coeff a.[0] * coeff a.[0] + coeff (state 0) * coeff zeta_word) Hbound.
  split; first exact Hrange.
  have HzR := zeta_mont_Rinv zeta_word z Hzeta.
  have Htz := montgomery_zeta_congr
    (coeff (state 0))
    (coeff a.[2] * coeff a.[2] - 2 * coeff a.[1] * coeff a.[3])
    (coeff zeta_word) z Hs0c HzR.
  have Hsum :
    (coeff a.[0] * coeff a.[0] + coeff (state 0) * coeff zeta_word) %% q =
    (coeff a.[0] * coeff a.[0] +
     (coeff a.[2] * coeff a.[2] - 2 * coeff a.[1] * coeff a.[3]) * z) %% q.
  + by rewrite -modzDmr Htz modzDmr.
  have Hu :
    coeff a.[0] * coeff a.[0] +
    (coeff a.[2] * coeff a.[2] - 2 * coeff a.[1] * coeff a.[3]) * z =
    inverse_u a z.
  + rewrite /inverse_u.
    ring.
  have Hscale := mul_mod_q_congr
    (coeff a.[0] * coeff a.[0] + coeff (state 0) * coeff zeta_word) Rinv
    (inverse_u a z) Rinv _ _.
  + by rewrite Hsum Hu.
  + done.
  by rewrite Hcongr Hscale.
qed.

lemma baseinv_trace3
    (a : W16.t Array4.t) (zeta_word : W16.t) (z : int) (state : int -> W16.t) :
  in_qrange4 a =>
  in_qrange zeta_word =>
  zeta_mont_relation zeta_word z =>
  (forall i, 0 <= i < 10 =>
    state i = mred_word_spec (baseinv_trace_expr a zeta_word state i)) =>
  in_qrange (state 3) /\
  coeff (state 3) %% q = (inverse_v a z * Rinv) %% q.
proof.
  move=> Ha Hzeta_w Hzeta Hstate.
  have [Ha0 [Ha1 [Ha2 _]]] := Ha.
  have Hs1 := baseinv_trace1 a zeta_word state Ha Hstate.
  move: Hs1 => [Hs1b Hs1c].
  have Hstate3 := Hstate 3.
  have -> :
    state 3 = mred_word_spec
      (coeff a.[1] * coeff a.[1] + coeff (state 1) * coeff zeta_word -
       2 * coeff a.[0] * coeff a.[2])
    by apply Hstate3; smt().
  have Hs1range : -q <= coeff (state 1) < q by rewrite /in_qrange in Hs1b.
  have Hbound :=
    square_plus_product_minus_double_product_bound
      (coeff a.[1]) (coeff (state 1)) (coeff zeta_word)
      (coeff a.[0]) (coeff a.[2])
      Ha1 Hs1range Hzeta_w Ha0 Ha2.
  have [Hrange Hcongr] := mred_word_spec_algebra
    (coeff a.[1] * coeff a.[1] + coeff (state 1) * coeff zeta_word -
     2 * coeff a.[0] * coeff a.[2]) Hbound.
  split; first exact Hrange.
  have HzR := zeta_mont_Rinv zeta_word z Hzeta.
  have Htz := montgomery_zeta_congr
    (coeff (state 1))
    (coeff a.[3] * coeff a.[3])
    (coeff zeta_word) z Hs1c HzR.
  have Hsum :
    (coeff a.[1] * coeff a.[1] + coeff (state 1) * coeff zeta_word -
     2 * coeff a.[0] * coeff a.[2]) %% q =
    (coeff a.[1] * coeff a.[1] + (coeff a.[3] * coeff a.[3]) * z -
     2 * coeff a.[0] * coeff a.[2]) %% q.
  + rewrite (_ :
      coeff a.[1] * coeff a.[1] + coeff (state 1) * coeff zeta_word -
      2 * coeff a.[0] * coeff a.[2] =
      coeff (state 1) * coeff zeta_word +
      (coeff a.[1] * coeff a.[1] - 2 * coeff a.[0] * coeff a.[2])).
    + ring.
    rewrite (_ :
      coeff a.[1] * coeff a.[1] + (coeff a.[3] * coeff a.[3]) * z -
      2 * coeff a.[0] * coeff a.[2] =
      (coeff a.[3] * coeff a.[3]) * z +
      (coeff a.[1] * coeff a.[1] - 2 * coeff a.[0] * coeff a.[2])).
    + ring.
    by rewrite -modzDml Htz modzDml.
  have Hv :
    coeff a.[1] * coeff a.[1] + (coeff a.[3] * coeff a.[3]) * z -
    2 * coeff a.[0] * coeff a.[2] = inverse_v a z.
  + rewrite /inverse_v.
    ring.
  have Hscale := mul_mod_q_congr
    (coeff a.[1] * coeff a.[1] + coeff (state 1) * coeff zeta_word -
     2 * coeff a.[0] * coeff a.[2]) Rinv
    (inverse_v a z) Rinv _ _.
  + by rewrite Hsum Hv.
  + done.
  by rewrite Hcongr Hscale.
qed.

lemma baseinv_trace4
    (a : W16.t Array4.t) (zeta_word : W16.t) (z : int) (state : int -> W16.t) :
  in_qrange4 a =>
  in_qrange zeta_word =>
  zeta_mont_relation zeta_word z =>
  (forall i, 0 <= i < 10 =>
    state i = mred_word_spec (baseinv_trace_expr a zeta_word state i)) =>
  in_qrange (state 4) /\
  coeff (state 4) %% q = (z * inverse_v a z * Rinv) %% q.
proof.
  move=> Ha Hzeta_w Hzeta Hstate.
  have Hs3 := baseinv_trace3 a zeta_word z state Ha Hzeta_w Hzeta Hstate.
  move: Hs3 => [Hs3b Hs3c].
  have Hstate4 := Hstate 4.
  have -> :
    state 4 = mred_word_spec (coeff (state 3) * coeff zeta_word)
    by apply Hstate4; smt().
  have Hs3range : -q <= coeff (state 3) < q by rewrite /in_qrange in Hs3b.
  have Hbound := product_bound (coeff (state 3)) (coeff zeta_word) Hs3range Hzeta_w.
  have [Hrange Hcongr] := mred_word_spec_algebra
    (coeff (state 3) * coeff zeta_word) Hbound.
  split; first exact Hrange.
  have HzR := zeta_mont_Rinv zeta_word z Hzeta.
  have Htz := montgomery_zeta_congr
    (coeff (state 3)) (inverse_v a z) (coeff zeta_word) z Hs3c HzR.
  have Hcomm : inverse_v a z * z = z * inverse_v a z by ring.
  have Hpre :
    (coeff (state 3) * coeff zeta_word) %% q =
    (z * inverse_v a z) %% q by rewrite Htz Hcomm.
  have Hscale := mul_mod_q_congr
    (coeff (state 3) * coeff zeta_word) Rinv
    (z * inverse_v a z) Rinv Hpre _.
  + done.
  by rewrite Hcongr Hscale.
qed.

lemma baseinv_trace5
    (a : W16.t Array4.t) (zeta_word : W16.t) (z : int) (state : int -> W16.t) :
  in_qrange4 a =>
  in_qrange zeta_word =>
  zeta_mont_relation zeta_word z =>
  (forall i, 0 <= i < 10 =>
    state i = mred_word_spec (baseinv_trace_expr a zeta_word state i)) =>
  in_qrange (state 5) /\
  coeff (state 5) %% q = (inverse_determinant a z * exp Rinv 3) %% q.
proof.
  move=> Ha Hzeta_w Hzeta Hstate.
  have Hs2 := baseinv_trace2 a zeta_word z state Ha Hzeta_w Hzeta Hstate.
  move: Hs2 => [Hs2b Hs2c].
  have Hs3 := baseinv_trace3 a zeta_word z state Ha Hzeta_w Hzeta Hstate.
  move: Hs3 => [Hs3b Hs3c].
  have Hs4 := baseinv_trace4 a zeta_word z state Ha Hzeta_w Hzeta Hstate.
  move: Hs4 => [Hs4b Hs4c].
  have Hstate5 := Hstate 5.
  have -> :
    state 5 = mred_word_spec
      (coeff (state 2) * coeff (state 2) - coeff (state 3) * coeff (state 4))
    by apply Hstate5; smt().
  have Hs2range : -q <= coeff (state 2) < q by rewrite /in_qrange in Hs2b.
  have Hs3range : -q <= coeff (state 3) < q by rewrite /in_qrange in Hs3b.
  have Hs4range : -q <= coeff (state 4) < q by rewrite /in_qrange in Hs4b.
  have Hbound :=
    square_minus_product_bound
      (coeff (state 2)) (coeff (state 3)) (coeff (state 4))
      Hs2range Hs3range Hs4range.
  have [Hrange Hcongr] := mred_word_spec_algebra
    (coeff (state 2) * coeff (state 2) - coeff (state 3) * coeff (state 4))
    Hbound.
  split; first exact Hrange.
  have Hsq : (coeff (state 2) * coeff (state 2)) %% q =
      (inverse_u a z * inverse_u a z * exp Rinv 2) %% q.
  + have := mul_mod_q_congr
      (coeff (state 2)) (coeff (state 2))
      (inverse_u a z * Rinv) (inverse_u a z * Rinv)
      Hs2c Hs2c.
    rewrite (_ :
      (inverse_u a z * Rinv) * (inverse_u a z * Rinv) =
      inverse_u a z * inverse_u a z * exp Rinv 2) => //.
    ring.
  have Hprod : (coeff (state 3) * coeff (state 4)) %% q =
      (z * inverse_v a z * inverse_v a z * exp Rinv 2) %% q.
  + have := mul_mod_q_congr
      (coeff (state 3)) (coeff (state 4))
      (inverse_v a z * Rinv) (z * inverse_v a z * Rinv)
      Hs3c Hs4c.
    rewrite (_ :
      (inverse_v a z * Rinv) * (z * inverse_v a z * Rinv) =
      z * inverse_v a z * inverse_v a z * exp Rinv 2) => //.
    ring.
  have Hneg :
    (-(coeff (state 3) * coeff (state 4))) %% q =
    (-(z * inverse_v a z * inverse_v a z * exp Rinv 2)) %% q.
  + by rewrite -modzNm Hprod modzNm.
  have Hdiff :
    (coeff (state 2) * coeff (state 2) -
     coeff (state 3) * coeff (state 4)) %% q =
    (inverse_u a z * inverse_u a z * exp Rinv 2 -
     z * inverse_v a z * inverse_v a z * exp Rinv 2) %% q.
  + rewrite (_ :
      coeff (state 2) * coeff (state 2) -
      coeff (state 3) * coeff (state 4) =
      coeff (state 2) * coeff (state 2) +
      (-(coeff (state 3) * coeff (state 4)))).
    + ring.
    rewrite (_ :
      inverse_u a z * inverse_u a z * exp Rinv 2 -
      z * inverse_v a z * inverse_v a z * exp Rinv 2 =
      inverse_u a z * inverse_u a z * exp Rinv 2 +
      (-(z * inverse_v a z * inverse_v a z * exp Rinv 2))).
    + ring.
    rewrite -modzDml Hsq modzDml -modzDmr Hneg modzDmr.
    done.
  have Hdetexpr :
    inverse_u a z * inverse_u a z * exp Rinv 2 -
    z * inverse_v a z * inverse_v a z * exp Rinv 2 =
    inverse_determinant a z * exp Rinv 2.
  + rewrite /inverse_determinant.
    ring.
  have Hpre :
    (coeff (state 2) * coeff (state 2) -
     coeff (state 3) * coeff (state 4)) %% q =
    (inverse_determinant a z * exp Rinv 2) %% q
    by rewrite Hdiff Hdetexpr.
  have Hscale := mul_mod_q_congr
    (coeff (state 2) * coeff (state 2) -
     coeff (state 3) * coeff (state 4)) Rinv
    (inverse_determinant a z * exp Rinv 2) Rinv Hpre _.
  + done.
  have Hpow :
    inverse_determinant a z * exp Rinv 2 * Rinv =
    inverse_determinant a z * exp Rinv 3 by ring.
  by rewrite Hcongr Hscale Hpow.
qed.

lemma trace5_zero_implies_determinant_zero
    (a : W16.t Array4.t) (zeta_word : W16.t) (z : int) (state : int -> W16.t) :
  in_qrange4 a =>
  in_qrange zeta_word =>
  zeta_mont_relation zeta_word z =>
  (forall i, 0 <= i < 10 =>
    state i = mred_word_spec (baseinv_trace_expr a zeta_word state i)) =>
  state 5 = W16.zero =>
  inverse_determinant a z %% q = 0.
proof.
  move=> Ha Hzeta_w Hzeta Hstate Hz0.
  have Hs5 := baseinv_trace5 a zeta_word z state Ha Hzeta_w Hzeta Hstate.
  move: Hs5 => [_ Hs5c].
  have Hzero : coeff (state 5) %% q = 0.
  + rewrite Hz0 /coeff /= /W16.to_sint /=.
    done.
  have Hscaled :
    (inverse_determinant a z * exp Rinv 3) %% q = 0
    by rewrite -Hs5c Hzero.
  have HR3inv :
    ((exp Rinv 3) * 3310 * 3310 * 3310) %% q = 1 %% q.
  + rewrite /Rinv /q /=.
    done.
  have Hmul := mul_mod_q_congr
    (inverse_determinant a z * exp Rinv 3) (3310 * 3310 * 3310)
    0 (3310 * 3310 * 3310) Hscaled _.
  + done.
  rewrite (_ :
    (inverse_determinant a z * exp Rinv 3) * (3310 * 3310 * 3310) =
    inverse_determinant a z * ((exp Rinv 3) * 3310 * 3310 * 3310)) in Hmul.
  + ring.
  rewrite -modzMmr HR3inv /= in Hmul.
  exact Hmul.
qed.

lemma trace5_residue_zero_iff_zero
    (a : W16.t Array4.t) (zeta_word : W16.t) (z : int) (state : int -> W16.t) :
  in_qrange4 a =>
  in_qrange zeta_word =>
  zeta_mont_relation zeta_word z =>
  (forall i, 0 <= i < 10 =>
    state i = mred_word_spec (baseinv_trace_expr a zeta_word state i)) =>
  (coeff (state 5) %% q = 0) <=> state 5 = W16.zero.
proof.
  move=> Ha Hzeta_w Hzeta Hstate.
  have [Hs2b _] := baseinv_trace2 a zeta_word z state Ha Hzeta_w Hzeta Hstate.
  have [Hs3b _] := baseinv_trace3 a zeta_word z state Ha Hzeta_w Hzeta Hstate.
  have [Hs4b _] := baseinv_trace4 a zeta_word z state Ha Hzeta_w Hzeta Hstate.
  have Hstate5 := Hstate 5.
  have -> :
    state 5 = mred_word_spec
      (coeff (state 2) * coeff (state 2) - coeff (state 3) * coeff (state 4))
    by apply Hstate5; smt().
  have Hs2range : -q <= coeff (state 2) < q by rewrite /in_qrange in Hs2b.
  have Hs3range : -q <= coeff (state 3) < q by rewrite /in_qrange in Hs3b.
  have Hs4range : -q <= coeff (state 4) < q by rewrite /in_qrange in Hs4b.
  exact (mred_word_spec_zero_mod_iff_zero
    (coeff (state 2) * coeff (state 2) - coeff (state 3) * coeff (state 4))
    (square_minus_product_bound
      (coeff (state 2)) (coeff (state 3)) (coeff (state 4))
      Hs2range Hs3range Hs4range)).
qed.

lemma determinant_zero_forces_trace5_zero
    (a : W16.t Array4.t) (zeta_word : W16.t) (z : int) (state : int -> W16.t) :
  in_qrange4 a =>
  in_qrange zeta_word =>
  zeta_mont_relation zeta_word z =>
  (forall i, 0 <= i < 10 =>
    state i = mred_word_spec (baseinv_trace_expr a zeta_word state i)) =>
  inverse_determinant a z %% q = 0 =>
  state 5 = W16.zero.
proof.
  move=> Ha Hzeta_w Hzeta Hstate Hdet0.
  have [_ Hs5c] := baseinv_trace5 a zeta_word z state Ha Hzeta_w Hzeta Hstate.
  have Hmod0 : coeff (state 5) %% q = 0.
  + have Hscaled := mul_mod_q_congr
      (inverse_determinant a z) (exp Rinv 3)
      0 (exp Rinv 3) Hdet0 _.
    - done.
    rewrite Hs5c Hscaled.
    done.
  rewrite -(trace5_residue_zero_iff_zero
    a zeta_word z state Ha Hzeta_w Hzeta Hstate).
  exact Hmod0.
qed.

lemma determinant_zero_iff_trace5_zero
    (a : W16.t Array4.t) (zeta_word : W16.t) (z : int) (state : int -> W16.t) :
  in_qrange4 a =>
  in_qrange zeta_word =>
  zeta_mont_relation zeta_word z =>
  (forall i, 0 <= i < 10 =>
    state i = mred_word_spec (baseinv_trace_expr a zeta_word state i)) =>
  (inverse_determinant a z %% q = 0) <=> state 5 = W16.zero.
proof.
  move=> Ha Hzeta_w Hzeta Hstate.
  split.
  + apply (determinant_zero_forces_trace5_zero
      a zeta_word z state Ha Hzeta_w Hzeta Hstate).
  apply (trace5_zero_implies_determinant_zero
    a zeta_word z state Ha Hzeta_w Hzeta Hstate).
qed.

lemma determinant_nonzero_implies_trace5_nonzero
    (a : W16.t Array4.t) (zeta_word : W16.t) (z : int) (state : int -> W16.t) :
  in_qrange4 a =>
  in_qrange zeta_word =>
  zeta_mont_relation zeta_word z =>
  (forall i, 0 <= i < 10 =>
    state i = mred_word_spec (baseinv_trace_expr a zeta_word state i)) =>
  inverse_determinant a z %% q <> 0 =>
  state 5 <> W16.zero.
proof.
  move=> Ha Hzeta_w Hzeta Hstate Hdet.
  have Hfail := trace5_zero_implies_determinant_zero
    a zeta_word z state Ha Hzeta_w Hzeta Hstate.
  smt().
qed.

lemma numerator0_pre_congr
    (a : W16.t Array4.t) (z s2 s4 : int) :
  s2 %% q = (inverse_u a z * Rinv) %% q =>
  s4 %% q = (z * inverse_v a z * Rinv) %% q =>
  (coeff a.[0] * s2 + coeff a.[2] * s4) %% q =
  (inverse_numerator0 a z * Rinv) %% q.
proof.
  move=> Hs2 Hs4.
  have Hu := mul_left_mod_q_congr
    (coeff a.[0]) s2 (inverse_u a z * Rinv) Hs2.
  have Hzv := mul_left_mod_q_congr
    (coeff a.[2]) s4 (z * inverse_v a z * Rinv) Hs4.
  have Hnorm :
    inverse_numerator0 a z * Rinv =
    coeff a.[0] * (inverse_u a z * Rinv) +
    coeff a.[2] * (z * inverse_v a z * Rinv).
  + rewrite /inverse_numerator0.
    ring.
  rewrite Hnorm.
  exact (add_mod_q_congr
    (coeff a.[0] * s2) (coeff a.[2] * s4)
    (coeff a.[0] * (inverse_u a z * Rinv))
    (coeff a.[2] * (z * inverse_v a z * Rinv))
    Hu Hzv).
qed.

lemma numerator1_pre_congr
    (a : W16.t Array4.t) (z s2 s4 : int) :
  s2 %% q = (inverse_u a z * Rinv) %% q =>
  s4 %% q = (z * inverse_v a z * Rinv) %% q =>
  (coeff a.[3] * s4 + coeff a.[1] * s2) %% q =
  ((-inverse_numerator1 a z) * Rinv) %% q.
proof.
  move=> Hs2 Hs4.
  have Hzv := mul_left_mod_q_congr
    (coeff a.[3]) s4 (z * inverse_v a z * Rinv) Hs4.
  have Hu := mul_left_mod_q_congr
    (coeff a.[1]) s2 (inverse_u a z * Rinv) Hs2.
  have Hnorm :
    (-inverse_numerator1 a z) * Rinv =
    coeff a.[3] * (z * inverse_v a z * Rinv) +
    coeff a.[1] * (inverse_u a z * Rinv).
  + rewrite /inverse_numerator1.
    ring.
  rewrite Hnorm.
  exact (add_mod_q_congr
    (coeff a.[3] * s4) (coeff a.[1] * s2)
    (coeff a.[3] * (z * inverse_v a z * Rinv))
    (coeff a.[1] * (inverse_u a z * Rinv))
    Hzv Hu).
qed.

lemma numerator2_pre_congr
    (a : W16.t Array4.t) (z s2 s3 : int) :
  s2 %% q = (inverse_u a z * Rinv) %% q =>
  s3 %% q = (inverse_v a z * Rinv) %% q =>
  (coeff a.[2] * s2 + coeff a.[0] * s3) %% q =
  (inverse_numerator2 a z * Rinv) %% q.
proof.
  move=> Hs2 Hs3.
  have Hu := mul_left_mod_q_congr
    (coeff a.[2]) s2 (inverse_u a z * Rinv) Hs2.
  have Hv := mul_left_mod_q_congr
    (coeff a.[0]) s3 (inverse_v a z * Rinv) Hs3.
  have Hnorm :
    inverse_numerator2 a z * Rinv =
    coeff a.[2] * (inverse_u a z * Rinv) +
    coeff a.[0] * (inverse_v a z * Rinv).
  + rewrite /inverse_numerator2.
    ring.
  rewrite Hnorm.
  exact (add_mod_q_congr
    (coeff a.[2] * s2) (coeff a.[0] * s3)
    (coeff a.[2] * (inverse_u a z * Rinv))
    (coeff a.[0] * (inverse_v a z * Rinv))
    Hu Hv).
qed.

lemma numerator3_pre_congr
    (a : W16.t Array4.t) (z s2 s3 : int) :
  s2 %% q = (inverse_u a z * Rinv) %% q =>
  s3 %% q = (inverse_v a z * Rinv) %% q =>
  (coeff a.[1] * s3 + coeff a.[3] * s2) %% q =
  ((-inverse_numerator3 a z) * Rinv) %% q.
proof.
  move=> Hs2 Hs3.
  have Hv3 := mul_left_mod_q_congr
    (coeff a.[1]) s3 (inverse_v a z * Rinv) Hs3.
  have Hu3 := mul_left_mod_q_congr
    (coeff a.[3]) s2 (inverse_u a z * Rinv) Hs2.
  have Hnorm :
    (-inverse_numerator3 a z) * Rinv =
    coeff a.[1] * (inverse_v a z * Rinv) +
    coeff a.[3] * (inverse_u a z * Rinv).
  + rewrite /inverse_numerator3.
    ring.
  rewrite Hnorm.
  exact (add_mod_q_congr
    (coeff a.[1] * s3) (coeff a.[3] * s2)
    (coeff a.[1] * (inverse_v a z * Rinv))
    (coeff a.[3] * (inverse_u a z * Rinv))
    Hv3 Hu3).
qed.

lemma baseinv_trace6789
    (a : W16.t Array4.t) (zeta_word : W16.t) (z : int) (state : int -> W16.t) :
  in_qrange4 a =>
  in_qrange zeta_word =>
  zeta_mont_relation zeta_word z =>
  (forall i, 0 <= i < 10 =>
    state i = mred_word_spec (baseinv_trace_expr a zeta_word state i)) =>
  in_qrange (state 6) /\
  coeff (state 6) %% q = (inverse_numerator0 a z * exp Rinv 2) %% q /\
  in_qrange (state 7) /\
  coeff (state 7) %% q = ((-inverse_numerator1 a z) * exp Rinv 2) %% q /\
  in_qrange (state 8) /\
  coeff (state 8) %% q = (inverse_numerator2 a z * exp Rinv 2) %% q /\
  in_qrange (state 9) /\
  coeff (state 9) %% q = ((-inverse_numerator3 a z) * exp Rinv 2) %% q.
proof.
  move=> Ha Hzeta_w Hzeta Hstate.
  have [Ha0 [Ha1 [Ha2 Ha3]]] := Ha.
  have [Hs2b Hs2c] :=
    baseinv_trace2 a zeta_word z state Ha Hzeta_w Hzeta Hstate.
  have [Hs3b Hs3c] :=
    baseinv_trace3 a zeta_word z state Ha Hzeta_w Hzeta Hstate.
  have [Hs4b Hs4c] :=
    baseinv_trace4 a zeta_word z state Ha Hzeta_w Hzeta Hstate.
  have Hs2range : -q <= coeff (state 2) < q by rewrite /in_qrange in Hs2b.
  have Hs3range : -q <= coeff (state 3) < q by rewrite /in_qrange in Hs3b.
  have Hs4range : -q <= coeff (state 4) < q by rewrite /in_qrange in Hs4b.

  have H6eq := Hstate 6.
  have -> :
    state 6 = mred_word_spec
      (coeff a.[0] * coeff (state 2) + coeff a.[2] * coeff (state 4))
    by apply H6eq; smt().
  have [Hs6b Hs6c] := mred_word_spec_algebra
    (coeff a.[0] * coeff (state 2) + coeff a.[2] * coeff (state 4))
    (product_sum2_bound
      (coeff a.[0]) (coeff a.[2]) (coeff (state 2)) (coeff (state 4))
      Ha0 Ha2 Hs2range Hs4range).

  have H7eq := Hstate 7.
  have -> :
    state 7 = mred_word_spec
      (coeff a.[3] * coeff (state 4) + coeff a.[1] * coeff (state 2))
    by apply H7eq; smt().
  have [Hs7b Hs7c] := mred_word_spec_algebra
    (coeff a.[3] * coeff (state 4) + coeff a.[1] * coeff (state 2))
    (product_sum2_bound
      (coeff a.[3]) (coeff a.[1]) (coeff (state 4)) (coeff (state 2))
      Ha3 Ha1 Hs4range Hs2range).

  have H8eq := Hstate 8.
  have -> :
    state 8 = mred_word_spec
      (coeff a.[2] * coeff (state 2) + coeff a.[0] * coeff (state 3))
    by apply H8eq; smt().
  have [Hs8b Hs8c] := mred_word_spec_algebra
    (coeff a.[2] * coeff (state 2) + coeff a.[0] * coeff (state 3))
    (product_sum2_bound
      (coeff a.[2]) (coeff a.[0]) (coeff (state 2)) (coeff (state 3))
      Ha2 Ha0 Hs2range Hs3range).

  have H9eq := Hstate 9.
  have -> :
    state 9 = mred_word_spec
      (coeff a.[1] * coeff (state 3) + coeff a.[3] * coeff (state 2))
    by apply H9eq; smt().
  have [Hs9b Hs9c] := mred_word_spec_algebra
    (coeff a.[1] * coeff (state 3) + coeff a.[3] * coeff (state 2))
    (product_sum2_bound
      (coeff a.[1]) (coeff a.[3]) (coeff (state 3)) (coeff (state 2))
      Ha1 Ha3 Hs3range Hs2range).

  have Hn0 :
    (coeff a.[0] * coeff (state 2) +
     coeff a.[2] * coeff (state 4)) %% q =
    (inverse_numerator0 a z * Rinv) %% q.
  + exact (numerator0_pre_congr
      a z (coeff (state 2)) (coeff (state 4)) Hs2c Hs4c).

  have Hn1 :
    (coeff a.[3] * coeff (state 4) +
     coeff a.[1] * coeff (state 2)) %% q =
    ((-inverse_numerator1 a z) * Rinv) %% q.
  + exact (numerator1_pre_congr
      a z (coeff (state 2)) (coeff (state 4)) Hs2c Hs4c).

  have Hn2 :
    (coeff a.[2] * coeff (state 2) +
     coeff a.[0] * coeff (state 3)) %% q =
    (inverse_numerator2 a z * Rinv) %% q.
  + exact (numerator2_pre_congr
      a z (coeff (state 2)) (coeff (state 3)) Hs2c Hs3c).

  have Hn3 :
    (coeff a.[1] * coeff (state 3) +
     coeff a.[3] * coeff (state 2)) %% q =
    ((-inverse_numerator3 a z) * Rinv) %% q.
  + exact (numerator3_pre_congr
      a z (coeff (state 2)) (coeff (state 3)) Hs2c Hs3c).

  have Hc6 :
    coeff (mred_word_spec
      (coeff a.[0] * coeff (state 2) +
       coeff a.[2] * coeff (state 4))) %% q =
    (inverse_numerator0 a z * exp Rinv 2) %% q.
  + rewrite Hs6c -modzMml Hn0 modzMml.
    rewrite (_ : inverse_numerator0 a z * Rinv * Rinv =
      inverse_numerator0 a z * exp Rinv 2).
    + ring.
    done.
  have Hc7 :
    coeff (mred_word_spec
      (coeff a.[3] * coeff (state 4) +
       coeff a.[1] * coeff (state 2))) %% q =
    ((-inverse_numerator1 a z) * exp Rinv 2) %% q.
  + rewrite Hs7c -modzMml Hn1 modzMml.
    rewrite (_ : (-inverse_numerator1 a z) * Rinv * Rinv =
      (-inverse_numerator1 a z) * exp Rinv 2).
    + ring.
    done.
  have Hc8 :
    coeff (mred_word_spec
      (coeff a.[2] * coeff (state 2) +
       coeff a.[0] * coeff (state 3))) %% q =
    (inverse_numerator2 a z * exp Rinv 2) %% q.
  + rewrite Hs8c -modzMml Hn2 modzMml.
    rewrite (_ : inverse_numerator2 a z * Rinv * Rinv =
      inverse_numerator2 a z * exp Rinv 2).
    + ring.
    done.
  have Hc9 :
    coeff (mred_word_spec
      (coeff a.[1] * coeff (state 3) +
       coeff a.[3] * coeff (state 2))) %% q =
    ((-inverse_numerator3 a z) * exp Rinv 2) %% q.
  + rewrite Hs9c -modzMml Hn3 modzMml.
    rewrite (_ : (-inverse_numerator3 a z) * Rinv * Rinv =
      (-inverse_numerator3 a z) * exp Rinv 2).
    + ring.
    done.
  split.
  + exact Hs6b.
  split.
  + exact Hc6.
  split.
  + exact Hs7b.
  split.
  + exact Hc7.
  split.
  + exact Hs8b.
  split.
  + exact Hc8.
  split.
  + exact Hs9b.
  exact Hc9.
qed.

lemma fqinv_word_spec_output_range_generic
    (a output : W16.t) (state : int -> W16.t)
    (p r : int -> int) (pout rout : int) :
  in_qrange a =>
  (forall i, 0 <= i < 16 =>
    fqmul_word_spec
      (fqinv_word_left a state i)
      (fqinv_word_right a state i) = state i) =>
  fqmul_word_spec fq_rinv_word (state 15) = output =>
  fqinv_exponent_relations p r pout rout =>
  in_qrange output.
proof.
  move=> Ha Hsteps Houtput Hexps.
  have Hfacts :
      in_qrange output /\ power_relation a output pout rout.
  + exact (fqinv_word_spec_power_relation_generic
      a output state p r pout rout Ha Hsteps Houtput Hexps).
  move: Hfacts => [Hrange _].
  exact Hrange.
qed.

lemma fqinv_word_spec_output_range
    (a output : W16.t) (state : int -> W16.t) :
  in_qrange a =>
  (forall i, 0 <= i < 16 =>
    fqmul_word_spec
      (fqinv_word_left a state i)
      (fqinv_word_right a state i) = state i) =>
  fqmul_word_spec fq_rinv_word (state 15) = output =>
  in_qrange output.
proof.
  move=> Ha Hsteps Houtput.
  exact (fqinv_word_spec_output_range_generic
    a output state fqinv_pe fqinv_re peinv reinv
    Ha Hsteps Houtput fqinv_exponent_schedule).
qed.

lemma baseinv_word_trace_strict_ranges
    (a : W16.t Array4.t) (zeta_word invword : W16.t) (z : int)
    (state fq_state : int -> W16.t) :
  in_qrange4 a =>
  in_qrange zeta_word =>
  zeta_mont_relation zeta_word z =>
  (forall i, 0 <= i < 14 =>
    state i = mred_word_spec
      (baseinv_full_trace_expr a zeta_word invword state i)) =>
  (forall i, 0 <= i < 16 =>
    fqmul_word_spec
      (fqinv_word_left (state 5) fq_state i)
      (fqinv_word_right (state 5) fq_state i) = fq_state i) =>
  fqmul_word_spec fq_rinv_word (fq_state 15) = invword =>
  forall i, 0 <= i < 14 => -q < coeff (state i) < q.
proof.
  move=> Ha Hzeta_w Hzeta Htrace.
  have Hstate :
      forall j, 0 <= j < 10 =>
        state j = mred_word_spec (baseinv_trace_expr a zeta_word state j).
  + move=> j Hj.
    have Hj14 : 0 <= j < 14 by smt().
    have H := Htrace j Hj14.
    rewrite /baseinv_full_trace_expr in H.
    by smt().
  have [Ha0 [Ha1 [Ha2 Ha3]]] := Ha.
  have [Hs0b _] := baseinv_trace0 a zeta_word state Ha Hstate.
  have [Hs1b _] := baseinv_trace1 a zeta_word state Ha Hstate.
  have [Hs2b _] := baseinv_trace2 a zeta_word z state Ha Hzeta_w Hzeta Hstate.
  have [Hs3b _] := baseinv_trace3 a zeta_word z state Ha Hzeta_w Hzeta Hstate.
  have [Hs4b _] := baseinv_trace4 a zeta_word z state Ha Hzeta_w Hzeta Hstate.
  have [Hs5b _] := baseinv_trace5 a zeta_word z state Ha Hzeta_w Hzeta Hstate.
  have [Hs6b [_ [Hs7b [_ [Hs8b [_ [Hs9b _]]]]]]] :=
    baseinv_trace6789 a zeta_word z state Ha Hzeta_w Hzeta Hstate.
  have Hs0range : -q <= coeff (state 0) < q by rewrite /in_qrange in Hs0b.
  have Hs1range : -q <= coeff (state 1) < q by rewrite /in_qrange in Hs1b.
  have Hs2range : -q <= coeff (state 2) < q by rewrite /in_qrange in Hs2b.
  have Hs3range : -q <= coeff (state 3) < q by rewrite /in_qrange in Hs3b.
  have Hs4range : -q <= coeff (state 4) < q by rewrite /in_qrange in Hs4b.
  have Hs6range : -q <= coeff (state 6) < q by rewrite /in_qrange in Hs6b.
  have Hs7range : -q <= coeff (state 7) < q by rewrite /in_qrange in Hs7b.
  have Hs8range : -q <= coeff (state 8) < q by rewrite /in_qrange in Hs8b.
  have Hs9range : -q <= coeff (state 9) < q by rewrite /in_qrange in Hs9b.
  have H0 : -q < coeff (state 0) < q.
  + have H0idx : 0 <= 0 < 10 by smt().
    have H0eq := Hstate 0 H0idx.
    rewrite H0eq.
    exact (mred_word_spec_strict_range
      (coeff a.[2] * coeff a.[2] - 2 * coeff a.[1] * coeff a.[3])
      (square_minus_double_product_bound
        (coeff a.[2]) (coeff a.[1]) (coeff a.[3]) Ha2 Ha1 Ha3)).
  have H1 : -q < coeff (state 1) < q.
  + have H1idx : 0 <= 1 < 10 by smt().
    have H1eq := Hstate 1 H1idx.
    rewrite H1eq.
    exact (mred_word_spec_strict_range
      (coeff a.[3] * coeff a.[3])
      (product_bound (coeff a.[3]) (coeff a.[3]) Ha3 Ha3)).
  have H2 : -q < coeff (state 2) < q.
  + have H2idx : 0 <= 2 < 10 by smt().
    have H2eq := Hstate 2 H2idx.
    rewrite H2eq.
    exact (mred_word_spec_strict_range
      (coeff a.[0] * coeff a.[0] + coeff (state 0) * coeff zeta_word)
      (square_plus_product_bound
        (coeff a.[0]) (coeff (state 0)) (coeff zeta_word)
        Ha0 Hs0range Hzeta_w)).
  have H3 : -q < coeff (state 3) < q.
  + have H3idx : 0 <= 3 < 10 by smt().
    have H3eq := Hstate 3 H3idx.
    rewrite H3eq.
    exact (mred_word_spec_strict_range
      (coeff a.[1] * coeff a.[1] + coeff (state 1) * coeff zeta_word -
       2 * coeff a.[0] * coeff a.[2])
      (square_plus_product_minus_double_product_bound
        (coeff a.[1]) (coeff (state 1)) (coeff zeta_word)
        (coeff a.[0]) (coeff a.[2])
        Ha1 Hs1range Hzeta_w Ha0 Ha2)).
  have H4 : -q < coeff (state 4) < q.
  + have H4idx : 0 <= 4 < 10 by smt().
    have H4eq := Hstate 4 H4idx.
    rewrite H4eq.
    exact (mred_word_spec_strict_range
      (coeff (state 3) * coeff zeta_word)
      (product_bound (coeff (state 3)) (coeff zeta_word) Hs3range Hzeta_w)).
  have H5 : -q < coeff (state 5) < q.
  + have H5idx : 0 <= 5 < 10 by smt().
    have H5eq := Hstate 5 H5idx.
    rewrite H5eq.
    exact (mred_word_spec_strict_range
      (coeff (state 2) * coeff (state 2) - coeff (state 3) * coeff (state 4))
      (square_minus_product_bound
        (coeff (state 2)) (coeff (state 3)) (coeff (state 4))
        Hs2range Hs3range Hs4range)).
  have H6 : -q < coeff (state 6) < q.
  + have H6idx : 0 <= 6 < 14 by smt().
    have H6eq := Htrace 6 H6idx.
    rewrite /baseinv_full_trace_expr in H6eq.
    rewrite H6eq.
    exact (mred_word_spec_strict_range
      (coeff a.[0] * coeff (state 2) + coeff a.[2] * coeff (state 4))
      (product_sum2_bound
        (coeff a.[0]) (coeff a.[2]) (coeff (state 2)) (coeff (state 4))
        Ha0 Ha2 Hs2range Hs4range)).
  have H7 : -q < coeff (state 7) < q.
  + have H7idx : 0 <= 7 < 14 by smt().
    have H7eq := Htrace 7 H7idx.
    rewrite /baseinv_full_trace_expr in H7eq.
    rewrite H7eq.
    exact (mred_word_spec_strict_range
      (coeff a.[3] * coeff (state 4) + coeff a.[1] * coeff (state 2))
      (product_sum2_bound
        (coeff a.[3]) (coeff a.[1]) (coeff (state 4)) (coeff (state 2))
        Ha3 Ha1 Hs4range Hs2range)).
  have H8 : -q < coeff (state 8) < q.
  + have H8idx : 0 <= 8 < 14 by smt().
    have H8eq := Htrace 8 H8idx.
    rewrite /baseinv_full_trace_expr in H8eq.
    rewrite H8eq.
    exact (mred_word_spec_strict_range
      (coeff a.[2] * coeff (state 2) + coeff a.[0] * coeff (state 3))
      (product_sum2_bound
        (coeff a.[2]) (coeff a.[0]) (coeff (state 2)) (coeff (state 3))
        Ha2 Ha0 Hs2range Hs3range)).
  have H9 : -q < coeff (state 9) < q.
  + have H9idx : 0 <= 9 < 14 by smt().
    have H9eq := Htrace 9 H9idx.
    rewrite /baseinv_full_trace_expr in H9eq.
    rewrite H9eq.
    exact (mred_word_spec_strict_range
      (coeff a.[1] * coeff (state 3) + coeff a.[3] * coeff (state 2))
      (product_sum2_bound
        (coeff a.[1]) (coeff a.[3]) (coeff (state 3)) (coeff (state 2))
        Ha1 Ha3 Hs3range Hs2range)).
  move=> Hfq Hfqout i Hi.
  have Hinvb := fqinv_word_spec_output_range
    (state 5) invword fq_state Hs5b Hfq Hfqout.
  have Hinvrange : -q <= coeff invword < q by rewrite /in_qrange in Hinvb.
  have H10 : -q < coeff (state 10) < q.
  + have H10idx : 0 <= 10 < 14 by smt().
    have H10eq := Htrace 10 H10idx.
    rewrite /baseinv_full_trace_expr in H10eq.
    rewrite /baseinv_final_mul_expr H10eq.
    exact (mred_word_spec_strict_range
      (coeff (state 6) * coeff invword)
      (product_bound (coeff (state 6)) (coeff invword) Hs6range Hinvrange)).
  have H11 : -q < coeff (state 11) < q.
  + have H11idx : 0 <= 11 < 14 by smt().
    have H11eq := Htrace 11 H11idx.
    rewrite /baseinv_full_trace_expr in H11eq.
    rewrite /baseinv_final_mul_expr H11eq.
    exact (mred_word_spec_strict_range
      (coeff (state 7) * coeff invword)
      (product_bound (coeff (state 7)) (coeff invword) Hs7range Hinvrange)).
  have H12 : -q < coeff (state 12) < q.
  + have H12idx : 0 <= 12 < 14 by smt().
    have H12eq := Htrace 12 H12idx.
    rewrite /baseinv_full_trace_expr in H12eq.
    rewrite /baseinv_final_mul_expr H12eq.
    exact (mred_word_spec_strict_range
      (coeff (state 8) * coeff invword)
      (product_bound (coeff (state 8)) (coeff invword) Hs8range Hinvrange)).
  have H13 : -q < coeff (state 13) < q.
  + have H13idx : 0 <= 13 < 14 by smt().
    have H13eq := Htrace 13 H13idx.
    rewrite /baseinv_full_trace_expr in H13eq.
    rewrite /baseinv_final_mul_expr H13eq.
    exact (mred_word_spec_strict_range
      (coeff (state 9) * coeff invword)
      (product_bound (coeff (state 9)) (coeff invword) Hs9range Hinvrange)).
  case (i = 0) => [->|Hi0]; first exact H0.
  case (i = 1) => [->|Hi1]; first exact H1.
  case (i = 2) => [->|Hi2]; first exact H2.
  case (i = 3) => [->|Hi3]; first exact H3.
  case (i = 4) => [->|Hi4]; first exact H4.
  case (i = 5) => [->|Hi5]; first exact H5.
  case (i = 6) => [->|Hi6]; first exact H6.
  case (i = 7) => [->|Hi7]; first exact H7.
  case (i = 8) => [->|Hi8]; first exact H8.
  case (i = 9) => [->|Hi9]; first exact H9.
  case (i = 10) => [->|Hi10]; first exact H10.
  case (i = 11) => [->|Hi11]; first exact H11.
  case (i = 12) => [->|Hi12]; first exact H12.
  have -> : i = 13 by smt().
  exact H13.
qed.

lemma baseinv_signed_output_qrange
    (a : W16.t Array4.t) (zeta_word invword : W16.t) (z : int)
    (state fq_state : int -> W16.t) :
  in_qrange4 a =>
  in_qrange zeta_word =>
  zeta_mont_relation zeta_word z =>
  (forall i, 0 <= i < 14 =>
    state i = mred_word_spec
      (baseinv_full_trace_expr a zeta_word invword state i)) =>
  (forall i, 0 <= i < 16 =>
    fqmul_word_spec
      (fqinv_word_left (state 5) fq_state i)
      (fqinv_word_right (state 5) fq_state i) = fq_state i) =>
  fqmul_word_spec fq_rinv_word (fq_state 15) = invword =>
  in_qrange4 (baseinv_signed_output state).
proof.
  move=> Ha Hzeta_w Hzeta Htrace Hfq Hfqout.
  have H10f := baseinv_word_trace_strict_ranges
    a zeta_word invword z state fq_state Ha Hzeta_w Hzeta Htrace Hfq Hfqout 10.
  have H11f := baseinv_word_trace_strict_ranges
    a zeta_word invword z state fq_state Ha Hzeta_w Hzeta Htrace Hfq Hfqout 11.
  have H12f := baseinv_word_trace_strict_ranges
    a zeta_word invword z state fq_state Ha Hzeta_w Hzeta Htrace Hfq Hfqout 12.
  have H13f := baseinv_word_trace_strict_ranges
    a zeta_word invword z state fq_state Ha Hzeta_w Hzeta Htrace Hfq Hfqout 13.
  have H10 : -q < coeff (state 10) < q by apply H10f; smt().
  have H11 : -q < coeff (state 11) < q by apply H11f; smt().
  have H12 : -q < coeff (state 12) < q by apply H12f; smt().
  have H13 : -q < coeff (state 13) < q by apply H13f; smt().
  rewrite /in_qrange4 /baseinv_signed_output !Array4.initiE 1..4:/# /=.
  split.
  + move: H10; smt().
  split.
  + exact (signed_word_in_qrange_strict (state 11) H11).
  split.
  + move: H12; smt().
  exact (signed_word_in_qrange_strict (state 13) H13).
qed.

lemma signed_word_mod (w : W16.t) :
  in_qrange w =>
  coeff (signed_word w) %% q = (-coeff w) %% q.
proof. by move=> Hw; rewrite signed_word_coeff. qed.

lemma neg_mod_q_congr (x x' : int) :
  x %% q = x' %% q =>
  (-x) %% q = (-x') %% q.
proof. by move=> H; rewrite -modzNm H modzNm. qed.

lemma final_mred_congruence
    (w invword output : W16.t) (n : int) :
  coeff w %% q = (n * exp Rinv 2) %% q =>
  coeff output %% q = ((coeff w * coeff invword) * Rinv) %% q =>
  coeff output %% q =
    (n * (coeff invword * exp Rinv 3)) %% q.
proof.
  move=> Hw Houtput.
  have Hprod := mul_mod_q_congr
    (coeff w) (coeff invword)
    (n * exp Rinv 2) (coeff invword) Hw _.
  + done.
  have Hscaled := mul_mod_q_congr
    (coeff w * coeff invword) Rinv
    ((n * exp Rinv 2) * coeff invword) Rinv Hprod _.
  + done.
  have Hmod :
      (((n * exp Rinv 2) * coeff invword) * Rinv) %% q =
      (n * (coeff invword * exp Rinv 3)) %% q.
  + apply (congr1 (fun x : int => x %% q)).
    ring.
  rewrite Houtput.
  rewrite Hscaled.
  exact Hmod.
qed.

lemma negated_product_mod_q_congr (x n scale : int) :
  x %% q = ((-n) * scale) %% q =>
  (-x) %% q = (n * scale) %% q.
proof.
  move=> H.
  rewrite -modzNm H modzNm.
  apply (congr1 (fun y : int => y %% q)).
  ring.
qed.

lemma final_signed_mred_congruence
    (w invword output : W16.t) (n : int) :
  in_qrange output =>
  coeff w %% q = ((-n) * exp Rinv 2) %% q =>
  coeff output %% q = ((coeff w * coeff invword) * Rinv) %% q =>
  coeff (signed_word output) %% q =
    (n * (coeff invword * exp Rinv 3)) %% q.
proof.
  move=> Hrange Hw Houtput.
  rewrite (signed_word_mod output Hrange).
  apply (negated_product_mod_q_congr
    (coeff output) n (coeff invword * exp Rinv 3)).
  exact (final_mred_congruence
    w invword output (-n) Hw Houtput).
qed.

lemma Rinv_cube_scale_unit :
  (exp Rinv 3 * 3310 * 3310 * 3310) %% q = 1 %% q.
proof. by rewrite /Rinv /q /=. qed.

lemma determinant_scaled_nonzero (d : int) :
  d %% q <> 0 =>
  (d * exp Rinv 3) %% q <> 0.
proof.
  move=> Hd.
  have Hzero : (d * exp Rinv 3) %% q = 0 => d %% q = 0.
  + move=> H0.
    have Hmul := mul_mod_q_congr
      (d * exp Rinv 3) (3310 * 3310 * 3310)
      0 (3310 * 3310 * 3310) H0 _.
    + done.
    rewrite (_ :
      (d * exp Rinv 3) * (3310 * 3310 * 3310) =
      d * (exp Rinv 3 * 3310 * 3310 * 3310)) in Hmul.
    + ring.
    rewrite -modzMmr Rinv_cube_scale_unit /= in Hmul.
    exact Hmul.
  smt().
qed.

lemma encoded_determinant_nonzero (d : int) (w : W16.t) :
  coeff w %% q = (d * exp Rinv 3) %% q =>
  d %% q <> 0 =>
  coeff w %% q <> 0.
proof.
  move=> Henc Hd.
  rewrite Henc.
  exact (determinant_scaled_nonzero d Hd).
qed.

lemma peinv_value : peinv = 3455.
proof. by rewrite /peinv. qed.

lemma reinv_value : reinv = 3456.
proof. by rewrite /reinv. qed.

lemma fqinv_word_spec_power_relation_only_generic
    (a output : W16.t) (state : int -> W16.t)
    (p r : int -> int) (pout rout : int) :
  in_qrange a =>
  (forall i, 0 <= i < 16 =>
    fqmul_word_spec
      (fqinv_word_left a state i)
      (fqinv_word_right a state i) = state i) =>
  fqmul_word_spec fq_rinv_word (state 15) = output =>
  fqinv_exponent_relations p r pout rout =>
  power_relation a output pout rout.
proof.
  move=> Ha Hsteps Houtput Hexps.
  have Hfacts :
      in_qrange output /\ power_relation a output pout rout.
  + exact (fqinv_word_spec_power_relation_generic
      a output state p r pout rout Ha Hsteps Houtput Hexps).
  move: Hfacts => [_ Hpower].
  exact Hpower.
qed.

lemma fqinv_word_spec_power_relation_only
    (a output : W16.t) (state : int -> W16.t) :
  in_qrange a =>
  (forall i, 0 <= i < 16 =>
    fqmul_word_spec
      (fqinv_word_left a state i)
      (fqinv_word_right a state i) = state i) =>
  fqmul_word_spec fq_rinv_word (state 15) = output =>
  power_relation a output peinv reinv.
proof.
  move=> Ha Hsteps Houtput.
  exact (fqinv_word_spec_power_relation_only_generic
    a output state fqinv_pe fqinv_re peinv reinv
    Ha Hsteps Houtput fqinv_exponent_schedule).
qed.

lemma fqinv_trace_rminus3_scaling
    (a output : W16.t) (state : int -> W16.t) (d : int) :
  in_qrange a =>
  coeff a %% q = (d * exp Rinv 3) %% q =>
  d %% q <> 0 =>
  (forall i, 0 <= i < 16 =>
    fqmul_word_spec
      (fqinv_word_left a state i)
      (fqinv_word_right a state i) = state i) =>
  fqmul_word_spec fq_rinv_word (state 15) = output =>
  (d * (coeff output * exp Rinv 3)) %% q = 1.
proof.
  move=> Ha Hencoded Hd.
  have Hnonzero : coeff a %% q <> 0.
  + rewrite Hencoded.
    apply determinant_scaled_nonzero.
    exact Hd.
  move=> Hsteps Houtput.
  apply (fqinv_word_spec_rminus3_scaling a output peinv reinv d).
  + exact (fqinv_word_spec_output_range
      a output state Ha Hsteps Houtput).
  + exact (fqinv_word_spec_power_relation_only
      a output state Ha Hsteps Houtput).
  + exact peinv_value.
  + exact reinv_value.
  + exact Hencoded.
  exact Hnonzero.
qed.

lemma fqinv_determinant_witness
    (a : W16.t Array4.t) (z : int) (t5 invword : W16.t) :
  in_qrange invword =>
  power_relation t5 invword peinv reinv =>
  coeff t5 %% q = (inverse_determinant a z * exp Rinv 3) %% q =>
  inverse_determinant a z %% q <> 0 =>
  determinant_inverse_witness a z (coeff invword * exp Rinv 3).
proof.
  move=> Hrange Hpower Hencoded Hdet.
  have Hnonzero : coeff t5 %% q <> 0.
  + rewrite Hencoded.
    apply determinant_scaled_nonzero.
    exact Hdet.
  rewrite /determinant_inverse_witness.
  exact (fqinv_word_spec_rminus3_scaling
    t5 invword peinv reinv (inverse_determinant a z)
    Hrange Hpower peinv_value reinv_value Hencoded Hnonzero).
qed.

lemma baseinv_word_trace_output_congruences
    (a : W16.t Array4.t) (zeta_word invword : W16.t) (z : int)
    (state fq_state : int -> W16.t) :
  in_qrange4 a =>
  in_qrange zeta_word =>
  zeta_mont_relation zeta_word z =>
  (forall i, 0 <= i < 14 =>
    state i = mred_word_spec
      (baseinv_full_trace_expr a zeta_word invword state i)) =>
  inverse_determinant a z %% q <> 0 =>
  (forall i, 0 <= i < 16 =>
    fqmul_word_spec
      (fqinv_word_left (state 5) fq_state i)
      (fqinv_word_right (state 5) fq_state i) = fq_state i) =>
  fqmul_word_spec fq_rinv_word (fq_state 15) = invword =>
  coeff (state 10) %% q =
    (inverse_numerator0 a z * (coeff invword * exp Rinv 3)) %% q /\
  coeff (signed_word (state 11)) %% q =
    (inverse_numerator1 a z * (coeff invword * exp Rinv 3)) %% q /\
  coeff (state 12) %% q =
    (inverse_numerator2 a z * (coeff invword * exp Rinv 3)) %% q /\
  coeff (signed_word (state 13)) %% q =
    (inverse_numerator3 a z * (coeff invword * exp Rinv 3)) %% q /\
  determinant_inverse_witness a z (coeff invword * exp Rinv 3).
proof.
  move=> Ha Hzeta_w Hzeta Htrace Hdet.
  have Hstate :
      forall i, 0 <= i < 10 =>
        state i = mred_word_spec (baseinv_trace_expr a zeta_word state i).
  + move=> i Hi.
    have Hi14 : 0 <= i < 14 by smt().
    have H := Htrace i Hi14.
    rewrite /baseinv_full_trace_expr in H.
    by smt().
  have [Hs5b Hs5c] :=
    baseinv_trace5 a zeta_word z state Ha Hzeta_w Hzeta Hstate.
  have [Hs6b [Hs6c [Hs7b [Hs7c [Hs8b [Hs8c [Hs9b Hs9c]]]]]]] :=
    baseinv_trace6789 a zeta_word z state Ha Hzeta_w Hzeta Hstate.
  have Hs6range : -q <= coeff (state 6) < q by rewrite /in_qrange in Hs6b.
  have Hs7range : -q <= coeff (state 7) < q by rewrite /in_qrange in Hs7b.
  have Hs8range : -q <= coeff (state 8) < q by rewrite /in_qrange in Hs8b.
  have Hs9range : -q <= coeff (state 9) < q by rewrite /in_qrange in Hs9b.
  move=> Hfq Hfqout.
  have Hwit :
      determinant_inverse_witness a z (coeff invword * exp Rinv 3).
  + rewrite /determinant_inverse_witness.
    exact (fqinv_trace_rminus3_scaling
      (state 5) invword fq_state (inverse_determinant a z)
      Hs5b Hs5c Hdet Hfq Hfqout).
  have Hinvb := fqinv_word_spec_output_range
    (state 5) invword fq_state Hs5b Hfq Hfqout.
  clear Hfq Hfqout Hs5b Hs5c.
  have Hinvrange : -q <= coeff invword < q by rewrite /in_qrange in Hinvb.

  have H10eq : state 10 = mred_word_spec (baseinv_final_mul_expr state invword 0).
  + have H10idx : 0 <= 10 < 14 by smt().
    have H := Htrace 10 H10idx.
    rewrite /baseinv_full_trace_expr in H.
    exact H.
  have H11eq : state 11 = mred_word_spec (baseinv_final_mul_expr state invword 1).
  + have H11idx : 0 <= 11 < 14 by smt().
    have H := Htrace 11 H11idx.
    rewrite /baseinv_full_trace_expr in H.
    exact H.
  have H12eq : state 12 = mred_word_spec (baseinv_final_mul_expr state invword 2).
  + have H12idx : 0 <= 12 < 14 by smt().
    have H := Htrace 12 H12idx.
    rewrite /baseinv_full_trace_expr in H.
    exact H.
  have H13eq : state 13 = mred_word_spec (baseinv_final_mul_expr state invword 3).
  + have H13idx : 0 <= 13 < 14 by smt().
    have H := Htrace 13 H13idx.
    rewrite /baseinv_full_trace_expr in H.
    exact H.

  rewrite /baseinv_final_mul_expr in H10eq.
  rewrite /baseinv_final_mul_expr in H11eq.
  rewrite /baseinv_final_mul_expr in H12eq.
  rewrite /baseinv_final_mul_expr in H13eq.
  have [H10b H10c] := mred_word_spec_algebra
    (coeff (state 6) * coeff invword)
    (product_bound (coeff (state 6)) (coeff invword) Hs6range Hinvrange).
  have [H11b H11c] := mred_word_spec_algebra
    (coeff (state 7) * coeff invword)
    (product_bound (coeff (state 7)) (coeff invword) Hs7range Hinvrange).
  have [H12b H12c] := mred_word_spec_algebra
    (coeff (state 8) * coeff invword)
    (product_bound (coeff (state 8)) (coeff invword) Hs8range Hinvrange).
  have [H13b H13c] := mred_word_spec_algebra
    (coeff (state 9) * coeff invword)
    (product_bound (coeff (state 9)) (coeff invword) Hs9range Hinvrange).
  rewrite -H10eq in H10b.
  rewrite -H10eq in H10c.
  rewrite -H11eq in H11b.
  rewrite -H11eq in H11c.
  rewrite -H12eq in H12b.
  rewrite -H12eq in H12c.
  rewrite -H13eq in H13b.
  rewrite -H13eq in H13c.

  split.
  + exact (final_mred_congruence
      (state 6) invword (state 10) (inverse_numerator0 a z)
      Hs6c H10c).
  split.
  + exact (final_signed_mred_congruence
      (state 7) invword (state 11) (inverse_numerator1 a z)
      H11b Hs7c H11c).
  split.
  + exact (final_mred_congruence
      (state 8) invword (state 12) (inverse_numerator2 a z)
      Hs8c H12c).
  split.
  + exact (final_signed_mred_congruence
      (state 9) invword (state 13) (inverse_numerator3 a z)
      H13b Hs9c H13c).
  exact Hwit.
qed.

lemma baseinv_word_trace_inverse_relation
    (a : W16.t Array4.t) (zeta_word invword : W16.t) (z : int)
    (state fq_state : int -> W16.t) :
  in_qrange4 a =>
  in_qrange zeta_word =>
  zeta_mont_relation zeta_word z =>
  (forall i, 0 <= i < 14 =>
    state i = mred_word_spec
      (baseinv_full_trace_expr a zeta_word invword state i)) =>
  (forall i, 0 <= i < 16 =>
    fqmul_word_spec
      (fqinv_word_left (state 5) fq_state i)
      (fqinv_word_right (state 5) fq_state i) = fq_state i) =>
  fqmul_word_spec fq_rinv_word (fq_state 15) = invword =>
  inverse_determinant a z %% q <> 0 =>
  inverse_coeff_relation
    a (baseinv_signed_output state) z
    (coeff invword * exp Rinv 3).
proof.
  move=> Ha Hzeta_w Hzeta Htrace Hfq Hfqout Hdet.
  have Hsigned := baseinv_signed_output_qrange
    a zeta_word invword z state fq_state
    Ha Hzeta_w Hzeta Htrace Hfq Hfqout.
  have [H0 [H1 [H2 [H3 _]]]] :=
    baseinv_word_trace_output_congruences
      a zeta_word invword z state fq_state
      Ha Hzeta_w Hzeta Htrace Hdet Hfq Hfqout.
  rewrite /inverse_coeff_relation.
  split; first exact Hsigned.
  split; first exact H0.
  split; first exact H1.
  split; first exact H2.
  exact H3.
qed.

lemma baseinv_word_trace_block_inverse
    (a : W16.t Array4.t) (zeta_word invword : W16.t) (z : int)
    (state fq_state : int -> W16.t) :
  in_qrange4 a =>
  in_qrange zeta_word =>
  zeta_mont_relation zeta_word z =>
  (forall i, 0 <= i < 14 =>
    state i = mred_word_spec
      (baseinv_full_trace_expr a zeta_word invword state i)) =>
  (forall i, 0 <= i < 16 =>
    fqmul_word_spec
      (fqinv_word_left (state 5) fq_state i)
      (fqinv_word_right (state 5) fq_state i) = fq_state i) =>
  fqmul_word_spec fq_rinv_word (fq_state 15) = invword =>
  inverse_determinant a z %% q <> 0 =>
  block_inverse_qring a (baseinv_signed_output state) z.
proof.
  move=> Ha Hzeta_w Hzeta Htrace Hfq Hfqout Hdet.
  have [_ [_ [_ [_ Hwit]]]] :=
    baseinv_word_trace_output_congruences
      a zeta_word invword z state fq_state
      Ha Hzeta_w Hzeta Htrace Hdet Hfq Hfqout.
  exact (inverse_coeff_relation_implies_block_inverse
    a (baseinv_signed_output state) z (coeff invword * exp Rinv 3)
    Hwit
    (baseinv_word_trace_inverse_relation
      a zeta_word invword z state fq_state
      Ha Hzeta_w Hzeta Htrace Hfq Hfqout Hdet)).
qed.
