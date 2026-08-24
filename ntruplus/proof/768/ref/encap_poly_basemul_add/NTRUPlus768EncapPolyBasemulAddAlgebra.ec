require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array4 Array768.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768PolyBasemulAlgebra.
require import NTRUPlus768PolyBasemulProof.
require import NTRUPlus768NTTRadix2_4Algebra.
require import NTRUPlus768NTTSchedule.

import Ring.IntID IntOrder.

(* Canonical array-value model of multiply-then-add in the terminal q-ring.
   It does not claim equality with every raw C output word or formal C
   procedure equivalence. *)

op centered_sum_int (product add : int) : int =
  let s = product + add in
  if s < -q then s + q else if q <= s then s - q else s.

op centered_add_word (product add : W16.t) : W16.t =
  W16.of_int (centered_sum_int (coeff product) (coeff add)).

op poly_centered_add_spec
    (product add : W16.t Array768.t) : W16.t Array768.t =
  Array768.init (fun j => centered_add_word product.[j] add.[j]).

op poly_centered_add_qring
    (product add output : W16.t Array768.t) : bool =
  in_qrange768 output /\
  forall j, 0 <= j < 768 =>
    coeff output.[j] %% q = (coeff product.[j] + coeff add.[j]) %% q.

op poly_basemul_add_qring
    (ap bp add output : W16.t Array768.t) (upto : int) : bool =
  forall k, 0 <= k < upto =>
    let ak = block4 ap k in
    let bk = block4 bp k in
    let mk = block4 add k in
    let ok = block4 output k in
      in_qrange4 ok /\
      coeff ok.[0] %% q = (coeff0 ak bk (terminal_value k) + coeff mk.[0]) %% q /\
      coeff ok.[1] %% q = (coeff1 ak bk (terminal_value k) + coeff mk.[1]) %% q /\
      coeff ok.[2] %% q = (coeff2 ak bk (terminal_value k) + coeff mk.[2]) %% q /\
      coeff ok.[3] %% q = (coeff3 ak bk (terminal_value k) + coeff mk.[3]) %% q.

lemma poly_basemul_qring_product_in_qrange768
    (ap bp product : W16.t Array768.t) :
  poly_basemul_qring ap bp product 192 =>
  in_qrange768 product.
proof.
  move=> Hproduct k Hk.
  have Hblock := Hproduct k Hk.
  move: Hblock => [Hrange _].
  exact Hrange.
qed.

lemma centered_sum_int_range (product add : int) :
  -q <= product < q =>
  -1728 <= add <= 1728 =>
  -q <= centered_sum_int product add < q.
proof.
  move=> Hp Ha.
  rewrite /centered_sum_int.
  have Hsum : -2 * q < product + add < 2 * q.
  + rewrite /q in Hp.
    smt().
  case (product + add < -q) => Hlt.
  + have Hmid : -2 * q < product + add <= -q by smt().
    rewrite /q.
    smt().
  case (q <= product + add) => Hge.
  + have Hmid : q <= product + add < 2 * q by smt().
    rewrite /q.
    smt().
  rewrite /q.
  smt().
qed.

lemma centered_sum_int_mod_q (product add : int) :
  -q <= product < q =>
  -1728 <= add <= 1728 =>
  centered_sum_int product add %% q = (product + add) %% q.
proof.
  move=> Hp Ha.
  rewrite /centered_sum_int.
  case (product + add < -q) => Hlt.
  + smt().
  case (q <= product + add) => Hge.
  + smt().
  smt().
qed.

lemma add_mod_q_congr (x y z : int) :
  x %% q = y %% q =>
  (x + z) %% q = (y + z) %% q.
proof. by move=> Hxy; rewrite -modzDml Hxy modzDml. qed.

lemma centered_add_word_coeff
    (product add : W16.t) :
  in_qrange product =>
  -1728 <= coeff add <= 1728 =>
  coeff (centered_add_word product add) =
    centered_sum_int (coeff product) (coeff add).
proof.
  move=> Hp Ha.
  rewrite /centered_add_word.
  rewrite /coeff.
  apply W16.to_sintK_small.
  have Hrange := centered_sum_int_range (coeff product) (coeff add) Hp Ha.
  rewrite /q in Hrange.
  smt().
qed.

lemma centered_add_word_mod_q
    (product add : W16.t) :
  in_qrange product =>
  -1728 <= coeff add <= 1728 =>
  coeff (centered_add_word product add) %% q =
    (coeff product + coeff add) %% q.
proof.
  move=> Hp Ha.
  rewrite centered_add_word_coeff 1:Hp 1:Ha.
  exact (centered_sum_int_mod_q (coeff product) (coeff add) Hp Ha).
qed.

lemma centered_input_shape_add_bound
    (add : W16.t Array768.t) (j : int) :
  NTRUPlus768NTTRadix2_4Algebra.centered_input_shape add =>
  0 <= j < 768 =>
  -1728 <= coeff add.[j] <= 1728.
proof.
  move=> Hadd Hj.
  rewrite /NTRUPlus768NTTRadix2_4Algebra.centered_input_shape in Hadd.
  exact (Hadd j Hj).
qed.

lemma in_qrange768_coeff
    (p : W16.t Array768.t) (j : int) :
  in_qrange768 p =>
  0 <= j < 768 =>
  -q <= coeff p.[j] < q.
proof.
  move=> Hp Hj.
  have Hk : 0 <= j %/ 4 < 192 by smt().
  have Hblock := Hp (j %/ 4) Hk.
  rewrite /in_qrange4 /block4 in Hblock.
  have Hmod : 0 <= j %% 4 < 4 by smt().
  have Hidx : 4 * (j %/ 4) + j %% 4 = j by smt().
  case (j %% 4 = 0) => H0.
  + move: Hblock => [Hq _].
    have -> : p.[j] = p.[4 * (j %/ 4)] by smt().
    exact Hq.
  case (j %% 4 = 1) => H1.
  + move: Hblock => [_ [Hq _]].
    have -> : p.[j] = p.[4 * (j %/ 4) + 1] by smt().
    exact Hq.
  case (j %% 4 = 2) => H2.
  + move: Hblock => [_ [_ [Hq _]]].
    have -> : p.[j] = p.[4 * (j %/ 4) + 2] by smt().
    exact Hq.
  have H3 : j %% 4 = 3 by smt().
  move: Hblock => [_ [_ [_ Hq]]].
  have -> : p.[j] = p.[4 * (j %/ 4) + 3] by smt().
  exact Hq.
qed.

lemma poly_centered_add_spec_coeff
    (product add : W16.t Array768.t) (j : int) :
  in_qrange768 product =>
  NTRUPlus768NTTRadix2_4Algebra.centered_input_shape add =>
  0 <= j < 768 =>
  coeff (poly_centered_add_spec product add).[j] =
    centered_sum_int (coeff product.[j]) (coeff add.[j]).
proof.
  move=> Hproduct Hadd Hj.
  rewrite /poly_centered_add_spec Array768.initiE 1:Hj.
  exact
    (centered_add_word_coeff product.[j] add.[j]
      (in_qrange768_coeff product j Hproduct Hj)
      (centered_input_shape_add_bound add j Hadd Hj)).
qed.

lemma poly_centered_add_spec_coeff_mod_q
    (product add : W16.t Array768.t) (j : int) :
  in_qrange768 product =>
  NTRUPlus768NTTRadix2_4Algebra.centered_input_shape add =>
  0 <= j < 768 =>
  coeff (poly_centered_add_spec product add).[j] %% q =
    (coeff product.[j] + coeff add.[j]) %% q.
proof.
  move=> Hproduct Hadd Hj.
  rewrite /poly_centered_add_spec Array768.initiE 1:Hj.
  exact
    (centered_add_word_mod_q product.[j] add.[j]
      (in_qrange768_coeff product j Hproduct Hj)
      (centered_input_shape_add_bound add j Hadd Hj)).
qed.

lemma poly_centered_add_spec_qring
    (product add : W16.t Array768.t) :
  in_qrange768 product =>
  NTRUPlus768NTTRadix2_4Algebra.centered_input_shape add =>
  poly_centered_add_qring product add (poly_centered_add_spec product add).
proof.
  move=> Hproduct Hadd.
  rewrite /poly_centered_add_qring.
  split.
  + move=> k Hk.
    rewrite /in_qrange4 /block4.
    split.
    - rewrite /in_qrange Array4.initiE 1:/#.
      have Hj : 0 <= 4 * k < 768 by smt().
      rewrite (poly_centered_add_spec_coeff product add (4 * k)
        Hproduct Hadd Hj).
      exact (centered_sum_int_range
        (coeff product.[4 * k]) (coeff add.[4 * k])
        (in_qrange768_coeff product (4 * k) Hproduct Hj)
        (centered_input_shape_add_bound add (4 * k) Hadd Hj)).
    split.
    - rewrite /in_qrange Array4.initiE 1:/#.
      have Hj : 0 <= 4 * k + 1 < 768 by smt().
      rewrite (poly_centered_add_spec_coeff product add (4 * k + 1)
        Hproduct Hadd Hj).
      exact (centered_sum_int_range
        (coeff product.[4 * k + 1]) (coeff add.[4 * k + 1])
        (in_qrange768_coeff product (4 * k + 1) Hproduct Hj)
        (centered_input_shape_add_bound add (4 * k + 1) Hadd Hj)).
    split.
    - rewrite /in_qrange Array4.initiE 1:/#.
      have Hj : 0 <= 4 * k + 2 < 768 by smt().
      rewrite (poly_centered_add_spec_coeff product add (4 * k + 2)
        Hproduct Hadd Hj).
      exact (centered_sum_int_range
        (coeff product.[4 * k + 2]) (coeff add.[4 * k + 2])
        (in_qrange768_coeff product (4 * k + 2) Hproduct Hj)
        (centered_input_shape_add_bound add (4 * k + 2) Hadd Hj)).
    rewrite /in_qrange Array4.initiE 1:/#.
    have Hj : 0 <= 4 * k + 3 < 768 by smt().
    rewrite (poly_centered_add_spec_coeff product add (4 * k + 3)
      Hproduct Hadd Hj).
    exact (centered_sum_int_range
      (coeff product.[4 * k + 3]) (coeff add.[4 * k + 3])
      (in_qrange768_coeff product (4 * k + 3) Hproduct Hj)
      (centered_input_shape_add_bound add (4 * k + 3) Hadd Hj)).
  move=> j Hj.
  exact (poly_centered_add_spec_coeff_mod_q product add j Hproduct Hadd Hj).
qed.

lemma poly_centered_add_qring_output_in_qrange768
    (product add output : W16.t Array768.t) :
  poly_centered_add_qring product add output =>
  in_qrange768 output.
proof.
  move=> [Hout _].
  exact Hout.
qed.

lemma poly_basemul_qring_centered_add_qring
    (ap bp product add output : W16.t Array768.t) :
  poly_basemul_qring ap bp product 192 =>
  poly_centered_add_qring product add output =>
  poly_basemul_add_qring ap bp add output 192.
proof.
  move=> Hprod [Hout Hmod] k Hk.
  have Hkprod := Hprod k Hk.
  have Hmod0 := Hmod (4 * k) _.
  + smt().
  have Hmod1 := Hmod (4 * k + 1) _.
  + smt().
  have Hmod2 := Hmod (4 * k + 2) _.
  + smt().
  have Hmod3 := Hmod (4 * k + 3) _.
  + smt().
  split.
  + exact (in_qrange768_block4 output k Hout Hk).
  split.
  + move: Hkprod => [_ [H0 _]].
    move: Hmod0 H0.
    rewrite /block4 !Array4.initiE 1..3:/#.
    move=> Hmod0 H0.
    apply (eq_trans _
      ((coeff product.[4 * k] + coeff add.[4 * k]) %% q)).
    + exact Hmod0.
    exact (add_mod_q_congr _ _ _ H0).
  split.
  + move: Hkprod => [_ [_ [H1 _]]].
    move: Hmod1 H1.
    rewrite /block4 !Array4.initiE 1..3:/#.
    move=> Hmod1 H1.
    apply (eq_trans _
      ((coeff product.[4 * k + 1] + coeff add.[4 * k + 1]) %% q)).
    + exact Hmod1.
    exact (add_mod_q_congr _ _ _ H1).
  split.
  + move: Hkprod => [_ [_ [_ [H2 _]]]].
    move: Hmod2 H2.
    rewrite /block4 !Array4.initiE 1..3:/#.
    move=> Hmod2 H2.
    apply (eq_trans _
      ((coeff product.[4 * k + 2] + coeff add.[4 * k + 2]) %% q)).
    + exact Hmod2.
    exact (add_mod_q_congr _ _ _ H2).
  move: Hkprod => [_ [_ [_ [_ H3]]]].
  move: Hmod3 H3.
  rewrite /block4 !Array4.initiE 1..3:/#.
  move=> Hmod3 H3.
  apply (eq_trans _
    ((coeff product.[4 * k + 3] + coeff add.[4 * k + 3]) %% q)).
  + exact Hmod3.
  exact (add_mod_q_congr _ _ _ H3).
qed.

lemma poly_basemul_add_spec_qring
    (ap bp product add : W16.t Array768.t) :
  poly_basemul_qring ap bp product 192 =>
  NTRUPlus768NTTRadix2_4Algebra.centered_input_shape add =>
  poly_basemul_add_qring ap bp add (poly_centered_add_spec product add) 192.
proof.
  move=> Hprod Hadd.
  apply (poly_basemul_qring_centered_add_qring ap bp product add).
  + exact Hprod.
  exact (poly_centered_add_spec_qring product add
    (poly_basemul_qring_product_in_qrange768 ap bp product Hprod) Hadd).
qed.
