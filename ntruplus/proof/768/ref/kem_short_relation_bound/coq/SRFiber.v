Set Warnings "-notation-overridden,-notation-incompatible-prefix,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra intdiv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section ColumnCounting.
Variable F : finFieldType.

Definition sr_col_code n (x : 'cV[F]_n) : {ffun 'I_n -> F} :=
 [ffun i => x i 0].

Lemma sr_col_code_inj n : injective (@sr_col_code n).
Proof.
move=> x y h; apply/matrixP => i j.
have := congr1 (fun f : {ffun 'I_n -> F} => f i) h.
by rewrite /sr_col_code !ffunE (ord1 j).
Qed.

Lemma sr_fiber_diagonal_card n (d : 'rV[F]_n) (b : 'cV[F]_n) :
 #|[pred x : 'cV[F]_n | diag_mx d *m x == b]| =
 (\prod_(i < n) #|[pred y : F | (d 0 i * y == b i 0)%R]|)%N.
Proof.
pose fam := family (fun i : 'I_n => [pred y : F | d 0 i * y == b i 0]).
have hc : #|[pred x : 'cV[F]_n | diag_mx d *m x == b]| = #|fam|.
  rewrite -(card_image (@sr_col_code_inj n)).
  apply: eq_card => f; apply/imageP/familyP.
  - move=> [x /eqP hx ->] i; rewrite /sr_col_code ffunE.
    have := congr1 (fun M : 'cV[F]_n => M i 0) hx.
    by rewrite mul_diag_mx mxE inE => ->.
  - move=> hf; exists (\col_i f i).
    + apply/eqP/matrixP => i j.
      rewrite mul_diag_mx !mxE (ord1 j).
      apply/eqP; exact: (hf i).
    + by apply/ffunP => i; rewrite /sr_col_code ffunE mxE.
rewrite hc /fam card_family foldrE big_map /=.
by rewrite big_enum.
Qed.

Lemma sr_fiber_unit_transform n (L D R : 'M[F]_n) (b : 'cV[F]_n) :
 L \in unitmx -> R \in unitmx ->
 (#|[pred x : 'cV[F]_n | (L *m D *m R *m x == b)%R]| <=
  #|[pred y : 'cV[F]_n | (D *m y == invmx L *m b)%R]|)%N.
Proof.
move=> uL uR.
have hi : injective (fun x : 'cV[F]_n => R *m x).
  exact: (can_inj (mulKmx uR)).
rewrite -(card_image hi).
apply: subset_leq_card; apply/subsetP => y /imageP [x /eqP hx ->].
apply/eqP.
have := congr1 (fun z : 'cV[F]_n => invmx L *m z) hx.
by rewrite -!mulmxA mulKmx.
Qed.

End ColumnCounting.

Section PrimeFibers.
Variable p : nat.
Hypothesis p_prime : prime p.

Lemma sr_fiber_cast_zero z : (z%:~R == 0 :> 'F_p) -> (p %| `|z|)%N.
Proof.
rewrite (dvdn_charf (char_Fp p_prime)).
case: z => [n|n] /=; first by [].
by rewrite oppr_eq0.
Qed.

Lemma sr_fiber_scalar_bound (z : int) (b : 'F_p) :
 z != 0 -> (#|[pred x : 'F_p | (z%:~R * x == b)%R]| <= `|z|)%N.
Proof.
move=> nz; have az : (0 < `|z|)%N by rewrite absz_gt0.
have [hz|hz] := boolP (z%:~R == 0 :> 'F_p).
- apply: (leq_trans (max_card _)); rewrite (card_Fp p_prime).
  exact: dvdn_leq az (sr_fiber_cast_zero hz).
apply: (leq_trans _ az); apply/card_le1P => x /eqP hx y.
apply/idP/eqP => [/eqP hy|->]; last by apply/eqP.
apply: (mulfI hz); by rewrite hx hy.
Qed.

Lemma sr_fiber_map_unit n (A : 'M[int]_n) :
 A \in unitmx -> map_mx (intr : int -> 'F_p) A \in unitmx.
Proof.
rewrite !unitmxE det_map_mx; exact: rmorph_unit.
Qed.

Lemma sr_fiber_abs_product (I : finType) (f : I -> int) :
 absz ((\prod_i f i)%R) = (\prod_i absz (f i))%N.
Proof. exact: (big_morph absz (id2:=1%R) abszM (erefl 1%N)). Qed.

Lemma sr_fiber_diagonal_bound n (d : 'rV[int]_n) (b : 'cV['F_p]_n) :
 (forall i, d 0 i != 0) ->
 (#|[pred x : 'cV['F_p]_n | (map_mx (intr : int -> 'F_p) (diag_mx d) *m x == b)%R]| <=
  `|\det (diag_mx d)|)%N.
Proof.
move=> hd; rewrite map_diag_mx sr_fiber_diagonal_card det_diag sr_fiber_abs_product.
apply: leq_prod => i _; rewrite mxE.
exact: sr_fiber_scalar_bound (hd i).
Qed.

Lemma sr_integer_matrix_fiber_bound n (A : 'M[int]_n) (b : 'cV['F_p]_n) :
 \det A != 0 ->
 (#|[pred x : 'cV['F_p]_n | (map_mx (intr : int -> 'F_p) A *m x == b)%R]| <=
  `|\det A|)%N.
Proof.
move=> hnA.
have [L uL [R uR [d _ hA]]] := int_Smith_normal_form A.
pose D := diag_mx (\row_(i < n) d`_i : 'rV[int]_n).
have hdiag : (\matrix_(i < n,j < n) (d`_i *+ (i == j :> nat))) = D.
  by apply/matrixP => i j; rewrite /D !mxE.
rewrite hdiag in hA.
have hdet : \det A = \det L * \det D * \det R by rewrite hA !det_mulmx.
have hnD : \det D != 0.
  apply: contraNneq hnA => hz; by rewrite hdet hz mulr0 mul0r.
have hd : forall i, (\row_(j < n) d`_j : 'rV[int]_n) 0 i != 0.
  move=> i; apply: contraNneq hnD => hz.
  by rewrite /D det_diag (bigD1 i) //= hz mul0r.
have hdiv : (`|\det D| %| `|\det A|)%N.
  rewrite hdet !abszM; apply: dvdn_mulr; apply: dvdn_mull; exact: dvdnn.
have hle : (`|\det D| <= `|\det A|)%N.
  apply: dvdn_leq hdiv; by rewrite absz_gt0.
rewrite {1}hA !map_mxM.
apply: (leq_trans (sr_fiber_unit_transform (map_mx (intr : int -> 'F_p) D) b
  (sr_fiber_map_unit uL) (sr_fiber_map_unit uR))).
apply: (leq_trans _ hle).
exact: sr_fiber_diagonal_bound hd.
Qed.

End PrimeFibers.

From Coq Require Import ZArith.
From mathcomp.word Require Import word_ssrZ.
Local Open Scope ring_scope.

Lemma sr_fiber_abs_Z (z : Z) :
 absz (Z_to_int z) = Z.to_nat (Z.abs z).
Proof. case: z => [|v|v] //=; by rewrite abszN. Qed.

Lemma sr_Z_matrix_fiber_bound p (p_prime : prime p) n
 (A : 'M[Z]_n) (b : 'cV['F_p]_n) :
 \det A != 0 ->
 (#|[pred x : 'cV['F_p]_n |
   (map_mx (fun z : Z => (Z_to_int z)%:~R : 'F_p) A *m x == b)%R]| <=
  Z.to_nat (Z.abs (\det A)) )%nat.
Proof.
move=> hnA.
have hn : \det (map_mx Z_to_int A) != 0.
  rewrite det_map_mx; apply: contraNneq hnA => hz.
  apply/eqP; apply: (can_inj Z_to_intK); by rewrite hz rmorph0.
have hb := @sr_integer_matrix_fiber_bound p p_prime n (map_mx Z_to_int A) b hn.
by move: hb; rewrite det_map_mx sr_fiber_abs_Z map_mx_comp.
Qed.

Lemma sr_fiber_prime_3457 : prime 3457.
Proof. by vm_compute. Qed.

Lemma sr_Z_3457_matrix_fiber_bound n (A : 'M[Z]_n) (b : 'cV['F_3457]_n) :
 \det A != 0 ->
 (#|[pred x : 'cV['F_3457]_n |
   (map_mx (fun z : Z => (Z_to_int z)%:~R : 'F_3457) A *m x == b)%R]| <=
  Z.to_nat (Z.abs (\det A)) )%nat.
Proof. exact: (@sr_Z_matrix_fiber_bound 3457 sr_fiber_prime_3457 n A b). Qed.
