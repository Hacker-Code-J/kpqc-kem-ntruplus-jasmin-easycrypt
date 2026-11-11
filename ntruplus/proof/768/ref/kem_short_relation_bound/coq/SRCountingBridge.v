Set Warnings "-notation-overridden,-notation-incompatible-prefix,-ambiguous-paths".
From Coq Require Import ZArith List Lia.
From mathcomp Require Import all_ssreflect all_algebra word_ssrZ.
Require Export SRCountingBase.
Require Import SRFiberKernel SRHadamard SRFiberEncoding.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Definition sr_Zmatrix (m : Z -> Z -> Z) : 'M[Z]_768 :=
  \matrix_(i,j) m (Z.of_nat (val i)) (Z.of_nat (val j)).

Definition sr_Zcolumn (a : Z -> Z) : 'cV[Z]_768 :=
  \col_i a (Z.of_nat (val i)).

Definition sr_Zcanonical (xs : list Z) : Prop :=
  List.length xs = 768%nat /\
  List.Forall (fun x => Z.le 0 x /\ Z.lt x 3457) xs.

Definition sr_Zequation (m : Z -> Z -> Z) (b : Z -> Z)
    (xs : list Z) : Prop :=
  forall k, Z.le 0 k /\ Z.lt k 768 ->
  Z.modulo (Z.add (sr_Zsum 768
    (fun j => Z.mul (m k j) (List.nth (Z.to_nat j) xs 0))) (b k)) 3457 = Z.zero.

Definition sr_Zkernel (m : Z -> Z -> Z) : Prop :=
  forall a : Z -> Z,
  (forall k, Z.le 0 k /\ Z.lt k 768 ->
    sr_Zsum 768 (fun j => Z.mul (m k j) (a j)) = Z.zero) ->
  forall j, Z.le 0 j /\ Z.lt j 768 -> a j = Z.zero.

Definition sr_Zrows (m : Z -> Z -> Z) : Prop :=
  forall k, Z.le 0 k /\ Z.lt k 768 ->
  Z.le (sr_Zsum 768 (fun j => Z.mul (m k j) (m k j))) 12288.

Lemma sr_Zindex_range (i : 'I_768) :
  Z.le 0 (Z.of_nat (val i)) /\ Z.lt (Z.of_nat (val i)) 768.
Proof.
have hi := ltn_ord i; move/ltP: hi => hi.
split; first exact: Nat2Z.is_nonneg.
exact: (proj1 (Nat2Z.inj_lt (val i) 768) hi).
Qed.

Lemma sr_Zindex_inord j : Z.le 0 j /\ Z.lt j 768 ->
  Z.of_nat (val (inord (Z.to_nat j) : 'I_768)) = j.
Proof.
move=> [hj hk].
have hp : Z.le 0 768 by lia.
have hn0 := proj1 (Z2Nat.inj_lt j 768 hj hp) hk.
have hn : (Z.to_nat j < 768)%N by apply/ltP; exact hn0.
change (Z.of_nat (nat_of_ord (inord (Z.to_nat j) : 'I_768)) = j).
rewrite inordK //; exact: Z2Nat.id.
Qed.

Lemma sr_Zsum768_ext f g :
  (forall j, Z.le 0 j /\ Z.lt j 768 -> f j = g j) ->
  sr_Zsum 768 f = sr_Zsum 768 g.
Proof.
move=> he; rewrite !sr_Zsum_big.
apply: eq_bigr => j _; exact: he (sr_Zindex_range j).
Qed.

Lemma sr_Zmatrix_nonsingular m :
  sr_Zkernel m -> \det (sr_Zmatrix m) != 0.
Proof.
move=> hk; apply: sr_Z_kernel_det_nonzero => x hx.
pose a j := x (inord (Z.to_nat j)) ord0.
have hat (i : 'I_768) : a (Z.of_nat (val i)) = x i ord0.
  by rewrite /a Nat2Z.id inord_val.
have hsum : forall k, Z.le 0 k /\ Z.lt k 768 ->
  sr_Zsum 768 (fun j => Z.mul (m k j) (a j)) = Z.zero.
  move=> k hkr.
  pose i : 'I_768 := inord (Z.to_nat k).
  have hi : Z.of_nat (val i) = k by exact: sr_Zindex_inord.
  have he := congr1 (fun y : 'cV[Z]_768 => y i ord0) hx.
  move: he; rewrite /sr_Zmatrix !mxE.
  under eq_bigr do rewrite mxE hi.
  move=> he.
  rewrite sr_Zsum_big.
  apply: eq_trans he.
  by apply: eq_bigr => j _; rewrite hat.
have ha := hk a hsum.
apply/colP => i; rewrite mxE.
have he := ha (Z.of_nat (val i)) (sr_Zindex_range i).
by move: he; rewrite hat.
Qed.

Lemma sr_Zmatrix_row_bound m : sr_Zrows m ->
  forall i, Z.le (\sum_j sr_Zmatrix m i j * sr_Zmatrix m i j) 12288.
Proof.
move=> hr i.
have h := hr (Z.of_nat (val i)) (sr_Zindex_range i).
rewrite sr_Zsum_big in h.
under eq_bigr do rewrite /sr_Zmatrix mxE.
exact h.
Qed.

Lemma sr_Zmatrix_det_bound m : sr_Zrows m ->
  Z.le (Z.abs (\det (sr_Zmatrix m))) (Z.pow 12288 384).
Proof.
move=> hr; apply: sr_hadamard_Z768.
exact: sr_Zmatrix_row_bound.
Qed.

Lemma sr_Zmatrix_equation m b xs : sr_Zequation m b xs ->
  forall i : 'I_768,
  Z.modulo (Z.add (\sum_j sr_Zmatrix m i j * List.nth (val j) xs Z.zero)
    (sr_Zcolumn b i ord0)) 3457 = Z.zero.
Proof.
move=> he i.
have h := he (Z.of_nat (val i)) (sr_Zindex_range i).
have hs : sr_Zsum 768 (fun j => Z.mul (m (Z.of_nat (val i)) j)
  (List.nth (Z.to_nat j) xs Z.zero)) =
  \sum_j sr_Zmatrix m i j * List.nth (val j) xs Z.zero.
  rewrite sr_Zsum_big; apply: eq_bigr => j _.
  by rewrite /sr_Zmatrix mxE Nat2Z.id.
rewrite hs in h; rewrite /sr_Zcolumn mxE.
exact h.
Qed.

Lemma sr_Z_solution_count_bound m b xss :
  sr_Zkernel m -> sr_Zrows m -> List.NoDup xss ->
  (forall xs, List.In xs xss -> sr_Zcanonical xs /\ sr_Zequation m b xs) ->
  Z.le (Z.of_nat (List.length xss)) (Z.pow 12288 384).
Proof.
move=> hk hr hu hall.
have hn := sr_Zmatrix_nonsingular hk.
have he : forall xs, List.In xs xss -> sr_encode_canonical 768 xs /\
  forall i : 'I_768,
  Z.modulo ((\sum_j sr_Zmatrix m i j * List.nth (val j) xs (0 : Z)) +
    sr_Zcolumn b i 0) 3457 = (0 : Z).
  move=> xs hx; have [hc he] := hall xs hx.
  split; first exact hc.
  exact: sr_Zmatrix_equation he.
have hc := @sr_encoded_list_fiber_bound_Z 768 (sr_Zmatrix m) (sr_Zcolumn b)
  xss hn hu he.
exact: (Z.le_trans _ _ _ hc (sr_Zmatrix_det_bound hr)).
Qed.

Print Assumptions sr_Z_solution_count_bound.

