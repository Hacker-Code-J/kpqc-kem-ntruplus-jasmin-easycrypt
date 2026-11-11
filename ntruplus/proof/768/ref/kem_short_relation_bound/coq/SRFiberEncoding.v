Set Warnings "-notation-overridden,-notation-incompatible-prefix,-ambiguous-paths".
From Coq Require Import ZArith List Lia.
From mathcomp Require Import all_ssreflect all_algebra word_ssrZ.
Require Import SRFiber.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Definition sr_encode_Z (z : Z) : 'F_3457 := (Z_to_int z)%:~R.
Definition sr_encode_list n (xs : list Z) : 'cV['F_3457]_n :=
 \col_i sr_encode_Z (List.nth (val i) xs (0 : Z)).
Definition sr_encode_canonical n (xs : list Z) : Prop :=
 List.length xs = n /\ List.Forall (fun z => Z.le 0 z /\ Z.lt z 3457) xs.

Lemma sr_encode_prime : sr_encode_Z 3457 = 0.
Proof. change (3457%:R = 0 :> 'F_3457); exact: char_Fp_0 sr_fiber_prime_3457. Qed.

Lemma sr_encode_mod_zero z : Z.modulo z 3457 = (0 : Z) -> sr_encode_Z z = 0.
Proof.
move=> hz; have hn : (3457 : Z) <> (0 : Z) by discriminate.
have [k hk] := (proj1 (Z.mod_divide z 3457 hn) hz).
rewrite /sr_encode_Z hk !rmorphM.
change (sr_encode_Z k * sr_encode_Z 3457 = 0).
by rewrite sr_encode_prime mulr0.
Qed.

Lemma sr_encode_Z_value z :
 Z.le 0 z -> Z.lt z 3457 -> Z.of_nat (val (sr_encode_Z z)) = z.
Proof.
move=> h0 hp.
have hz : z = Z.of_nat (Z.to_nat z) by symmetry; exact: Z2Nat.id.
have hn : (Z.to_nat z < 3457)%nat by apply/ltP; lia.
rewrite /sr_encode_Z {1}hz Z_to_int_of_natE /= (val_Fp_nat sr_fiber_prime_3457) (modn_small hn).
by rewrite -hz.
Qed.

Lemma sr_encode_Z_inj x y :
 Z.le 0 x -> Z.lt x 3457 -> Z.le 0 y -> Z.lt y 3457 ->
 sr_encode_Z x = sr_encode_Z y -> x = y.
Proof.
move=> hx0 hxp hy0 hyp he.
have := congr1 (fun z : 'F_3457 => Z.of_nat (val z)) he.
by rewrite (sr_encode_Z_value hx0 hxp) (sr_encode_Z_value hy0 hyp).
Qed.

Lemma sr_encode_nth_range n xs i :
 sr_encode_canonical n xs -> Nat.lt i n ->
 Z.le 0 (List.nth i xs (0 : Z)) /\ Z.lt (List.nth i xs (0 : Z)) 3457.
Proof.
move=> [hlen hall] hi.
apply: (proj1 (List.Forall_forall _ _) hall).
apply: List.nth_In; by rewrite hlen.
Qed.

Lemma sr_encode_list_inj n xs ys :
 sr_encode_canonical n xs -> sr_encode_canonical n ys ->
 sr_encode_list n xs = sr_encode_list n ys -> xs = ys.
Proof.
move=> hx hy he.
apply: (@List.nth_ext Z xs ys (0 : Z) (0 : Z)).
- by case: hx => h1 _; case: hy => h2 _; rewrite h1 h2.
- move=> i hi.
  have hn : Nat.lt i n by case: hx => hlen _; by rewrite -hlen.
  have hiN : (i < n)%nat by apply/ltP.
  have [hx0 hxp] := sr_encode_nth_range hx hn.
  have [hy0 hyp] := sr_encode_nth_range hy hn.
  apply: (sr_encode_Z_inj hx0 hxp hy0 hyp).
  have := congr1 (fun v : 'cV['F_3457]_n => v (Ordinal hiN) 0) he.
  by rewrite /sr_encode_list !mxE.
Qed.

Lemma sr_encode_product_row n (A : 'M[Z]_n) xs (i : 'I_n) :
 (map_mx sr_encode_Z A *m sr_encode_list n xs) i 0 =
 sr_encode_Z (\sum_(j < n) A i j * List.nth (val j) xs (0 : Z)).
Proof.
rewrite mxE /sr_encode_Z !rmorph_sum.
apply: eq_bigr => j _; by rewrite /sr_encode_list !mxE /sr_encode_Z !rmorphM.
Qed.

Lemma sr_encode_equation n (A : 'M[Z]_n) (b : 'cV[Z]_n) xs :
 (forall i : 'I_n, Z.modulo ((\sum_(j < n) A i j * List.nth (val j) xs (0 : Z)) + b i 0) 3457 = (0 : Z)) ->
 map_mx sr_encode_Z A *m sr_encode_list n xs = - map_mx sr_encode_Z b.
Proof.
move=> he; apply/matrixP => i j; rewrite (ord1 j) sr_encode_product_row !mxE.
have hz := sr_encode_mod_zero (he i).
move: hz; rewrite /sr_encode_Z !rmorphD => hz.
apply/eqP; rewrite -addr_eq0; by apply/eqP.
Qed.

Lemma sr_encode_mem_In (T : eqType) (x : T) xs :
 (x \in xs) <-> List.In x xs.
Proof.
elim: xs => [|y ys ih] /=; first by split.
rewrite in_cons; split.
- move/orP => [/eqP he|hm].
  + left; by symmetry.
  + right; exact: (proj1 ih hm).
- move=> [he|hi].
  + apply/orP; left; apply/eqP; by symmetry.
  + apply/orP; right; exact: (proj2 ih hi).
Qed.

Lemma sr_encode_NoDup_uniq (T : eqType) (xs : list T) : List.NoDup xs -> uniq xs.
Proof.
elim: xs => [|x xs ih] //=.
move/List.NoDup_cons_iff => [hn ht]; apply/andP; split.
- apply/negP => hm; apply: hn; exact: (proj1 (sr_encode_mem_In x xs) hm).
- exact: ih ht.
Qed.

Lemma sr_encoded_list_fiber_bound n (A : 'M[Z]_n) (b : 'cV[Z]_n) (xss : list (list Z)) :
 \det A != 0 -> List.NoDup xss ->
 (forall xs, List.In xs xss -> sr_encode_canonical n xs /\
   forall i : 'I_n, Z.modulo ((\sum_(j < n) A i j * List.nth (val j) xs (0 : Z)) + b i 0) 3457 = (0 : Z)) ->
 (List.length xss <= Z.to_nat (Z.abs (\det A)))%nat.
Proof.
move=> hnA hnd hall.
have hinj : {in xss &, injective (@sr_encode_list n)}.
  move=> xs ys hx hy he.
  have [hcx _] := hall xs (proj1 (sr_encode_mem_In xs xss) hx).
  have [hcy _] := hall ys (proj1 (sr_encode_mem_In ys xss) hy).
  exact: sr_encode_list_inj hcx hcy he.
have hu : uniq (map (@sr_encode_list n) xss).
  rewrite (map_inj_in_uniq hinj); exact: sr_encode_NoDup_uniq hnd.
have hc : (List.length xss <=
 #|[pred x : 'cV['F_3457]_n | (map_mx sr_encode_Z A *m x == - map_mx sr_encode_Z b)%R]|)%nat.
  apply/card_geqP; exists (map (@sr_encode_list n) xss); split.
  - exact: hu.
  - by rewrite size_map.
  - move=> v /mapP [xs hx ->].
    have [_ he] := hall xs (proj1 (sr_encode_mem_In xs xss) hx).
    apply/eqP; exact: sr_encode_equation he.
apply: (leq_trans hc).
exact: (@sr_Z_3457_matrix_fiber_bound n A (- map_mx sr_encode_Z b) hnA).
Qed.

Lemma sr_encoded_list_fiber_bound_Z n (A : 'M[Z]_n) (b : 'cV[Z]_n) (xss : list (list Z)) :
 \det A != 0 -> List.NoDup xss ->
 (forall xs, List.In xs xss -> sr_encode_canonical n xs /\
   forall i : 'I_n, Z.modulo ((\sum_(j < n) A i j * List.nth (val j) xs (0 : Z)) + b i 0) 3457 = (0 : Z)) ->
 Z.le (Z.of_nat (List.length xss)) (Z.abs (\det A)).
Proof.
move=> hnA hu he.
have /leP h := sr_encoded_list_fiber_bound hnA hu he.
have hz := proj1 (Nat2Z.inj_le _ _) h.
rewrite Z2Nat.id in hz; last exact: Z.abs_nonneg.
exact: hz.
Qed.
