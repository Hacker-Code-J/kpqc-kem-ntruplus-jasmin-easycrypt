Set Warnings "-notation-overridden,-notation-incompatible-prefix,-ambiguous-paths".
From Coq Require Import ZArith List Lia.
From mathcomp Require Import all_ssreflect all_algebra word_ssrZ.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Fixpoint sr_Zrange (start : Z) (length : nat) : list Z :=
  match length with
  | O => nil
  | S length' => cons start (sr_Zrange (Z.add start 1) length')
  end.

Definition sr_Zsum (length : nat) (f : Z -> Z) : Z :=
  List.fold_right Z.add 0 (List.map f (sr_Zrange 0 length)).

Lemma sr_Zrange_length start length :
  List.length (sr_Zrange start length) = length.
Proof. elim: length start => [|n ih] start //=; by rewrite ih. Qed.

Lemma sr_Zrange_iota start length :
  sr_Zrange start length =
  List.map (fun i => Z.add start (Z.of_nat i)) (iota 0 length).
Proof.
elim: length start => [|n ih] start //=.
rewrite Z.add_0_r; congr cons.
rewrite ih (iotaDl 1 0 n) map_map.
apply eq_map => i; simpl.
lia.
Qed.

Lemma sr_Zsum_big length f :
  sr_Zsum length f = \sum_(j < length) f (Z.of_nat (val j)).
Proof.
rewrite /sr_Zsum sr_Zrange_iota map_map.
change (foldr +%R 0 (map (fun i => f (Z.add 0 (Z.of_nat i))) (iota 0 length)) =
  \sum_(j < length) f (Z.of_nat (val j))).
rewrite foldrE big_map.
rewrite -(@big_mkord Z 0 Z.add length predT (fun j => f (Z.of_nat j))) /index_iota subn0.
by apply eq_bigr => i _; rewrite Z.add_0_l.
Qed.


Print Assumptions sr_Zsum_big.
