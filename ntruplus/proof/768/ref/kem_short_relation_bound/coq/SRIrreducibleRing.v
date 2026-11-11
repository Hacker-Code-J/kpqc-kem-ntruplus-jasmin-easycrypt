From Coq Require Import Ring.
From mathcomp Require Import all_ssreflect all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Import GRing.Theory.
Local Open Scope ring_scope.

Lemma sri_ring_theory (R : comRingType) :
 ring_theory (0 : R) 1 +%R *%R (fun x y => x-y) -%R eq.
Proof.
constructor.
- exact: add0r.
- exact: addrC.
- exact: addrA.
- exact: mul1r.
- exact: mulrC.
- exact: mulrA.
- exact: mulrDl.
- by [].
- exact: addrN.
Qed.

Lemma sri_bool_poly_morph :
 @ring_morph {poly bool} 0 1 +%R *%R (fun x y => x-y) -%R eq
  bool false true xorb andb xorb id Bool.eqb (fun b : bool => b%:P).
Proof.
constructor.
- by [].
- by [].
- move=> x y; have -> : xorb x y = x+y by case: x; case: y.
  exact: polyCD.
- move=> x y; have -> : xorb x y = x-y by case: x; case: y.
  exact: polyCB.
- exact: polyCM.
- exact: polyCN.
- by case; case.
Qed.

Lemma sri_bool_poly_ring_theory :
 @ring_theory (GRing.Nmodule.sort (poly_polynomial__canonical__GRing_Nmodule bool))
  0 1 +%R *%R (fun x y => x-y) -%R eq.
Proof. exact: sri_ring_theory. Qed.

Add Ring sri_poly_bool_ring : sri_bool_poly_ring_theory
 (morphism sri_bool_poly_morph).

Lemma sri_bool_poly_semiring_theory :
 @ring_theory (GRing.Nmodule.sort (poly_polynomial__canonical__GRing_SemiRing bool))
  0 1 +%R *%R (fun x y => x-y) -%R eq.
Proof. exact: sri_ring_theory. Qed.
Add Ring sri_poly_bool_semiring : sri_bool_poly_semiring_theory
 (morphism sri_bool_poly_morph).

Lemma sri_ring_bool_test (x : {poly bool}) : x+x=0.
Proof. ring. Qed.

Lemma sri_bezout7_alg (x : {poly bool}) :
 (x^+6+x^+3+1)+(x^+4+x^+3)*(x^+2+x+1)= 1.
Proof. rewrite !exprS !expr0; ring. Qed.

Lemma sri_bezout11_alg (x : {poly bool}) :
 x^+2*(x^+6+x^+3+1)+(x^+5+x^+3+x+1)*(x^+3+x+1)= 1.
Proof. rewrite !exprS !expr0; ring. Qed.

Lemma sri_bezout13_alg (x : {poly bool}) :
 (x^+2+x)*(x^+6+x^+3+1)+(x^+5+x+1)*(x^+3+x^+2+1)= 1.
Proof. rewrite !exprS !expr0; ring. Qed.

Lemma sri_horner7_alg (x : {poly bool}) : (x+1)*x+1=x^+2+x+1.
Proof. by rewrite expr2 mulrDl mul1r. Qed.
Lemma sri_horner11_alg (x : {poly bool}) : (x*x+1)*x+1=x^+3+x+1.
Proof. by rewrite (exprSr x 2) expr2 mulrDl mul1r. Qed.
Lemma sri_horner13_alg (x : {poly bool}) : (x+1)*x*x+1=x^+3+x^+2+1.
Proof. by rewrite (exprSr x 2) expr2 !mulrDl !mul1r. Qed.
