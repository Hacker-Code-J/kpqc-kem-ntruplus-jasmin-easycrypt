From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(* Concrete polynomials for the Schoenemann argument at 2.  The
   degree-six residue polynomial is proved irreducible using its roots,
   explicit Bezout identities, and the degrees of possible factors. *)
Definition sri_g (R : ringType) : {poly R} := 'X^6 + 'X^3 + 1.
Definition sri_phi (R : ringType) : {poly R} := 'X^768 - 'X^384 + 1.

Lemma sri_g_size (R : ringType) : size (sri_g R) = 7%N.
Proof.
rewrite /sri_g size_addl ?size_poly1; last by rewrite size_addl !size_polyXn.
by rewrite size_addl !size_polyXn.
Qed.

Lemma sri_g_monic (R : ringType) : sri_g R \is monic.
Proof.
apply/monicP; rewrite /sri_g lead_coefDl ?size_poly1;
  last by rewrite size_addl !size_polyXn.
by rewrite lead_coefDl ?lead_coefXn // !size_polyXn.
Qed.

Lemma sri_phi_size (R : ringType) : size (sri_phi R) = 769%N.
Proof.
rewrite /sri_phi size_addl ?size_poly1;
  last by rewrite size_addl ?size_opp !size_polyXn.
by rewrite size_addl ?size_opp !size_polyXn.
Qed.

Lemma sri_phi_monic (R : ringType) : sri_phi R \is monic.
Proof.
apply/monicP; rewrite /sri_phi lead_coefDl ?size_poly1;
  last by rewrite size_addl ?size_opp !size_polyXn.
by rewrite lead_coefDl ?lead_coefXn // size_opp !size_polyXn.
Qed.
