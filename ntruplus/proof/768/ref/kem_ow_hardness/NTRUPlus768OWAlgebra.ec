require import AllCore Ring.
require import NTRUPlus768CyclotomicFactorization NTRUPlus768EvaluationSemantics.
require import NTRUPlus768TerminalRepresentation NTRUPlus768PKEKeyDistribution.
abbrev ( + ) = NTRUPoly.PolyComRing.( + ).
abbrev ( * ) = NTRUPoly.PolyComRing.( * ).

(* Quotient-ring unit laws. No assumption that the quotient is a field. *)
lemma ow_unit_congr p q : eqm_global p q =>
 (pke_rq_unit p <=> pke_rq_unit q).
proof.
 move=>he; rewrite /pke_rq_unit; split.
 + move=>[r hr]; exists r.
   exact(eqm_global_trans _ _ _
    (eqm_global_mul q p r r (eqm_global_sym p q he) (eqm_global_refl r)) hr).
 move=>[r hr]; exists r.
 exact(eqm_global_trans _ _ _
  (eqm_global_mul p q r r he (eqm_global_refl r)) hr).
qed.

lemma ow_unit_mul p q :
 pke_rq_unit(p*q) <=> pke_rq_unit p /\ pke_rq_unit q.
proof.
 rewrite /pke_rq_unit; split.
 + move=>[r hr]; split.
   + exists(q*r).
     have ee:p*(q*r)=(p*q)*r by ring.
     by rewrite ee.
   exists(p*r).
   have ee:q*(p*r)=(p*q)*r by ring.
   by rewrite ee.
 move=>[[r hr] [s hs]]; exists(r*s).
 have he: eqm_global ((p*r)*(q*s)) (NTRUPoly.poly1*NTRUPoly.poly1).
 + exact(eqm_global_mul _ _ _ _ hr hs).
 have ee:(p*q)*(r*s)=(p*r)*(q*s) by ring.
 have eo:NTRUPoly.poly1*NTRUPoly.poly1=NTRUPoly.poly1.
 + by rewrite /NTRUPoly.PolyComRing.( * ) NTRUPoly.mul1p.
 by rewrite ee; move:he; rewrite eo.
qed.
