require import AllCore Ring.
require import NTRUPlus768CyclotomicFactorization NTRUPlus768EvaluationSemantics.
require import NTRUPlus768TerminalRepresentation NTRUPlus768CoefficientRecovery.
require import NTRUPlus768PKEKeyDistribution NTRUPlus768KeygenGlobalUnit.
abbrev ( + ) = NTRUPoly.PolyComRing.( + ).
abbrev ( * ) = NTRUPoly.PolyComRing.( * ).

(* Figure 18 is specified in the polynomial quotient, independently of its
   NTT implementation. Degree is the polynomial coefficient-list size, so
   deg <= 768 means the unique representative of ordinary degree < 768. *)
op [opaque] gen_shape_f (p:NTRUPoly.poly) =
 NTRUPoly.poly1+NTRUPoly.polyC(lift_int 3)*p.
op [opaque] gen_public_relation (f g h:NTRUPoly.poly) =
 NTRUPoly.deg h<=768 /\ eqm_global(h*f)(NTRUPoly.polyC(lift_int 3)*g).
op [opaque] gen_public_defined (f g:NTRUPoly.poly) =
 exists h,gen_public_relation f g h.
op [opaque] gen_public_key (f g:NTRUPoly.poly) =
 choiceb (gen_public_relation f g) NTRUPoly.poly0.
op [opaque] gen_key_from_fg (fg:NTRUPoly.poly*NTRUPoly.poly) =
 (gen_public_key fg.`1 fg.`2,fg.`1).

lemma gen_shape_fE p :
 NTRUPoly.poly1+NTRUPoly.polyC(lift_int 3)*p=gen_shape_f p.
proof. by rewrite /gen_shape_f. qed.

lemma gen_public_relation_unique f g h1 h2 :
 pke_rq_unit f => gen_public_relation f g h1 => gen_public_relation f g h2 =>h1=h2.
proof.
 move=>hu; rewrite /gen_public_relation.
 move=>[hd1 he1] [hd2 he2].
 have he:eqm_global(h1*f)(h2*f).
 + exact(eqm_global_trans _ _ _ he1 (eqm_global_sym _ _ he2)).
 have he':eqm_global(f*h1)(f*h2).
 + have e1:f*h1=h1*f by ring.
   have e2:f*h2=h2*f by ring.
   by rewrite e1 e2.
 exact(eqm_global_low_degree_unique h1 h2 hd1 hd2 (gen_rq_unit_cancel f h1 h2 hu he')).
qed.

lemma gen_public_defined_witness f g h :
 gen_public_relation f g h =>gen_public_defined f g.
proof. rewrite /gen_public_defined; move=>hh; exists h; exact hh. qed.

lemma gen_public_key_relation f g :
 gen_public_defined f g =>gen_public_relation f g (gen_public_key f g).
proof.
 rewrite /gen_public_defined /gen_public_key.
 exact(choicebP (gen_public_relation f g) NTRUPoly.poly0).
qed.

lemma gen_public_key_unique f g h :
 pke_rq_unit f =>gen_public_relation f g h =>gen_public_key f g=h.
proof.
 move=>hu hh; apply(gen_public_relation_unique f g _ h hu).
 + exact(gen_public_key_relation f g (gen_public_defined_witness f g h hh)).
 exact hh.
qed.

lemma gen_key_from_fgE f g h :
 pke_rq_unit f =>gen_public_relation f g h =>gen_key_from_fg(f,g)=(h,f).
proof.
 move=>hu hh; rewrite /gen_key_from_fg /= (gen_public_key_unique f g h hu hh).
 done.
qed.

(* The default branch is explicit; later support theorems prove it is never
   used on the distribution of valid generated keys. *)
lemma gen_public_key_undefined f g :
 !gen_public_defined f g =>gen_public_key f g=NTRUPoly.poly0.
proof.
 rewrite /gen_public_defined /gen_public_key negb_exists=>hn.
 exact(choiceb_dfl _ _ hn).
qed.
