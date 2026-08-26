require import AllCore Ring StdOrder.
from Jasmin require import JWord.

require import Array768.
require import NTRUPlus768EvaluationSemantics.
require import NTRUPlus768PolyBasemulAlgebra NTRUPlus768PolyBasemulProof.

(* A terminal Array768 value represents one global polynomial when each of
   its 192 four-coefficient blocks is congruent to that polynomial modulo the
   corresponding terminal quartic.  This relational formulation requires
   neither pairwise coprimality nor a CRT isomorphism. *)

op eqm_global (p q : poly) : bool =
  exists h, q - p = h * global_modulus.

op terminal_represents (a : W16.t Array768.t) (p : poly) : bool =
  forall k, 0 <= k < 192 =>
    eqm4 k p (block_poly (block4 a k)).

lemma eqm_global_refl (p : poly) :
  eqm_global p p.
proof.
  rewrite /eqm_global.
  exists poly0.
  ring.
qed.

lemma eqm_global_sym (p q : poly) :
  eqm_global p q => eqm_global q p.
proof.
  rewrite /eqm_global.
  move=> [h Hh].
  exists (-h).
  have -> : p - q = -(q - p) by ring.
  rewrite Hh.
  ring.
qed.

lemma eqm_global_trans (p q r : poly) :
  eqm_global p q => eqm_global q r => eqm_global p r.
proof.
  rewrite /eqm_global.
  move=> [h Hh] [j Hj].
  exists (h + j).
  have -> : r - p = (q - p) + (r - q) by ring.
  rewrite Hh Hj.
  ring.
qed.

lemma eqm_global_add (p q r s : poly) :
  eqm_global p q => eqm_global r s =>
  eqm_global (p + r) (q + s).
proof.
  rewrite /eqm_global.
  move=> [h Hh] [j Hj].
  exists (h + j).
  have -> : q + s - (p + r) = (q - p) + (s - r) by ring.
  rewrite Hh Hj.
  ring.
qed.

lemma eqm_global_mul (p q r s : poly) :
  eqm_global p q => eqm_global r s =>
  eqm_global (p * r) (q * s).
proof.
  rewrite /eqm_global.
  move=> [h Hh] [j Hj].
  exists (h * s + p * j).
  have -> : q * s - p * r = (q - p) * s + p * (s - r) by ring.
  rewrite Hh Hj.
  ring.
qed.

lemma eqm_global_implies_eqm4 (p q : poly) (k : int) :
  eqm_global p q =>
  0 <= k < 192 =>
  eqm4 k p q.
proof.
  rewrite /eqm_global /eqm4.
  move=> [h Hh] Hk.
  have [g Hg] := quartic_modulus_divides_global k Hk.
  exists (h * g).
  rewrite Hh Hg.
  ring.
qed.

lemma terminal_represents_global_congr
    (a : W16.t Array768.t) (p q : poly) :
  eqm_global p q =>
  terminal_represents a p =>
  terminal_represents a q.
proof.
  move=> Hpq Ha.
  rewrite /terminal_represents in Ha.
  rewrite /terminal_represents.
  move=> k Hk.
  have Hlocal := eqm_global_implies_eqm4 p q k Hpq Hk.
  have Hqp := eqm4_sym k p q Hlocal.
  exact
    (eqm4_trans k q p (block_poly (block4 a k)) Hqp (Ha k Hk)).
qed.

lemma terminal_represents_global_iff
    (a : W16.t Array768.t) (p q : poly) :
  eqm_global p q =>
  (terminal_represents a p <=> terminal_represents a q).
proof.
  move=> Hpq.
  split.
  + exact (terminal_represents_global_congr a p q Hpq).
  exact
    (terminal_represents_global_congr a q p (eqm_global_sym p q Hpq)).
qed.

lemma poly_basemul_qring_represents_product
    (ap bp rp : W16.t Array768.t) (p q : poly) :
  terminal_represents ap p =>
  terminal_represents bp q =>
  poly_basemul_qring ap bp rp 192 =>
  terminal_represents rp (p * q).
proof.
  move=> Hap Hbp Hcontract.
  rewrite /terminal_represents in Hap.
  rewrite /terminal_represents in Hbp.
  rewrite /terminal_represents.
  move=> k Hk.
  have HA := Hap k Hk.
  have HB := Hbp k Hk.
  have Hinputs :=
    eqm4_mul k p (block_poly (block4 ap k))
      q (block_poly (block4 bp k)) HA HB.
  have Houtput :=
    poly_basemul_qring_block_eqm4 ap bp rp k Hcontract Hk.
  have Houtput_sym :=
    eqm4_sym k
      (block_poly (block4 rp k))
      (block_poly (block4 ap k) * block_poly (block4 bp k))
      Houtput.
  exact
    (eqm4_trans k
      (p * q)
      (block_poly (block4 ap k) * block_poly (block4 bp k))
      (block_poly (block4 rp k))
      Hinputs Houtput_sym).
qed.
