require import AllCore IntDiv List Ring StdBigop StdOrder.
from Jasmin require import JWord.

require import Array4 Array768.
require import NTRUPlus768CyclotomicFactorization.
require import NTRUPlus768BasemulAlgebra NTRUPlus768NTTSchedule.
require import NTRUPlus768PolyBasemulAlgebra NTRUPlus768PolyBasemulProof.

(* This theory gives the 192 terminal four-coefficient blocks their first
   quotient-ring meaning.  It deliberately stops short of specifying the
   forward NTT: the statement below only lifts the already verified
   poly_basemul_qring coefficient contract into F_q[X]/(X^4-zeta_k). *)

type poly = NTRUPoly.poly.

import NTRUPoly.BigPoly.

abbrev poly0 = NTRUPoly.PolyComRing.zeror.
abbrev poly1 = NTRUPoly.PolyComRing.oner.
abbrev polyC = NTRUPoly.polyC.
abbrev X = NTRUPoly.X.
abbrev ( + ) = NTRUPoly.PolyComRing.( + ).
abbrev [ - ] = NTRUPoly.PolyComRing.([-]).
abbrev ( * ) = NTRUPoly.PolyComRing.( * ).
abbrev ( - ) p q = p + (-q).
abbrev exp = NTRUPoly.PolyComRing.exp.

instance ring with poly
  op rzero = NTRUPoly.PolyComRing.zeror
  op rone = NTRUPoly.PolyComRing.oner
  op add = NTRUPoly.PolyComRing.( + )
  op mul = NTRUPoly.PolyComRing.( * )
  op opp = NTRUPoly.PolyComRing.([-])
  op expr = NTRUPoly.PolyComRing.exp
  op ofint = NTRUPoly.PolyComRing.ofint

  proof oner_neq0 by exact NTRUPoly.PolyComRing.oner_neq0
  proof addr0 by exact NTRUPoly.PolyComRing.addr0
  proof addrA by exact NTRUPoly.PolyComRing.addrA
  proof addrC by exact NTRUPoly.PolyComRing.addrC
  proof addrN by exact NTRUPoly.PolyComRing.addrN
  proof mulr1 by exact NTRUPoly.PolyComRing.mulr1
  proof mulrA by exact NTRUPoly.PolyComRing.mulrA
  proof mulrC by exact NTRUPoly.PolyComRing.mulrC
  proof mulrDl by exact NTRUPoly.PolyComRing.mulrDl
  proof expr0 by exact NTRUPoly.PolyComRing.expr0
  proof exprS by exact NTRUPoly.PolyComRing.exprS
  proof ofint0 by exact NTRUPoly.PolyComRing.ofint0
  proof ofint1 by exact NTRUPoly.PolyComRing.ofint1
  proof ofintS by exact NTRUPoly.PolyComRing.ofintS
  proof ofintN by exact NTRUPoly.PolyComRing.ofintN.

op lift_int (x : int) : CycloFq.cyclocoeff = CycloFq.incyclocoeff x.

op lift_word (x : W16.t) : CycloFq.cyclocoeff = lift_int (coeff x).

op block_poly_fq
    (a0 a1 a2 a3 : CycloFq.cyclocoeff) : poly =
  polyC a0 +
  polyC a1 * X +
  polyC a2 * exp X 2 +
  polyC a3 * exp X 3.

op block_poly (a : W16.t Array4.t) : poly =
  block_poly_fq
    (lift_word a.[0]) (lift_word a.[1])
    (lift_word a.[2]) (lift_word a.[3]).

op reduced_block_poly
    (a b : W16.t Array4.t) (zeta_math : int) : poly =
  block_poly_fq
    (lift_int (coeff0 a b zeta_math))
    (lift_int (coeff1 a b zeta_math))
    (lift_int (coeff2 a b zeta_math))
    (lift_int (coeff3 a b zeta_math)).

op block_coeff_poly (a : W16.t Array4.t) (i : int) : poly =
  polyC (lift_word a.[i]).

op low_block_poly (a b : W16.t Array4.t) : poly =
  block_coeff_poly a 0 * block_coeff_poly b 0 +
  (block_coeff_poly a 0 * block_coeff_poly b 1 +
   block_coeff_poly a 1 * block_coeff_poly b 0) * X +
  (block_coeff_poly a 0 * block_coeff_poly b 2 +
   block_coeff_poly a 1 * block_coeff_poly b 1 +
   block_coeff_poly a 2 * block_coeff_poly b 0) * exp X 2 +
  (block_coeff_poly a 0 * block_coeff_poly b 3 +
   block_coeff_poly a 1 * block_coeff_poly b 2 +
   block_coeff_poly a 2 * block_coeff_poly b 1 +
   block_coeff_poly a 3 * block_coeff_poly b 0) * exp X 3.

op high_block_poly (a b : W16.t Array4.t) : poly =
  (block_coeff_poly a 1 * block_coeff_poly b 3 +
   block_coeff_poly a 2 * block_coeff_poly b 2 +
   block_coeff_poly a 3 * block_coeff_poly b 1) +
  (block_coeff_poly a 2 * block_coeff_poly b 3 +
   block_coeff_poly a 3 * block_coeff_poly b 2) * X +
  (block_coeff_poly a 3 * block_coeff_poly b 3) * exp X 2.

op quartic_modulus (k : int) : poly =
  exp X 4 - polyC (terminal_root_field k).

op eqm4 (k : int) (p q : poly) : bool =
  exists h, q - p = h * quartic_modulus k.

op global_modulus : poly =
  exp X 768 - exp X 384 + poly1.

lemma eqm4_refl (k : int) (p : poly) :
  eqm4 k p p.
proof.
  rewrite /eqm4.
  exists poly0.
  ring.
qed.

lemma eqm4_sym (k : int) (p q : poly) :
  eqm4 k p q => eqm4 k q p.
proof.
  rewrite /eqm4.
  move=> [h Hh].
  exists (-h).
  have -> : p - q = -(q - p) by ring.
  rewrite Hh.
  ring.
qed.

lemma eqm4_trans (k : int) (p q r : poly) :
  eqm4 k p q => eqm4 k q r => eqm4 k p r.
proof.
  rewrite /eqm4.
  move=> [h Hh] [j Hj].
  exists (h + j).
  have -> : r - p = (q - p) + (r - q) by ring.
  rewrite Hh Hj.
  ring.
qed.

lemma eqm4_add (k : int) (p q r s : poly) :
  eqm4 k p q => eqm4 k r s => eqm4 k (p + r) (q + s).
proof.
  rewrite /eqm4.
  move=> [h Hh] [j Hj].
  exists (h + j).
  have -> : q + s - (p + r) = (q - p) + (s - r) by ring.
  rewrite Hh Hj.
  ring.
qed.

lemma eqm4_mul (k : int) (p q r s : poly) :
  eqm4 k p q => eqm4 k r s => eqm4 k (p * r) (q * s).
proof.
  rewrite /eqm4.
  move=> [h Hh] [j Hj].
  exists (h * s + p * j).
  have -> : q * s - p * r = (q - p) * s + p * (s - r) by ring.
  rewrite Hh Hj.
  ring.
qed.

lemma terminal_quartic_product_global :
  PCM.big predT quartic_modulus (range 0 192) = global_modulus.
proof.
  rewrite /quartic_modulus /global_modulus.
  exact terminal_quartic_factorization_explicit.
qed.

lemma quartic_modulus_divides_global (k : int) :
  0 <= k < 192 =>
  exists h, global_modulus = h * quartic_modulus k.
proof.
  move=> Hk.
  have Hmem : mem (range 0 192) k by rewrite mem_range.
  exists (PCM.big (predC1 k) quartic_modulus (range 0 192)).
  rewrite -terminal_quartic_product_global.
  rewrite (PCM.bigD1 quartic_modulus (range 0 192) k) 1:Hmem 1:range_uniq.
  apply NTRUPoly.PolyComRing.mulrC.
qed.

lemma global_modulus_eqm4_zero (k : int) :
  0 <= k < 192 => eqm4 k poly0 global_modulus.
proof.
  move=> Hk.
  have [h Hh] := quartic_modulus_divides_global k Hk.
  rewrite /eqm4.
  exists h.
  have -> : global_modulus - poly0 = global_modulus by ring.
  exact Hh.
qed.

lemma block_product_split (a b : W16.t Array4.t) :
  block_poly a * block_poly b =
  low_block_poly a b + high_block_poly a b * exp X 4.
proof.
  rewrite /block_poly /block_poly_fq.
  rewrite /low_block_poly /high_block_poly /block_coeff_poly.
  ring.
qed.

lemma lift_coeff0_polyE
    (a b : W16.t Array4.t) (zeta_math : int) :
  polyC (lift_int (coeff0 a b zeta_math)) =
  block_coeff_poly a 0 * block_coeff_poly b 0 +
  polyC (lift_int zeta_math) *
    (block_coeff_poly a 1 * block_coeff_poly b 3 +
     block_coeff_poly a 2 * block_coeff_poly b 2 +
     block_coeff_poly a 3 * block_coeff_poly b 1).
proof.
  rewrite /coeff0 /block_coeff_poly /lift_word /lift_int.
  rewrite !CycloFq.incyclocoeffD !CycloFq.incyclocoeffM.
  rewrite !CycloFq.incyclocoeffD !CycloFq.incyclocoeffM.
  rewrite !NTRUPoly.polyCD !NTRUPoly.polyCM.
  by rewrite !NTRUPoly.polyCD !NTRUPoly.polyCM.
qed.

lemma lift_coeff1_polyE
    (a b : W16.t Array4.t) (zeta_math : int) :
  polyC (lift_int (coeff1 a b zeta_math)) =
  block_coeff_poly a 0 * block_coeff_poly b 1 +
  block_coeff_poly a 1 * block_coeff_poly b 0 +
  polyC (lift_int zeta_math) *
    (block_coeff_poly a 2 * block_coeff_poly b 3 +
     block_coeff_poly a 3 * block_coeff_poly b 2).
proof.
  rewrite /coeff1 /block_coeff_poly /lift_word /lift_int.
  rewrite !CycloFq.incyclocoeffD !CycloFq.incyclocoeffM.
  rewrite !CycloFq.incyclocoeffD !CycloFq.incyclocoeffM.
  rewrite !NTRUPoly.polyCD !NTRUPoly.polyCM.
  by rewrite !NTRUPoly.polyCD !NTRUPoly.polyCM.
qed.

lemma lift_coeff2_polyE
    (a b : W16.t Array4.t) (zeta_math : int) :
  polyC (lift_int (coeff2 a b zeta_math)) =
  block_coeff_poly a 0 * block_coeff_poly b 2 +
  block_coeff_poly a 1 * block_coeff_poly b 1 +
  block_coeff_poly a 2 * block_coeff_poly b 0 +
  polyC (lift_int zeta_math) *
    (block_coeff_poly a 3 * block_coeff_poly b 3).
proof.
  rewrite /coeff2 /block_coeff_poly /lift_word /lift_int.
  rewrite !CycloFq.incyclocoeffD !CycloFq.incyclocoeffM.
  rewrite !NTRUPoly.polyCD !NTRUPoly.polyCM.
  done.
qed.

lemma lift_coeff3_polyE
    (a b : W16.t Array4.t) (zeta_math : int) :
  polyC (lift_int (coeff3 a b zeta_math)) =
  block_coeff_poly a 0 * block_coeff_poly b 3 +
  block_coeff_poly a 1 * block_coeff_poly b 2 +
  block_coeff_poly a 2 * block_coeff_poly b 1 +
  block_coeff_poly a 3 * block_coeff_poly b 0.
proof.
  rewrite /coeff3 /block_coeff_poly /lift_word /lift_int.
  rewrite !CycloFq.incyclocoeffD !CycloFq.incyclocoeffM.
  rewrite !NTRUPoly.polyCD !NTRUPoly.polyCM.
  done.
qed.

lemma reduced_block_poly_split
    (a b : W16.t Array4.t) (zeta_math : int) :
  reduced_block_poly a b zeta_math =
  low_block_poly a b +
  polyC (lift_int zeta_math) * high_block_poly a b.
proof.
  rewrite /reduced_block_poly /block_poly_fq.
  rewrite lift_coeff0_polyE lift_coeff1_polyE.
  rewrite lift_coeff2_polyE lift_coeff3_polyE.
  rewrite /low_block_poly /high_block_poly /block_coeff_poly.
  ring.
qed.

lemma reduced_product_factor
    (a b : W16.t Array4.t) (zeta_math : int) :
  block_poly a * block_poly b - reduced_block_poly a b zeta_math =
  high_block_poly a b * (exp X 4 - polyC (lift_int zeta_math)).
proof.
  rewrite block_product_split reduced_block_poly_split.
  ring.
qed.

lemma lift_int_eq (x y : int) :
  x %% q = y %% q => lift_int x = lift_int y.
proof.
  move=> Hxy.
  rewrite /lift_int.
  apply/CycloFq.eq_incyclocoeff.
  exact Hxy.
qed.

lemma block_poly_eq_of_lifts
    (a : W16.t Array4.t) (c0 c1 c2 c3 : CycloFq.cyclocoeff) :
  lift_word a.[0] = c0 =>
  lift_word a.[1] = c1 =>
  lift_word a.[2] = c2 =>
  lift_word a.[3] = c3 =>
  block_poly a = block_poly_fq c0 c1 c2 c3.
proof.
  move=> H0 H1 H2 H3.
  by rewrite /block_poly H0 H1 H2 H3.
qed.

lemma poly_basemul_qring_block_eqm4
    (ap bp rp : W16.t Array768.t) (k : int) :
  poly_basemul_qring ap bp rp 192 =>
  0 <= k < 192 =>
  eqm4 k
    (block_poly (block4 rp k))
    (block_poly (block4 ap k) * block_poly (block4 bp k)).
proof.
  move=> Hcontract Hk.
  rewrite /poly_basemul_qring in Hcontract.
  have [_ [H0 [H1 [H2 H3]]]] := Hcontract k Hk.
  have E0 :
      lift_word (block4 rp k).[0] =
      lift_int (coeff0 (block4 ap k) (block4 bp k) (terminal_value k)).
  + apply lift_int_eq.
    exact H0.
  have E1 :
      lift_word (block4 rp k).[1] =
      lift_int (coeff1 (block4 ap k) (block4 bp k) (terminal_value k)).
  + apply lift_int_eq.
    exact H1.
  have E2 :
      lift_word (block4 rp k).[2] =
      lift_int (coeff2 (block4 ap k) (block4 bp k) (terminal_value k)).
  + apply lift_int_eq.
    exact H2.
  have E3 :
      lift_word (block4 rp k).[3] =
      lift_int (coeff3 (block4 ap k) (block4 bp k) (terminal_value k)).
  + apply lift_int_eq.
    exact H3.
  have Er :
      block_poly (block4 rp k) =
      reduced_block_poly (block4 ap k) (block4 bp k) (terminal_value k).
  + apply block_poly_eq_of_lifts.
    + exact E0.
    + exact E1.
    + exact E2.
    + exact E3.
  rewrite /eqm4.
  exists (high_block_poly (block4 ap k) (block4 bp k)).
  rewrite Er /quartic_modulus /terminal_root_field.
  exact
    (reduced_product_factor
      (block4 ap k) (block4 bp k) (terminal_value k)).
qed.

lemma poly_basemul_qring_all_blocks_eqm4
    (ap bp rp : W16.t Array768.t) :
  poly_basemul_qring ap bp rp 192 =>
  forall k, 0 <= k < 192 =>
    eqm4 k
      (block_poly (block4 rp k))
      (block_poly (block4 ap k) * block_poly (block4 bp k)).
proof.
  move=> Hcontract k Hk.
  exact (poly_basemul_qring_block_eqm4 ap bp rp k Hcontract Hk).
qed.
