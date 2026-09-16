require import AllCore IntDiv List Ring StdBigop StdOrder.

require import Array768.
require import NTRUPlus768CyclotomicFactorization.
require import NTRUPlus768EvaluationSemantics.
require import NTRUPlus768TerminalRepresentation.
require import NTRUPlus768CoefficientRecovery.

import NTRUPoly.BigPoly.

abbrev ( + ) = NTRUPoly.PolyComRing.( + ).
abbrev [ - ] = NTRUPoly.PolyComRing.([-]).
abbrev ( * ) = NTRUPoly.PolyComRing.( * ).
abbrev ( - ) p q = p + (-q).
abbrev exp = NTRUPoly.PolyComRing.exp.

(* This product is computed over the integers.  Its only reduction is by
   X^768 - X^384 + 1; in particular, no coefficient reduction modulo q is
   hidden in the noise coefficients used by the recovery theorem. *)
op integer_zero : int Array768.t = Array768.init (fun _ => 0).

op integer_unit (i : int) : int Array768.t =
  Array768.init (fun j => if j = i then 1 else 0).

op integer_add (a b : int Array768.t) : int Array768.t =
  Array768.init (fun j => a.[j] + b.[j]).

op integer_scale (c : int) (a : int Array768.t) : int Array768.t =
  Array768.init (fun j => c * a.[j]).

op integer_sum (vs : int Array768.t list) : int Array768.t =
  foldr integer_add integer_zero vs.

op integer_reduced_monomial (s : int) : int Array768.t =
  if s < 768 then integer_unit s
  else if s < 1152 then
    integer_add (integer_unit (s - 384))
      (integer_scale (-1) (integer_unit (s - 768)))
  else integer_scale (-1) (integer_unit (s - 1152)).

op integer_product (a b : int Array768.t) : int Array768.t =
  integer_sum (map
    (fun i => integer_sum (map
      (fun j => integer_scale (a.[i] * b.[j])
        (integer_reduced_monomial (i + j)))
      (range 0 768)))
    (range 0 768)).

lemma integer_zero_get (j : int) :
  0 <= j < 768 => integer_zero.[j] = 0.
proof. by move=> Hj; rewrite /integer_zero Array768.initiE. qed.

lemma integer_unit_get (i j : int) :
  0 <= j < 768 => (integer_unit i).[j] = if j = i then 1 else 0.
proof. by move=> Hj; rewrite /integer_unit Array768.initiE. qed.

lemma integer_add_get (a b : int Array768.t) (j : int) :
  0 <= j < 768 => (integer_add a b).[j] = a.[j] + b.[j].
proof. by move=> Hj; rewrite /integer_add Array768.initiE. qed.

lemma integer_scale_get (c : int) (a : int Array768.t) (j : int) :
  0 <= j < 768 => (integer_scale c a).[j] = c * a.[j].
proof. by move=> Hj; rewrite /integer_scale Array768.initiE. qed.

lemma int_poly_zero : int_poly integer_zero = poly0.
proof.
  apply NTRUPoly.poly_eqP => j Hj.
  rewrite NTRUPoly.poly0E.
  case (j < 768) => Hbound.
  + by rewrite int_poly_coeff 1:/# integer_zero_get 1:/# /lift_int.
  by rewrite int_poly_coeff_out 1:/#.
qed.

lemma int_poly_add (a b : int Array768.t) :
  int_poly (integer_add a b) = int_poly a + int_poly b.
proof.
  rewrite /int_poly /NTRUPoly.PolyComRing.( + ) -PCA.big_split.
  apply PCA.eq_big_int => j Hj /=.
  rewrite integer_add_get 1:Hj /lift_int CycloFq.incyclocoeffD
    NTRUPoly.polyCD.
  exact (NTRUPoly.PolyComRing.mulrDl _ _ _).
qed.

lemma int_poly_scale (c : int) (a : int Array768.t) :
  int_poly (integer_scale c a) = polyC (lift_int c) * int_poly a.
proof.
  rewrite /int_poly /NTRUPoly.PolyComRing.( * ) PCA.mulr_sumr.
  apply PCA.eq_big_int => j Hj /=.
  rewrite integer_scale_get 1:Hj /lift_int CycloFq.incyclocoeffM
    NTRUPoly.polyCM.
  apply/eq_sym.
  exact (NTRUPoly.PolyComRing.mulrA _ _ _).
qed.

lemma int_poly_unit (i : int) :
  0 <= i < 768 => int_poly (integer_unit i) = exp X i.
proof.
  move=> Hi.
  apply NTRUPoly.poly_eqP => j Hj.
  rewrite NTRUPoly.polyXnE 1:/#.
  case (j < 768) => Hbound.
  + rewrite int_poly_coeff 1:/# integer_unit_get 1:/#.
    by case (j = i) => //=.
  by rewrite int_poly_coeff_out 1:/# (_ : j <> i) 1:/# /=.
qed.

lemma int_poly_integer_sum_indexed
    (f : int -> int Array768.t) (s : int list) :
  int_poly (integer_sum (map f s)) =
  PCA.big predT (fun i => int_poly (f i)) s.
proof.
  elim: s => [| i s IH].
  + by rewrite /integer_sum /= int_poly_zero PCA.big_nil.
  by rewrite /integer_sum /= int_poly_add -/integer_sum IH PCA.big_consT.
qed.

lemma eqm_global_big (f g : int -> poly) (s : int list) :
  (forall i, mem s i => eqm_global (f i) (g i)) =>
  eqm_global (PCA.big predT f s) (PCA.big predT g s).
proof.
  elim: s => [| i s IH] Hfg.
  + rewrite !PCA.big_nil.
    exact (eqm_global_refl poly0).
  rewrite !PCA.big_consT.
  apply eqm_global_add.
  + apply Hfg; by rewrite /=.
  apply IH => j Hj.
  apply Hfg; by rewrite /= Hj.
qed.

lemma eqm_global_bigi (f g : int -> poly) (lo hi : int) :
  (forall i, lo <= i < hi => eqm_global (f i) (g i)) =>
  eqm_global (PCA.bigi predT f lo hi) (PCA.bigi predT g lo hi).
proof.
  move=> Hfg.
  apply eqm_global_big => i /mem_range Hi.
  exact (Hfg i Hi).
qed.

lemma global_monomial_middle (s : int) :
  768 <= s =>
  eqm_global (exp X s) (exp X (s - 384) - exp X (s - 768)).
proof.
  move=> Hs.
  have HsE : exp X s = exp X (s - 768) * exp X 768.
  + have Hnn : 0 <= s - 768 by smt().
    have Hz : 0 <= 768 by done.
    have H := NTRUPoly.PolyComRing.exprD_nneg X (s - 768) 768 Hnn Hz.
    smt().
  have Hmiddle : exp X (s - 384) = exp X (s - 768) * exp X 384.
  + have Hnn : 0 <= s - 768 by smt().
    have Hz : 0 <= 384 by done.
    have H := NTRUPoly.PolyComRing.exprD_nneg X (s - 768) 384 Hnn Hz.
    smt().
  rewrite /eqm_global.
  exists (-exp X (s - 768)).
  rewrite HsE Hmiddle /global_modulus.
  ring.
qed.

lemma global_monomial_high (s : int) :
  1152 <= s => eqm_global (exp X s) (-exp X (s - 1152)).
proof.
  move=> Hs.
  have HsE : exp X s = exp X (s - 1152) * exp X 1152.
  + have Hnn : 0 <= s - 1152 by smt().
    have Hz : 0 <= 1152 by done.
    have H := NTRUPoly.PolyComRing.exprD_nneg X (s - 1152) 1152 Hnn Hz.
    smt().
  have H768 : exp X 768 = exp (exp X 384) 2.
  + exact (NTRUPoly.PolyComRing.exprM X 384 2).
  have H1152 : exp X 1152 = exp (exp X 384) 3.
  + exact (NTRUPoly.PolyComRing.exprM X 384 3).
  rewrite /eqm_global.
  exists (-(exp X (s - 1152) * (exp X 384 + poly1))).
  rewrite HsE /global_modulus H768 H1152.
  ring.
qed.

lemma integer_reduced_monomial_eqm_global (s : int) :
  0 <= s <= 1534 =>
  eqm_global (exp X s) (int_poly (integer_reduced_monomial s)).
proof.
  move=> Hs.
  rewrite /integer_reduced_monomial.
  case (s < 768) => Hlow /=.
  + rewrite int_poly_unit 1:/#.
    exact (eqm_global_refl (exp X s)).
  case (s < 1152) => Hmiddle /=.
  + rewrite int_poly_add int_poly_scale !int_poly_unit 1:/# 1:/#.
    have Hone : polyC (lift_int (-1)) = -poly1.
    + by rewrite /lift_int CycloFq.incyclocoeffN NTRUPoly.polyCN.
    have Hmul := NTRUPoly.PolyComRing.mulN1r (exp X (s - 768)).
    have Hrange : 768 <= s by smt().
    have Hcongr := global_monomial_middle s Hrange.
    smt().
  rewrite int_poly_scale int_poly_unit 1:/#.
  have Hone : polyC (lift_int (-1)) = -poly1.
  + by rewrite /lift_int CycloFq.incyclocoeffN NTRUPoly.polyCN.
  have Hmul := NTRUPoly.PolyComRing.mulN1r (exp X (s - 1152)).
  have Hrange : 1152 <= s by smt().
  have Hhigh := global_monomial_high s Hrange.
  smt().
qed.

lemma int_poly_mulE (a b : int Array768.t) :
  int_poly a * int_poly b =
  PCA.bigi predT (fun i =>
    PCA.bigi predT (fun j =>
      polyC (lift_int (a.[i] * b.[j])) * exp X (i + j))
      0 768) 0 768.
proof.
  rewrite /int_poly /NTRUPoly.PolyComRing.( * ) PCA.mulr_suml.
  apply PCA.eq_big_int => i Hi /=.
  rewrite PCA.mulr_sumr.
  apply PCA.eq_big_int => j Hj /=.
  rewrite /lift_int CycloFq.incyclocoeffM NTRUPoly.polyCM
    NTRUPoly.PolyComRing.exprD_nneg 1:/# 1:/#.
  exact (NTRUPoly.PolyComRing.mulrACA _ _ _ _).
qed.

lemma integer_product_eqm_global (a b : int Array768.t) :
  eqm_global (int_poly a * int_poly b) (int_poly (integer_product a b)).
proof.
  rewrite int_poly_mulE /integer_product int_poly_integer_sum_indexed.
  apply eqm_global_bigi => i Hi /=.
  rewrite int_poly_integer_sum_indexed.
  apply eqm_global_bigi => j Hj /=.
  rewrite int_poly_scale.
  apply eqm_global_mul.
  + exact (eqm_global_refl (polyC (lift_int (a.[i] * b.[j])))).
  apply integer_reduced_monomial_eqm_global.
  smt().
qed.
