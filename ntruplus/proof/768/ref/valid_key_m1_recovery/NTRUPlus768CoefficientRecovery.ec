require import AllCore IntDiv List Ring StdBigop StdOrder IntMin.
from Jasmin require import JWord.

require import Array768.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768CyclotomicFactorization.
require import NTRUPlus768EvaluationSemantics.
require import NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768TerminalRepresentation.

import NTRUPoly.BigPoly.

(* Integer coefficient arrays are lifted into F_q[X] before any quotient is
   taken.  Equality modulo the degree-768 modulus then determines every
   coefficient of representatives supported on indices 0,...,767. *)
op int_poly (v : int Array768.t) : poly =
  PCA.bigi predT
    (fun i => polyC (lift_int v.[i]) * exp X i) 0 768.

lemma monomial_coeff (c : CycloFq.cyclocoeff) (i j : int) :
  0 <= i =>
  NTRUPoly."_.[_]" (polyC c * exp X i) j =
    if j = i then c else CycloFq.zero.
proof.
  move=> Hi.
  rewrite /NTRUPoly.PolyComRing.( * ) -NTRUPoly.scalepE.
  rewrite NTRUPoly.polyZE NTRUPoly.polyXnE //.
  case (j = i) => //=.
  + by rewrite NTRUPoly.Coeff.mulr1.
  by rewrite NTRUPoly.Coeff.mulr0.
qed.

lemma int_poly_coeff (v : int Array768.t) (j : int) :
  0 <= j < 768 =>
  NTRUPoly."_.[_]" (int_poly v) j = lift_int v.[j].
proof.
  move=> Hj.
  rewrite /int_poly NTRUPoly.BigPoly.polysumE /=.
  rewrite (NTRUPoly.BigCf.BCA.bigD1 _ _ j) ?(mem_range, range_uniq) //=.
  rewrite monomial_coeff 1:/# /=.
  rewrite NTRUPoly.BigCf.BCA.big1_seq ?NTRUPoly.Coeff.addr0 //=.
  move=> @/predC1 i [Hne /mem_range Hi].
  by rewrite monomial_coeff 1:/# (_ : j <> i) 1:/#.
qed.

lemma int_poly_coeff_out (v : int Array768.t) (j : int) :
  !(0 <= j < 768) =>
  NTRUPoly."_.[_]" (int_poly v) j = CycloFq.zero.
proof.
  move=> Hj.
  rewrite /int_poly NTRUPoly.BigPoly.polysumE /=.
  rewrite NTRUPoly.BigCf.BCA.big_seq NTRUPoly.BigCf.BCA.big1 //=.
  move=> i /mem_range Hi.
  by rewrite monomial_coeff 1:/# (_ : j <> i) 1:/#.
qed.

lemma int_poly_degree (v : int Array768.t) :
  NTRUPoly.deg (int_poly v) <= 768.
proof.
  apply NTRUPoly.deg_leP => // i Hi.
  apply int_poly_coeff_out.
  smt().
qed.

lemma int_poly_words (a : W16.t Array768.t) :
  int_poly (Array768.map coeff a) = input_poly a.
proof.
  rewrite /int_poly /input_poly /segment_poly.
  rewrite (PCA.big_cat_int 384) //.
  rewrite /NTRUPoly.PolyComRing.( + ).
  congr.
  + apply PCA.eq_big_int => i Hi.
    by rewrite /= Array768.mapiE 1:/# /lift_word.
  rewrite (PCA.big_addn 0 768 384) /=.
  rewrite /NTRUPoly.PolyComRing.( * ).
  rewrite (PCA.mulr_suml predT
    (fun i => polyC (lift_word a.[i + 384]) * exp X i)
    (range 0 384) (exp X 384)).
  apply PCA.eq_big_int => i Hi.
  rewrite /= Array768.mapiE 1:/# /lift_word.
  rewrite (NTRUPoly.PolyComRing.exprD_nneg X i 384) 1:/# 1:/#.
  by rewrite /NTRUPoly.PolyComRing.( * ) NTRUPoly.mulpA.
qed.

lemma global_modulus_degree : NTRUPoly.deg global_modulus = 769.
proof.
  rewrite /global_modulus.
  have Htail : NTRUPoly.deg (-exp X 384 + poly1) <= 385.
  + have Hd := NTRUPoly.degD (-exp X 384) poly1.
    rewrite NTRUPoly.degN NTRUPoly.deg_polyXn // NTRUPoly.deg1 /= in Hd.
    smt().
  have -> : exp X 768 - exp X 384 + poly1 =
    exp X 768 + (-exp X 384 + poly1) by ring.
  rewrite NTRUPoly.degDl.
  + rewrite NTRUPoly.deg_polyXn //; smt().
  by rewrite NTRUPoly.deg_polyXn.
qed.

lemma global_modulus_leading :
  NTRUPoly.lc global_modulus = CycloFq.one.
proof.
  rewrite global_modulus_degree /= /global_modulus.
  rewrite !NTRUPoly.polyDE NTRUPoly.polyNE !NTRUPoly.polyXnE //=.
  by rewrite NTRUPoly.polyCE /=
    NTRUPoly.Coeff.oppr0 !NTRUPoly.Coeff.addr0.
qed.

lemma eqm_global_low_degree_unique (p r : poly) :
  NTRUPoly.deg p <= 768 => NTRUPoly.deg r <= 768 =>
  eqm_global p r => p = r.
proof.
  move=> Hp Hr [h Hh].
  have Hd := NTRUPoly.degB r p.
  have Hlow : NTRUPoly.deg (r - p) <= 768 by smt(IntOrder.ler_maxrP).
  case (h = poly0) => Hzero.
  + have Hdiff : r - p = poly0.
    + rewrite Hh Hzero.
      exact (NTRUPoly.PolyComRing.mul0r global_modulus).
    have -> : r = (r - p) + p by ring.
    rewrite Hdiff.
    apply/eq_sym.
    exact (NTRUPoly.PolyComRing.add0r p).
  have Hlc : CycloFq.( * ) (NTRUPoly.lc h)
      (NTRUPoly.lc global_modulus) <> CycloFq.zero.
  + by rewrite global_modulus_leading NTRUPoly.Coeff.mulr1
      NTRUPoly.lc_eq0.
  have Hdeg := NTRUPoly.degM_proper h global_modulus Hlc.
  rewrite global_modulus_degree in Hdeg.
  have Hpos := NTRUPoly.ge0_deg h.
  have Hnonzero : NTRUPoly.deg h <> 0 by rewrite NTRUPoly.deg_eq0.
  rewrite Hh in Hlow.
  smt().
qed.

lemma eqm_global_int_poly_coeff (u v : int Array768.t) (j : int) :
  eqm_global (int_poly u) (int_poly v) =>
  0 <= j < 768 => u.[j] %% q = v.[j] %% q.
proof.
  move=> Huv Hj.
  have Heq := eqm_global_low_degree_unique (int_poly u) (int_poly v)
    (int_poly_degree u) (int_poly_degree v) Huv.
  have Hcoeff : lift_int u.[j] = lift_int v.[j].
  + by rewrite -(int_poly_coeff u j Hj) -(int_poly_coeff v j Hj) Heq.
  move/(congr1 CycloFq.asint): Hcoeff.
  by rewrite /lift_int !CycloFq.incyclocoeffK.
qed.
