require import AllCore IntDiv List Ring StdBigop StdOrder.
require import Poly ZModP.

require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768FqInvPrime.
require import NTRUPlus768NTTSchedule.

(* This is the first global-ring node above the verified NTT schedule.  It
   proves the exact cyclotomic factorization followed by the implementation,
   but deliberately does not postulate a CRT isomorphism or transform
   semantics. *)

clone import ZModField as CycloFq with
  op p <- q
  rename "zmod" as "cyclocoeff"
  rename "ZModp" as "CycloFq"
  proof prime_p by exact q_prime
  proof *.

clone import PolyComRing as NTRUPoly with
  type coeff <- cyclocoeff,
  op Coeff.zeror <- CycloFq.zero,
  op Coeff.oner <- CycloFq.one,
  op Coeff.( + ) <- CycloFq.( + ),
  op Coeff.([-]) <- CycloFq.([-]),
  op Coeff.( * ) <- CycloFq.( * ),
  op Coeff.invr <- CycloFq.inv,
  pred Coeff.unit <- CycloFq.unit
  proof Coeff.addrA by exact CycloFqField.addrA
  proof Coeff.addrC by exact CycloFqField.addrC
  proof Coeff.add0r by exact CycloFqField.add0r
  proof Coeff.addNr by exact CycloFqField.addNr
  proof Coeff.oner_neq0 by exact CycloFqField.oner_neq0
  proof Coeff.mulrA by exact CycloFqField.mulrA
  proof Coeff.mulrC by exact CycloFqField.mulrC
  proof Coeff.mul1r by exact CycloFqField.mul1r
  proof Coeff.mulrDl by exact CycloFqField.mulrDl
  proof Coeff.mulVr by exact CycloFqRing.mulVr
  proof Coeff.unitP by exact CycloFqRing.unitP
  proof Coeff.unitout by exact CycloFqRing.unitout.

import NTRUPoly.BigPoly.
import NTRUPoly.PolyComRing.

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

op zeta_field : cyclocoeff = incyclocoeff zeta_root.

op factor (a : poly) (m e : int) : poly =
  exp a m - polyC (exp zeta_field e).

op factor_product (a : poly) (m : int) (es : int list) : poly =
  PCM.big predT (factor a m) es.

lemma zeta_field_expE (e : int) :
  0 <= e => exp zeta_field e = incyclocoeff (zeta_root ^ e).
proof.
  move=> He.
  rewrite /zeta_field.
  move: (incyclocoeff_exp zeta_root e).
  rewrite ifT 1:He.
  by move=> <-.
qed.

lemma zeta_doubleE (e : int) :
  exp zeta_field (2 * e) = exp (exp zeta_field e) 2.
proof.
  rewrite [2 * e]mulrC.
  exact (CycloFqField.exprM zeta_field e 2).
qed.

lemma poly_zeta_doubleE (e : int) :
  polyC (exp zeta_field (2 * e)) =
  polyC (exp zeta_field e) * polyC (exp zeta_field e).
proof.
  rewrite zeta_doubleE CycloFqField.expr2.
  exact (polyCM (exp zeta_field e) (exp zeta_field e)).
qed.

lemma zeta96E : exp zeta_field 96 = incyclocoeff 2735.
proof.
  rewrite zeta_field_expE 1://.
  apply/eq_incyclocoeff.
  by rewrite /zeta_root /q /=.
qed.

lemma zeta192E : exp zeta_field 192 = incyclocoeff 2734.
proof.
  rewrite zeta_field_expE 1://.
  apply/eq_incyclocoeff.
  by rewrite /zeta_root /q /=.
qed.

lemma zeta288E : exp zeta_field 288 = -one.
proof.
  rewrite zeta_field_expE 1://.
  change (incyclocoeff (zeta_root ^ 288) = -incyclocoeff 1).
  rewrite -incyclocoeffN.
  apply/eq_incyclocoeff.
  by rewrite /zeta_root /q /=.
qed.

lemma zeta384E : exp zeta_field 384 = incyclocoeff 722.
proof.
  rewrite zeta_field_expE 1://.
  apply/eq_incyclocoeff.
  by rewrite /zeta_root /q /=.
qed.

lemma zeta480E : exp zeta_field 480 = incyclocoeff 723.
proof.
  rewrite zeta_field_expE 1://.
  apply/eq_incyclocoeff.
  by rewrite /zeta_root /q /=.
qed.

lemma zeta576E : exp zeta_field 576 = one.
proof.
  rewrite zeta_field_expE 1://.
  change (incyclocoeff (zeta_root ^ 576) = incyclocoeff 1).
  apply/eq_incyclocoeff.
  by rewrite /zeta_root /q /=.
qed.

lemma residue2735_723_sum :
  incyclocoeff 2735 + incyclocoeff 723 = one.
proof.
  apply CycloFq.asint_inj.
  by rewrite CycloFq.addE CycloFq.oneE !incyclocoeffK /q /=.
qed.

lemma residue2735_723_product :
  incyclocoeff 2735 * incyclocoeff 723 = one.
proof.
  apply CycloFq.asint_inj.
  by rewrite CycloFq.mulE CycloFq.oneE !incyclocoeffK /q /=.
qed.

lemma zeta192_sum :
  one + exp zeta_field 192 + exp zeta_field 384 = zero.
proof.
  rewrite zeta192E zeta384E.
  apply CycloFq.asint_inj.
  by rewrite !CycloFq.addE CycloFq.oneE CycloFq.zeroE
             !incyclocoeffK /q /=.
qed.

lemma sub_cancel_middle (c x : poly) :
  c - x - c = -x.
proof.
  apply (@addIr c).
  rewrite subrK.
  by rewrite addrC.
qed.

lemma quadratic_split_identity (x u : poly) :
  (x - u) * (x - (poly1 - u)) =
    x * x - x + u * (poly1 - u).
proof.
  rewrite mulrBl !mulrBr.
  rewrite [x * u]mulrC.
  rewrite !opprB.
  rewrite addrACA.
  rewrite !mulr1 sub_cancel_middle.
  rewrite -!addrA.
  change
    (x * x + (u + (- (u * u) + -x)) =
     x * x + (-x + (u + -(u * u)))).
  rewrite [(- (u * u)) + -x]NTRUPoly.PolyComRing.addrC.
  by rewrite [u + ((-x) - u * u)]NTRUPoly.PolyComRing.addrCA.
qed.

lemma initial_factorization (a : poly) :
  factor_product a 96 roots_initial =
    exp a 192 - exp a 96 + poly1.
proof.
  change
    (factor a 96 96 * (factor a 96 480 * poly1) =
     exp a 192 - exp a 96 + poly1).
  rewrite /factor.
  rewrite zeta96E zeta480E.
  rewrite mulr1.
  have -> : exp a 192 = exp (exp a 96) 2.
  + by rewrite -exprM.
  rewrite expr2.
  have Hsum :
      polyC (incyclocoeff 2735) + polyC (incyclocoeff 723) = poly1.
  + by rewrite -polyCD residue2735_723_sum.
  have Hproduct :
      polyC (incyclocoeff 2735) * polyC (incyclocoeff 723) = poly1.
  + by rewrite -polyCM residue2735_723_product.
  have H723 :
      polyC (incyclocoeff 723) =
        poly1 - polyC (incyclocoeff 2735).
  + apply/eq_sym.
    rewrite subr_eq addrC.
    by rewrite -polyCD residue2735_723_sum.
  have Hproduct' :
      polyC (incyclocoeff 2735) *
        (poly1 - polyC (incyclocoeff 2735)) = poly1.
  + by rewrite -H723.
  rewrite H723.
  rewrite quadratic_split_identity Hproduct'.
  done.
qed.

lemma zeta_shift_288 (e : int) :
  0 <= e => exp zeta_field (e + 288) = -(exp zeta_field e).
proof.
  move=> He.
  rewrite CycloFqField.exprD_nneg 1:He 1:// zeta288E.
  by rewrite CycloFqField.mulrN1.
qed.

lemma difference_squares (x y : poly) :
  exp x 2 - exp y 2 = (x - y) * (x + y).
proof.
  rewrite mulrBl !mulrDr [y * x]mulrC.
  by rewrite [x * x + _]addrC subrACA subrr add0r !expr2.
qed.

lemma factor_split2 (a : poly) (m r : int) :
  0 <= m =>
  0 <= r =>
  factor a (2 * m) (2 * r) =
    factor a m r * factor a m (r + 288).
proof.
  move=> Hm Hr.
  rewrite /factor.
  have -> : exp a (2 * m) = exp (exp a m) 2.
  + rewrite [2 * m]mulrC.
    exact (exprM a m 2).
  have -> : exp zeta_field (2 * r) = exp (exp zeta_field r) 2.
  + rewrite [2 * r]mulrC.
    exact (CycloFqField.exprM zeta_field r 2).
  rewrite zeta_shift_288 1:Hr polyCN opprK.
  rewrite -(polyCX (exp zeta_field r) 2) 1://.
  rewrite difference_squares.
  done.
qed.

lemma split2_children_evenE (p : int) :
  0 <= p =>
  p %% 2 = 0 =>
  split2_children p = [p %/ 2; p %/ 2 + 288].
proof.
  move=> Hp Heven.
  rewrite /split2_children /ell /=.
  change ((p + 576) %/ 2 = p %/ 2 + 288).
  have -> : p + 576 = 288 * 2 + p by ring.
  rewrite divzMDl 1://.
  exact (Ring.IntID.addrC 288 (p %/ 2)).
qed.

lemma factor_product_split2 (a : poly) (m : int) (es : int list) :
  0 <= m =>
  all (fun e => 0 <= e /\ e %% 2 = 0) es =>
  factor_product a (2 * m) es =
    factor_product a m (flatten (map split2_children es)).
proof.
  move=> Hm.
  elim es => [|e es IH] /=.
  + by rewrite /factor_product !PCM.big_nil.
  move=> [[He0 Heven] Hes].
  have Her : 0 <= e %/ 2.
  + rewrite divz_ge0 1://.
    exact He0.
  have Heq : e = 2 * (e %/ 2).
  + rewrite {1}(divz_eq e 2) Heven /=.
    exact (Ring.IntID.mulrC (e %/ 2) 2).
  rewrite /factor_product !PCM.big_cons /predT /=.
  rewrite split2_children_evenE 1:He0 1:Heven /=.
  trivial.
  rewrite flatten_cons PCM.big_cat !PCM.big_cons /predT /=.
  rewrite {1}Heq factor_split2 1:Hm 1:Her.
  rewrite PCM.big_nil mulr1.
  have IH' :
      PCM.big predT (factor a (2 * m)) es =
      PCM.big predT (factor a m) (flatten (map split2_children es)).
  + exact (IH Hes).
  rewrite IH'.
  rewrite /predT.
  done.
qed.

lemma quadratic_roots_identity (x u s : poly) :
  (x - u) * (x - (s - u)) =
    x * x - x * s + u * (s - u).
proof.
  rewrite mulrBl !mulrBr.
  rewrite [x * u]mulrC.
  rewrite !opprB addrACA sub_cancel_middle.
  rewrite -!addrA.
  rewrite [(- (u * u)) - x * s]NTRUPoly.PolyComRing.addrC.
  by rewrite
    [u * s + (-(x * s) - u * u)]NTRUPoly.PolyComRing.addrCA.
qed.

lemma difference_cubes (x y : poly) :
  exp x 3 - exp y 3 =
    (x - y) * (x * x + x * y + y * y).
proof.
  rewrite (NTRUPoly.BigPoly.subrXX x y 3) 1://.
  congr.
  rewrite range_ltn 1:// range_ltn 1:// range_ltn 1:// range_geq 1://.
  rewrite !PCA.big_cons PCA.big_nil /predT /=.
  rewrite !expr0 !expr1 !expr2 !mulr1 !mul1r.
  rewrite addr0 addrA.
  done.
qed.

lemma zeta192_pair_sum :
  exp zeta_field 192 + exp zeta_field 384 = -one.
proof.
  rewrite zeta192E zeta384E.
  apply CycloFq.asint_inj.
  by rewrite CycloFq.addE CycloFq.oppE CycloFq.oneE
             !incyclocoeffK /q /=.
qed.

lemma zeta192_pair_product :
  exp zeta_field 192 * exp zeta_field 384 = one.
proof.
  rewrite zeta192E zeta384E.
  apply CycloFq.asint_inj.
  by rewrite CycloFq.mulE CycloFq.oneE !incyclocoeffK /q /=.
qed.

lemma zeta_shift_192 (e : int) :
  0 <= e =>
  exp zeta_field (e + 192) =
    exp zeta_field e * exp zeta_field 192.
proof.
  move=> He.
  by rewrite CycloFqField.exprD_nneg 1:He 1://.
qed.

lemma zeta_shift_384 (e : int) :
  0 <= e =>
  exp zeta_field (e + 384) =
    exp zeta_field e * exp zeta_field 384.
proof.
  move=> He.
  by rewrite CycloFqField.exprD_nneg 1:He 1://.
qed.

lemma zeta_shifted_pair_sum (e : int) :
  0 <= e =>
  exp zeta_field (e + 192) + exp zeta_field (e + 384) =
    -(exp zeta_field e).
proof.
  move=> He.
  rewrite zeta_shift_192 1:He zeta_shift_384 1:He.
  rewrite -CycloFqField.mulrDr zeta192_pair_sum.
  by rewrite CycloFqField.mulrN1.
qed.

lemma zeta_shifted_pair_product (e : int) :
  0 <= e =>
  exp zeta_field (e + 192) * exp zeta_field (e + 384) =
    exp zeta_field e * exp zeta_field e.
proof.
  move=> He.
  rewrite zeta_shift_192 1:He zeta_shift_384 1:He.
  rewrite CycloFqField.mulrACA zeta192_pair_product.
  by rewrite CycloFqField.mulr1.
qed.

lemma poly_zeta_shifted_pair_sum (e : int) :
  0 <= e =>
  polyC (exp zeta_field (e + 192)) +
    polyC (exp zeta_field (e + 384)) =
  -(polyC (exp zeta_field e)).
proof.
  move=> He.
  rewrite -polyCD zeta_shifted_pair_sum 1:He.
  by rewrite polyCN.
qed.

lemma poly_zeta_shifted_pair_product (e : int) :
  0 <= e =>
  polyC (exp zeta_field (e + 192)) *
    polyC (exp zeta_field (e + 384)) =
  polyC (exp zeta_field e) * polyC (exp zeta_field e).
proof.
  move=> He.
  rewrite -!polyCM zeta_shifted_pair_product 1:He.
  done.
qed.

lemma factor_split3 (a : poly) (m r : int) :
  0 <= m =>
  0 <= r =>
  factor a (3 * m) (3 * r) =
    factor a m r *
      (factor a m (r + 192) * factor a m (r + 384)).
proof.
  move=> Hm Hr.
  rewrite /factor.
  have Ha : exp a (3 * m) = exp (exp a m) 3.
  + rewrite [3 * m]Ring.IntID.mulrC.
    exact (exprM a m 3).
  have Hz : exp zeta_field (3 * r) = exp (exp zeta_field r) 3.
  + rewrite [3 * r]Ring.IntID.mulrC.
    exact (CycloFqField.exprM zeta_field r 3).
  rewrite Ha Hz.
  have Hsum :
      polyC (exp zeta_field (r + 192)) +
        polyC (exp zeta_field (r + 384)) =
      -(polyC (exp zeta_field r)).
  + exact (poly_zeta_shifted_pair_sum r Hr).
  have Hproduct :
      polyC (exp zeta_field (r + 192)) *
        polyC (exp zeta_field (r + 384)) =
      polyC (exp zeta_field r) * polyC (exp zeta_field r).
  + exact (poly_zeta_shifted_pair_product r Hr).
  have Hv :
      polyC (exp zeta_field (r + 384)) =
        -(polyC (exp zeta_field r)) -
          polyC (exp zeta_field (r + 192)).
  + apply/eq_sym.
    rewrite subr_eq addrC.
    rewrite -polyCD zeta_shifted_pair_sum 1:Hr polyCN.
    done.
  have Hproduct' :
      polyC (exp zeta_field (r + 192)) *
        (-(polyC (exp zeta_field r)) -
          polyC (exp zeta_field (r + 192))) =
      polyC (exp zeta_field r) * polyC (exp zeta_field r).
  + by rewrite -Hv.
  rewrite Hv.
  rewrite quadratic_roots_identity Hproduct'.
  rewrite mulrN opprK.
  rewrite -(polyCX (exp zeta_field r) 3) 1://.
  rewrite difference_cubes.
  done.
qed.

lemma div_add576_by3 (p : int) :
  (p + 576) %/ 3 = p %/ 3 + 192.
proof.
  have -> : p + 576 = 192 * 3 + p by ring.
  rewrite divzMDl 1://.
  exact (Ring.IntID.addrC 192 (p %/ 3)).
qed.

lemma div_add1152_by3 (p : int) :
  (p + 2 * 576) %/ 3 = p %/ 3 + 384.
proof.
  have -> : p + 2 * 576 = 384 * 3 + p by ring.
  rewrite divzMDl 1://.
  exact (Ring.IntID.addrC 384 (p %/ 3)).
qed.

lemma split3_children_multipleE (p : int) :
  split3_children p = [p %/ 3; p %/ 3 + 192; p %/ 3 + 384].
proof.
  rewrite /split3_children /ell /=.
  rewrite div_add576_by3 div_add1152_by3.
  done.
qed.

lemma factor_product_split3 (a : poly) (m : int) (es : int list) :
  0 <= m =>
  all (fun e => 0 <= e /\ e %% 3 = 0) es =>
  factor_product a (3 * m) es =
    factor_product a m (flatten (map split3_children es)).
proof.
  move=> Hm.
  elim es => [|e es IH] /=.
  + by rewrite /factor_product !PCM.big_nil.
  move=> [[He0 Hmultiple] Hes].
  have Her : 0 <= e %/ 3.
  + rewrite divz_ge0 1://.
    exact He0.
  have Heq : e = 3 * (e %/ 3).
  + rewrite {1}(divz_eq e 3) Hmultiple /=.
    exact (Ring.IntID.mulrC (e %/ 3) 3).
  rewrite /factor_product !PCM.big_cons /predT /=.
  rewrite split3_children_multipleE /=.
  trivial.
  rewrite flatten_cons PCM.big_cat !PCM.big_cons /predT /=.
  rewrite {1}Heq factor_split3 1:Hm 1:Her.
  rewrite PCM.big_nil mulr1.
  have IH' :
      PCM.big predT (factor a (3 * m)) es =
      PCM.big predT (factor a m) (flatten (map split3_children es)).
  + exact (IH Hes).
  rewrite IH' /predT.
  done.
qed.

lemma roots_initial_multiple3 :
  all (fun e => 0 <= e /\ e %% 3 = 0) roots_initial.
proof. by rewrite /roots_initial /ell /=. qed.

lemma roots_after_radix3_even :
  all (fun e => 0 <= e /\ e %% 2 = 0) roots_after_radix3.
proof.
  by rewrite /roots_after_radix3 /roots_initial /split3_children /ell /=.
qed.

lemma roots_after_radix2_64_even :
  all (fun e => 0 <= e /\ e %% 2 = 0) roots_after_radix2_64.
proof.
  rewrite /roots_after_radix2_64 /roots_after_radix3 /roots_initial.
  by rewrite /split3_children /split2_children /ell /=.
qed.

lemma roots_after_radix2_32_even :
  all (fun e => 0 <= e /\ e %% 2 = 0) roots_after_radix2_32.
proof.
  rewrite /roots_after_radix2_32 /roots_after_radix2_64.
  rewrite /roots_after_radix3 /roots_initial.
  by rewrite /split3_children /split2_children /ell /=.
qed.

lemma roots_after_radix2_16_even :
  all (fun e => 0 <= e /\ e %% 2 = 0) roots_after_radix2_16.
proof.
  rewrite /roots_after_radix2_16 /roots_after_radix2_32.
  rewrite /roots_after_radix2_64 /roots_after_radix3 /roots_initial.
  by rewrite /split3_children /split2_children /ell /=.
qed.

lemma roots_after_radix2_8_even :
  all (fun e => 0 <= e /\ e %% 2 = 0) roots_after_radix2_8.
proof.
  rewrite /roots_after_radix2_8 /roots_after_radix2_16.
  rewrite /roots_after_radix2_32 /roots_after_radix2_64.
  rewrite /roots_after_radix3 /roots_initial.
  by rewrite /split3_children /split2_children /ell /=.
qed.

lemma factor_roots_initial_to_radix3 (a : poly) :
  factor_product a 96 roots_initial =
    factor_product a 32 roots_after_radix3.
proof.
  rewrite /roots_after_radix3.
  exact (factor_product_split3 a 32 roots_initial _ roots_initial_multiple3).
qed.

lemma factor_roots_radix3_to_radix2_64 (a : poly) :
  factor_product a 32 roots_after_radix3 =
    factor_product a 16 roots_after_radix2_64.
proof.
  rewrite /roots_after_radix2_64.
  exact
    (factor_product_split2 a 16 roots_after_radix3 _
      roots_after_radix3_even).
qed.

lemma factor_roots_radix2_64_to_radix2_32 (a : poly) :
  factor_product a 16 roots_after_radix2_64 =
    factor_product a 8 roots_after_radix2_32.
proof.
  rewrite /roots_after_radix2_32.
  exact
    (factor_product_split2 a 8 roots_after_radix2_64 _
      roots_after_radix2_64_even).
qed.

lemma factor_roots_radix2_32_to_radix2_16 (a : poly) :
  factor_product a 8 roots_after_radix2_32 =
    factor_product a 4 roots_after_radix2_16.
proof.
  rewrite /roots_after_radix2_16.
  exact
    (factor_product_split2 a 4 roots_after_radix2_32 _
      roots_after_radix2_32_even).
qed.

lemma factor_roots_radix2_16_to_radix2_8 (a : poly) :
  factor_product a 4 roots_after_radix2_16 =
    factor_product a 2 roots_after_radix2_8.
proof.
  rewrite /roots_after_radix2_8.
  exact
    (factor_product_split2 a 2 roots_after_radix2_16 _
      roots_after_radix2_16_even).
qed.

lemma factor_roots_radix2_8_to_radix2_4 (a : poly) :
  factor_product a 2 roots_after_radix2_8 =
    factor_product a 1 roots_after_radix2_4.
proof.
  rewrite /roots_after_radix2_4.
  exact
    (factor_product_split2 a 1 roots_after_radix2_8 _
      roots_after_radix2_8_even).
qed.

lemma factor_split_tree (a : poly) :
  factor_product a 96 roots_initial =
    factor_product a 1 figure22_indices192.
proof.
  rewrite factor_roots_initial_to_radix3.
  rewrite factor_roots_radix3_to_radix2_64.
  rewrite factor_roots_radix2_64_to_radix2_32.
  rewrite factor_roots_radix2_32_to_radix2_16.
  rewrite factor_roots_radix2_16_to_radix2_8.
  rewrite factor_roots_radix2_8_to_radix2_4.
  change
    (factor_product a 1 generated_terminal_exponents192 =
     factor_product a 1 figure22_indices192).
  rewrite generated_terminal_scheduleE.
  done.
qed.

lemma scheduled_factorization (a : poly) :
  factor_product a 1 figure22_indices192 =
    exp a 192 - exp a 96 + poly1.
proof.
  rewrite -(factor_split_tree a).
  exact (initial_factorization a).
qed.

(* Re-index the mathematical exponent schedule by the concrete terminal
   values consumed by the 192 four-coefficient basemul blocks. *)

op terminal_root_field (i : int) : cyclocoeff =
  incyclocoeff (terminal_value i).

op terminal_factor_product (a : poly) : poly =
  PCM.big predT
    (fun i => exp a 1 - polyC (terminal_root_field i))
    (range 0 192).

lemma terminal_root_fieldE (i : int) :
  0 <= i < 192 =>
  terminal_root_field i = exp zeta_field (figure22_index i).
proof.
  move=> Hi.
  have [He0 _] := figure22_index_range i Hi.
  rewrite /terminal_root_field /terminal_value.
  rewrite -incyclocoeff_mod.
  rewrite zeta_field_expE 1:He0.
  done.
qed.

lemma figure22_indices_rangeE :
  map figure22_index (range 0 192) = figure22_indices192.
proof.
  rewrite /figure22_index -size_figure22_indices192.
  exact (map_nth_range witness figure22_indices192).
qed.

lemma terminal_factor_productE (a : poly) :
  terminal_factor_product a = factor_product a 1 figure22_indices192.
proof.
  rewrite /terminal_factor_product /factor_product -figure22_indices_rangeE.
  rewrite PCM.big_mapT /(\o) /=.
  apply PCM.eq_big_seq => i Hi.
  have Hirange : 0 <= i < 192 by move: Hi; rewrite mem_range.
  change
    (exp a 1 - polyC (terminal_root_field i) =
     exp a 1 - polyC (exp zeta_field (figure22_index i))).
  rewrite terminal_root_fieldE 1:Hirange.
  done.
qed.

lemma terminal_linear_factorization :
  terminal_factor_product X = exp X 192 - exp X 96 + poly1.
proof.
  rewrite terminal_factor_productE.
  exact (scheduled_factorization X).
qed.

lemma terminal_quartic_factorization :
  terminal_factor_product (exp X 4) =
    exp X 768 - exp X 384 + poly1.
proof.
  rewrite terminal_factor_productE scheduled_factorization.
  rewrite -!exprM /=.
  done.
qed.

lemma terminal_quartic_factorization_explicit :
  PCM.big predT
      (fun i => exp X 4 - polyC (terminal_root_field i))
      (range 0 192) =
    exp X 768 - exp X 384 + poly1.
proof.
  rewrite -terminal_quartic_factorization.
  rewrite /terminal_factor_product expr1.
  done.
qed.

lemma figure22_indices192_uniq :
  uniq figure22_indices192.
proof. by rewrite /figure22_indices192 /=. qed.
