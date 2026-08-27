(* Algebraic reconstruction for the first inverse NTT layer. *)
require import AllCore IntDiv List Ring StdBigop StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array768.
require import NTRUPlus768CyclotomicFactorization.
require import NTRUPlus768EvaluationSemantics.
require import NTRUPlus768TerminalRepresentation.
require import NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768ForwardNTTRadix3Semantics.
require import NTRUPlus768ForwardNTTRadix2_4Semantics.
require import NTRUPlus768NTTSchedule.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768PolyBasemulAlgebra NTRUPlus768PolyBasemulProof.
require import NTRUPlus768InvNTTRadix2_4.
require import NTRUPlus768InvNTTRadix2_4Algebra NTRUPlus768InvNTTRadix2_4Proof.

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

instance ring with NTRUPoly.poly
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

op invntt_radix2_4_schedule_exp (b : int) : int =
  zetas192_exp
    (NTRUPlus768InvNTTRadix2_4Algebra.invntt_radix2_4_schedule_index b).

lemma invntt_radix2_4_schedule_expE (b : int) :
  0 <= b < 96 =>
  invntt_radix2_4_schedule_exp b = terminal_exp (95 - b).
proof.
  move=> Hb.
  rewrite /invntt_radix2_4_schedule_exp
          /NTRUPlus768InvNTTRadix2_4Algebra.invntt_radix2_4_schedule_index
          /invntt_rev_index /terminal_exp /terminal_exponents96.
  have Hidx : 0 <= 95 - b < 96 by smt().
  rewrite nth_drop 1:// 1:/#.
  have -> : 95 - b + 96 = 191 - b by smt().
  done.
qed.

lemma terminal_exp_reverse_sum_288 (b : int) :
  0 <= b < 96 =>
  terminal_exp b + terminal_exp (95 - b) = 288.
proof.
  move=> Hb.
  have Hcases :
      b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/
      b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/
      b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/
      b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/
      b = 26 \/ b = 27 \/ b = 28 \/ b = 29 \/ b = 30 \/ b = 31 \/
      b = 32 \/ b = 33 \/ b = 34 \/ b = 35 \/ b = 36 \/ b = 37 \/
      b = 38 \/ b = 39 \/ b = 40 \/ b = 41 \/ b = 42 \/ b = 43 \/
      b = 44 \/ b = 45 \/ b = 46 \/ b = 47 \/ b = 48 \/ b = 49 \/
      b = 50 \/ b = 51 \/ b = 52 \/ b = 53 \/ b = 54 \/ b = 55 \/
      b = 56 \/ b = 57 \/ b = 58 \/ b = 59 \/ b = 60 \/ b = 61 \/
      b = 62 \/ b = 63 \/ b = 64 \/ b = 65 \/ b = 66 \/ b = 67 \/
      b = 68 \/ b = 69 \/ b = 70 \/ b = 71 \/ b = 72 \/ b = 73 \/
      b = 74 \/ b = 75 \/ b = 76 \/ b = 77 \/ b = 78 \/ b = 79 \/
      b = 80 \/ b = 81 \/ b = 82 \/ b = 83 \/ b = 84 \/ b = 85 \/
      b = 86 \/ b = 87 \/ b = 88 \/ b = 89 \/ b = 90 \/ b = 91 \/
      b = 92 \/ b = 93 \/ b = 94 \/ b = 95 by smt().
  rewrite /terminal_exp /terminal_exponents96 /zetas192_exponents /=.
  smt().
qed.

lemma invntt_radix2_4_schedule_sumE (b : int) :
  0 <= b < 96 =>
  invntt_radix2_4_schedule_exp b + terminal_exp b = 288.
proof.
  move=> Hb.
  rewrite (invntt_radix2_4_schedule_expE b Hb).
  rewrite addrC.
  exact (terminal_exp_reverse_sum_288 b Hb).
qed.

lemma invntt_radix2_4_schedule_nonneg (b : int) :
  0 <= b < 96 =>
  0 <= invntt_radix2_4_schedule_exp b.
proof.
  move=> Hb.
  rewrite (invntt_radix2_4_schedule_expE b Hb).
  have Hidx : 0 <= 95 - b < 96 by smt().
  exact (terminal_exp_nonneg (95 - b) Hidx).
qed.

lemma root_poly_288E :
  root_poly 288 = -poly1.
proof.
  by rewrite /root_poly zeta288E NTRUPoly.polyCN.
qed.

lemma zeta_complement_product_neg1 (e e' : int) :
  0 <= e =>
  0 <= e' =>
  e' + e = 288 =>
  CycloFq.( * ) (CycloFq.exp zeta_field e')
    (CycloFq.exp zeta_field e) = CycloFq.([-]) CycloFq.one.
proof.
  move=> He He' Hsum.
  rewrite zeta_field_expE 1:He' zeta_field_expE 1:He.
  rewrite -CycloFq.incyclocoeffM.
  have -> :
      NTRUPlus768NTTSchedule.zeta_root ^ e' *
      NTRUPlus768NTTSchedule.zeta_root ^ e =
      NTRUPlus768NTTSchedule.zeta_root ^ (e' + e).
  + by rewrite Ring.IntID.exprD_nneg 1:He' 1:He.
  rewrite Hsum.
  move: zeta288E.
  rewrite zeta_field_expE 1://.
  done.
qed.

lemma invntt_radix2_4_root_cancelE (b : int) :
  0 <= b < 96 =>
  root_poly (invntt_radix2_4_schedule_exp b) * root_poly (terminal_exp b) = -poly1.
proof.
  move=> Hb.
  rewrite /root_poly.
  have Hfield :
      CycloFq.( * )
        (CycloFq.exp zeta_field (invntt_radix2_4_schedule_exp b))
        (CycloFq.exp zeta_field (terminal_exp b)) =
      CycloFq.([-]) CycloFq.one
    by exact
      (zeta_complement_product_neg1
        (terminal_exp b) (invntt_radix2_4_schedule_exp b)
        (terminal_exp_nonneg b Hb)
        (invntt_radix2_4_schedule_nonneg b Hb)
        (invntt_radix2_4_schedule_sumE b Hb)).
  have -> :
      polyC (CycloFq.exp zeta_field (invntt_radix2_4_schedule_exp b)) *
      polyC (CycloFq.exp zeta_field (terminal_exp b)) =
      polyC
        (CycloFq.( * )
          (CycloFq.exp zeta_field (invntt_radix2_4_schedule_exp b))
          (CycloFq.exp zeta_field (terminal_exp b))).
  + apply/eq_sym.
    apply NTRUPoly.polyCM.
  by rewrite Hfield NTRUPoly.polyCN.
qed.

lemma terminal_represents_factor_eqm_left
    (input : W16.t Array768.t) (p : NTRUPoly.poly) (b : int) :
  terminal_represents input p =>
  0 <= b < 96 =>
  factor_eqm 4 (terminal_exp b)
    p (segment_poly input (8 * b) 4).
proof.
  move=> Hrep Hb.
  have Hk : 0 <= 2 * b < 192 by smt().
  have Hlocal :
      eqm4 (2 * b) p (segment_poly input (8 * b) 4).
  + have -> : 8 * b = 4 * (2 * b) by ring.
    rewrite segment_poly4_block_polyE 1:Hk.
    exact (Hrep (2 * b) Hk).
  rewrite /eqm4 /quartic_modulus terminal_root_fieldE 1:Hk in Hlocal.
  move: Hlocal.
  have Hfig := figure22_index_relation (2 * b) Hk.
  have -> : figure22_index (2 * b) = terminal_exp b.
  + move: Hfig.
    have -> : (2 * b) %% 2 = 0 by smt().
    have -> : (2 * b) %/ 2 = b by smt().
    done.
  rewrite /factor_eqm /schedule_factor_modulus.
  done.
qed.

lemma terminal_represents_factor_eqm_right
    (input : W16.t Array768.t) (p : NTRUPoly.poly) (b : int) :
  terminal_represents input p =>
  0 <= b < 96 =>
  factor_eqm 4 (terminal_exp b + 288)
    p (segment_poly input (8 * b + 4) 4).
proof.
  move=> Hrep Hb.
  have Hk : 0 <= 2 * b + 1 < 192 by smt().
  have Hlocal :
      eqm4 (2 * b + 1) p (segment_poly input (8 * b + 4) 4).
  + have -> : 8 * b + 4 = 4 * (2 * b + 1) by ring.
    rewrite segment_poly4_block_polyE 1:Hk.
    exact (Hrep (2 * b + 1) Hk).
  rewrite /eqm4 /quartic_modulus terminal_root_fieldE 1:Hk in Hlocal.
  move: Hlocal.
  have Hfig := figure22_index_relation (2 * b + 1) Hk.
  have -> : figure22_index (2 * b + 1) = terminal_exp b + 288.
  + move: Hfig.
    have -> : (2 * b + 1) %% 2 = 1 by smt().
    have -> : (2 * b + 1) %/ 2 = b by smt().
    done.
  rewrite /factor_eqm /schedule_factor_modulus.
  done.
qed.

lemma invntt_radix2_4_segment_leftE
    (input output : W16.t Array768.t) (b : int) :
  0 <= b < 96 =>
  NTRUPlus768InvNTTRadix2_4Algebra.invntt_radix2_4_algebra input output =>
  segment_poly output (8 * b) 4 =
    radix2_4_eval_poly input (8 * b) 0.
proof.
  move=> Hb Halg.
  apply segment_poly_radix2_4_evalE; first smt().
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 8 * b) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768InvNTTRadix2_4Algebra.invntt_radix2_4_math
          /NTRUPlus768InvNTTRadix2_4Proof.invntt_radix2_4_block_id
          /NTRUPlus768InvNTTRadix2_4Proof.invntt_radix2_4_block_base
          /NTRUPlus768InvNTTRadix2_4Proof.invntt_radix2_4_lane_index
          /NTRUPlus768InvNTTRadix2_4Proof.invntt_radix2_4_block_offset
          /NTRUPlus768InvNTTRadix2_4Algebra.double_block
          /NTRUPlus768InvNTTRadix2_4Algebra.block.
  have -> : (i + 8 * b) %/ 8 = b by smt().
  have -> : (i + 8 * b) %% 8 = i by smt().
  move=> Hcoeff.
  move: Hcoeff; simplify.
  rewrite ifT 1:/# ifT 1:/# /=.
  move=> Hcoeff.
  rewrite /NTRUPlus768InvNTTRadix2_4Algebra.invntt_radix2_4_pair_math_at
          /NTRUPlus768InvNTTRadix2_4Algebra.invntt_radix2_4_pair_math
          /NTRUPlus768InvNTTRadix2_4Proof.double_block
          [8 * b + i]addrC in Hcoeff.
  rewrite /schedule_root /zeta_root /q /=.
  exact Hcoeff.
qed.

lemma poly_sub_mul_reorder
    (a b c x : NTRUPoly.poly) :
  (a - b) * c * x = c * (a * x) - c * (b * x).
proof. ring. qed.

op invntt_radix2_4_scaled_diff_poly
    (a : W16.t Array768.t) (base c : int) : NTRUPoly.poly =
  PCA.bigi predT
    (fun i =>
      polyC
        (lift_int
          ((coeff a.[i + base + 4] +
            Int.([-]) (coeff a.[i + base])) * c)) *
      exp X i)
    0 4.

lemma invntt_radix2_4_scaled_diff_polyE
    (a : W16.t Array768.t) (base c : int) :
  invntt_radix2_4_scaled_diff_poly a base c =
  polyC (lift_int c) *
    (segment_poly a (base + 4) 4 - segment_poly a base 4).
proof.
  rewrite /invntt_radix2_4_scaled_diff_poly /segment_poly.
  have Hdist_hi :
      polyC (lift_int c) *
        PCA.bigi predT
          (fun i => polyC (lift_word a.[i + (base + 4)]) * exp X i)
          0 4 =
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c) *
            (polyC (lift_word a.[i + (base + 4)]) * exp X i))
        0 4.
  + exact
      (PCA.mulr_sumr predT
        (fun i => polyC (lift_word a.[i + (base + 4)]) * exp X i)
        (range 0 4) (polyC (lift_int c))).
  have Hdist_lo :
      polyC (lift_int c) *
        PCA.bigi predT
          (fun i => polyC (lift_word a.[i + base]) * exp X i)
          0 4 =
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c) *
            (polyC (lift_word a.[i + base]) * exp X i))
        0 4.
  + exact
      (PCA.mulr_sumr predT
        (fun i => polyC (lift_word a.[i + base]) * exp X i)
        (range 0 4) (polyC (lift_int c))).
  have Hsplit :
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c) *
            (polyC (lift_word a.[i + (base + 4)]) * exp X i))
        0 4 -
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c) *
            (polyC (lift_word a.[i + base]) * exp X i))
        0 4 =
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c) *
            (polyC (lift_word a.[i + (base + 4)]) * exp X i) -
          polyC (lift_int c) *
            (polyC (lift_word a.[i + base]) * exp X i))
        0 4.
  + exact
      (PCA.sumrB predT
        (fun i =>
          polyC (lift_int c) *
            (polyC (lift_word a.[i + (base + 4)]) * exp X i))
        (fun i =>
          polyC (lift_int c) *
            (polyC (lift_word a.[i + base]) * exp X i))
        (range 0 4)).
  have Houter :
      polyC (lift_int c) *
        (PCA.bigi predT
           (fun i => polyC (lift_word a.[i + (base + 4)]) * exp X i)
           0 4 -
         PCA.bigi predT
           (fun i => polyC (lift_word a.[i + base]) * exp X i)
           0 4) =
      polyC (lift_int c) *
        PCA.bigi predT
          (fun i => polyC (lift_word a.[i + (base + 4)]) * exp X i)
          0 4 -
      polyC (lift_int c) *
        PCA.bigi predT
          (fun i => polyC (lift_word a.[i + base]) * exp X i)
          0 4 by ring.
  rewrite Houter Hdist_hi Hdist_lo Hsplit.
  apply PCA.eq_big_int => i Hi.
  rewrite /lift_word /lift_int /=.
  rewrite CycloFq.incyclocoeffM CycloFq.incyclocoeffD
          CycloFq.incyclocoeffN.
  rewrite NTRUPoly.polyCM NTRUPoly.polyCD NTRUPoly.polyCN.
  have Hidx : i + base + 4 = i + (base + 4) by ring.
  rewrite Hidx.
  apply poly_sub_mul_reorder.
qed.

lemma segment_poly_scaled_diffE
    (input output : W16.t Array768.t)
    (input_base output_base c : int) :
  (forall i, 0 <= i < 4 =>
    coeff output.[i + output_base] %% q =
    ((coeff input.[i + input_base + 4] +
      Int.([-]) (coeff input.[i + input_base])) * c) %% q) =>
  segment_poly output output_base 4 =
    invntt_radix2_4_scaled_diff_poly input input_base c.
proof.
  move=> Hcoeff.
  rewrite /segment_poly /invntt_radix2_4_scaled_diff_poly.
  apply PCA.eq_big_int => i Hi.
  have Hmod := Hcoeff i Hi.
  have Elift :
      lift_word output.[i + output_base] =
      lift_int
        ((coeff input.[i + input_base + 4] +
          Int.([-]) (coeff input.[i + input_base])) * c).
  + rewrite /lift_word.
    apply lift_int_eq.
    exact Hmod.
  by rewrite /= Elift.
qed.

lemma invntt_radix2_4_segment_rightE
    (input output : W16.t Array768.t) (b : int) :
  0 <= b < 96 =>
  NTRUPlus768InvNTTRadix2_4Algebra.invntt_radix2_4_algebra input output =>
  segment_poly output (8 * b + 4) 4 =
    invntt_radix2_4_scaled_diff_poly
      input (8 * b) (NTRUPlus768InvNTTRadix2_4Algebra.invntt_radix2_4_zeta_root b).
proof.
  move=> Hb Halg.
  apply segment_poly_scaled_diffE.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + (8 * b + 4)) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768InvNTTRadix2_4Algebra.invntt_radix2_4_math
          /NTRUPlus768InvNTTRadix2_4Proof.invntt_radix2_4_block_id
          /NTRUPlus768InvNTTRadix2_4Proof.invntt_radix2_4_block_base
          /NTRUPlus768InvNTTRadix2_4Proof.invntt_radix2_4_lane_index
          /NTRUPlus768InvNTTRadix2_4Proof.invntt_radix2_4_block_offset
          /NTRUPlus768InvNTTRadix2_4Algebra.double_block
          /NTRUPlus768InvNTTRadix2_4Algebra.block.
  have -> : (i + (8 * b + 4)) %/ 8 = b by smt().
  have -> : (i + (8 * b + 4)) %% 8 = i + 4 by smt().
  move=> Hcoeff.
  move: Hcoeff; simplify.
  rewrite ifF 1:/# ifF 1:/# /=.
  move=> Hcoeff.
  rewrite /NTRUPlus768InvNTTRadix2_4Algebra.invntt_radix2_4_pair_math_at
          /NTRUPlus768InvNTTRadix2_4Algebra.invntt_radix2_4_pair_math
          /NTRUPlus768InvNTTRadix2_4Proof.double_block
          [8 * b + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma invntt_radix2_4_output_segmentE
    (input output : W16.t Array768.t) (b : int) :
  0 <= b < 96 =>
  NTRUPlus768InvNTTRadix2_4Algebra.invntt_radix2_4_algebra input output =>
  segment_poly output (8 * b) 8 =
    radix2_4_eval_poly input (8 * b) 0 +
    invntt_radix2_4_scaled_diff_poly
      input (8 * b) (NTRUPlus768InvNTTRadix2_4Algebra.invntt_radix2_4_zeta_root b) *
      exp X 4.
proof.
  move=> Hb Halg.
  rewrite segment_poly_split2_4.
  rewrite /segment2_4_poly.
  rewrite (invntt_radix2_4_segment_leftE input output b Hb Halg).
  rewrite (invntt_radix2_4_segment_rightE input output b Hb Halg).
  done.
qed.

lemma invntt_radix2_4_interpolation_identity
    (s t u r x : NTRUPoly.poly) :
  u * r = -poly1 =>
  s * (x - r) + t * (x + r) +
      u * (t * (x + r) - s * (x - r)) * x =
    (t - s) * u * ((x - r) * (x + r)).
proof.
  move=> Hur.
  have Hzero : poly1 + u * r = poly0 by rewrite Hur; ring.
  have Hfactor :
      s * (x - r) + t * (x + r) +
          u * (t * (x + r) - s * (x - r)) * x =
        (t - s) * u * ((x - r) * (x + r)) +
          (poly1 + u * r) * ((s + t) * x + (t - s) * r) by ring.
  rewrite Hzero in Hfactor.
  rewrite Hfactor.
  ring.
qed.

lemma invntt_radix2_4_abstract_recombine
    (p a0 a1 u r x : NTRUPoly.poly) :
  u * r = -poly1 =>
  (exists s, a0 - p = s * (x - r)) =>
  (exists t, a1 - p = t * (x + r)) =>
  exists h,
    a0 + a1 + u * (a1 - a0) * x - (p + p) =
      h * ((x - r) * (x + r)).
proof.
  move=> Hur [s Hs] [t Ht].
  exists ((t - s) * u).
  have Hlhs :
      a0 + a1 + u * (a1 - a0) * x - (p + p) =
      (a0 - p) + (a1 - p) + u * ((a1 - p) - (a0 - p)) * x by ring.
  rewrite Hlhs Hs Ht.
  exact (invntt_radix2_4_interpolation_identity s t u r x Hur).
qed.

lemma invntt_radix2_4_recombine_factor_eqm
    (p a0 a1 : NTRUPoly.poly) (e e' : int) :
  0 <= e =>
  0 <= e' =>
  e' + e = 288 =>
  factor_eqm 4 e p a0 =>
  factor_eqm 4 (e + 288) p a1 =>
  factor_eqm 8 (2 * e) (p + p)
    (a0 + a1 + root_poly e' * (a1 - a0) * exp X 4).
proof.
  move=> He He' Hsum Hleft Hright.
  rewrite /factor_eqm.
  rewrite schedule_modulus_split2_4 1:He.
  rewrite /schedule_factor_modulus /root_poly.
  rewrite zeta_shift_288 1:He.
  rewrite NTRUPoly.polyCN.
  have Hplus :
      exp X 4 - (-polyC (CycloFq.exp zeta_field e)) =
      exp X 4 + polyC (CycloFq.exp zeta_field e).
  + ring.
  rewrite Hplus.
  apply (invntt_radix2_4_abstract_recombine
    p a0 a1
    (polyC (CycloFq.exp zeta_field e'))
    (polyC (CycloFq.exp zeta_field e))
    (exp X 4)).
  + have Hcancel := zeta_complement_product_neg1 e e' He He' Hsum.
    have -> :
        polyC (CycloFq.exp zeta_field e') *
          polyC (CycloFq.exp zeta_field e) =
        polyC
          (CycloFq.( * ) (CycloFq.exp zeta_field e')
            (CycloFq.exp zeta_field e)).
    - apply/eq_sym.
      apply NTRUPoly.polyCM.
    by rewrite Hcancel NTRUPoly.polyCN.
  + move: Hleft.
    rewrite /factor_eqm /schedule_factor_modulus /root_poly.
    done.
  + move: Hright.
    rewrite /factor_eqm /schedule_factor_modulus /root_poly.
    rewrite zeta_shift_288 1:He NTRUPoly.polyCN.
    rewrite Hplus.
    done.
qed.
