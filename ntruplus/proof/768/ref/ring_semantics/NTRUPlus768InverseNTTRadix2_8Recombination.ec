(* Algebraic reconstruction for the second inverse NTT layer. *)
require import AllCore IntDiv List Ring StdBigop StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array768.
require import NTRUPlus768CyclotomicFactorization.
require import NTRUPlus768EvaluationSemantics.
require import NTRUPlus768TerminalRepresentation.
require import NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768ForwardNTTRadix3Semantics.
require import NTRUPlus768ForwardNTTRadix2_8Semantics.
require import NTRUPlus768ForwardNTTRadix2_4Semantics.
require import NTRUPlus768NTTSchedule.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768PolyBasemulAlgebra NTRUPlus768PolyBasemulProof.
require import NTRUPlus768InvNTTRadix2_4.
require import NTRUPlus768InvNTTRadix2_4Algebra NTRUPlus768InvNTTRadix2_4Proof.
require import NTRUPlus768InvNTTRadix2_8.
require import NTRUPlus768InvNTTRadix2_8Algebra NTRUPlus768InvNTTRadix2_8Proof.
require import NTRUPlus768NTTRadix2_8Algebra.
require import NTRUPlus768InverseNTTRadix2_4Recombination.
require import NTRUPlus768InverseNTTRadix2_4Semantics.

import NTRUPoly.BigPoly.

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

op invntt_radix2_8_schedule_exp (b : int) : int =
  zetas192_exp
    (NTRUPlus768InvNTTRadix2_8Algebra.invntt_radix2_8_schedule_index b).

lemma invntt_radix2_8_schedule_forwardE (b : int) :
  0 <= b < 48 =>
  invntt_radix2_8_schedule_exp b = radix2_8_schedule_exp (47 - b).
proof.
  move=> Hb.
  rewrite /invntt_radix2_8_schedule_exp /radix2_8_schedule_exp.
  rewrite /NTRUPlus768InvNTTRadix2_8Algebra.invntt_radix2_8_schedule_index.
  rewrite /NTRUPlus768NTTRadix2_8Algebra.radix2_8_schedule_index.
  rewrite /NTRUPlus768InvNTTRadix2_8Algebra.nblocks /ntt_radix2_8_start.
  done.
qed.

lemma radix2_8_schedule_exp_nonneg (b : int) :
  0 <= b < 48 =>
  0 <= radix2_8_schedule_exp b.
proof.
  move=> Hb.
  have Hchild : 0 <= 2 * b < 96 by smt().
  have Hparent := radix2_4_parent_scheduleE (2 * b) Hchild.
  move: Hparent.
  rewrite (radix2_4_schedule_exp_terminalE (2 * b) Hchild).
  rewrite (_ : (2 * b) %% 2 = 0) 1:/#.
  rewrite (_ : (2 * b) %/ 2 = b) 1:/#.
  move=> Hparent.
  have Hterm := terminal_exp_nonneg (2 * b) Hchild.
  smt().
qed.

lemma invntt_radix2_8_child_scheduleE (b : int) :
  0 <= b < 48 =>
  2 * terminal_exp (2 * b + 1) =
    2 * terminal_exp (2 * b) + 288.
proof.
  move=> Hb.
  have Hleft : 0 <= 2 * b < 96 by smt().
  have Hright : 0 <= 2 * b + 1 < 96 by smt().
  have Heven := radix2_4_parent_scheduleE (2 * b) Hleft.
  have Hodd := radix2_4_parent_scheduleE (2 * b + 1) Hright.
  move: Heven Hodd.
  rewrite (radix2_4_schedule_exp_terminalE (2 * b) Hleft).
  rewrite (radix2_4_schedule_exp_terminalE (2 * b + 1) Hright).
  rewrite (_ : (2 * b) %% 2 = 0) 1:/#.
  rewrite (_ : (2 * b) %/ 2 = b) 1:/#.
  rewrite (_ : (2 * b + 1) %% 2 = 1) 1:/#.
  rewrite (_ : (2 * b + 1) %/ 2 = b) 1:/#.
  move=> Heven Hodd.
  smt().
qed.

lemma radix2_8_schedule_reverse_sum_288 (b : int) :
  0 <= b < 48 =>
  radix2_8_schedule_exp b + radix2_8_schedule_exp (47 - b) = 288.
proof.
  move=> Hb.
  have Hchild : 0 <= 2 * b < 96 by smt().
  have Hrevchild : 0 <= 95 - 2 * b < 96 by smt().
  have Hsum := terminal_exp_reverse_sum_288 (2 * b) Hchild.
  have Heven := radix2_4_parent_scheduleE (2 * b) Hchild.
  have Hodd := radix2_4_parent_scheduleE (95 - 2 * b) Hrevchild.
  move: Heven Hodd.
  rewrite (radix2_4_schedule_exp_terminalE (2 * b) Hchild).
  rewrite (radix2_4_schedule_exp_terminalE (95 - 2 * b) Hrevchild).
  rewrite (_ : (2 * b) %% 2 = 0) 1:/#.
  rewrite (_ : (2 * b) %/ 2 = b) 1:/#.
  rewrite (_ : (95 - 2 * b) %% 2 = 1) 1:/#.
  rewrite (_ : (95 - 2 * b) %/ 2 = 47 - b) 1:/#.
  move=> Heven Hodd.
  move: Hsum.
  smt().
qed.

lemma invntt_radix2_8_schedule_sumE (b : int) :
  0 <= b < 48 =>
  invntt_radix2_8_schedule_exp b + 2 * terminal_exp (2 * b) = 288.
proof.
  move=> Hb.
  have Hchild : 0 <= 2 * b < 96 by smt().
  have Hparent := radix2_4_parent_scheduleE (2 * b) Hchild.
  move: Hparent.
  rewrite (radix2_4_schedule_exp_terminalE (2 * b) Hchild).
  rewrite (_ : (2 * b) %% 2 = 0) 1:/#.
  rewrite (_ : (2 * b) %/ 2 = b) 1:/#.
  move=> Hparent.
  rewrite (invntt_radix2_8_schedule_forwardE b Hb).
  rewrite Hparent addrC.
  exact (radix2_8_schedule_reverse_sum_288 b Hb).
qed.

lemma invntt_radix2_8_schedule_nonneg (b : int) :
  0 <= b < 48 =>
  0 <= invntt_radix2_8_schedule_exp b.
proof.
  move=> Hb.
  rewrite (invntt_radix2_8_schedule_forwardE b Hb).
  have Hidx : 0 <= 47 - b < 48 by smt().
  exact (radix2_8_schedule_exp_nonneg (47 - b) Hidx).
qed.

lemma invntt_radix2_8_child_exp_nonneg (b : int) :
  0 <= b < 48 =>
  0 <= 2 * terminal_exp (2 * b).
proof.
  move=> Hb.
  have Hidx : 0 <= 2 * b < 96 by smt().
  have Hterm := terminal_exp_nonneg (2 * b) Hidx.
  smt().
qed.

lemma invntt_radix2_8_root_cancelE (b : int) :
  0 <= b < 48 =>
  root_poly (invntt_radix2_8_schedule_exp b) *
    root_poly (2 * terminal_exp (2 * b)) = -poly1.
proof.
  move=> Hb.
  rewrite /root_poly.
  have Hchild : 0 <= 2 * terminal_exp (2 * b).
  + have Hidx : 0 <= 2 * b < 96 by smt().
    have Hterm := terminal_exp_nonneg (2 * b) Hidx.
    smt().
  have Hfield :
      CycloFq.( * )
        (CycloFq.exp zeta_field (invntt_radix2_8_schedule_exp b))
        (CycloFq.exp zeta_field (2 * terminal_exp (2 * b))) =
      CycloFq.([-]) CycloFq.one.
  + exact
      (zeta_complement_product_neg1
        (2 * terminal_exp (2 * b)) (invntt_radix2_8_schedule_exp b)
        Hchild
        (invntt_radix2_8_schedule_nonneg b Hb)
        (invntt_radix2_8_schedule_sumE b Hb)).
  have -> :
      polyC (CycloFq.exp zeta_field (invntt_radix2_8_schedule_exp b)) *
        polyC (CycloFq.exp zeta_field (2 * terminal_exp (2 * b))) =
      polyC
        (CycloFq.( * )
          (CycloFq.exp zeta_field (invntt_radix2_8_schedule_exp b))
          (CycloFq.exp zeta_field (2 * terminal_exp (2 * b)))).
  + apply/eq_sym.
    apply NTRUPoly.polyCM.
  by rewrite Hfield NTRUPoly.polyCN.
qed.

lemma invntt_radix2_4_semantics_child_left
    (p : NTRUPoly.poly) (input : W16.t Array768.t) (b : int) :
  invntt_radix2_4_semantics p input =>
  0 <= b < 48 =>
  factor_eqm 8 (2 * terminal_exp (2 * b))
    (p + p)
    (segment_poly input (16 * b) 8).
proof.
  move=> Hsem Hb.
  rewrite /invntt_radix2_4_semantics in Hsem.
  have Hidx : 0 <= 2 * b < 96 by smt().
  have Hchild := Hsem (2 * b) Hidx.
  have Hbase : 8 * (2 * b) = 16 * b by ring.
  rewrite -Hbase.
  exact Hchild.
qed.

lemma invntt_radix2_4_semantics_child_right
    (p : NTRUPoly.poly) (input : W16.t Array768.t) (b : int) :
  invntt_radix2_4_semantics p input =>
  0 <= b < 48 =>
  factor_eqm 8 (2 * terminal_exp (2 * b) + 288)
    (p + p)
    (segment_poly input (16 * b + 8) 8).
proof.
  move=> Hsem Hb.
  rewrite /invntt_radix2_4_semantics in Hsem.
  have Hidx : 0 <= 2 * b + 1 < 96 by smt().
  have Hchild := Hsem (2 * b + 1) Hidx.
  have Hbase : 8 * (2 * b + 1) = 16 * b + 8 by ring.
  rewrite -Hbase.
  rewrite -(invntt_radix2_8_child_scheduleE b Hb).
  exact Hchild.
qed.

lemma invntt_radix2_8_segment_leftE
    (input output : W16.t Array768.t) (b : int) :
  0 <= b < 48 =>
  NTRUPlus768InvNTTRadix2_8Algebra.invntt_radix2_8_algebra input output =>
  segment_poly output (16 * b) 8 =
    segment_poly input (16 * b) 8 +
    segment_poly input (16 * b + 8) 8.
proof.
  move=> Hb Halg.
  have Hleft :
      segment_poly output (16 * b) 8 =
      radix2_8_eval_poly input (16 * b) 0.
  + apply segment_poly_radix2_8_evalE; first smt().
    move=> i Hi.
    have [_ Hcoeff] := Halg (i + 16 * b) _; first smt().
    move: Hcoeff.
    rewrite /NTRUPlus768InvNTTRadix2_8Algebra.invntt_radix2_8_math.
    rewrite /NTRUPlus768InvNTTRadix2_8Proof.invntt_radix2_8_block_id.
    rewrite /NTRUPlus768InvNTTRadix2_8Proof.invntt_radix2_8_block_base.
    rewrite /NTRUPlus768InvNTTRadix2_8Proof.invntt_radix2_8_lane_index.
    rewrite /NTRUPlus768InvNTTRadix2_8Proof.invntt_radix2_8_block_offset.
    rewrite /NTRUPlus768InvNTTRadix2_8Algebra.double_block.
    rewrite /NTRUPlus768InvNTTRadix2_8Algebra.block.
    have -> : (i + 16 * b) %/ 16 = b by smt().
    have -> : (i + 16 * b) %% 16 = i by smt().
    move=> Hcoeff.
    move: Hcoeff; simplify.
    rewrite ifT 1:/# ifT 1:/# /=.
    move=> Hcoeff.
    rewrite /NTRUPlus768InvNTTRadix2_8Algebra.invntt_radix2_8_pair_math_at
            /NTRUPlus768InvNTTRadix2_8Algebra.invntt_radix2_8_pair_math
            /NTRUPlus768InvNTTRadix2_8Proof.double_block
            [16 * b + i]addrC in Hcoeff.
    rewrite /schedule_root /zeta_root /q /=.
    exact Hcoeff.
  rewrite Hleft /radix2_8_eval_poly /root_poly.
  have Hroot0 :
      CycloFq.exp zeta_field 0 = CycloFq.one
    by rewrite zeta_field_expE 1:// /=.
  rewrite Hroot0.
  have Hone :
      NTRUPoly.polyC CycloFq.one = NTRUPoly.PolyComRing.oner by done.
  rewrite Hone.
  have Hshape :
      segment_poly input (16 * b + 8) 8 *
        NTRUPoly.PolyComRing.oner =
      segment_poly input (16 * b + 8) 8.
  + exact
      (NTRUPoly.PolyComRing.mulr1
        (segment_poly input (16 * b + 8) 8)).
  by rewrite Hshape.
qed.

op invntt_radix2_8_scaled_diff_poly
    (a : W16.t Array768.t) (base c : int) : NTRUPoly.poly =
  PCA.bigi predT
    (fun i =>
      polyC
        (lift_int
          ((coeff a.[i + base + 8] +
            Int.([-]) (coeff a.[i + base])) * c)) *
      exp X i)
    0 8.

lemma invntt_radix2_8_scaled_diff_polyE
    (a : W16.t Array768.t) (base c : int) :
  invntt_radix2_8_scaled_diff_poly a base c =
  polyC (lift_int c) *
    (segment_poly a (base + 8) 8 - segment_poly a base 8).
proof.
  rewrite /invntt_radix2_8_scaled_diff_poly /segment_poly.
  have Hdist_hi :
      polyC (lift_int c) *
        PCA.bigi predT
          (fun i => polyC (lift_word a.[i + (base + 8)]) * exp X i)
          0 8 =
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c) *
            (polyC (lift_word a.[i + (base + 8)]) * exp X i))
        0 8.
  + exact
      (PCA.mulr_sumr predT
        (fun i => polyC (lift_word a.[i + (base + 8)]) * exp X i)
        (range 0 8) (polyC (lift_int c))).
  have Hdist_lo :
      polyC (lift_int c) *
        PCA.bigi predT
          (fun i => polyC (lift_word a.[i + base]) * exp X i)
          0 8 =
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c) *
            (polyC (lift_word a.[i + base]) * exp X i))
        0 8.
  + exact
      (PCA.mulr_sumr predT
        (fun i => polyC (lift_word a.[i + base]) * exp X i)
        (range 0 8) (polyC (lift_int c))).
  have Hsplit :
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c) *
            (polyC (lift_word a.[i + (base + 8)]) * exp X i))
        0 8 -
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c) *
            (polyC (lift_word a.[i + base]) * exp X i))
        0 8 =
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c) *
            (polyC (lift_word a.[i + (base + 8)]) * exp X i) -
          polyC (lift_int c) *
            (polyC (lift_word a.[i + base]) * exp X i))
        0 8.
  + exact
      (PCA.sumrB predT
        (fun i =>
          polyC (lift_int c) *
            (polyC (lift_word a.[i + (base + 8)]) * exp X i))
        (fun i =>
          polyC (lift_int c) *
            (polyC (lift_word a.[i + base]) * exp X i))
        (range 0 8)).
  have Houter :
      polyC (lift_int c) *
        (PCA.bigi predT
           (fun i => polyC (lift_word a.[i + (base + 8)]) * exp X i)
           0 8 -
         PCA.bigi predT
           (fun i => polyC (lift_word a.[i + base]) * exp X i)
           0 8) =
      polyC (lift_int c) *
        PCA.bigi predT
          (fun i => polyC (lift_word a.[i + (base + 8)]) * exp X i)
          0 8 -
      polyC (lift_int c) *
        PCA.bigi predT
          (fun i => polyC (lift_word a.[i + base]) * exp X i)
          0 8 by ring.
  rewrite Houter Hdist_hi Hdist_lo Hsplit.
  apply PCA.eq_big_int => i Hi.
  rewrite /lift_word /lift_int /=.
  rewrite CycloFq.incyclocoeffM CycloFq.incyclocoeffD
          CycloFq.incyclocoeffN.
  rewrite NTRUPoly.polyCM NTRUPoly.polyCD NTRUPoly.polyCN.
  have Hidx : i + base + 8 = i + (base + 8) by ring.
  rewrite Hidx.
  apply poly_sub_mul_reorder.
qed.

lemma segment_poly_scaled_diff2_8E
    (input output : W16.t Array768.t)
    (input_base output_base c : int) :
  (forall i, 0 <= i < 8 =>
    coeff output.[i + output_base] %% q =
    ((coeff input.[i + input_base + 8] +
      Int.([-]) (coeff input.[i + input_base])) * c) %% q) =>
  segment_poly output output_base 8 =
    invntt_radix2_8_scaled_diff_poly input input_base c.
proof.
  move=> Hcoeff.
  rewrite /segment_poly /invntt_radix2_8_scaled_diff_poly.
  apply PCA.eq_big_int => i Hi.
  have Hmod := Hcoeff i Hi.
  have Elift :
      lift_word output.[i + output_base] =
      lift_int
        ((coeff input.[i + input_base + 8] +
          Int.([-]) (coeff input.[i + input_base])) * c).
  + rewrite /lift_word.
    apply lift_int_eq.
    exact Hmod.
  by rewrite /= Elift.
qed.

lemma invntt_radix2_8_segment_rightE
    (input output : W16.t Array768.t) (b : int) :
  0 <= b < 48 =>
  NTRUPlus768InvNTTRadix2_8Algebra.invntt_radix2_8_algebra input output =>
  segment_poly output (16 * b + 8) 8 =
    invntt_radix2_8_scaled_diff_poly
      input (16 * b) (NTRUPlus768InvNTTRadix2_8Algebra.invntt_radix2_8_zeta_root b).
proof.
  move=> Hb Halg.
  apply segment_poly_scaled_diff2_8E.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + (16 * b + 8)) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768InvNTTRadix2_8Algebra.invntt_radix2_8_math.
  rewrite /NTRUPlus768InvNTTRadix2_8Proof.invntt_radix2_8_block_id.
  rewrite /NTRUPlus768InvNTTRadix2_8Proof.invntt_radix2_8_block_base.
  rewrite /NTRUPlus768InvNTTRadix2_8Proof.invntt_radix2_8_lane_index.
  rewrite /NTRUPlus768InvNTTRadix2_8Proof.invntt_radix2_8_block_offset.
  rewrite /NTRUPlus768InvNTTRadix2_8Algebra.double_block.
  rewrite /NTRUPlus768InvNTTRadix2_8Algebra.block.
  have -> : (i + (16 * b + 8)) %/ 16 = b by smt().
  have -> : (i + (16 * b + 8)) %% 16 = i + 8 by smt().
  move=> Hcoeff.
  move: Hcoeff; simplify.
  rewrite ifF 1:/# ifF 1:/# /=.
  move=> Hcoeff.
  rewrite /NTRUPlus768InvNTTRadix2_8Algebra.invntt_radix2_8_pair_math_at
          /NTRUPlus768InvNTTRadix2_8Algebra.invntt_radix2_8_pair_math
          /NTRUPlus768InvNTTRadix2_8Proof.double_block
          [16 * b + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma invntt_radix2_8_output_segmentE
    (input output : W16.t Array768.t) (b : int) :
  0 <= b < 48 =>
  NTRUPlus768InvNTTRadix2_8Algebra.invntt_radix2_8_algebra input output =>
  segment_poly output (16 * b) 16 =
    segment_poly input (16 * b) 8 +
    segment_poly input (16 * b + 8) 8 +
    invntt_radix2_8_scaled_diff_poly
      input (16 * b) (NTRUPlus768InvNTTRadix2_8Algebra.invntt_radix2_8_zeta_root b) *
      exp X 8.
proof.
  move=> Hb Halg.
  rewrite segment_poly_split2_8 /segment2_8_poly.
  rewrite (invntt_radix2_8_segment_leftE input output b Hb Halg).
  rewrite (invntt_radix2_8_segment_rightE input output b Hb Halg).
  done.
qed.

lemma invntt_radix2_8_recombine_factor_eqm
    (p a0 a1 : NTRUPoly.poly) (e e' : int) :
  0 <= e =>
  0 <= e' =>
  e' + e = 288 =>
  factor_eqm 8 e p a0 =>
  factor_eqm 8 (e + 288) p a1 =>
  factor_eqm 16 (2 * e) (p + p)
    (a0 + a1 + root_poly e' * (a1 - a0) * exp X 8).
proof.
  move=> He He' Hsum Hleft Hright.
  rewrite /factor_eqm.
  rewrite schedule_modulus_split2_8 1:He.
  rewrite /schedule_factor_modulus /root_poly.
  rewrite zeta_shift_288 1:He.
  rewrite NTRUPoly.polyCN.
  have Hplus :
      exp X 8 - (-polyC (CycloFq.exp zeta_field e)) =
      exp X 8 + polyC (CycloFq.exp zeta_field e).
  + ring.
  rewrite Hplus.
  apply (invntt_radix2_4_abstract_recombine
    p a0 a1
    (polyC (CycloFq.exp zeta_field e'))
    (polyC (CycloFq.exp zeta_field e))
    (exp X 8)).
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
