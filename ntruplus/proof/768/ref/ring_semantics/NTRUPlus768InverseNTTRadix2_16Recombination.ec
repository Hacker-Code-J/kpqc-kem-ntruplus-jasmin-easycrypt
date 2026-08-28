(* Algebraic reconstruction for the third inverse NTT layer. *)
require import AllCore IntDiv List Ring StdBigop StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array768.
require import NTRUPlus768CyclotomicFactorization.
require import NTRUPlus768EvaluationSemantics.
require import NTRUPlus768TerminalRepresentation.
require import NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768ForwardNTTRadix3Semantics.
require import NTRUPlus768ForwardNTTRadix2_16Semantics.
require import NTRUPlus768ForwardNTTRadix2_8Semantics.
require import NTRUPlus768ForwardNTTRadix2_4Semantics.
require import NTRUPlus768NTTSchedule.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768PolyBasemulAlgebra NTRUPlus768PolyBasemulProof.
require import NTRUPlus768InvNTTRadix2_4.
require import NTRUPlus768InvNTTRadix2_4Algebra NTRUPlus768InvNTTRadix2_4Proof.
require import NTRUPlus768InvNTTRadix2_8.
require import NTRUPlus768InvNTTRadix2_8Algebra NTRUPlus768InvNTTRadix2_8Proof.
require import NTRUPlus768InvNTTRadix2_16.
require import NTRUPlus768InvNTTRadix2_16Algebra NTRUPlus768InvNTTRadix2_16Proof.
require import NTRUPlus768InverseNTTRadix2_4Recombination.
require import NTRUPlus768InverseNTTRadix2_4Semantics.
require import NTRUPlus768InverseNTTRadix2_8Recombination.
require import NTRUPlus768InverseNTTRadix2_8Semantics.

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

op invntt_radix2_16_schedule_exp (b : int) : int =
  zetas192_exp
    (NTRUPlus768InvNTTRadix2_16Algebra.invntt_radix2_16_schedule_index b).

lemma invntt_radix2_16_schedule_forwardE (b : int) :
  0 <= b < 24 =>
  invntt_radix2_16_schedule_exp b = radix2_16_schedule_exp (23 - b).
proof.
  move=> Hb.
  rewrite /invntt_radix2_16_schedule_exp /radix2_16_schedule_exp.
  rewrite /NTRUPlus768InvNTTRadix2_16Algebra.invntt_radix2_16_schedule_index.
  rewrite /NTRUPlus768NTTRadix2_16Algebra.radix2_16_schedule_index.
  rewrite /NTRUPlus768InvNTTRadix2_16Algebra.nblocks /ntt_radix2_16_start.
  done.
qed.

op radix2_16_schedule_exps24 : int list =
  take 24 (drop ntt_radix2_16_start zetas192_exponents).

lemma radix2_16_schedule_exps24E :
  radix2_16_schedule_exps24 = [
    4; 148; 76; 220; 28; 172; 100; 244;
    52; 196; 124; 268; 20; 164; 92; 236;
    44; 188; 116; 260; 68; 212; 140; 284
  ].
proof.
  by rewrite /radix2_16_schedule_exps24 /ntt_radix2_16_start
             /zetas192_exponents /=.
qed.

lemma radix2_16_schedule_exp24E (b : int) :
  0 <= b < 24 =>
  radix2_16_schedule_exp b = nth witness radix2_16_schedule_exps24 b.
proof.
  move=> Hb.
  rewrite /radix2_16_schedule_exp
          /NTRUPlus768NTTRadix2_16Algebra.radix2_16_schedule_index
          /ntt_radix2_16_start /zetas192_exp
          /radix2_16_schedule_exps24.
  smt(nth_take nth_drop).
qed.

op radix2_16_parent_exps48 : int list =
  flatten
    (map (fun e => [e; e + 288]) radix2_16_schedule_exps24).

lemma radix2_8_parent_exps16E :
  radix2_16_parent_exps48 =
  map (fun e => 2 * e) radix2_8_schedule_exps.
proof.
  by rewrite /radix2_16_parent_exps48
             radix2_16_schedule_exps24E radix2_8_schedule_expsE /=.
qed.

lemma radix2_8_parent_scheduleE16 (b : int) :
  0 <= b < 48 =>
  2 * radix2_8_schedule_exp b =
    if b %% 2 = 0 then
      radix2_16_schedule_exp (b %/ 2)
    else
      radix2_16_schedule_exp (b %/ 2) + 288.
proof.
  move=> Hb.
  have Hhalf : 0 <= b %/ 2 < 24 by smt().
  have Hsize16 : size radix2_16_schedule_exps24 = 24
    by rewrite radix2_16_schedule_exps24E /=.
  have Hsize8 : size radix2_8_schedule_exps = 48
    by rewrite radix2_8_schedule_expsE /=.
  have Hinterleave :=
    nth_generated_figure22_pair radix2_16_schedule_exps24 b _.
  + rewrite Hsize16.
    smt().
  rewrite /ell /= in Hinterleave.
  have Hlists :
      nth witness radix2_16_parent_exps48 b =
      nth witness (map (fun e => 2 * e) radix2_8_schedule_exps) b
    by rewrite radix2_8_parent_exps16E.
  rewrite /radix2_16_parent_exps48 Hinterleave in Hlists.
  rewrite (nth_map witness) 1:/# in Hlists.
  rewrite (radix2_8_schedule_expE b Hb)
          (radix2_16_schedule_exp24E (b %/ 2) Hhalf).
  move: Hlists; simplify.
  smt().
qed.

lemma radix2_16_schedule_exp_terminalE (b : int) :
  0 <= b < 24 =>
  radix2_16_schedule_exp b = 4 * terminal_exp (4 * b).
proof.
  move=> Hb.
  have Hchild : 0 <= 4 * b < 96 by smt().
  have Hterminal := radix2_4_parent_scheduleE (4 * b) Hchild.
  move: Hterminal.
  rewrite (radix2_4_schedule_exp_terminalE (4 * b) Hchild).
  rewrite (_ : (4 * b) %% 2 = 0) 1:/#.
  rewrite (_ : (4 * b) %/ 2 = 2 * b) 1:/#.
  move=> Hterminal.
  have Hparent := radix2_8_parent_scheduleE16 (2 * b) _; first smt().
  move: Hparent.
  rewrite (_ : (2 * b) %% 2 = 0) 1:/#.
  rewrite (_ : (2 * b) %/ 2 = b) 1:/#.
  move=> Hparent.
  smt().
qed.

lemma invntt_radix2_16_child_scheduleE (b : int) :
  0 <= b < 24 =>
  4 * terminal_exp (4 * b + 2) =
    4 * terminal_exp (4 * b) + 288.
proof.
  move=> Hb.
  have Hleft : 0 <= 4 * b < 96 by smt().
  have Hright : 0 <= 4 * b + 2 < 96 by smt().
  have Hterminal_left := radix2_4_parent_scheduleE (4 * b) Hleft.
  have Hterminal_right := radix2_4_parent_scheduleE (4 * b + 2) Hright.
  move: Hterminal_left Hterminal_right.
  rewrite (radix2_4_schedule_exp_terminalE (4 * b) Hleft).
  rewrite (radix2_4_schedule_exp_terminalE (4 * b + 2) Hright).
  rewrite (_ : (4 * b) %% 2 = 0) 1:/#.
  rewrite (_ : (4 * b) %/ 2 = 2 * b) 1:/#.
  rewrite (_ : (4 * b + 2) %% 2 = 0) 1:/#.
  rewrite (_ : (4 * b + 2) %/ 2 = 2 * b + 1) 1:/#.
  move=> Hterminal_left Hterminal_right.
  have Hparent_left := radix2_8_parent_scheduleE16 (2 * b) _; first smt().
  have Hparent_right := radix2_8_parent_scheduleE16 (2 * b + 1) _; first smt().
  move: Hparent_left Hparent_right.
  rewrite (_ : (2 * b) %% 2 = 0) 1:/#.
  rewrite (_ : (2 * b) %/ 2 = b) 1:/#.
  rewrite (_ : (2 * b + 1) %% 2 = 1) 1:/#.
  rewrite (_ : (2 * b + 1) %/ 2 = b) 1:/#.
  move=> Hparent_left Hparent_right.
  smt().
qed.

lemma radix2_16_schedule_reverse_sum_288 (b : int) :
  0 <= b < 24 =>
  radix2_16_schedule_exp b + radix2_16_schedule_exp (23 - b) = 288.
proof.
  move=> Hb.
  have Hodd : 0 <= 2 * b + 1 < 48 by smt().
  have Hrev : 0 <= 46 - 2 * b < 48 by smt().
  have Hsum := radix2_8_schedule_reverse_sum_288 (2 * b + 1) Hodd.
  have Hsum_normalized :
      radix2_8_schedule_exp (2 * b + 1) +
        radix2_8_schedule_exp (46 - 2 * b) = 288.
  + have -> : 46 - 2 * b = 47 - (2 * b + 1) by ring.
    exact Hsum.
  clear Hsum.
  have Hparent_odd := radix2_8_parent_scheduleE16 (2 * b + 1) Hodd.
  have Hparent_rev := radix2_8_parent_scheduleE16 (46 - 2 * b) Hrev.
  move: Hparent_odd Hparent_rev.
  rewrite (_ : (2 * b + 1) %% 2 = 1) 1:/#.
  rewrite (_ : (2 * b + 1) %/ 2 = b) 1:/#.
  rewrite (_ : (46 - 2 * b) %% 2 = 0) 1:/#.
  rewrite (_ : (46 - 2 * b) %/ 2 = 23 - b) 1:/#.
  move=> Hparent_odd Hparent_rev.
  clear Hb Hodd Hrev.
  smt().
qed.

lemma invntt_radix2_16_schedule_sumE (b : int) :
  0 <= b < 24 =>
  invntt_radix2_16_schedule_exp b + 4 * terminal_exp (4 * b) = 288.
proof.
  move=> Hb.
  rewrite (invntt_radix2_16_schedule_forwardE b Hb).
  rewrite -(radix2_16_schedule_exp_terminalE b Hb) addrC.
  exact (radix2_16_schedule_reverse_sum_288 b Hb).
qed.

lemma invntt_radix2_16_schedule_nonneg (b : int) :
  0 <= b < 24 =>
  0 <= invntt_radix2_16_schedule_exp b.
proof.
  move=> Hb.
  rewrite (invntt_radix2_16_schedule_forwardE b Hb).
  have Hidx : 0 <= 23 - b < 24 by smt().
  rewrite (radix2_16_schedule_exp_terminalE (23 - b) Hidx).
  have Hterm : 0 <= terminal_exp (4 * (23 - b)).
  + have Hchild : 0 <= 4 * (23 - b) < 96 by smt().
    exact (terminal_exp_nonneg (4 * (23 - b)) Hchild).
  smt().
qed.

lemma invntt_radix2_16_child_exp_nonneg (b : int) :
  0 <= b < 24 =>
  0 <= 4 * terminal_exp (4 * b).
proof.
  move=> Hb.
  have Hidx : 0 <= 4 * b < 96 by smt().
  have Hterm := terminal_exp_nonneg (4 * b) Hidx.
  smt().
qed.

lemma invntt_radix2_16_root_cancelE (b : int) :
  0 <= b < 24 =>
  root_poly (invntt_radix2_16_schedule_exp b) *
    root_poly (4 * terminal_exp (4 * b)) = -poly1.
proof.
  move=> Hb.
  rewrite /root_poly.
  have Hchild : 0 <= 4 * terminal_exp (4 * b).
  + exact (invntt_radix2_16_child_exp_nonneg b Hb).
  have Hfield :
      CycloFq.( * )
        (CycloFq.exp zeta_field (invntt_radix2_16_schedule_exp b))
        (CycloFq.exp zeta_field (4 * terminal_exp (4 * b))) =
      CycloFq.([-]) CycloFq.one.
  + exact
      (zeta_complement_product_neg1
        (4 * terminal_exp (4 * b)) (invntt_radix2_16_schedule_exp b)
        Hchild
        (invntt_radix2_16_schedule_nonneg b Hb)
        (invntt_radix2_16_schedule_sumE b Hb)).
  have -> :
      polyC (CycloFq.exp zeta_field (invntt_radix2_16_schedule_exp b)) *
        polyC (CycloFq.exp zeta_field (4 * terminal_exp (4 * b))) =
      polyC
        (CycloFq.( * )
          (CycloFq.exp zeta_field (invntt_radix2_16_schedule_exp b))
          (CycloFq.exp zeta_field (4 * terminal_exp (4 * b)))).
  + apply/eq_sym.
    apply NTRUPoly.polyCM.
  by rewrite Hfield NTRUPoly.polyCN.
qed.

lemma invntt_radix2_8_semantics_child_left
    (p : NTRUPoly.poly) (input : W16.t Array768.t) (b : int) :
  invntt_radix2_8_semantics p input =>
  0 <= b < 24 =>
  factor_eqm 16 (4 * terminal_exp (4 * b))
    (doubled_twice p)
    (segment_poly input (32 * b) 16).
proof.
  move=> Hsem Hb.
  rewrite /invntt_radix2_8_semantics in Hsem.
  have Hidx : 0 <= 2 * b < 48 by smt().
  have Hchild := Hsem (2 * b) Hidx.
  have Hbase : 16 * (2 * b) = 32 * b by ring.
  have Hexp : 2 * (2 * b) = 4 * b by ring.
  rewrite -Hbase.
  rewrite -Hexp.
  exact Hchild.
qed.

lemma invntt_radix2_8_semantics_child_right
    (p : NTRUPoly.poly) (input : W16.t Array768.t) (b : int) :
  invntt_radix2_8_semantics p input =>
  0 <= b < 24 =>
  factor_eqm 16 (4 * terminal_exp (4 * b) + 288)
    (doubled_twice p)
    (segment_poly input (32 * b + 16) 16).
proof.
  move=> Hsem Hb.
  rewrite /invntt_radix2_8_semantics in Hsem.
  have Hidx : 0 <= 2 * b + 1 < 48 by smt().
  have Hchild := Hsem (2 * b + 1) Hidx.
  have Hbase : 16 * (2 * b + 1) = 32 * b + 16 by ring.
  have Hexp : 2 * (2 * b + 1) = 4 * b + 2 by ring.
  rewrite -Hbase.
  rewrite -(invntt_radix2_16_child_scheduleE b Hb).
  rewrite -Hexp.
  exact Hchild.
qed.

lemma invntt_radix2_16_segment_leftE
    (input output : W16.t Array768.t) (b : int) :
  0 <= b < 24 =>
  NTRUPlus768InvNTTRadix2_16Algebra.invntt_radix2_16_algebra input output =>
  segment_poly output (32 * b) 16 =
    segment_poly input (32 * b) 16 +
    segment_poly input (32 * b + 16) 16.
proof.
  move=> Hb Halg.
  have Hleft :
      segment_poly output (32 * b) 16 =
      radix2_16_eval_poly input (32 * b) 0.
  + apply segment_poly_radix2_16_evalE; first smt().
    move=> i Hi.
    have [_ Hcoeff] := Halg (i + 32 * b) _; first smt().
    move: Hcoeff.
    rewrite /NTRUPlus768InvNTTRadix2_16Algebra.invntt_radix2_16_math.
    rewrite /NTRUPlus768InvNTTRadix2_16Proof.invntt_radix2_16_block_id.
    rewrite /NTRUPlus768InvNTTRadix2_16Proof.invntt_radix2_16_block_base.
    rewrite /NTRUPlus768InvNTTRadix2_16Proof.invntt_radix2_16_lane_index.
    rewrite /NTRUPlus768InvNTTRadix2_16Proof.invntt_radix2_16_block_offset.
    rewrite /NTRUPlus768InvNTTRadix2_16Algebra.double_block.
    rewrite /NTRUPlus768InvNTTRadix2_16Algebra.block.
    have -> : (i + 32 * b) %/ 32 = b by smt().
    have -> : (i + 32 * b) %% 32 = i by smt().
    move=> Hcoeff.
    move: Hcoeff; simplify.
    rewrite ifT 1:/# ifT 1:/# /=.
    move=> Hcoeff.
    rewrite /NTRUPlus768InvNTTRadix2_16Algebra.invntt_radix2_16_pair_math_at
            /NTRUPlus768InvNTTRadix2_16Algebra.invntt_radix2_16_pair_math
            /NTRUPlus768InvNTTRadix2_16Proof.double_block
            [32 * b + i]addrC in Hcoeff.
    rewrite /schedule_root /zeta_root /q /=.
    exact Hcoeff.
  rewrite Hleft /radix2_16_eval_poly /root_poly.
  have Hroot0 :
      CycloFq.exp zeta_field 0 = CycloFq.one
    by rewrite zeta_field_expE 1:// /=.
  rewrite Hroot0.
  have Hone :
      NTRUPoly.polyC CycloFq.one = NTRUPoly.PolyComRing.oner by done.
  rewrite Hone.
  have Hshape :
      segment_poly input (32 * b + 16) 16 *
        NTRUPoly.PolyComRing.oner =
      segment_poly input (32 * b + 16) 16.
  + exact
      (NTRUPoly.PolyComRing.mulr1
        (segment_poly input (32 * b + 16) 16)).
  by rewrite Hshape.
qed.

op invntt_radix2_16_scaled_diff_poly
    (a : W16.t Array768.t) (base c : int) : NTRUPoly.poly =
  PCA.bigi predT
    (fun i =>
      polyC
        (lift_int
          ((coeff a.[i + base + 16] +
            Int.([-]) (coeff a.[i + base])) * c)) *
      exp X i)
    0 16.

lemma invntt_radix2_16_scaled_diff_polyE
    (a : W16.t Array768.t) (base c : int) :
  invntt_radix2_16_scaled_diff_poly a base c =
  polyC (lift_int c) *
    (segment_poly a (base + 16) 16 - segment_poly a base 16).
proof.
  rewrite /invntt_radix2_16_scaled_diff_poly /segment_poly.
  have Hdist_hi :
      polyC (lift_int c) *
        PCA.bigi predT
          (fun i => polyC (lift_word a.[i + (base + 16)]) * exp X i)
          0 16 =
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c) *
            (polyC (lift_word a.[i + (base + 16)]) * exp X i))
        0 16.
  + exact
      (PCA.mulr_sumr predT
        (fun i => polyC (lift_word a.[i + (base + 16)]) * exp X i)
        (range 0 16) (polyC (lift_int c))).
  have Hdist_lo :
      polyC (lift_int c) *
        PCA.bigi predT
          (fun i => polyC (lift_word a.[i + base]) * exp X i)
          0 16 =
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c) *
            (polyC (lift_word a.[i + base]) * exp X i))
        0 16.
  + exact
      (PCA.mulr_sumr predT
        (fun i => polyC (lift_word a.[i + base]) * exp X i)
        (range 0 16) (polyC (lift_int c))).
  have Hsplit :
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c) *
            (polyC (lift_word a.[i + (base + 16)]) * exp X i))
        0 16 -
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c) *
            (polyC (lift_word a.[i + base]) * exp X i))
        0 16 =
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c) *
            (polyC (lift_word a.[i + (base + 16)]) * exp X i) -
          polyC (lift_int c) *
            (polyC (lift_word a.[i + base]) * exp X i))
        0 16.
  + exact
      (PCA.sumrB predT
        (fun i =>
          polyC (lift_int c) *
            (polyC (lift_word a.[i + (base + 16)]) * exp X i))
        (fun i =>
          polyC (lift_int c) *
            (polyC (lift_word a.[i + base]) * exp X i))
        (range 0 16)).
  have Houter :
      polyC (lift_int c) *
        (PCA.bigi predT
           (fun i => polyC (lift_word a.[i + (base + 16)]) * exp X i)
           0 16 -
         PCA.bigi predT
           (fun i => polyC (lift_word a.[i + base]) * exp X i)
           0 16) =
      polyC (lift_int c) *
        PCA.bigi predT
          (fun i => polyC (lift_word a.[i + (base + 16)]) * exp X i)
          0 16 -
      polyC (lift_int c) *
        PCA.bigi predT
          (fun i => polyC (lift_word a.[i + base]) * exp X i)
          0 16 by ring.
  rewrite Houter Hdist_hi Hdist_lo Hsplit.
  apply PCA.eq_big_int => i Hi.
  rewrite /lift_word /lift_int /=.
  rewrite CycloFq.incyclocoeffM CycloFq.incyclocoeffD
          CycloFq.incyclocoeffN.
  rewrite NTRUPoly.polyCM NTRUPoly.polyCD NTRUPoly.polyCN.
  have Hidx : i + base + 16 = i + (base + 16) by ring.
  rewrite Hidx.
  apply poly_sub_mul_reorder.
qed.

lemma segment_poly_scaled_diff2_16E
    (input output : W16.t Array768.t)
    (input_base output_base c : int) :
  (forall i, 0 <= i < 16 =>
    coeff output.[i + output_base] %% q =
    ((coeff input.[i + input_base + 16] +
      Int.([-]) (coeff input.[i + input_base])) * c) %% q) =>
  segment_poly output output_base 16 =
    invntt_radix2_16_scaled_diff_poly input input_base c.
proof.
  move=> Hcoeff.
  rewrite /segment_poly /invntt_radix2_16_scaled_diff_poly.
  apply PCA.eq_big_int => i Hi.
  have Hmod := Hcoeff i Hi.
  have Elift :
      lift_word output.[i + output_base] =
      lift_int
        ((coeff input.[i + input_base + 16] +
          Int.([-]) (coeff input.[i + input_base])) * c).
  + rewrite /lift_word.
    apply lift_int_eq.
    exact Hmod.
  by rewrite /= Elift.
qed.

lemma invntt_radix2_16_segment_rightE
    (input output : W16.t Array768.t) (b : int) :
  0 <= b < 24 =>
  NTRUPlus768InvNTTRadix2_16Algebra.invntt_radix2_16_algebra input output =>
  segment_poly output (32 * b + 16) 16 =
    invntt_radix2_16_scaled_diff_poly
      input (32 * b) (NTRUPlus768InvNTTRadix2_16Algebra.invntt_radix2_16_zeta_root b).
proof.
  move=> Hb Halg.
  apply segment_poly_scaled_diff2_16E.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + (32 * b + 16)) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768InvNTTRadix2_16Algebra.invntt_radix2_16_math.
  rewrite /NTRUPlus768InvNTTRadix2_16Proof.invntt_radix2_16_block_id.
  rewrite /NTRUPlus768InvNTTRadix2_16Proof.invntt_radix2_16_block_base.
  rewrite /NTRUPlus768InvNTTRadix2_16Proof.invntt_radix2_16_lane_index.
  rewrite /NTRUPlus768InvNTTRadix2_16Proof.invntt_radix2_16_block_offset.
  rewrite /NTRUPlus768InvNTTRadix2_16Algebra.double_block.
  rewrite /NTRUPlus768InvNTTRadix2_16Algebra.block.
  have -> : (i + (32 * b + 16)) %/ 32 = b by smt().
  have -> : (i + (32 * b + 16)) %% 32 = i + 16 by smt().
  move=> Hcoeff.
  move: Hcoeff; simplify.
  rewrite ifF 1:/# ifF 1:/# /=.
  move=> Hcoeff.
  rewrite /NTRUPlus768InvNTTRadix2_16Algebra.invntt_radix2_16_pair_math_at
          /NTRUPlus768InvNTTRadix2_16Algebra.invntt_radix2_16_pair_math
          /NTRUPlus768InvNTTRadix2_16Proof.double_block
          [32 * b + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma invntt_radix2_16_output_segmentE
    (input output : W16.t Array768.t) (b : int) :
  0 <= b < 24 =>
  NTRUPlus768InvNTTRadix2_16Algebra.invntt_radix2_16_algebra input output =>
  segment_poly output (32 * b) 32 =
    segment_poly input (32 * b) 16 +
    segment_poly input (32 * b + 16) 16 +
    invntt_radix2_16_scaled_diff_poly
      input (32 * b) (NTRUPlus768InvNTTRadix2_16Algebra.invntt_radix2_16_zeta_root b) *
      exp X 16.
proof.
  move=> Hb Halg.
  rewrite segment_poly_split2_16 /segment2_16_poly.
  rewrite (invntt_radix2_16_segment_leftE input output b Hb Halg).
  rewrite (invntt_radix2_16_segment_rightE input output b Hb Halg).
  done.
qed.

lemma invntt_radix2_16_recombine_factor_eqm
    (p a0 a1 : NTRUPoly.poly) (e e' : int) :
  0 <= e =>
  0 <= e' =>
  e' + e = 288 =>
  factor_eqm 16 e p a0 =>
  factor_eqm 16 (e + 288) p a1 =>
  factor_eqm 32 (2 * e) (p + p)
    (a0 + a1 + root_poly e' * (a1 - a0) * exp X 16).
proof.
  move=> He He' Hsum Hleft Hright.
  rewrite /factor_eqm.
  rewrite schedule_modulus_split2_16 1:He.
  rewrite /schedule_factor_modulus /root_poly.
  rewrite zeta_shift_288 1:He.
  rewrite NTRUPoly.polyCN.
  have Hplus :
      exp X 16 - (-polyC (CycloFq.exp zeta_field e)) =
      exp X 16 + polyC (CycloFq.exp zeta_field e).
  + ring.
  rewrite Hplus.
  apply (invntt_radix2_4_abstract_recombine
    p a0 a1
    (polyC (CycloFq.exp zeta_field e'))
    (polyC (CycloFq.exp zeta_field e))
    (exp X 16)).
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
