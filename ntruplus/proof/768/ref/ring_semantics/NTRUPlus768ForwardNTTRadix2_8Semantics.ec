require import AllCore IntDiv List Ring StdBigop StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array768.
require import NTRUPlus768BasemulAlgebra NTRUPlus768NTTSchedule.
require import NTRUPlus768CyclotomicFactorization.
require import NTRUPlus768EvaluationSemantics.
require import NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768ForwardNTTRadix3Semantics.
require import NTRUPlus768ForwardNTTRadix2_64Semantics.
require import NTRUPlus768ForwardNTTRadix2_32Semantics.
require import NTRUPlus768ForwardNTTRadix2_16Semantics.
require import NTRUPlus768NTTRadix2_8.
require import NTRUPlus768NTTRadix2_8Algebra NTRUPlus768NTTRadix2_8Proof.

import NTRUPoly.BigPoly.

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

(* The fourth binary layer refines every degree-16 representative into two
   degree-8 representatives. *)

op segment2_8_poly (a : W16.t Array768.t) (base : int) : NTRUPoly.poly =
  segment_poly a base 8 +
  segment_poly a (base + 8) 8 * exp X 8.

op radix2_8_eval_poly
    (a : W16.t Array768.t) (base e : int) : NTRUPoly.poly =
  segment_poly a base 8 +
  segment_poly a (base + 8) 8 * root_poly e.

lemma segment_poly_split2_8 (a : W16.t Array768.t) (base : int) :
  segment_poly a base 16 = segment2_8_poly a base.
proof.
  rewrite /segment2_8_poly.
  rewrite (segment_poly_split a base 8 8) 1:// 1://.
  done.
qed.

lemma radix2_8_eval_factor_eqm
    (a : W16.t Array768.t) (base e : int) :
  factor_eqm 8 e
    (segment2_8_poly a base) (radix2_8_eval_poly a base e).
proof.
  rewrite /factor_eqm /schedule_factor_modulus.
  exists (-(segment_poly a (base + 8) 8)).
  rewrite /segment2_8_poly /radix2_8_eval_poly /root_poly.
  ring.
qed.

lemma schedule_modulus_split2_8 (r : int) :
  0 <= r =>
  schedule_factor_modulus 16 (2 * r) =
  schedule_factor_modulus 8 r *
    schedule_factor_modulus 8 (r + 288).
proof.
  move=> Hr.
  move: (factor_split2 X 8 r _ Hr); first smt().
  rewrite /factor /schedule_factor_modulus /=.
  done.
qed.

lemma factor_eqm_split2_8_left
    (r : int) (p q : NTRUPoly.poly) :
  0 <= r =>
  factor_eqm 16 (2 * r) p q =>
  factor_eqm 8 r p q.
proof.
  move=> Hr.
  apply factor_eqm_weaken.
  exists (schedule_factor_modulus 8 (r + 288)).
  exact (schedule_modulus_split2_8 r Hr).
qed.

lemma factor_eqm_split2_8_right
    (r : int) (p q : NTRUPoly.poly) :
  0 <= r =>
  factor_eqm 16 (2 * r) p q =>
  factor_eqm 8 (r + 288) p q.
proof.
  move=> Hr.
  apply factor_eqm_weaken.
  exists (schedule_factor_modulus 8 r).
  rewrite schedule_modulus_split2_8 1:Hr.
  ring.
qed.

lemma radix2_8_pair_child0_eqm (a0 a1 r : int) :
  (NTRUPlus768NTTRadix2_8Algebra.radix2_8_pair_math
     a0 a1 (schedule_root r)).`1 %% q =
  (a0 + a1 * schedule_root r) %% q.
proof.
  by rewrite /NTRUPlus768NTTRadix2_8Algebra.radix2_8_pair_math.
qed.

lemma radix2_8_pair_child1_eqm (a0 a1 r : int) :
  0 <= r =>
  (NTRUPlus768NTTRadix2_8Algebra.radix2_8_pair_math
     a0 a1 (schedule_root r)).`2 %% q =
  (a0 + a1 * schedule_root (r + 288)) %% q.
proof.
  move=> Hr.
  rewrite /NTRUPlus768NTTRadix2_8Algebra.radix2_8_pair_math.
  have Hroot := schedule_root_shift_288_eqm r Hr.
  have Hmul :
      (a1 * (- schedule_root r)) %% q =
      (a1 * schedule_root (r + 288)) %% q.
  + apply (IntDiv.eqmM q a1 a1
      (- schedule_root r) (schedule_root (r + 288))).
    - done.
    - exact Hroot.
  have Hadd :
      (a0 + a1 * (- schedule_root r)) %% q =
      (a0 + a1 * schedule_root (r + 288)) %% q.
  + apply (IntDiv.eqmD q a0 a0
      (a1 * (- schedule_root r))
      (a1 * schedule_root (r + 288))).
    - done.
    - exact Hmul.
  have -> : a0 - a1 * schedule_root r =
      a0 + a1 * (- schedule_root r) by ring.
  exact Hadd.
qed.

op linear2_8_remainder_poly
    (a : W16.t Array768.t) (base c : int) : NTRUPoly.poly =
  PCA.bigi predT
    (fun i =>
      polyC
        (lift_int
          (coeff a.[i + base] +
           coeff a.[i + base + 8] * c)) *
      exp X i)
    0 8.

lemma linear2_8_remainder_polyE
    (a : W16.t Array768.t) (base c : int) :
  linear2_8_remainder_poly a base c =
  segment_poly a base 8 +
  polyC (lift_int c) * segment_poly a (base + 8) 8.
proof.
  rewrite /linear2_8_remainder_poly /segment_poly.
  have Hdist :
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
  have Hsplit :
      PCA.bigi predT
        (fun i => polyC (lift_word a.[i + base]) * exp X i)
        0 8 +
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c) *
            (polyC (lift_word a.[i + (base + 8)]) * exp X i))
        0 8 =
      PCA.bigi predT
        (fun i =>
          polyC (lift_word a.[i + base]) * exp X i +
          polyC (lift_int c) *
            (polyC (lift_word a.[i + (base + 8)]) * exp X i))
        0 8.
  + apply/eq_sym.
    exact
      (PCA.big_split predT
        (fun i => polyC (lift_word a.[i + base]) * exp X i)
        (fun i =>
          polyC (lift_int c) *
            (polyC (lift_word a.[i + (base + 8)]) * exp X i))
        (range 0 8)).
  rewrite Hdist Hsplit.
  apply PCA.eq_big_int => i Hi.
  rewrite /lift_word /lift_int /=.
  rewrite CycloFq.incyclocoeffD CycloFq.incyclocoeffM.
  rewrite NTRUPoly.polyCD NTRUPoly.polyCM.
  rewrite poly_mul_add_right.
  congr.
  have Hidx : i + base + 8 = i + (base + 8) by ring.
  rewrite Hidx.
  apply poly_mul_reorder.
qed.

lemma segment_poly_linear2_8E
    (input output : W16.t Array768.t)
    (input_base output_base c : int) :
  (forall i, 0 <= i < 8 =>
    coeff output.[i + output_base] %% q =
    (coeff input.[i + input_base] +
     coeff input.[i + input_base + 8] * c) %% q) =>
  segment_poly output output_base 8 =
  linear2_8_remainder_poly input input_base c.
proof.
  move=> Hcoeff.
  rewrite /segment_poly /linear2_8_remainder_poly.
  apply PCA.eq_big_int => i Hi.
  have Hmod := Hcoeff i Hi.
  have Elift :
      lift_word output.[i + output_base] =
      lift_int
        (coeff input.[i + input_base] +
         coeff input.[i + input_base + 8] * c).
  + rewrite /lift_word.
    apply lift_int_eq.
    exact Hmod.
  by rewrite /= Elift.
qed.

lemma linear2_8_remainder_radix2_evalE
    (a : W16.t Array768.t) (base e : int) :
  0 <= e =>
  linear2_8_remainder_poly a base (schedule_root e) =
  radix2_8_eval_poly a base e.
proof.
  move=> He.
  rewrite linear2_8_remainder_polyE /radix2_8_eval_poly /root_poly.
  rewrite schedule_root_fieldE 1:He.
  ring.
qed.

lemma segment_poly_radix2_8_evalE
    (input output : W16.t Array768.t)
    (input_base output_base e : int) :
  0 <= e =>
  (forall i, 0 <= i < 8 =>
    coeff output.[i + output_base] %% q =
    (coeff input.[i + input_base] +
     coeff input.[i + input_base + 8] * schedule_root e) %% q) =>
  segment_poly output output_base 8 =
  radix2_8_eval_poly input input_base e.
proof.
  move=> He Hcoeff.
  have Hsegment :
      segment_poly output output_base 8 =
      linear2_8_remainder_poly input input_base (schedule_root e).
  + apply segment_poly_linear2_8E.
    exact Hcoeff.
  rewrite Hsegment.
  apply linear2_8_remainder_radix2_evalE.
  exact He.
qed.

op radix2_8_schedule_exp (b : int) : int =
  zetas192_exp
    (NTRUPlus768NTTRadix2_8Algebra.radix2_8_schedule_index b).

op radix2_8_schedule_exps : int list =
  take 48 (drop ntt_radix2_8_start zetas192_exponents).

lemma radix2_8_schedule_expsE :
  radix2_8_schedule_exps = [
    2; 146; 74; 218; 38; 182; 110; 254;
    14; 158; 86; 230; 50; 194; 122; 266;
    26; 170; 98; 242; 62; 206; 134; 278;
    10; 154; 82; 226; 46; 190; 118; 262;
    22; 166; 94; 238; 58; 202; 130; 274;
    34; 178; 106; 250; 70; 214; 142; 286
  ].
proof.
  by rewrite /radix2_8_schedule_exps /ntt_radix2_8_start
             /zetas192_exponents /=.
qed.

lemma radix2_8_schedule_expE (b : int) :
  0 <= b < 48 =>
  radix2_8_schedule_exp b = nth witness radix2_8_schedule_exps b.
proof.
  move=> Hb.
  rewrite /radix2_8_schedule_exp
          /NTRUPlus768NTTRadix2_8Algebra.radix2_8_schedule_index
          /ntt_radix2_8_start /zetas192_exp /radix2_8_schedule_exps.
  smt(nth_take nth_drop).
qed.

lemma radix2_8_zeta_scheduleE (b : int) :
  NTRUPlus768NTTRadix2_8Algebra.radix2_8_zeta_root b =
  schedule_root (radix2_8_schedule_exp b).
proof.
  by rewrite /NTRUPlus768NTTRadix2_8Algebra.radix2_8_zeta_root
             /radix2_8_schedule_exp /schedule_root.
qed.

lemma radix2_8_segment_left_evalE
    (input output : W16.t Array768.t) (b : int) :
  0 <= b < 48 =>
  0 <= radix2_8_schedule_exp b =>
  NTRUPlus768NTTRadix2_8Algebra.radix2_8_algebra input output =>
  segment_poly output (16 * b) 8 =
    radix2_8_eval_poly input (16 * b) (radix2_8_schedule_exp b).
proof.
  move=> Hb He Halg.
  apply segment_poly_radix2_8_evalE; first exact He.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 16 * b) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_8Algebra.radix2_8_math
          /NTRUPlus768NTTRadix2_8Algebra.radix2_8_block_id
          /NTRUPlus768NTTRadix2_8Algebra.radix2_8_block_base
          /NTRUPlus768NTTRadix2_8Algebra.radix2_8_lane_index
          /NTRUPlus768NTTRadix2_8Algebra.radix2_8_block_offset
          /NTRUPlus768NTTRadix2_8Algebra.double_block
          /NTRUPlus768NTTRadix2_8Algebra.block.
  have -> : (i + 16 * b) %/ 16 = b by smt().
  have -> : (i + 16 * b) %% 16 = i by smt().
  move=> Hcoeff.
  move: Hcoeff; simplify.
  rewrite ifT 1:/# ifT 1:/# /=.
  move=> Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_8Algebra.radix2_8_pair_math_at
          radix2_8_zeta_scheduleE radix2_8_pair_child0_eqm in Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_8Algebra.block
          [16 * b + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_8_segment_right_evalE
    (input output : W16.t Array768.t) (b : int) :
  0 <= b < 48 =>
  0 <= radix2_8_schedule_exp b =>
  NTRUPlus768NTTRadix2_8Algebra.radix2_8_algebra input output =>
  segment_poly output (16 * b + 8) 8 =
    radix2_8_eval_poly input (16 * b) (radix2_8_schedule_exp b + 288).
proof.
  move=> Hb He Halg.
  apply segment_poly_radix2_8_evalE; first smt().
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + (16 * b + 8)) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_8Algebra.radix2_8_math
          /NTRUPlus768NTTRadix2_8Algebra.radix2_8_block_id
          /NTRUPlus768NTTRadix2_8Algebra.radix2_8_block_base
          /NTRUPlus768NTTRadix2_8Algebra.radix2_8_lane_index
          /NTRUPlus768NTTRadix2_8Algebra.radix2_8_block_offset
          /NTRUPlus768NTTRadix2_8Algebra.double_block
          /NTRUPlus768NTTRadix2_8Algebra.block.
  have -> : (i + (16 * b + 8)) %/ 16 = b by smt().
  have -> : (i + (16 * b + 8)) %% 16 = i + 8 by smt().
  move=> Hcoeff.
  move: Hcoeff; simplify.
  rewrite ifF 1:/# ifF 1:/# /=.
  move=> Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_8Algebra.radix2_8_pair_math_at
          radix2_8_zeta_scheduleE in Hcoeff.
  rewrite radix2_8_pair_child1_eqm 1:He in Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_8Algebra.block
          [16 * b + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_8_segment_factor_eqm
    (input output : W16.t Array768.t)
    (input_base output_base e : int) :
  segment_poly output output_base 8 =
    radix2_8_eval_poly input input_base e =>
  factor_eqm 8 e
    (segment_poly input input_base 16)
    (segment_poly output output_base 8).
proof.
  move=> Houtput.
  rewrite segment_poly_split2_8 Houtput.
  exact (radix2_8_eval_factor_eqm input input_base e).
qed.

lemma radix2_8_refine_left
    (original input output : W16.t Array768.t)
    (input_base output_base r : int) :
  0 <= r =>
  factor_eqm 16 (2 * r)
    (input_poly original) (segment_poly input input_base 16) =>
  segment_poly output output_base 8 =
    radix2_8_eval_poly input input_base r =>
  factor_eqm 8 r
    (input_poly original) (segment_poly output output_base 8).
proof.
  move=> Hr Hparent HlocalE.
  have Hparent' : factor_eqm 8 r
      (input_poly original) (segment_poly input input_base 16).
  + apply factor_eqm_split2_8_left; first exact Hr.
    exact Hparent.
  have Hlocal : factor_eqm 8 r
      (segment_poly input input_base 16)
      (segment_poly output output_base 8).
  + apply radix2_8_segment_factor_eqm.
    exact HlocalE.
  apply (factor_eqm_trans 8 r
    (input_poly original) (segment_poly input input_base 16)
    (segment_poly output output_base 8)).
  + exact Hparent'.
  + exact Hlocal.
qed.

lemma radix2_8_refine_right
    (original input output : W16.t Array768.t)
    (input_base output_base r : int) :
  0 <= r =>
  factor_eqm 16 (2 * r)
    (input_poly original) (segment_poly input input_base 16) =>
  segment_poly output output_base 8 =
    radix2_8_eval_poly input input_base (r + 288) =>
  factor_eqm 8 (r + 288)
    (input_poly original) (segment_poly output output_base 8).
proof.
  move=> Hr Hparent HlocalE.
  have Hparent' : factor_eqm 8 (r + 288)
      (input_poly original) (segment_poly input input_base 16).
  + apply factor_eqm_split2_8_right; first exact Hr.
    exact Hparent.
  have Hlocal : factor_eqm 8 (r + 288)
      (segment_poly input input_base 16)
      (segment_poly output output_base 8).
  + apply radix2_8_segment_factor_eqm.
    exact HlocalE.
  apply (factor_eqm_trans 8 (r + 288)
    (input_poly original) (segment_poly input input_base 16)
    (segment_poly output output_base 8)).
  + exact Hparent'.
  + exact Hlocal.
qed.

lemma radix2_8_refine_block_pair
    (original input output : W16.t Array768.t) (b : int) :
  0 <= b < 48 =>
  0 <= radix2_8_schedule_exp b =>
  factor_eqm 16 (2 * radix2_8_schedule_exp b)
    (input_poly original) (segment_poly input (16 * b) 16) =>
  NTRUPlus768NTTRadix2_8Algebra.radix2_8_algebra input output =>
  factor_eqm 8 (radix2_8_schedule_exp b)
      (input_poly original) (segment_poly output (16 * b) 8) /\
  factor_eqm 8 (radix2_8_schedule_exp b + 288)
      (input_poly original) (segment_poly output (16 * b + 8) 8).
proof.
  move=> Hb He Hparent Halg.
  split.
  + apply (radix2_8_refine_left original input output
      (16 * b) (16 * b) (radix2_8_schedule_exp b)).
    - exact He.
    - exact Hparent.
    - exact (radix2_8_segment_left_evalE input output b Hb He Halg).
  + apply (radix2_8_refine_right original input output
      (16 * b) (16 * b + 8) (radix2_8_schedule_exp b)).
    - exact He.
    - exact Hparent.
    - exact (radix2_8_segment_right_evalE input output b Hb He Halg).
qed.

lemma radix2_16_semantics_parent_at
    (original input : W16.t Array768.t) (b : int) :
  radix2_16_semantics original input =>
  0 <= b < 48 =>
  0 <= radix2_8_schedule_exp b /\
  factor_eqm 16 (2 * radix2_8_schedule_exp b)
    (input_poly original) (segment_poly input (16 * b) 16).
proof.
  move=> Hsem Hb.
  rewrite /radix2_16_semantics in Hsem.
  have [H4 Hrest1] := Hsem.
  have [H292 Hrest2] := Hrest1.
  have [H148 Hrest3] := Hrest2.
  have [H436 Hrest4] := Hrest3.
  have [H76 Hrest5] := Hrest4.
  have [H364 Hrest6] := Hrest5.
  have [H220 Hrest7] := Hrest6.
  have [H508 Hrest8] := Hrest7.
  have [H28 Hrest9] := Hrest8.
  have [H316 Hrest10] := Hrest9.
  have [H172 Hrest11] := Hrest10.
  have [H460 Hrest12] := Hrest11.
  have [H100 Hrest13] := Hrest12.
  have [H388 Hrest14] := Hrest13.
  have [H244 Hrest15] := Hrest14.
  have [H532 Hrest16] := Hrest15.
  have [H52 Hrest17] := Hrest16.
  have [H340 Hrest18] := Hrest17.
  have [H196 Hrest19] := Hrest18.
  have [H484 Hrest20] := Hrest19.
  have [H124 Hrest21] := Hrest20.
  have [H412 Hrest22] := Hrest21.
  have [H268 Hrest23] := Hrest22.
  have [H556 Hrest24] := Hrest23.
  have [H20 Hrest25] := Hrest24.
  have [H308 Hrest26] := Hrest25.
  have [H164 Hrest27] := Hrest26.
  have [H452 Hrest28] := Hrest27.
  have [H92 Hrest29] := Hrest28.
  have [H380 Hrest30] := Hrest29.
  have [H236 Hrest31] := Hrest30.
  have [H524 Hrest32] := Hrest31.
  have [H44 Hrest33] := Hrest32.
  have [H332 Hrest34] := Hrest33.
  have [H188 Hrest35] := Hrest34.
  have [H476 Hrest36] := Hrest35.
  have [H116 Hrest37] := Hrest36.
  have [H404 Hrest38] := Hrest37.
  have [H260 Hrest39] := Hrest38.
  have [H548 Hrest40] := Hrest39.
  have [H68 Hrest41] := Hrest40.
  have [H356 Hrest42] := Hrest41.
  have [H212 Hrest43] := Hrest42.
  have [H500 Hrest44] := Hrest43.
  have [H140 Hrest45] := Hrest44.
  have [H428 Hrest46] := Hrest45.
  have [H284 H572] := Hrest46.

  case (b = 0) => Hb0.
  + move: Hb0 => ->.
    rewrite (radix2_8_schedule_expE 0 _) 1://
            radix2_8_schedule_expsE /=.
    exact H4.
  case (b = 1) => Hb1.
  + move: Hb1 => ->.
    rewrite (radix2_8_schedule_expE 1 _) 1://
            radix2_8_schedule_expsE /=.
    exact H292.
  case (b = 2) => Hb2.
  + move: Hb2 => ->.
    rewrite (radix2_8_schedule_expE 2 _) 1://
            radix2_8_schedule_expsE /=.
    exact H148.
  case (b = 3) => Hb3.
  + move: Hb3 => ->.
    rewrite (radix2_8_schedule_expE 3 _) 1://
            radix2_8_schedule_expsE /=.
    exact H436.
  case (b = 4) => Hb4.
  + move: Hb4 => ->.
    rewrite (radix2_8_schedule_expE 4 _) 1://
            radix2_8_schedule_expsE /=.
    exact H76.
  case (b = 5) => Hb5.
  + move: Hb5 => ->.
    rewrite (radix2_8_schedule_expE 5 _) 1://
            radix2_8_schedule_expsE /=.
    exact H364.
  case (b = 6) => Hb6.
  + move: Hb6 => ->.
    rewrite (radix2_8_schedule_expE 6 _) 1://
            radix2_8_schedule_expsE /=.
    exact H220.
  case (b = 7) => Hb7.
  + move: Hb7 => ->.
    rewrite (radix2_8_schedule_expE 7 _) 1://
            radix2_8_schedule_expsE /=.
    exact H508.
  case (b = 8) => Hb8.
  + move: Hb8 => ->.
    rewrite (radix2_8_schedule_expE 8 _) 1://
            radix2_8_schedule_expsE /=.
    exact H28.
  case (b = 9) => Hb9.
  + move: Hb9 => ->.
    rewrite (radix2_8_schedule_expE 9 _) 1://
            radix2_8_schedule_expsE /=.
    exact H316.
  case (b = 10) => Hb10.
  + move: Hb10 => ->.
    rewrite (radix2_8_schedule_expE 10 _) 1://
            radix2_8_schedule_expsE /=.
    exact H172.
  case (b = 11) => Hb11.
  + move: Hb11 => ->.
    rewrite (radix2_8_schedule_expE 11 _) 1://
            radix2_8_schedule_expsE /=.
    exact H460.
  case (b = 12) => Hb12.
  + move: Hb12 => ->.
    rewrite (radix2_8_schedule_expE 12 _) 1://
            radix2_8_schedule_expsE /=.
    exact H100.
  case (b = 13) => Hb13.
  + move: Hb13 => ->.
    rewrite (radix2_8_schedule_expE 13 _) 1://
            radix2_8_schedule_expsE /=.
    exact H388.
  case (b = 14) => Hb14.
  + move: Hb14 => ->.
    rewrite (radix2_8_schedule_expE 14 _) 1://
            radix2_8_schedule_expsE /=.
    exact H244.
  case (b = 15) => Hb15.
  + move: Hb15 => ->.
    rewrite (radix2_8_schedule_expE 15 _) 1://
            radix2_8_schedule_expsE /=.
    exact H532.
  case (b = 16) => Hb16.
  + move: Hb16 => ->.
    rewrite (radix2_8_schedule_expE 16 _) 1://
            radix2_8_schedule_expsE /=.
    exact H52.
  case (b = 17) => Hb17.
  + move: Hb17 => ->.
    rewrite (radix2_8_schedule_expE 17 _) 1://
            radix2_8_schedule_expsE /=.
    exact H340.
  case (b = 18) => Hb18.
  + move: Hb18 => ->.
    rewrite (radix2_8_schedule_expE 18 _) 1://
            radix2_8_schedule_expsE /=.
    exact H196.
  case (b = 19) => Hb19.
  + move: Hb19 => ->.
    rewrite (radix2_8_schedule_expE 19 _) 1://
            radix2_8_schedule_expsE /=.
    exact H484.
  case (b = 20) => Hb20.
  + move: Hb20 => ->.
    rewrite (radix2_8_schedule_expE 20 _) 1://
            radix2_8_schedule_expsE /=.
    exact H124.
  case (b = 21) => Hb21.
  + move: Hb21 => ->.
    rewrite (radix2_8_schedule_expE 21 _) 1://
            radix2_8_schedule_expsE /=.
    exact H412.
  case (b = 22) => Hb22.
  + move: Hb22 => ->.
    rewrite (radix2_8_schedule_expE 22 _) 1://
            radix2_8_schedule_expsE /=.
    exact H268.
  case (b = 23) => Hb23.
  + move: Hb23 => ->.
    rewrite (radix2_8_schedule_expE 23 _) 1://
            radix2_8_schedule_expsE /=.
    exact H556.
  case (b = 24) => Hb24.
  + move: Hb24 => ->.
    rewrite (radix2_8_schedule_expE 24 _) 1://
            radix2_8_schedule_expsE /=.
    exact H20.
  case (b = 25) => Hb25.
  + move: Hb25 => ->.
    rewrite (radix2_8_schedule_expE 25 _) 1://
            radix2_8_schedule_expsE /=.
    exact H308.
  case (b = 26) => Hb26.
  + move: Hb26 => ->.
    rewrite (radix2_8_schedule_expE 26 _) 1://
            radix2_8_schedule_expsE /=.
    exact H164.
  case (b = 27) => Hb27.
  + move: Hb27 => ->.
    rewrite (radix2_8_schedule_expE 27 _) 1://
            radix2_8_schedule_expsE /=.
    exact H452.
  case (b = 28) => Hb28.
  + move: Hb28 => ->.
    rewrite (radix2_8_schedule_expE 28 _) 1://
            radix2_8_schedule_expsE /=.
    exact H92.
  case (b = 29) => Hb29.
  + move: Hb29 => ->.
    rewrite (radix2_8_schedule_expE 29 _) 1://
            radix2_8_schedule_expsE /=.
    exact H380.
  case (b = 30) => Hb30.
  + move: Hb30 => ->.
    rewrite (radix2_8_schedule_expE 30 _) 1://
            radix2_8_schedule_expsE /=.
    exact H236.
  case (b = 31) => Hb31.
  + move: Hb31 => ->.
    rewrite (radix2_8_schedule_expE 31 _) 1://
            radix2_8_schedule_expsE /=.
    exact H524.
  case (b = 32) => Hb32.
  + move: Hb32 => ->.
    rewrite (radix2_8_schedule_expE 32 _) 1://
            radix2_8_schedule_expsE /=.
    exact H44.
  case (b = 33) => Hb33.
  + move: Hb33 => ->.
    rewrite (radix2_8_schedule_expE 33 _) 1://
            radix2_8_schedule_expsE /=.
    exact H332.
  case (b = 34) => Hb34.
  + move: Hb34 => ->.
    rewrite (radix2_8_schedule_expE 34 _) 1://
            radix2_8_schedule_expsE /=.
    exact H188.
  case (b = 35) => Hb35.
  + move: Hb35 => ->.
    rewrite (radix2_8_schedule_expE 35 _) 1://
            radix2_8_schedule_expsE /=.
    exact H476.
  case (b = 36) => Hb36.
  + move: Hb36 => ->.
    rewrite (radix2_8_schedule_expE 36 _) 1://
            radix2_8_schedule_expsE /=.
    exact H116.
  case (b = 37) => Hb37.
  + move: Hb37 => ->.
    rewrite (radix2_8_schedule_expE 37 _) 1://
            radix2_8_schedule_expsE /=.
    exact H404.
  case (b = 38) => Hb38.
  + move: Hb38 => ->.
    rewrite (radix2_8_schedule_expE 38 _) 1://
            radix2_8_schedule_expsE /=.
    exact H260.
  case (b = 39) => Hb39.
  + move: Hb39 => ->.
    rewrite (radix2_8_schedule_expE 39 _) 1://
            radix2_8_schedule_expsE /=.
    exact H548.
  case (b = 40) => Hb40.
  + move: Hb40 => ->.
    rewrite (radix2_8_schedule_expE 40 _) 1://
            radix2_8_schedule_expsE /=.
    exact H68.
  case (b = 41) => Hb41.
  + move: Hb41 => ->.
    rewrite (radix2_8_schedule_expE 41 _) 1://
            radix2_8_schedule_expsE /=.
    exact H356.
  case (b = 42) => Hb42.
  + move: Hb42 => ->.
    rewrite (radix2_8_schedule_expE 42 _) 1://
            radix2_8_schedule_expsE /=.
    exact H212.
  case (b = 43) => Hb43.
  + move: Hb43 => ->.
    rewrite (radix2_8_schedule_expE 43 _) 1://
            radix2_8_schedule_expsE /=.
    exact H500.
  case (b = 44) => Hb44.
  + move: Hb44 => ->.
    rewrite (radix2_8_schedule_expE 44 _) 1://
            radix2_8_schedule_expsE /=.
    exact H140.
  case (b = 45) => Hb45.
  + move: Hb45 => ->.
    rewrite (radix2_8_schedule_expE 45 _) 1://
            radix2_8_schedule_expsE /=.
    exact H428.
  case (b = 46) => Hb46.
  + move: Hb46 => ->.
    rewrite (radix2_8_schedule_expE 46 _) 1://
            radix2_8_schedule_expsE /=.
    exact H284.
  have -> : b = 47 by smt().
  rewrite (radix2_8_schedule_expE 47 _) 1://
          radix2_8_schedule_expsE /=.
  exact H572.
qed.

op radix2_8_semantics
    (original output : W16.t Array768.t) : bool =
  forall b, 0 <= b < 48 =>
    factor_eqm 8 (radix2_8_schedule_exp b)
      (input_poly original) (segment_poly output (16 * b) 8) /\
    factor_eqm 8 (radix2_8_schedule_exp b + 288)
      (input_poly original) (segment_poly output (16 * b + 8) 8).

lemma radix2_8_algebra_refines_radix2_16_semantics
    (original input output : W16.t Array768.t) :
  radix2_16_semantics original input =>
  NTRUPlus768NTTRadix2_8Algebra.radix2_8_algebra input output =>
  radix2_8_semantics original output.
proof.
  move=> Hsem Halg.
  rewrite /radix2_8_semantics.
  move=> b Hb.
  have [He Hparent] :=
    radix2_16_semantics_parent_at original input b Hsem Hb.
  exact (radix2_8_refine_block_pair
    original input output b Hb He Hparent Halg).
qed.

lemma radix2_8_spec_semantics
    (original input : W16.t Array768.t) :
  radix2_16_semantics original input =>
  NTRUPlus768NTTRadix2_8Algebra.centered_input_shape input =>
  radix2_8_semantics original
    (NTRUPlus768NTTRadix2_8Proof.radix2_8_spec input).
proof.
  move=> Hsem Hshape.
  apply (radix2_8_algebra_refines_radix2_16_semantics
    original input (NTRUPlus768NTTRadix2_8Proof.radix2_8_spec input)).
  + exact Hsem.
  + rewrite NTRUPlus768NTTRadix2_8Algebra.radix2_8_word_specE.
    exact (NTRUPlus768NTTRadix2_8Algebra.radix2_8_spec_algebra input Hshape).
qed.

lemma ntt_radix2_8_semantics_functional
    (original rp0 : W16.t Array768.t) :
  radix2_16_semantics original rp0 =>
  NTRUPlus768NTTRadix2_8Algebra.centered_input_shape rp0 =>
  hoare [NTRUPlus768NTTRadix2_8.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_8 :
    rp = rp0 ==> radix2_8_semantics original res].
proof.
  move=> Hsem Hshape.
  conseq
    (NTRUPlus768NTTRadix2_8Algebra.ntt_radix2_8_algebra_functional
      rp0 Hshape) => />.
  move=> result Halg.
  apply (radix2_8_algebra_refines_radix2_16_semantics original rp0 result).
  + exact Hsem.
  + exact Halg.
qed.

lemma ntt_radix2_8_correct_semantics
    (original rp0 : W16.t Array768.t) :
  radix2_16_semantics original rp0 =>
  NTRUPlus768NTTRadix2_8Algebra.centered_input_shape rp0 =>
  phoare [NTRUPlus768NTTRadix2_8.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_8 :
    rp = rp0 ==> radix2_8_semantics original res] = 1%r.
proof.
  move=> Hsem Hshape.
  have Hfunctional :
      hoare [NTRUPlus768NTTRadix2_8.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_8 :
        rp = rp0 ==> radix2_8_semantics original res].
  + apply ntt_radix2_8_semantics_functional.
    - exact Hsem.
    - exact Hshape.
  by conseq NTRUPlus768NTTRadix2_8Proof.ntt_radix2_8_lossless Hfunctional.
qed.
