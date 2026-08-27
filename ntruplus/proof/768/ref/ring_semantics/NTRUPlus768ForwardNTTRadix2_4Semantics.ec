require import AllCore IntDiv List Ring StdBigop StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array4 Array768.
require import NTRUPlus768BasemulAlgebra NTRUPlus768NTTSchedule.
require import NTRUPlus768PolyBasemulAlgebra NTRUPlus768PolyBasemulProof.
require import NTRUPlus768CyclotomicFactorization.
require import NTRUPlus768EvaluationSemantics.
require import NTRUPlus768TerminalRepresentation.
require import NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768ForwardNTTRadix3Semantics.
require import NTRUPlus768ForwardNTTRadix2_64Semantics.
require import NTRUPlus768ForwardNTTRadix2_32Semantics.
require import NTRUPlus768ForwardNTTRadix2_8Semantics.
require import NTRUPlus768NTTRadix2_4.
require import NTRUPlus768NTTRadix2_4Algebra NTRUPlus768NTTRadix2_4Proof.

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

(* The final binary layer refines every degree-8 representative into two
   degree-4 representatives. *)

op segment2_4_poly (a : W16.t Array768.t) (base : int) : NTRUPoly.poly =
  segment_poly a base 4 +
  segment_poly a (base + 4) 4 * exp X 4.

op radix2_4_eval_poly
    (a : W16.t Array768.t) (base e : int) : NTRUPoly.poly =
  segment_poly a base 4 +
  segment_poly a (base + 4) 4 * root_poly e.

lemma segment_poly_split2_4 (a : W16.t Array768.t) (base : int) :
  segment_poly a base 8 = segment2_4_poly a base.
proof.
  rewrite /segment2_4_poly.
  rewrite (segment_poly_split a base 4 4) 1:// 1://.
  done.
qed.

lemma radix2_4_eval_factor_eqm
    (a : W16.t Array768.t) (base e : int) :
  factor_eqm 4 e
    (segment2_4_poly a base) (radix2_4_eval_poly a base e).
proof.
  rewrite /factor_eqm /schedule_factor_modulus.
  exists (-(segment_poly a (base + 4) 4)).
  rewrite /segment2_4_poly /radix2_4_eval_poly /root_poly.
  ring.
qed.

lemma schedule_modulus_split2_4 (r : int) :
  0 <= r =>
  schedule_factor_modulus 8 (2 * r) =
  schedule_factor_modulus 4 r *
    schedule_factor_modulus 4 (r + 288).
proof.
  move=> Hr.
  move: (factor_split2 X 4 r _ Hr); first smt().
  rewrite /factor /schedule_factor_modulus /=.
  done.
qed.

lemma factor_eqm_split2_4_left
    (r : int) (p q : NTRUPoly.poly) :
  0 <= r =>
  factor_eqm 8 (2 * r) p q =>
  factor_eqm 4 r p q.
proof.
  move=> Hr.
  apply factor_eqm_weaken.
  exists (schedule_factor_modulus 4 (r + 288)).
  exact (schedule_modulus_split2_4 r Hr).
qed.

lemma factor_eqm_split2_4_right
    (r : int) (p q : NTRUPoly.poly) :
  0 <= r =>
  factor_eqm 8 (2 * r) p q =>
  factor_eqm 4 (r + 288) p q.
proof.
  move=> Hr.
  apply factor_eqm_weaken.
  exists (schedule_factor_modulus 4 r).
  rewrite schedule_modulus_split2_4 1:Hr.
  ring.
qed.

lemma radix2_4_pair_child0_eqm (a0 a1 r : int) :
  (NTRUPlus768NTTRadix2_4Algebra.radix2_4_pair_math
     a0 a1 (schedule_root r)).`1 %% q =
  (a0 + a1 * schedule_root r) %% q.
proof.
  by rewrite /NTRUPlus768NTTRadix2_4Algebra.radix2_4_pair_math.
qed.

lemma radix2_4_pair_child1_eqm (a0 a1 r : int) :
  0 <= r =>
  (NTRUPlus768NTTRadix2_4Algebra.radix2_4_pair_math
     a0 a1 (schedule_root r)).`2 %% q =
  (a0 + a1 * schedule_root (r + 288)) %% q.
proof.
  move=> Hr.
  rewrite /NTRUPlus768NTTRadix2_4Algebra.radix2_4_pair_math.
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

op linear2_4_remainder_poly
    (a : W16.t Array768.t) (base c : int) : NTRUPoly.poly =
  PCA.bigi predT
    (fun i =>
      polyC
        (lift_int
          (coeff a.[i + base] +
           coeff a.[i + base + 4] * c)) *
      exp X i)
    0 4.

lemma linear2_4_remainder_polyE
    (a : W16.t Array768.t) (base c : int) :
  linear2_4_remainder_poly a base c =
  segment_poly a base 4 +
  polyC (lift_int c) * segment_poly a (base + 4) 4.
proof.
  rewrite /linear2_4_remainder_poly /segment_poly.
  have Hdist :
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
  have Hsplit :
      PCA.bigi predT
        (fun i => polyC (lift_word a.[i + base]) * exp X i)
        0 4 +
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c) *
            (polyC (lift_word a.[i + (base + 4)]) * exp X i))
        0 4 =
      PCA.bigi predT
        (fun i =>
          polyC (lift_word a.[i + base]) * exp X i +
          polyC (lift_int c) *
            (polyC (lift_word a.[i + (base + 4)]) * exp X i))
        0 4.
  + apply/eq_sym.
    exact
      (PCA.big_split predT
        (fun i => polyC (lift_word a.[i + base]) * exp X i)
        (fun i =>
          polyC (lift_int c) *
            (polyC (lift_word a.[i + (base + 4)]) * exp X i))
        (range 0 4)).
  rewrite Hdist Hsplit.
  apply PCA.eq_big_int => i Hi.
  rewrite /lift_word /lift_int /=.
  rewrite CycloFq.incyclocoeffD CycloFq.incyclocoeffM.
  rewrite NTRUPoly.polyCD NTRUPoly.polyCM.
  rewrite poly_mul_add_right.
  congr.
  have Hidx : i + base + 4 = i + (base + 4) by ring.
  rewrite Hidx.
  apply poly_mul_reorder.
qed.

lemma segment_poly_linear2_4E
    (input output : W16.t Array768.t)
    (input_base output_base c : int) :
  (forall i, 0 <= i < 4 =>
    coeff output.[i + output_base] %% q =
    (coeff input.[i + input_base] +
     coeff input.[i + input_base + 4] * c) %% q) =>
  segment_poly output output_base 4 =
  linear2_4_remainder_poly input input_base c.
proof.
  move=> Hcoeff.
  rewrite /segment_poly /linear2_4_remainder_poly.
  apply PCA.eq_big_int => i Hi.
  have Hmod := Hcoeff i Hi.
  have Elift :
      lift_word output.[i + output_base] =
      lift_int
        (coeff input.[i + input_base] +
         coeff input.[i + input_base + 4] * c).
  + rewrite /lift_word.
    apply lift_int_eq.
    exact Hmod.
  by rewrite /= Elift.
qed.

lemma linear2_4_remainder_radix2_evalE
    (a : W16.t Array768.t) (base e : int) :
  0 <= e =>
  linear2_4_remainder_poly a base (schedule_root e) =
  radix2_4_eval_poly a base e.
proof.
  move=> He.
  rewrite linear2_4_remainder_polyE /radix2_4_eval_poly /root_poly.
  rewrite schedule_root_fieldE 1:He.
  ring.
qed.

lemma segment_poly_radix2_4_evalE
    (input output : W16.t Array768.t)
    (input_base output_base e : int) :
  0 <= e =>
  (forall i, 0 <= i < 4 =>
    coeff output.[i + output_base] %% q =
    (coeff input.[i + input_base] +
     coeff input.[i + input_base + 4] * schedule_root e) %% q) =>
  segment_poly output output_base 4 =
  radix2_4_eval_poly input input_base e.
proof.
  move=> He Hcoeff.
  have Hsegment :
      segment_poly output output_base 4 =
      linear2_4_remainder_poly input input_base (schedule_root e).
  + apply segment_poly_linear2_4E.
    exact Hcoeff.
  rewrite Hsegment.
  apply linear2_4_remainder_radix2_evalE.
  exact He.
qed.


op radix2_4_schedule_exp (b : int) : int =
  zetas192_exp
    (NTRUPlus768NTTRadix2_4Algebra.radix2_4_schedule_index b).

op radix2_4_schedule_exps : int list =
  take 96 (drop ntt_radix2_4_start zetas192_exponents).

lemma radix2_4_schedule_expsE :
  radix2_4_schedule_exps = [
    1; 145; 73; 217; 37; 181; 109; 253;
    19; 163; 91; 235; 55; 199; 127; 271;
    7; 151; 79; 223; 43; 187; 115; 259;
    25; 169; 97; 241; 61; 205; 133; 277;
    13; 157; 85; 229; 49; 193; 121; 265;
    31; 175; 103; 247; 67; 211; 139; 283;
    5; 149; 77; 221; 41; 185; 113; 257;
    23; 167; 95; 239; 59; 203; 131; 275;
    11; 155; 83; 227; 47; 191; 119; 263;
    29; 173; 101; 245; 65; 209; 137; 281;
    17; 161; 89; 233; 53; 197; 125; 269;
    35; 179; 107; 251; 71; 215; 143; 287
  ].
proof.
  by rewrite /radix2_4_schedule_exps /ntt_radix2_4_start
             /zetas192_exponents /=.
qed.

lemma radix2_4_schedule_expE (b : int) :
  0 <= b < 96 =>
  radix2_4_schedule_exp b = nth witness radix2_4_schedule_exps b.
proof.
  move=> Hb.
  rewrite /radix2_4_schedule_exp
          /NTRUPlus768NTTRadix2_4Algebra.radix2_4_schedule_index
          /ntt_radix2_4_start /zetas192_exp /radix2_4_schedule_exps.
  smt(nth_take nth_drop).
qed.

lemma radix2_4_schedule_exp_terminalE (b : int) :
  0 <= b < 96 =>
  radix2_4_schedule_exp b = terminal_exp b.
proof.
  move=> Hb.
  rewrite /radix2_4_schedule_exp
          /NTRUPlus768NTTRadix2_4Algebra.radix2_4_schedule_index
          /ntt_radix2_4_start.
  by rewrite terminal_exponents_suffix 1:Hb.
qed.

lemma radix2_4_schedule_exp_nonneg (b : int) :
  0 <= b < 96 =>
  0 <= radix2_4_schedule_exp b.
proof.
  move=> Hb.
  rewrite (radix2_4_schedule_exp_terminalE b Hb).
  exact (terminal_exp_nonneg b Hb).
qed.

lemma radix2_4_zeta_scheduleE (b : int) :
  NTRUPlus768NTTRadix2_4Algebra.radix2_4_zeta_root b =
  schedule_root (radix2_4_schedule_exp b).
proof.
  by rewrite /NTRUPlus768NTTRadix2_4Algebra.radix2_4_zeta_root
             /radix2_4_schedule_exp /schedule_root.
qed.

lemma radix2_4_segment_left_evalE
    (input output : W16.t Array768.t) (b : int) :
  0 <= b < 96 =>
  0 <= radix2_4_schedule_exp b =>
  NTRUPlus768NTTRadix2_4Algebra.radix2_4_algebra input output =>
  segment_poly output (8 * b) 4 =
    radix2_4_eval_poly input (8 * b) (radix2_4_schedule_exp b).
proof.
  move=> Hb He Halg.
  apply segment_poly_radix2_4_evalE; first exact He.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 8 * b) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_4Algebra.radix2_4_math
          /NTRUPlus768NTTRadix2_4Algebra.radix2_4_block_id
          /NTRUPlus768NTTRadix2_4Algebra.radix2_4_block_base
          /NTRUPlus768NTTRadix2_4Algebra.radix2_4_lane_index
          /NTRUPlus768NTTRadix2_4Algebra.radix2_4_block_offset
          /NTRUPlus768NTTRadix2_4Algebra.double_block
          /NTRUPlus768NTTRadix2_4Algebra.block.
  have -> : (i + 8 * b) %/ 8 = b by smt().
  have -> : (i + 8 * b) %% 8 = i by smt().
  move=> Hcoeff.
  move: Hcoeff; simplify.
  rewrite ifT 1:/# ifT 1:/# /=.
  move=> Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_4Algebra.radix2_4_pair_math_at
          radix2_4_zeta_scheduleE radix2_4_pair_child0_eqm in Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_4Algebra.block
          [8 * b + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_4_segment_right_evalE
    (input output : W16.t Array768.t) (b : int) :
  0 <= b < 96 =>
  0 <= radix2_4_schedule_exp b =>
  NTRUPlus768NTTRadix2_4Algebra.radix2_4_algebra input output =>
  segment_poly output (8 * b + 4) 4 =
    radix2_4_eval_poly input (8 * b) (radix2_4_schedule_exp b + 288).
proof.
  move=> Hb He Halg.
  apply segment_poly_radix2_4_evalE; first smt().
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + (8 * b + 4)) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_4Algebra.radix2_4_math
          /NTRUPlus768NTTRadix2_4Algebra.radix2_4_block_id
          /NTRUPlus768NTTRadix2_4Algebra.radix2_4_block_base
          /NTRUPlus768NTTRadix2_4Algebra.radix2_4_lane_index
          /NTRUPlus768NTTRadix2_4Algebra.radix2_4_block_offset
          /NTRUPlus768NTTRadix2_4Algebra.double_block
          /NTRUPlus768NTTRadix2_4Algebra.block.
  have -> : (i + (8 * b + 4)) %/ 8 = b by smt().
  have -> : (i + (8 * b + 4)) %% 8 = i + 4 by smt().
  move=> Hcoeff.
  move: Hcoeff; simplify.
  rewrite ifF 1:/# ifF 1:/# /=.
  move=> Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_4Algebra.radix2_4_pair_math_at
          radix2_4_zeta_scheduleE in Hcoeff.
  rewrite radix2_4_pair_child1_eqm 1:He in Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_4Algebra.block
          [8 * b + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_4_segment_factor_eqm
    (input output : W16.t Array768.t)
    (input_base output_base e : int) :
  segment_poly output output_base 4 =
    radix2_4_eval_poly input input_base e =>
  factor_eqm 4 e
    (segment_poly input input_base 8)
    (segment_poly output output_base 4).
proof.
  move=> Houtput.
  rewrite segment_poly_split2_4 Houtput.
  exact (radix2_4_eval_factor_eqm input input_base e).
qed.

lemma radix2_4_refine_left
    (original input output : W16.t Array768.t)
    (input_base output_base r : int) :
  0 <= r =>
  factor_eqm 8 (2 * r)
    (input_poly original) (segment_poly input input_base 8) =>
  segment_poly output output_base 4 =
    radix2_4_eval_poly input input_base r =>
  factor_eqm 4 r
    (input_poly original) (segment_poly output output_base 4).
proof.
  move=> Hr Hparent HlocalE.
  have Hparent' : factor_eqm 4 r
      (input_poly original) (segment_poly input input_base 8).
  + apply factor_eqm_split2_4_left; first exact Hr.
    exact Hparent.
  have Hlocal : factor_eqm 4 r
      (segment_poly input input_base 8)
      (segment_poly output output_base 4).
  + apply radix2_4_segment_factor_eqm.
    exact HlocalE.
  apply (factor_eqm_trans 4 r
    (input_poly original) (segment_poly input input_base 8)
    (segment_poly output output_base 4)).
  + exact Hparent'.
  + exact Hlocal.
qed.

lemma radix2_4_refine_right
    (original input output : W16.t Array768.t)
    (input_base output_base r : int) :
  0 <= r =>
  factor_eqm 8 (2 * r)
    (input_poly original) (segment_poly input input_base 8) =>
  segment_poly output output_base 4 =
    radix2_4_eval_poly input input_base (r + 288) =>
  factor_eqm 4 (r + 288)
    (input_poly original) (segment_poly output output_base 4).
proof.
  move=> Hr Hparent HlocalE.
  have Hparent' : factor_eqm 4 (r + 288)
      (input_poly original) (segment_poly input input_base 8).
  + apply factor_eqm_split2_4_right; first exact Hr.
    exact Hparent.
  have Hlocal : factor_eqm 4 (r + 288)
      (segment_poly input input_base 8)
      (segment_poly output output_base 4).
  + apply radix2_4_segment_factor_eqm.
    exact HlocalE.
  apply (factor_eqm_trans 4 (r + 288)
    (input_poly original) (segment_poly input input_base 8)
    (segment_poly output output_base 4)).
  + exact Hparent'.
  + exact Hlocal.
qed.

lemma radix2_4_refine_block_pair
    (original input output : W16.t Array768.t) (b : int) :
  0 <= b < 96 =>
  0 <= radix2_4_schedule_exp b =>
  factor_eqm 8 (2 * radix2_4_schedule_exp b)
    (input_poly original) (segment_poly input (8 * b) 8) =>
  NTRUPlus768NTTRadix2_4Algebra.radix2_4_algebra input output =>
  factor_eqm 4 (radix2_4_schedule_exp b)
      (input_poly original) (segment_poly output (8 * b) 4) /\
  factor_eqm 4 (radix2_4_schedule_exp b + 288)
      (input_poly original) (segment_poly output (8 * b + 4) 4).
proof.
  move=> Hb He Hparent Halg.
  split.
  + apply (radix2_4_refine_left original input output
      (8 * b) (8 * b) (radix2_4_schedule_exp b)).
    - exact He.
    - exact Hparent.
    - exact (radix2_4_segment_left_evalE input output b Hb He Halg).
  + apply (radix2_4_refine_right original input output
      (8 * b) (8 * b + 4) (radix2_4_schedule_exp b)).
    - exact He.
    - exact Hparent.
    - exact (radix2_4_segment_right_evalE input output b Hb He Halg).
qed.


op radix2_8_parent_exps : int list =
  flatten
    (map (fun e => [e; e + 288]) radix2_8_schedule_exps).

lemma radix2_4_parent_expsE :
  radix2_8_parent_exps =
  map (fun e => 2 * e) radix2_4_schedule_exps.
proof.
  by rewrite /radix2_8_parent_exps
             radix2_8_schedule_expsE radix2_4_schedule_expsE /=.
qed.

lemma radix2_4_parent_scheduleE (b : int) :
  0 <= b < 96 =>
  2 * radix2_4_schedule_exp b =
    if b %% 2 = 0 then
      radix2_8_schedule_exp (b %/ 2)
    else
      radix2_8_schedule_exp (b %/ 2) + 288.
proof.
  move=> Hb.
  have Hhalf : 0 <= b %/ 2 < 48 by smt().
  have Hsize8 : size radix2_8_schedule_exps = 48
    by rewrite radix2_8_schedule_expsE /=.
  have Hsize4 : size radix2_4_schedule_exps = 96
    by rewrite radix2_4_schedule_expsE /=.
  have Hinterleave :=
    nth_generated_figure22_pair radix2_8_schedule_exps b _.
  + rewrite Hsize8.
    smt().
  rewrite /ell /= in Hinterleave.
  have Hlists :
      nth witness radix2_8_parent_exps b =
      nth witness (map (fun e => 2 * e) radix2_4_schedule_exps) b
    by rewrite radix2_4_parent_expsE.
  rewrite /radix2_8_parent_exps Hinterleave in Hlists.
  rewrite (nth_map witness) 1:/# in Hlists.
  rewrite (radix2_4_schedule_expE b Hb)
          (radix2_8_schedule_expE (b %/ 2) Hhalf).
  move: Hlists; simplify.
  smt().
qed.

lemma radix2_8_semantics_parent_at
    (original input : W16.t Array768.t) (b : int) :
  radix2_8_semantics original input =>
  0 <= b < 96 =>
  0 <= radix2_4_schedule_exp b /\
  factor_eqm 8 (2 * radix2_4_schedule_exp b)
    (input_poly original) (segment_poly input (8 * b) 8).
proof.
  move=> Hsem Hb.
  have Hhalf : 0 <= b %/ 2 < 48 by smt().
  have [Hleft Hright] := Hsem (b %/ 2) Hhalf.
  have Hschedule := radix2_4_parent_scheduleE b Hb.
  split.
  + exact (radix2_4_schedule_exp_nonneg b Hb).
  + move: Hschedule.
    case (b %% 2 = 0).
    - simplify.
      move=> Heven Hschedule.
      have -> :
          2 * radix2_4_schedule_exp b =
          radix2_8_schedule_exp (b %/ 2)
        by exact Hschedule.
      have -> : 8 * b = 16 * (b %/ 2) by smt().
      exact Hleft.
    - simplify.
      move=> Hneven Hschedule.
      have -> :
          2 * radix2_4_schedule_exp b =
          radix2_8_schedule_exp (b %/ 2) + 288
        by exact Hschedule.
      have -> : 8 * b = 16 * (b %/ 2) + 8 by smt().
      exact Hright.
qed.

op radix2_4_semantics
    (original output : W16.t Array768.t) : bool =
  forall b, 0 <= b < 96 =>
    factor_eqm 4 (radix2_4_schedule_exp b)
      (input_poly original) (segment_poly output (8 * b) 4) /\
    factor_eqm 4 (radix2_4_schedule_exp b + 288)
      (input_poly original) (segment_poly output (8 * b + 4) 4).

lemma radix2_4_algebra_refines_radix2_8_semantics
    (original input output : W16.t Array768.t) :
  radix2_8_semantics original input =>
  NTRUPlus768NTTRadix2_4Algebra.radix2_4_algebra input output =>
  radix2_4_semantics original output.
proof.
  move=> Hsem Halg.
  rewrite /radix2_4_semantics.
  move=> b Hb.
  have [He Hparent] :=
    radix2_8_semantics_parent_at original input b Hsem Hb.
  exact (radix2_4_refine_block_pair
    original input output b Hb He Hparent Halg).
qed.

lemma radix2_4_spec_semantics
    (original input : W16.t Array768.t) :
  radix2_8_semantics original input =>
  NTRUPlus768NTTRadix2_4Algebra.centered_input_shape input =>
  radix2_4_semantics original
    (NTRUPlus768NTTRadix2_4Proof.radix2_4_spec input).
proof.
  move=> Hsem Hshape.
  apply (radix2_4_algebra_refines_radix2_8_semantics
    original input (NTRUPlus768NTTRadix2_4Proof.radix2_4_spec input)).
  + exact Hsem.
  + rewrite NTRUPlus768NTTRadix2_4Algebra.radix2_4_word_specE.
    exact (NTRUPlus768NTTRadix2_4Algebra.radix2_4_spec_algebra input Hshape).
qed.

lemma ntt_radix2_4_semantics_functional
    (original rp0 : W16.t Array768.t) :
  radix2_8_semantics original rp0 =>
  NTRUPlus768NTTRadix2_4Algebra.centered_input_shape rp0 =>
  hoare [NTRUPlus768NTTRadix2_4.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_4 :
    rp = rp0 ==> radix2_4_semantics original res].
proof.
  move=> Hsem Hshape.
  conseq
    (NTRUPlus768NTTRadix2_4Algebra.ntt_radix2_4_algebra_functional
      rp0 Hshape) => />.
  move=> result Halg.
  apply (radix2_4_algebra_refines_radix2_8_semantics original rp0 result).
  + exact Hsem.
  + exact Halg.
qed.

lemma ntt_radix2_4_correct_semantics
    (original rp0 : W16.t Array768.t) :
  radix2_8_semantics original rp0 =>
  NTRUPlus768NTTRadix2_4Algebra.centered_input_shape rp0 =>
  phoare [NTRUPlus768NTTRadix2_4.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_4 :
    rp = rp0 ==> radix2_4_semantics original res] = 1%r.
proof.
  move=> Hsem Hshape.
  have Hfunctional :
      hoare [NTRUPlus768NTTRadix2_4.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_4 :
        rp = rp0 ==> radix2_4_semantics original res].
  + apply ntt_radix2_4_semantics_functional.
    - exact Hsem.
    - exact Hshape.
  by conseq NTRUPlus768NTTRadix2_4Proof.ntt_radix2_4_lossless Hfunctional.
qed.

lemma segment_poly4_block_polyE
    (a : W16.t Array768.t) (k : int) :
  0 <= k < 192 =>
  segment_poly a (4 * k) 4 = block_poly (block4 a k).
proof.
  move=> Hk.
  rewrite /segment_poly /block_poly /block_poly_fq /block4.
  rewrite !Array4.initiE 1,2,3,4:/#.
  rewrite (PCA.big_ltn 0 4) 1:/#.
  rewrite (PCA.big_ltn 1 4) 1:/#.
  rewrite (PCA.big_ltn 2 4) 1:/#.
  rewrite (PCA.big_int1 3).
  rewrite /=.
  have Hone :
      NTRUPlus768ForwardNTTRadix2_8Semantics.polyC CycloFq.one =
      NTRUPoly.PolyComRing.oner
    by done.
  rewrite !NTRUPoly.PolyComRing.expr0 !NTRUPoly.PolyComRing.expr1.
  rewrite Hone.
  have Hmulone :
      NTRUPlus768ForwardNTTRadix2_8Semantics.( * )
        (NTRUPlus768ForwardNTTRadix2_8Semantics.polyC
          (lift_word a.[4 * k]))
        NTRUPoly.PolyComRing.oner =
      NTRUPlus768ForwardNTTRadix2_8Semantics.polyC
        (lift_word a.[4 * k])
    by exact (NTRUPoly.PolyComRing.mulr1 _).
  rewrite Hmulone.
  have Hidx1 : 1 + 4 * k = 4 * k + 1 by ring.
  have Hidx2 : 2 + 4 * k = 4 * k + 2 by ring.
  have Hidx3 : 3 + 4 * k = 4 * k + 3 by ring.
  rewrite Hidx1 Hidx2 Hidx3.
  pose p0 := NTRUPlus768ForwardNTTRadix2_8Semantics.polyC
    (lift_word a.[4 * k]).
  pose p1 := NTRUPlus768ForwardNTTRadix2_8Semantics.( * )
    (NTRUPlus768ForwardNTTRadix2_8Semantics.polyC
      (lift_word a.[4 * k + 1]))
    NTRUPlus768ForwardNTTRadix2_8Semantics.X.
  pose p2 := NTRUPlus768ForwardNTTRadix2_8Semantics.( * )
    (NTRUPlus768ForwardNTTRadix2_8Semantics.polyC
      (lift_word a.[4 * k + 2]))
    (NTRUPlus768ForwardNTTRadix2_8Semantics.exp
      NTRUPlus768ForwardNTTRadix2_8Semantics.X 2).
  pose p3 := NTRUPlus768ForwardNTTRadix2_8Semantics.( * )
    (NTRUPlus768ForwardNTTRadix2_8Semantics.polyC
      (lift_word a.[4 * k + 3]))
    (NTRUPlus768ForwardNTTRadix2_8Semantics.exp
      NTRUPlus768ForwardNTTRadix2_8Semantics.X 3).
  change
    (NTRUPoly.PolyComRing.( + ) p0
       (NTRUPoly.PolyComRing.( + ) p1
         (NTRUPoly.PolyComRing.( + ) p2 p3)) =
     NTRUPoly.PolyComRing.( + )
       (NTRUPoly.PolyComRing.( + )
         (NTRUPoly.PolyComRing.( + ) p0 p1) p2) p3).
  ring.
qed.

lemma factor_eqm_terminal_eqm4
    (a : W16.t Array768.t) (p : NTRUPoly.poly) (k : int) :
  0 <= k < 192 =>
  factor_eqm 4 (figure22_index k)
    p (segment_poly a (4 * k) 4) =>
  eqm4 k p (block_poly (block4 a k)).
proof.
  move=> Hk Hfactor.
  rewrite -(segment_poly4_block_polyE a k Hk).
  rewrite /eqm4 /quartic_modulus.
  rewrite terminal_root_fieldE 1:Hk.
  rewrite /factor_eqm /schedule_factor_modulus in Hfactor.
  exact Hfactor.
qed.

lemma radix2_4_semantics_terminal_represents
    (original output : W16.t Array768.t) :
  radix2_4_semantics original output =>
  terminal_represents output (input_poly original).
proof.
  move=> Hsem.
  rewrite /terminal_represents.
  move=> k Hk.
  have Hhalf : 0 <= k %/ 2 < 96 by smt().
  have [Hleft Hright] := Hsem (k %/ 2) Hhalf.
  have Hschedule := radix2_4_schedule_exp_terminalE (k %/ 2) Hhalf.
  have Hfig := figure22_index_relation k Hk.
  apply (factor_eqm_terminal_eqm4 output (input_poly original) k Hk).
  move: Hfig.
  case (k %% 2 = 0).
  + simplify.
    move=> Heven Hfig.
    have -> :
        figure22_index k = radix2_4_schedule_exp (k %/ 2)
      by rewrite Hfig Hschedule.
    have -> : 4 * k = 8 * (k %/ 2) by smt().
    exact Hleft.
  + simplify.
    move=> Hneven Hfig.
    have -> :
        figure22_index k = radix2_4_schedule_exp (k %/ 2) + 288
      by rewrite Hfig Hschedule.
    have -> : 4 * k = 8 * (k %/ 2) + 4 by smt().
    exact Hright.
qed.

lemma radix2_4_algebra_refines_terminal_representation
    (original input output : W16.t Array768.t) :
  radix2_8_semantics original input =>
  NTRUPlus768NTTRadix2_4Algebra.radix2_4_algebra input output =>
  terminal_represents output (input_poly original).
proof.
  move=> Hsem Halg.
  apply radix2_4_semantics_terminal_represents.
  exact
    (radix2_4_algebra_refines_radix2_8_semantics
      original input output Hsem Halg).
qed.

lemma radix2_4_spec_terminal_represents
    (original input : W16.t Array768.t) :
  radix2_8_semantics original input =>
  NTRUPlus768NTTRadix2_4Algebra.centered_input_shape input =>
  terminal_represents
    (NTRUPlus768NTTRadix2_4Proof.radix2_4_spec input)
    (input_poly original).
proof.
  move=> Hsem Hshape.
  apply radix2_4_semantics_terminal_represents.
  exact (radix2_4_spec_semantics original input Hsem Hshape).
qed.

lemma ntt_radix2_4_terminal_represents_functional
    (original rp0 : W16.t Array768.t) :
  radix2_8_semantics original rp0 =>
  NTRUPlus768NTTRadix2_4Algebra.centered_input_shape rp0 =>
  hoare [NTRUPlus768NTTRadix2_4.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_4 :
    rp = rp0 ==> terminal_represents res (input_poly original)].
proof.
  move=> Hsem Hshape.
  conseq (ntt_radix2_4_semantics_functional original rp0 Hsem Hshape) => />.
  move=> result Hresult.
  exact (radix2_4_semantics_terminal_represents original result Hresult).
qed.

lemma ntt_radix2_4_correct_terminal_represents
    (original rp0 : W16.t Array768.t) :
  radix2_8_semantics original rp0 =>
  NTRUPlus768NTTRadix2_4Algebra.centered_input_shape rp0 =>
  phoare [NTRUPlus768NTTRadix2_4.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_4 :
    rp = rp0 ==> terminal_represents res (input_poly original)] = 1%r.
proof.
  move=> Hsem Hshape.
  have Hfunctional :
      hoare [NTRUPlus768NTTRadix2_4.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_4 :
        rp = rp0 ==> terminal_represents res (input_poly original)].
  + exact
      (ntt_radix2_4_terminal_represents_functional
        original rp0 Hsem Hshape).
  by conseq NTRUPlus768NTTRadix2_4Proof.ntt_radix2_4_lossless Hfunctional.
qed.
