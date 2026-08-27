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
require import NTRUPlus768NTTRadix2_16.
require import NTRUPlus768NTTRadix2_16Algebra NTRUPlus768NTTRadix2_16Proof.

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

(* The third binary layer refines every degree-32 representative into two
   degree-16 representatives. *)

op segment2_16_poly (a : W16.t Array768.t) (base : int) : NTRUPoly.poly =
  segment_poly a base 16 +
  segment_poly a (base + 16) 16 * exp X 16.

op radix2_16_eval_poly
    (a : W16.t Array768.t) (base e : int) : NTRUPoly.poly =
  segment_poly a base 16 +
  segment_poly a (base + 16) 16 * root_poly e.

lemma segment_poly_split2_16 (a : W16.t Array768.t) (base : int) :
  segment_poly a base 32 = segment2_16_poly a base.
proof.
  rewrite /segment2_16_poly.
  rewrite (segment_poly_split a base 16 16) 1:// 1://.
  done.
qed.

lemma radix2_16_eval_factor_eqm
    (a : W16.t Array768.t) (base e : int) :
  factor_eqm 16 e
    (segment2_16_poly a base) (radix2_16_eval_poly a base e).
proof.
  rewrite /factor_eqm /schedule_factor_modulus.
  exists (-(segment_poly a (base + 16) 16)).
  rewrite /segment2_16_poly /radix2_16_eval_poly /root_poly.
  ring.
qed.

lemma schedule_modulus_split2_16 (r : int) :
  0 <= r =>
  schedule_factor_modulus 32 (2 * r) =
  schedule_factor_modulus 16 r *
    schedule_factor_modulus 16 (r + 288).
proof.
  move=> Hr.
  move: (factor_split2 X 16 r _ Hr); first smt().
  rewrite /factor /schedule_factor_modulus /=.
  done.
qed.

lemma factor_eqm_split2_16_left
    (r : int) (p q : NTRUPoly.poly) :
  0 <= r =>
  factor_eqm 32 (2 * r) p q =>
  factor_eqm 16 r p q.
proof.
  move=> Hr.
  apply factor_eqm_weaken.
  exists (schedule_factor_modulus 16 (r + 288)).
  exact (schedule_modulus_split2_16 r Hr).
qed.

lemma factor_eqm_split2_16_right
    (r : int) (p q : NTRUPoly.poly) :
  0 <= r =>
  factor_eqm 32 (2 * r) p q =>
  factor_eqm 16 (r + 288) p q.
proof.
  move=> Hr.
  apply factor_eqm_weaken.
  exists (schedule_factor_modulus 16 r).
  rewrite schedule_modulus_split2_16 1:Hr.
  ring.
qed.

lemma radix2_16_pair_child0_eqm (a0 a1 r : int) :
  (NTRUPlus768NTTRadix2_16Algebra.radix2_16_pair_math
     a0 a1 (schedule_root r)).`1 %% q =
  (a0 + a1 * schedule_root r) %% q.
proof.
  by rewrite /NTRUPlus768NTTRadix2_16Algebra.radix2_16_pair_math.
qed.

lemma radix2_16_pair_child1_eqm (a0 a1 r : int) :
  0 <= r =>
  (NTRUPlus768NTTRadix2_16Algebra.radix2_16_pair_math
     a0 a1 (schedule_root r)).`2 %% q =
  (a0 + a1 * schedule_root (r + 288)) %% q.
proof.
  move=> Hr.
  rewrite /NTRUPlus768NTTRadix2_16Algebra.radix2_16_pair_math.
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

op linear2_16_remainder_poly
    (a : W16.t Array768.t) (base c : int) : NTRUPoly.poly =
  PCA.bigi predT
    (fun i =>
      polyC
        (lift_int
          (coeff a.[i + base] +
           coeff a.[i + base + 16] * c)) *
      exp X i)
    0 16.

lemma linear2_16_remainder_polyE
    (a : W16.t Array768.t) (base c : int) :
  linear2_16_remainder_poly a base c =
  segment_poly a base 16 +
  polyC (lift_int c) * segment_poly a (base + 16) 16.
proof.
  rewrite /linear2_16_remainder_poly /segment_poly.
  have Hdist :
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
  have Hsplit :
      PCA.bigi predT
        (fun i => polyC (lift_word a.[i + base]) * exp X i)
        0 16 +
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c) *
            (polyC (lift_word a.[i + (base + 16)]) * exp X i))
        0 16 =
      PCA.bigi predT
        (fun i =>
          polyC (lift_word a.[i + base]) * exp X i +
          polyC (lift_int c) *
            (polyC (lift_word a.[i + (base + 16)]) * exp X i))
        0 16.
  + apply/eq_sym.
    exact
      (PCA.big_split predT
        (fun i => polyC (lift_word a.[i + base]) * exp X i)
        (fun i =>
          polyC (lift_int c) *
            (polyC (lift_word a.[i + (base + 16)]) * exp X i))
        (range 0 16)).
  rewrite Hdist Hsplit.
  apply PCA.eq_big_int => i Hi.
  rewrite /lift_word /lift_int /=.
  rewrite CycloFq.incyclocoeffD CycloFq.incyclocoeffM.
  rewrite NTRUPoly.polyCD NTRUPoly.polyCM.
  rewrite poly_mul_add_right.
  congr.
  have Hidx : i + base + 16 = i + (base + 16) by ring.
  rewrite Hidx.
  apply poly_mul_reorder.
qed.

lemma segment_poly_linear2_16E
    (input output : W16.t Array768.t)
    (input_base output_base c : int) :
  (forall i, 0 <= i < 16 =>
    coeff output.[i + output_base] %% q =
    (coeff input.[i + input_base] +
     coeff input.[i + input_base + 16] * c) %% q) =>
  segment_poly output output_base 16 =
  linear2_16_remainder_poly input input_base c.
proof.
  move=> Hcoeff.
  rewrite /segment_poly /linear2_16_remainder_poly.
  apply PCA.eq_big_int => i Hi.
  have Hmod := Hcoeff i Hi.
  have Elift :
      lift_word output.[i + output_base] =
      lift_int
        (coeff input.[i + input_base] +
         coeff input.[i + input_base + 16] * c).
  + rewrite /lift_word.
    apply lift_int_eq.
    exact Hmod.
  by rewrite /= Elift.
qed.

lemma linear2_16_remainder_radix2_evalE
    (a : W16.t Array768.t) (base e : int) :
  0 <= e =>
  linear2_16_remainder_poly a base (schedule_root e) =
  radix2_16_eval_poly a base e.
proof.
  move=> He.
  rewrite linear2_16_remainder_polyE /radix2_16_eval_poly /root_poly.
  rewrite schedule_root_fieldE 1:He.
  ring.
qed.

lemma segment_poly_radix2_16_evalE
    (input output : W16.t Array768.t)
    (input_base output_base e : int) :
  0 <= e =>
  (forall i, 0 <= i < 16 =>
    coeff output.[i + output_base] %% q =
    (coeff input.[i + input_base] +
     coeff input.[i + input_base + 16] * schedule_root e) %% q) =>
  segment_poly output output_base 16 =
  radix2_16_eval_poly input input_base e.
proof.
  move=> He Hcoeff.
  have Hsegment :
      segment_poly output output_base 16 =
      linear2_16_remainder_poly input input_base (schedule_root e).
  + apply segment_poly_linear2_16E.
    exact Hcoeff.
  rewrite Hsegment.
  apply linear2_16_remainder_radix2_evalE.
  exact He.
qed.

op radix2_16_schedule_exp (b : int) : int =
  zetas192_exp
    (NTRUPlus768NTTRadix2_16Algebra.radix2_16_schedule_index b).

lemma radix2_16_zeta_scheduleE (b : int) :
  NTRUPlus768NTTRadix2_16Algebra.radix2_16_zeta_root b =
  schedule_root (radix2_16_schedule_exp b).
proof.
  by rewrite /NTRUPlus768NTTRadix2_16Algebra.radix2_16_zeta_root
             /radix2_16_schedule_exp /schedule_root.
qed.

lemma radix2_16_segment_left_evalE
    (input output : W16.t Array768.t) (b : int) :
  0 <= b < 24 =>
  0 <= radix2_16_schedule_exp b =>
  NTRUPlus768NTTRadix2_16Algebra.radix2_16_algebra input output =>
  segment_poly output (32 * b) 16 =
    radix2_16_eval_poly input (32 * b) (radix2_16_schedule_exp b).
proof.
  move=> Hb He Halg.
  apply segment_poly_radix2_16_evalE; first exact He.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 32 * b) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_16Algebra.radix2_16_math
          /NTRUPlus768NTTRadix2_16Algebra.radix2_16_block_id
          /NTRUPlus768NTTRadix2_16Algebra.radix2_16_block_base
          /NTRUPlus768NTTRadix2_16Algebra.radix2_16_lane_index
          /NTRUPlus768NTTRadix2_16Algebra.radix2_16_block_offset
          /NTRUPlus768NTTRadix2_16Algebra.double_block
          /NTRUPlus768NTTRadix2_16Algebra.block.
  have -> : (i + 32 * b) %/ 32 = b by smt().
  have -> : (i + 32 * b) %% 32 = i by smt().
  move=> Hcoeff.
  move: Hcoeff; simplify.
  rewrite ifT 1:/# ifT 1:/# /=.
  move=> Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_16Algebra.radix2_16_pair_math_at
          radix2_16_zeta_scheduleE radix2_16_pair_child0_eqm in Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_16Algebra.block
          [32 * b + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_16_segment_right_evalE
    (input output : W16.t Array768.t) (b : int) :
  0 <= b < 24 =>
  0 <= radix2_16_schedule_exp b =>
  NTRUPlus768NTTRadix2_16Algebra.radix2_16_algebra input output =>
  segment_poly output (32 * b + 16) 16 =
    radix2_16_eval_poly input (32 * b) (radix2_16_schedule_exp b + 288).
proof.
  move=> Hb He Halg.
  apply segment_poly_radix2_16_evalE; first smt().
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + (32 * b + 16)) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_16Algebra.radix2_16_math
          /NTRUPlus768NTTRadix2_16Algebra.radix2_16_block_id
          /NTRUPlus768NTTRadix2_16Algebra.radix2_16_block_base
          /NTRUPlus768NTTRadix2_16Algebra.radix2_16_lane_index
          /NTRUPlus768NTTRadix2_16Algebra.radix2_16_block_offset
          /NTRUPlus768NTTRadix2_16Algebra.double_block
          /NTRUPlus768NTTRadix2_16Algebra.block.
  have -> : (i + (32 * b + 16)) %/ 32 = b by smt().
  have -> : (i + (32 * b + 16)) %% 32 = i + 16 by smt().
  move=> Hcoeff.
  move: Hcoeff; simplify.
  rewrite ifF 1:/# ifF 1:/# /=.
  move=> Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_16Algebra.radix2_16_pair_math_at
          radix2_16_zeta_scheduleE in Hcoeff.
  rewrite radix2_16_pair_child1_eqm 1:He in Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_16Algebra.block
          [32 * b + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_16_segment_factor_eqm
    (input output : W16.t Array768.t)
    (input_base output_base e : int) :
  segment_poly output output_base 16 =
    radix2_16_eval_poly input input_base e =>
  factor_eqm 16 e
    (segment_poly input input_base 32)
    (segment_poly output output_base 16).
proof.
  move=> Houtput.
  rewrite segment_poly_split2_16 Houtput.
  exact (radix2_16_eval_factor_eqm input input_base e).
qed.

lemma radix2_16_refine_left
    (original input output : W16.t Array768.t)
    (input_base output_base r : int) :
  0 <= r =>
  factor_eqm 32 (2 * r)
    (input_poly original) (segment_poly input input_base 32) =>
  segment_poly output output_base 16 =
    radix2_16_eval_poly input input_base r =>
  factor_eqm 16 r
    (input_poly original) (segment_poly output output_base 16).
proof.
  move=> Hr Hparent HlocalE.
  have Hparent' : factor_eqm 16 r
      (input_poly original) (segment_poly input input_base 32).
  + apply factor_eqm_split2_16_left; first exact Hr.
    exact Hparent.
  have Hlocal : factor_eqm 16 r
      (segment_poly input input_base 32)
      (segment_poly output output_base 16).
  + apply radix2_16_segment_factor_eqm.
    exact HlocalE.
  apply (factor_eqm_trans 16 r
    (input_poly original) (segment_poly input input_base 32)
    (segment_poly output output_base 16)).
  + exact Hparent'.
  + exact Hlocal.
qed.

lemma radix2_16_refine_right
    (original input output : W16.t Array768.t)
    (input_base output_base r : int) :
  0 <= r =>
  factor_eqm 32 (2 * r)
    (input_poly original) (segment_poly input input_base 32) =>
  segment_poly output output_base 16 =
    radix2_16_eval_poly input input_base (r + 288) =>
  factor_eqm 16 (r + 288)
    (input_poly original) (segment_poly output output_base 16).
proof.
  move=> Hr Hparent HlocalE.
  have Hparent' : factor_eqm 16 (r + 288)
      (input_poly original) (segment_poly input input_base 32).
  + apply factor_eqm_split2_16_right; first exact Hr.
    exact Hparent.
  have Hlocal : factor_eqm 16 (r + 288)
      (segment_poly input input_base 32)
      (segment_poly output output_base 16).
  + apply radix2_16_segment_factor_eqm.
    exact HlocalE.
  apply (factor_eqm_trans 16 (r + 288)
    (input_poly original) (segment_poly input input_base 32)
    (segment_poly output output_base 16)).
  + exact Hparent'.
  + exact Hlocal.
qed.

lemma radix2_16_refine_block_left
    (original input output : W16.t Array768.t) (b r : int) :
  0 <= b < 24 =>
  0 <= r =>
  radix2_16_schedule_exp b = r =>
  factor_eqm 32 (2 * r)
    (input_poly original) (segment_poly input (32 * b) 32) =>
  NTRUPlus768NTTRadix2_16Algebra.radix2_16_algebra input output =>
  factor_eqm 16 r
    (input_poly original) (segment_poly output (32 * b) 16).
proof.
  move=> Hb Hr Hexp Hparent Halg.
  have Hlocal :
      segment_poly output (32 * b) 16 =
      radix2_16_eval_poly input (32 * b) r.
  + have Hscheduled :=
      radix2_16_segment_left_evalE input output b Hb _ Halg.
    - rewrite Hexp; exact Hr.
    rewrite Hexp in Hscheduled.
    exact Hscheduled.
  apply (radix2_16_refine_left
    original input output (32 * b) (32 * b) r).
  + exact Hr.
  + exact Hparent.
  + exact Hlocal.
qed.

lemma radix2_16_refine_block_right
    (original input output : W16.t Array768.t) (b r : int) :
  0 <= b < 24 =>
  0 <= r =>
  radix2_16_schedule_exp b = r =>
  factor_eqm 32 (2 * r)
    (input_poly original) (segment_poly input (32 * b) 32) =>
  NTRUPlus768NTTRadix2_16Algebra.radix2_16_algebra input output =>
  factor_eqm 16 (r + 288)
    (input_poly original) (segment_poly output (32 * b + 16) 16).
proof.
  move=> Hb Hr Hexp Hparent Halg.
  have Hlocal :
      segment_poly output (32 * b + 16) 16 =
      radix2_16_eval_poly input (32 * b) (r + 288).
  + have Hscheduled :=
      radix2_16_segment_right_evalE input output b Hb _ Halg.
    - rewrite Hexp; exact Hr.
    rewrite Hexp in Hscheduled.
    exact Hscheduled.
  apply (radix2_16_refine_right
    original input output (32 * b) (32 * b + 16) r).
  + exact Hr.
  + exact Hparent.
  + exact Hlocal.
qed.

lemma radix2_16_schedule_exp_0E : radix2_16_schedule_exp 0 = 4.
proof. by rewrite /radix2_16_schedule_exp
  /NTRUPlus768NTTRadix2_16Algebra.radix2_16_schedule_index
  /ntt_radix2_16_start /zetas192_exp /zetas192_exponents /=. qed.

lemma radix2_16_schedule_exp_1E : radix2_16_schedule_exp 1 = 148.
proof. by rewrite /radix2_16_schedule_exp
  /NTRUPlus768NTTRadix2_16Algebra.radix2_16_schedule_index
  /ntt_radix2_16_start /zetas192_exp /zetas192_exponents /=. qed.

lemma radix2_16_schedule_exp_2E : radix2_16_schedule_exp 2 = 76.
proof. by rewrite /radix2_16_schedule_exp
  /NTRUPlus768NTTRadix2_16Algebra.radix2_16_schedule_index
  /ntt_radix2_16_start /zetas192_exp /zetas192_exponents /=. qed.

lemma radix2_16_schedule_exp_3E : radix2_16_schedule_exp 3 = 220.
proof. by rewrite /radix2_16_schedule_exp
  /NTRUPlus768NTTRadix2_16Algebra.radix2_16_schedule_index
  /ntt_radix2_16_start /zetas192_exp /zetas192_exponents /=. qed.

lemma radix2_16_schedule_exp_4E : radix2_16_schedule_exp 4 = 28.
proof. by rewrite /radix2_16_schedule_exp
  /NTRUPlus768NTTRadix2_16Algebra.radix2_16_schedule_index
  /ntt_radix2_16_start /zetas192_exp /zetas192_exponents /=. qed.

lemma radix2_16_schedule_exp_5E : radix2_16_schedule_exp 5 = 172.
proof. by rewrite /radix2_16_schedule_exp
  /NTRUPlus768NTTRadix2_16Algebra.radix2_16_schedule_index
  /ntt_radix2_16_start /zetas192_exp /zetas192_exponents /=. qed.

lemma radix2_16_schedule_exp_6E : radix2_16_schedule_exp 6 = 100.
proof. by rewrite /radix2_16_schedule_exp
  /NTRUPlus768NTTRadix2_16Algebra.radix2_16_schedule_index
  /ntt_radix2_16_start /zetas192_exp /zetas192_exponents /=. qed.

lemma radix2_16_schedule_exp_7E : radix2_16_schedule_exp 7 = 244.
proof. by rewrite /radix2_16_schedule_exp
  /NTRUPlus768NTTRadix2_16Algebra.radix2_16_schedule_index
  /ntt_radix2_16_start /zetas192_exp /zetas192_exponents /=. qed.

lemma radix2_16_schedule_exp_8E : radix2_16_schedule_exp 8 = 52.
proof. by rewrite /radix2_16_schedule_exp
  /NTRUPlus768NTTRadix2_16Algebra.radix2_16_schedule_index
  /ntt_radix2_16_start /zetas192_exp /zetas192_exponents /=. qed.

lemma radix2_16_schedule_exp_9E : radix2_16_schedule_exp 9 = 196.
proof. by rewrite /radix2_16_schedule_exp
  /NTRUPlus768NTTRadix2_16Algebra.radix2_16_schedule_index
  /ntt_radix2_16_start /zetas192_exp /zetas192_exponents /=. qed.

lemma radix2_16_schedule_exp_10E : radix2_16_schedule_exp 10 = 124.
proof. by rewrite /radix2_16_schedule_exp
  /NTRUPlus768NTTRadix2_16Algebra.radix2_16_schedule_index
  /ntt_radix2_16_start /zetas192_exp /zetas192_exponents /=. qed.

lemma radix2_16_schedule_exp_11E : radix2_16_schedule_exp 11 = 268.
proof. by rewrite /radix2_16_schedule_exp
  /NTRUPlus768NTTRadix2_16Algebra.radix2_16_schedule_index
  /ntt_radix2_16_start /zetas192_exp /zetas192_exponents /=. qed.

lemma radix2_16_schedule_exp_12E : radix2_16_schedule_exp 12 = 20.
proof. by rewrite /radix2_16_schedule_exp
  /NTRUPlus768NTTRadix2_16Algebra.radix2_16_schedule_index
  /ntt_radix2_16_start /zetas192_exp /zetas192_exponents /=. qed.

lemma radix2_16_schedule_exp_13E : radix2_16_schedule_exp 13 = 164.
proof. by rewrite /radix2_16_schedule_exp
  /NTRUPlus768NTTRadix2_16Algebra.radix2_16_schedule_index
  /ntt_radix2_16_start /zetas192_exp /zetas192_exponents /=. qed.

lemma radix2_16_schedule_exp_14E : radix2_16_schedule_exp 14 = 92.
proof. by rewrite /radix2_16_schedule_exp
  /NTRUPlus768NTTRadix2_16Algebra.radix2_16_schedule_index
  /ntt_radix2_16_start /zetas192_exp /zetas192_exponents /=. qed.

lemma radix2_16_schedule_exp_15E : radix2_16_schedule_exp 15 = 236.
proof. by rewrite /radix2_16_schedule_exp
  /NTRUPlus768NTTRadix2_16Algebra.radix2_16_schedule_index
  /ntt_radix2_16_start /zetas192_exp /zetas192_exponents /=. qed.

lemma radix2_16_schedule_exp_16E : radix2_16_schedule_exp 16 = 44.
proof. by rewrite /radix2_16_schedule_exp
  /NTRUPlus768NTTRadix2_16Algebra.radix2_16_schedule_index
  /ntt_radix2_16_start /zetas192_exp /zetas192_exponents /=. qed.

lemma radix2_16_schedule_exp_17E : radix2_16_schedule_exp 17 = 188.
proof. by rewrite /radix2_16_schedule_exp
  /NTRUPlus768NTTRadix2_16Algebra.radix2_16_schedule_index
  /ntt_radix2_16_start /zetas192_exp /zetas192_exponents /=. qed.

lemma radix2_16_schedule_exp_18E : radix2_16_schedule_exp 18 = 116.
proof. by rewrite /radix2_16_schedule_exp
  /NTRUPlus768NTTRadix2_16Algebra.radix2_16_schedule_index
  /ntt_radix2_16_start /zetas192_exp /zetas192_exponents /=. qed.

lemma radix2_16_schedule_exp_19E : radix2_16_schedule_exp 19 = 260.
proof. by rewrite /radix2_16_schedule_exp
  /NTRUPlus768NTTRadix2_16Algebra.radix2_16_schedule_index
  /ntt_radix2_16_start /zetas192_exp /zetas192_exponents /=. qed.

lemma radix2_16_schedule_exp_20E : radix2_16_schedule_exp 20 = 68.
proof. by rewrite /radix2_16_schedule_exp
  /NTRUPlus768NTTRadix2_16Algebra.radix2_16_schedule_index
  /ntt_radix2_16_start /zetas192_exp /zetas192_exponents /=. qed.

lemma radix2_16_schedule_exp_21E : radix2_16_schedule_exp 21 = 212.
proof. by rewrite /radix2_16_schedule_exp
  /NTRUPlus768NTTRadix2_16Algebra.radix2_16_schedule_index
  /ntt_radix2_16_start /zetas192_exp /zetas192_exponents /=. qed.

lemma radix2_16_schedule_exp_22E : radix2_16_schedule_exp 22 = 140.
proof. by rewrite /radix2_16_schedule_exp
  /NTRUPlus768NTTRadix2_16Algebra.radix2_16_schedule_index
  /ntt_radix2_16_start /zetas192_exp /zetas192_exponents /=. qed.

lemma radix2_16_schedule_exp_23E : radix2_16_schedule_exp 23 = 284.
proof. by rewrite /radix2_16_schedule_exp
  /NTRUPlus768NTTRadix2_16Algebra.radix2_16_schedule_index
  /ntt_radix2_16_start /zetas192_exp /zetas192_exponents /=. qed.

op radix2_16_semantics
    (original output : W16.t Array768.t) : bool =
  factor_eqm 16 4
    (input_poly original) (segment_poly output 0 16) /\
  factor_eqm 16 292
    (input_poly original) (segment_poly output 16 16) /\
  factor_eqm 16 148
    (input_poly original) (segment_poly output 32 16) /\
  factor_eqm 16 436
    (input_poly original) (segment_poly output 48 16) /\
  factor_eqm 16 76
    (input_poly original) (segment_poly output 64 16) /\
  factor_eqm 16 364
    (input_poly original) (segment_poly output 80 16) /\
  factor_eqm 16 220
    (input_poly original) (segment_poly output 96 16) /\
  factor_eqm 16 508
    (input_poly original) (segment_poly output 112 16) /\
  factor_eqm 16 28
    (input_poly original) (segment_poly output 128 16) /\
  factor_eqm 16 316
    (input_poly original) (segment_poly output 144 16) /\
  factor_eqm 16 172
    (input_poly original) (segment_poly output 160 16) /\
  factor_eqm 16 460
    (input_poly original) (segment_poly output 176 16) /\
  factor_eqm 16 100
    (input_poly original) (segment_poly output 192 16) /\
  factor_eqm 16 388
    (input_poly original) (segment_poly output 208 16) /\
  factor_eqm 16 244
    (input_poly original) (segment_poly output 224 16) /\
  factor_eqm 16 532
    (input_poly original) (segment_poly output 240 16) /\
  factor_eqm 16 52
    (input_poly original) (segment_poly output 256 16) /\
  factor_eqm 16 340
    (input_poly original) (segment_poly output 272 16) /\
  factor_eqm 16 196
    (input_poly original) (segment_poly output 288 16) /\
  factor_eqm 16 484
    (input_poly original) (segment_poly output 304 16) /\
  factor_eqm 16 124
    (input_poly original) (segment_poly output 320 16) /\
  factor_eqm 16 412
    (input_poly original) (segment_poly output 336 16) /\
  factor_eqm 16 268
    (input_poly original) (segment_poly output 352 16) /\
  factor_eqm 16 556
    (input_poly original) (segment_poly output 368 16) /\
  factor_eqm 16 20
    (input_poly original) (segment_poly output 384 16) /\
  factor_eqm 16 308
    (input_poly original) (segment_poly output 400 16) /\
  factor_eqm 16 164
    (input_poly original) (segment_poly output 416 16) /\
  factor_eqm 16 452
    (input_poly original) (segment_poly output 432 16) /\
  factor_eqm 16 92
    (input_poly original) (segment_poly output 448 16) /\
  factor_eqm 16 380
    (input_poly original) (segment_poly output 464 16) /\
  factor_eqm 16 236
    (input_poly original) (segment_poly output 480 16) /\
  factor_eqm 16 524
    (input_poly original) (segment_poly output 496 16) /\
  factor_eqm 16 44
    (input_poly original) (segment_poly output 512 16) /\
  factor_eqm 16 332
    (input_poly original) (segment_poly output 528 16) /\
  factor_eqm 16 188
    (input_poly original) (segment_poly output 544 16) /\
  factor_eqm 16 476
    (input_poly original) (segment_poly output 560 16) /\
  factor_eqm 16 116
    (input_poly original) (segment_poly output 576 16) /\
  factor_eqm 16 404
    (input_poly original) (segment_poly output 592 16) /\
  factor_eqm 16 260
    (input_poly original) (segment_poly output 608 16) /\
  factor_eqm 16 548
    (input_poly original) (segment_poly output 624 16) /\
  factor_eqm 16 68
    (input_poly original) (segment_poly output 640 16) /\
  factor_eqm 16 356
    (input_poly original) (segment_poly output 656 16) /\
  factor_eqm 16 212
    (input_poly original) (segment_poly output 672 16) /\
  factor_eqm 16 500
    (input_poly original) (segment_poly output 688 16) /\
  factor_eqm 16 140
    (input_poly original) (segment_poly output 704 16) /\
  factor_eqm 16 428
    (input_poly original) (segment_poly output 720 16) /\
  factor_eqm 16 284
    (input_poly original) (segment_poly output 736 16) /\
  factor_eqm 16 572
    (input_poly original) (segment_poly output 752 16).

lemma radix2_16_refine_block_pair
    (original input output : W16.t Array768.t) (b r : int) :
  0 <= b < 24 =>
  0 <= r =>
  radix2_16_schedule_exp b = r =>
  factor_eqm 32 (2 * r)
    (input_poly original) (segment_poly input (32 * b) 32) =>
  NTRUPlus768NTTRadix2_16Algebra.radix2_16_algebra input output =>
  factor_eqm 16 r
      (input_poly original) (segment_poly output (32 * b) 16) /\
  factor_eqm 16 (r + 288)
      (input_poly original) (segment_poly output (32 * b + 16) 16).
proof.
  move=> Hb Hr Hexp Hparent Halg.
  split.
  + apply (radix2_16_refine_block_left
      original input output b r Hb Hr Hexp Hparent Halg).
  + apply (radix2_16_refine_block_right
      original input output b r Hb Hr Hexp Hparent Halg).
qed.

lemma radix2_16_algebra_refines_radix2_32_semantics
    (original input output : W16.t Array768.t) :
  radix2_32_semantics original input =>
  NTRUPlus768NTTRadix2_16Algebra.radix2_16_algebra input output =>
  radix2_16_semantics original output.
proof.
  move=> Hsem Halg.
  rewrite /radix2_32_semantics in Hsem.
  have [H8 Hrest1] := Hsem.
  have [H296 Hrest2] := Hrest1.
  have [H152 Hrest3] := Hrest2.
  have [H440 Hrest4] := Hrest3.
  have [H56 Hrest5] := Hrest4.
  have [H344 Hrest6] := Hrest5.
  have [H200 Hrest7] := Hrest6.
  have [H488 Hrest8] := Hrest7.
  have [H104 Hrest9] := Hrest8.
  have [H392 Hrest10] := Hrest9.
  have [H248 Hrest11] := Hrest10.
  have [H536 Hrest12] := Hrest11.
  have [H40 Hrest13] := Hrest12.
  have [H328 Hrest14] := Hrest13.
  have [H184 Hrest15] := Hrest14.
  have [H472 Hrest16] := Hrest15.
  have [H88 Hrest17] := Hrest16.
  have [H376 Hrest18] := Hrest17.
  have [H232 Hrest19] := Hrest18.
  have [H520 Hrest20] := Hrest19.
  have [H136 Hrest21] := Hrest20.
  have [H424 Hrest22] := Hrest21.
  have [H280 H568] := Hrest22.

  have [HL0 HR0] :=
    radix2_16_refine_block_pair original input output 0 4 _ _
      radix2_16_schedule_exp_0E H8 Halg.
  + done.
  + done.
  have [HL1 HR1] :=
    radix2_16_refine_block_pair original input output 1 148 _ _
      radix2_16_schedule_exp_1E H296 Halg.
  + done.
  + done.
  have [HL2 HR2] :=
    radix2_16_refine_block_pair original input output 2 76 _ _
      radix2_16_schedule_exp_2E H152 Halg.
  + done.
  + done.
  have [HL3 HR3] :=
    radix2_16_refine_block_pair original input output 3 220 _ _
      radix2_16_schedule_exp_3E H440 Halg.
  + done.
  + done.
  have [HL4 HR4] :=
    radix2_16_refine_block_pair original input output 4 28 _ _
      radix2_16_schedule_exp_4E H56 Halg.
  + done.
  + done.
  have [HL5 HR5] :=
    radix2_16_refine_block_pair original input output 5 172 _ _
      radix2_16_schedule_exp_5E H344 Halg.
  + done.
  + done.
  have [HL6 HR6] :=
    radix2_16_refine_block_pair original input output 6 100 _ _
      radix2_16_schedule_exp_6E H200 Halg.
  + done.
  + done.
  have [HL7 HR7] :=
    radix2_16_refine_block_pair original input output 7 244 _ _
      radix2_16_schedule_exp_7E H488 Halg.
  + done.
  + done.
  have [HL8 HR8] :=
    radix2_16_refine_block_pair original input output 8 52 _ _
      radix2_16_schedule_exp_8E H104 Halg.
  + done.
  + done.
  have [HL9 HR9] :=
    radix2_16_refine_block_pair original input output 9 196 _ _
      radix2_16_schedule_exp_9E H392 Halg.
  + done.
  + done.
  have [HL10 HR10] :=
    radix2_16_refine_block_pair original input output 10 124 _ _
      radix2_16_schedule_exp_10E H248 Halg.
  + done.
  + done.
  have [HL11 HR11] :=
    radix2_16_refine_block_pair original input output 11 268 _ _
      radix2_16_schedule_exp_11E H536 Halg.
  + done.
  + done.
  have [HL12 HR12] :=
    radix2_16_refine_block_pair original input output 12 20 _ _
      radix2_16_schedule_exp_12E H40 Halg.
  + done.
  + done.
  have [HL13 HR13] :=
    radix2_16_refine_block_pair original input output 13 164 _ _
      radix2_16_schedule_exp_13E H328 Halg.
  + done.
  + done.
  have [HL14 HR14] :=
    radix2_16_refine_block_pair original input output 14 92 _ _
      radix2_16_schedule_exp_14E H184 Halg.
  + done.
  + done.
  have [HL15 HR15] :=
    radix2_16_refine_block_pair original input output 15 236 _ _
      radix2_16_schedule_exp_15E H472 Halg.
  + done.
  + done.
  have [HL16 HR16] :=
    radix2_16_refine_block_pair original input output 16 44 _ _
      radix2_16_schedule_exp_16E H88 Halg.
  + done.
  + done.
  have [HL17 HR17] :=
    radix2_16_refine_block_pair original input output 17 188 _ _
      radix2_16_schedule_exp_17E H376 Halg.
  + done.
  + done.
  have [HL18 HR18] :=
    radix2_16_refine_block_pair original input output 18 116 _ _
      radix2_16_schedule_exp_18E H232 Halg.
  + done.
  + done.
  have [HL19 HR19] :=
    radix2_16_refine_block_pair original input output 19 260 _ _
      radix2_16_schedule_exp_19E H520 Halg.
  + done.
  + done.
  have [HL20 HR20] :=
    radix2_16_refine_block_pair original input output 20 68 _ _
      radix2_16_schedule_exp_20E H136 Halg.
  + done.
  + done.
  have [HL21 HR21] :=
    radix2_16_refine_block_pair original input output 21 212 _ _
      radix2_16_schedule_exp_21E H424 Halg.
  + done.
  + done.
  have [HL22 HR22] :=
    radix2_16_refine_block_pair original input output 22 140 _ _
      radix2_16_schedule_exp_22E H280 Halg.
  + done.
  + done.
  have [HL23 HR23] :=
    radix2_16_refine_block_pair original input output 23 284 _ _
      radix2_16_schedule_exp_23E H568 Halg.
  + done.
  + done.

  rewrite /radix2_16_semantics.
  split; first exact HL0.
  split; first exact HR0.
  split; first exact HL1.
  split; first exact HR1.
  split; first exact HL2.
  split; first exact HR2.
  split; first exact HL3.
  split; first exact HR3.
  split; first exact HL4.
  split; first exact HR4.
  split; first exact HL5.
  split; first exact HR5.
  split; first exact HL6.
  split; first exact HR6.
  split; first exact HL7.
  split; first exact HR7.
  split; first exact HL8.
  split; first exact HR8.
  split; first exact HL9.
  split; first exact HR9.
  split; first exact HL10.
  split; first exact HR10.
  split; first exact HL11.
  split; first exact HR11.
  split; first exact HL12.
  split; first exact HR12.
  split; first exact HL13.
  split; first exact HR13.
  split; first exact HL14.
  split; first exact HR14.
  split; first exact HL15.
  split; first exact HR15.
  split; first exact HL16.
  split; first exact HR16.
  split; first exact HL17.
  split; first exact HR17.
  split; first exact HL18.
  split; first exact HR18.
  split; first exact HL19.
  split; first exact HR19.
  split; first exact HL20.
  split; first exact HR20.
  split; first exact HL21.
  split; first exact HR21.
  split; first exact HL22.
  split; first exact HR22.
  split; first exact HL23.
  exact HR23.
qed.

lemma radix2_16_spec_semantics
    (original input : W16.t Array768.t) :
  radix2_32_semantics original input =>
  NTRUPlus768NTTRadix2_16Algebra.centered_input_shape input =>
  radix2_16_semantics original
    (NTRUPlus768NTTRadix2_16Proof.radix2_16_spec input).
proof.
  move=> Hsem Hshape.
  apply (radix2_16_algebra_refines_radix2_32_semantics
    original input (NTRUPlus768NTTRadix2_16Proof.radix2_16_spec input)).
  + exact Hsem.
  + rewrite NTRUPlus768NTTRadix2_16Algebra.radix2_16_word_specE.
    exact
      (NTRUPlus768NTTRadix2_16Algebra.radix2_16_spec_algebra input Hshape).
qed.

lemma ntt_radix2_16_semantics_functional
    (original rp0 : W16.t Array768.t) :
  radix2_32_semantics original rp0 =>
  NTRUPlus768NTTRadix2_16Algebra.centered_input_shape rp0 =>
  hoare [NTRUPlus768NTTRadix2_16.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_16 :
    rp = rp0 ==> radix2_16_semantics original res].
proof.
  move=> Hsem Hshape.
  conseq
    (NTRUPlus768NTTRadix2_16Algebra.ntt_radix2_16_algebra_functional
      rp0 Hshape) => />.
  move=> result Halg.
  apply (radix2_16_algebra_refines_radix2_32_semantics original rp0 result).
  + exact Hsem.
  + exact Halg.
qed.

lemma ntt_radix2_16_correct_semantics
    (original rp0 : W16.t Array768.t) :
  radix2_32_semantics original rp0 =>
  NTRUPlus768NTTRadix2_16Algebra.centered_input_shape rp0 =>
  phoare [NTRUPlus768NTTRadix2_16.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_16 :
    rp = rp0 ==> radix2_16_semantics original res] = 1%r.
proof.
  move=> Hsem Hshape.
  have Hfunctional :
      hoare [NTRUPlus768NTTRadix2_16.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_16 :
        rp = rp0 ==> radix2_16_semantics original res].
  + apply ntt_radix2_16_semantics_functional.
    - exact Hsem.
    - exact Hshape.
  by conseq NTRUPlus768NTTRadix2_16Proof.ntt_radix2_16_lossless Hfunctional.
qed.
