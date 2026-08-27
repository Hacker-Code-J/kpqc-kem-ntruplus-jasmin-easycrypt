require import AllCore IntDiv List Ring StdBigop StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array768.
require import NTRUPlus768BasemulAlgebra NTRUPlus768NTTSchedule.
require import NTRUPlus768CyclotomicFactorization.
require import NTRUPlus768EvaluationSemantics.
require import NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768ForwardNTTRadix3Semantics.
require import NTRUPlus768ForwardNTTRadix2_64Semantics.
require import NTRUPlus768NTTRadix2_32.
require import NTRUPlus768NTTRadix2_32Algebra NTRUPlus768NTTRadix2_32Proof.

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

(* The second binary layer refines each degree-64 representative into two
   degree-32 representatives. *)

op segment2_32_poly (a : W16.t Array768.t) (base : int) : NTRUPoly.poly =
  segment_poly a base 32 +
  segment_poly a (base + 32) 32 * exp X 32.

op radix2_32_eval_poly
    (a : W16.t Array768.t) (base e : int) : NTRUPoly.poly =
  segment_poly a base 32 +
  segment_poly a (base + 32) 32 * root_poly e.

lemma segment_poly_split2_32 (a : W16.t Array768.t) (base : int) :
  segment_poly a base 64 = segment2_32_poly a base.
proof.
  rewrite /segment2_32_poly.
  rewrite (segment_poly_split a base 32 32) 1:// 1://.
  done.
qed.

lemma radix2_32_eval_factor_eqm
    (a : W16.t Array768.t) (base e : int) :
  factor_eqm 32 e
    (segment2_32_poly a base) (radix2_32_eval_poly a base e).
proof.
  rewrite /factor_eqm /schedule_factor_modulus.
  exists (-(segment_poly a (base + 32) 32)).
  rewrite /segment2_32_poly /radix2_32_eval_poly /root_poly.
  ring.
qed.

lemma schedule_modulus_split2_32 (r : int) :
  0 <= r =>
  schedule_factor_modulus 64 (2 * r) =
  schedule_factor_modulus 32 r *
    schedule_factor_modulus 32 (r + 288).
proof.
  move=> Hr.
  move: (factor_split2 X 32 r _ Hr); first smt().
  rewrite /factor /schedule_factor_modulus /=.
  done.
qed.

lemma factor_eqm_split2_32_left
    (r : int) (p q : NTRUPoly.poly) :
  0 <= r =>
  factor_eqm 64 (2 * r) p q =>
  factor_eqm 32 r p q.
proof.
  move=> Hr.
  apply factor_eqm_weaken.
  exists (schedule_factor_modulus 32 (r + 288)).
  exact (schedule_modulus_split2_32 r Hr).
qed.

lemma factor_eqm_split2_32_right
    (r : int) (p q : NTRUPoly.poly) :
  0 <= r =>
  factor_eqm 64 (2 * r) p q =>
  factor_eqm 32 (r + 288) p q.
proof.
  move=> Hr.
  apply factor_eqm_weaken.
  exists (schedule_factor_modulus 32 r).
  rewrite schedule_modulus_split2_32 1:Hr.
  ring.
qed.

lemma radix2_32_pair_child0_eqm (a0 a1 r : int) :
  (NTRUPlus768NTTRadix2_32Algebra.radix2_32_pair_math
     a0 a1 (schedule_root r)).`1 %% q =
  (a0 + a1 * schedule_root r) %% q.
proof.
  by rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_pair_math.
qed.

lemma radix2_32_pair_child1_eqm (a0 a1 r : int) :
  0 <= r =>
  (NTRUPlus768NTTRadix2_32Algebra.radix2_32_pair_math
     a0 a1 (schedule_root r)).`2 %% q =
  (a0 + a1 * schedule_root (r + 288)) %% q.
proof.
  move=> Hr.
  rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_pair_math.
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

op linear2_32_remainder_poly
    (a : W16.t Array768.t) (base c : int) : NTRUPoly.poly =
  PCA.bigi predT
    (fun i =>
      polyC
        (lift_int
          (coeff a.[i + base] +
           coeff a.[i + base + 32] * c)) *
      exp X i)
    0 32.

lemma linear2_32_remainder_polyE
    (a : W16.t Array768.t) (base c : int) :
  linear2_32_remainder_poly a base c =
  segment_poly a base 32 +
  polyC (lift_int c) * segment_poly a (base + 32) 32.
proof.
  rewrite /linear2_32_remainder_poly /segment_poly.
  have Hdist :
      polyC (lift_int c) *
        PCA.bigi predT
          (fun i => polyC (lift_word a.[i + (base + 32)]) * exp X i)
          0 32 =
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c) *
            (polyC (lift_word a.[i + (base + 32)]) * exp X i))
        0 32.
  + exact
      (PCA.mulr_sumr predT
        (fun i => polyC (lift_word a.[i + (base + 32)]) * exp X i)
        (range 0 32) (polyC (lift_int c))).
  have Hsplit :
      PCA.bigi predT
        (fun i => polyC (lift_word a.[i + base]) * exp X i)
        0 32 +
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c) *
            (polyC (lift_word a.[i + (base + 32)]) * exp X i))
        0 32 =
      PCA.bigi predT
        (fun i =>
          polyC (lift_word a.[i + base]) * exp X i +
          polyC (lift_int c) *
            (polyC (lift_word a.[i + (base + 32)]) * exp X i))
        0 32.
  + apply/eq_sym.
    exact
      (PCA.big_split predT
        (fun i => polyC (lift_word a.[i + base]) * exp X i)
        (fun i =>
          polyC (lift_int c) *
            (polyC (lift_word a.[i + (base + 32)]) * exp X i))
        (range 0 32)).
  rewrite Hdist Hsplit.
  apply PCA.eq_big_int => i Hi.
  rewrite /lift_word /lift_int /=.
  rewrite CycloFq.incyclocoeffD CycloFq.incyclocoeffM.
  rewrite NTRUPoly.polyCD NTRUPoly.polyCM.
  rewrite poly_mul_add_right.
  congr.
  have Hidx : i + base + 32 = i + (base + 32) by ring.
  rewrite Hidx.
  apply poly_mul_reorder.
qed.

lemma segment_poly_linear2_32E
    (input output : W16.t Array768.t)
    (input_base output_base c : int) :
  (forall i, 0 <= i < 32 =>
    coeff output.[i + output_base] %% q =
    (coeff input.[i + input_base] +
     coeff input.[i + input_base + 32] * c) %% q) =>
  segment_poly output output_base 32 =
  linear2_32_remainder_poly input input_base c.
proof.
  move=> Hcoeff.
  rewrite /segment_poly /linear2_32_remainder_poly.
  apply PCA.eq_big_int => i Hi.
  have Hmod := Hcoeff i Hi.
  have Elift :
      lift_word output.[i + output_base] =
      lift_int
        (coeff input.[i + input_base] +
         coeff input.[i + input_base + 32] * c).
  + rewrite /lift_word.
    apply lift_int_eq.
    exact Hmod.
  by rewrite /= Elift.
qed.

lemma linear2_32_remainder_radix2_evalE
    (a : W16.t Array768.t) (base e : int) :
  0 <= e =>
  linear2_32_remainder_poly a base (schedule_root e) =
  radix2_32_eval_poly a base e.
proof.
  move=> He.
  rewrite linear2_32_remainder_polyE /radix2_32_eval_poly /root_poly.
  rewrite schedule_root_fieldE 1:He.
  ring.
qed.

lemma segment_poly_radix2_32_evalE
    (input output : W16.t Array768.t)
    (input_base output_base e : int) :
  0 <= e =>
  (forall i, 0 <= i < 32 =>
    coeff output.[i + output_base] %% q =
    (coeff input.[i + input_base] +
     coeff input.[i + input_base + 32] * schedule_root e) %% q) =>
  segment_poly output output_base 32 =
  radix2_32_eval_poly input input_base e.
proof.
  move=> He Hcoeff.
  have Hsegment :
      segment_poly output output_base 32 =
      linear2_32_remainder_poly input input_base (schedule_root e).
  + apply segment_poly_linear2_32E.
    exact Hcoeff.
  rewrite Hsegment.
  apply linear2_32_remainder_radix2_evalE.
  exact He.
qed.

lemma radix2_32_zeta1_scheduleE :
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_zeta1_root = schedule_root 8.
proof.
  by rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_zeta1_root
             /schedule_root.
qed.

lemma radix2_32_zeta2_scheduleE :
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_zeta2_root = schedule_root 152.
proof.
  by rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_zeta2_root
             /schedule_root.
qed.

lemma radix2_32_zeta3_scheduleE :
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_zeta3_root = schedule_root 56.
proof.
  by rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_zeta3_root
             /schedule_root.
qed.

lemma radix2_32_zeta4_scheduleE :
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_zeta4_root = schedule_root 200.
proof.
  by rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_zeta4_root
             /schedule_root.
qed.

lemma radix2_32_zeta5_scheduleE :
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_zeta5_root = schedule_root 104.
proof.
  by rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_zeta5_root
             /schedule_root.
qed.

lemma radix2_32_zeta6_scheduleE :
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_zeta6_root = schedule_root 248.
proof.
  by rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_zeta6_root
             /schedule_root.
qed.

lemma radix2_32_zeta7_scheduleE :
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_zeta7_root = schedule_root 40.
proof.
  by rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_zeta7_root
             /schedule_root.
qed.

lemma radix2_32_zeta8_scheduleE :
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_zeta8_root = schedule_root 184.
proof.
  by rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_zeta8_root
             /schedule_root.
qed.

lemma radix2_32_zeta9_scheduleE :
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_zeta9_root = schedule_root 88.
proof.
  by rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_zeta9_root
             /schedule_root.
qed.

lemma radix2_32_zeta10_scheduleE :
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_zeta10_root = schedule_root 232.
proof.
  by rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_zeta10_root
             /schedule_root.
qed.

lemma radix2_32_zeta11_scheduleE :
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_zeta11_root = schedule_root 136.
proof.
  by rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_zeta11_root
             /schedule_root.
qed.

lemma radix2_32_zeta12_scheduleE :
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_zeta12_root = schedule_root 280.
proof.
  by rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_zeta12_root
             /schedule_root.
qed.

lemma radix2_32_segment_0_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_algebra input output =>
  segment_poly output 0 32 = radix2_32_eval_poly input 0 8.
proof.
  move=> Halg.
  apply segment_poly_radix2_32_evalE; first done.
  move=> i Hi.
  have [_ Hcoeff] := Halg i _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_math
          /NTRUPlus768NTTRadix2_32Algebra.radix2_32_pair_math_at
          /NTRUPlus768NTTRadix2_32Proof.block
          /NTRUPlus768NTTRadix2_32Proof.double_block
          /NTRUPlus768NTTRadix2_32Algebra.second_base
          ifT 1:/# /=.
  rewrite radix2_32_zeta1_scheduleE radix2_32_pair_child0_eqm.
  done.
qed.

lemma radix2_32_segment_32_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_algebra input output =>
  segment_poly output 32 32 = radix2_32_eval_poly input 0 296.
proof.
  move=> Halg.
  apply segment_poly_radix2_32_evalE; first done.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 32) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_math
          /NTRUPlus768NTTRadix2_32Algebra.radix2_32_pair_math_at
          /NTRUPlus768NTTRadix2_32Proof.block
          /NTRUPlus768NTTRadix2_32Proof.double_block
          /NTRUPlus768NTTRadix2_32Algebra.second_base
          ifF 1:/# ifT 1:/# /=.
  rewrite radix2_32_zeta1_scheduleE.
  rewrite radix2_32_pair_child1_eqm 1://.
  done.
qed.

lemma radix2_32_segment_64_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_algebra input output =>
  segment_poly output 64 32 = radix2_32_eval_poly input 64 152.
proof.
  move=> Halg.
  apply segment_poly_radix2_32_evalE; first done.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 64) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_math
          /NTRUPlus768NTTRadix2_32Algebra.radix2_32_pair_math_at
          /NTRUPlus768NTTRadix2_32Proof.block
          /NTRUPlus768NTTRadix2_32Proof.double_block
          /NTRUPlus768NTTRadix2_32Algebra.second_base
          ifF 1:/# ifF 1:/# ifT 1:/# /=.
  rewrite radix2_32_zeta2_scheduleE radix2_32_pair_child0_eqm.
  move=> Hcoeff.
  rewrite [64 + i]addrC [96 + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_32_segment_96_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_algebra input output =>
  segment_poly output 96 32 = radix2_32_eval_poly input 64 440.
proof.
  move=> Halg.
  apply segment_poly_radix2_32_evalE; first done.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 96) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_math
          /NTRUPlus768NTTRadix2_32Algebra.radix2_32_pair_math_at
          /NTRUPlus768NTTRadix2_32Proof.block
          /NTRUPlus768NTTRadix2_32Proof.double_block
          /NTRUPlus768NTTRadix2_32Algebra.second_base
          ifF 1:/# ifF 1:/# ifF 1:/# ifT 1:/# /=.
  rewrite radix2_32_zeta2_scheduleE.
  rewrite radix2_32_pair_child1_eqm 1://.
  move=> Hcoeff.
  rewrite [64 + i]addrC [96 + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_32_segment_128_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_algebra input output =>
  segment_poly output 128 32 = radix2_32_eval_poly input 128 56.
proof.
  move=> Halg.
  apply segment_poly_radix2_32_evalE; first done.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 128) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_math
          /NTRUPlus768NTTRadix2_32Algebra.radix2_32_pair_math_at
          /NTRUPlus768NTTRadix2_32Proof.block
          /NTRUPlus768NTTRadix2_32Proof.double_block
          /NTRUPlus768NTTRadix2_32Algebra.second_base
          ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifT 1:/# /=.
  rewrite radix2_32_zeta3_scheduleE radix2_32_pair_child0_eqm.
  move=> Hcoeff.
  rewrite [128 + i]addrC [160 + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_32_segment_160_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_algebra input output =>
  segment_poly output 160 32 = radix2_32_eval_poly input 128 344.
proof.
  move=> Halg.
  apply segment_poly_radix2_32_evalE; first done.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 160) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_math
          /NTRUPlus768NTTRadix2_32Algebra.radix2_32_pair_math_at
          /NTRUPlus768NTTRadix2_32Proof.block
          /NTRUPlus768NTTRadix2_32Proof.double_block
          /NTRUPlus768NTTRadix2_32Algebra.second_base
          ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifT 1:/# /=.
  rewrite radix2_32_zeta3_scheduleE.
  rewrite radix2_32_pair_child1_eqm 1://.
  move=> Hcoeff.
  rewrite [128 + i]addrC [160 + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_32_segment_192_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_algebra input output =>
  segment_poly output 192 32 = radix2_32_eval_poly input 192 200.
proof.
  move=> Halg.
  apply segment_poly_radix2_32_evalE; first done.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 192) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_math
          /NTRUPlus768NTTRadix2_32Algebra.radix2_32_pair_math_at
          /NTRUPlus768NTTRadix2_32Proof.block
          /NTRUPlus768NTTRadix2_32Proof.double_block
          /NTRUPlus768NTTRadix2_32Algebra.second_base
          ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/#
          ifT 1:/# /=.
  rewrite radix2_32_zeta4_scheduleE radix2_32_pair_child0_eqm.
  move=> Hcoeff.
  rewrite [192 + i]addrC [224 + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_32_segment_224_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_algebra input output =>
  segment_poly output 224 32 = radix2_32_eval_poly input 192 488.
proof.
  move=> Halg.
  apply segment_poly_radix2_32_evalE; first done.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 224) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_math
          /NTRUPlus768NTTRadix2_32Algebra.radix2_32_pair_math_at
          /NTRUPlus768NTTRadix2_32Proof.block
          /NTRUPlus768NTTRadix2_32Proof.double_block
          /NTRUPlus768NTTRadix2_32Algebra.second_base
          ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/#
          ifF 1:/# ifT 1:/# /=.
  rewrite radix2_32_zeta4_scheduleE.
  rewrite radix2_32_pair_child1_eqm 1://.
  move=> Hcoeff.
  rewrite [192 + i]addrC [224 + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_32_segment_256_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_algebra input output =>
  segment_poly output 256 32 = radix2_32_eval_poly input 256 104.
proof.
  move=> Halg.
  apply segment_poly_radix2_32_evalE; first done.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 256) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_math
          /NTRUPlus768NTTRadix2_32Algebra.radix2_32_pair_math_at
          /NTRUPlus768NTTRadix2_32Proof.block
          /NTRUPlus768NTTRadix2_32Proof.double_block
          /NTRUPlus768NTTRadix2_32Algebra.second_base
          ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/#
          ifF 1:/# ifF 1:/# ifT 1:/# /=.
  rewrite radix2_32_zeta5_scheduleE radix2_32_pair_child0_eqm.
  move=> Hcoeff.
  rewrite [256 + i]addrC [288 + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_32_segment_288_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_algebra input output =>
  segment_poly output 288 32 = radix2_32_eval_poly input 256 392.
proof.
  move=> Halg.
  apply segment_poly_radix2_32_evalE; first done.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 288) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_math
          /NTRUPlus768NTTRadix2_32Algebra.radix2_32_pair_math_at
          /NTRUPlus768NTTRadix2_32Proof.block
          /NTRUPlus768NTTRadix2_32Proof.double_block
          /NTRUPlus768NTTRadix2_32Algebra.second_base
          ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/#
          ifF 1:/# ifF 1:/# ifF 1:/# ifT 1:/# /=.
  rewrite radix2_32_zeta5_scheduleE.
  rewrite radix2_32_pair_child1_eqm 1://.
  move=> Hcoeff.
  rewrite [256 + i]addrC [288 + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_32_segment_320_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_algebra input output =>
  segment_poly output 320 32 = radix2_32_eval_poly input 320 248.
proof.
  move=> Halg.
  apply segment_poly_radix2_32_evalE; first done.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 320) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_math
          /NTRUPlus768NTTRadix2_32Algebra.radix2_32_pair_math_at
          /NTRUPlus768NTTRadix2_32Proof.block
          /NTRUPlus768NTTRadix2_32Proof.double_block
          /NTRUPlus768NTTRadix2_32Algebra.second_base
          ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/#
          ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifT 1:/# /=.
  rewrite radix2_32_zeta6_scheduleE radix2_32_pair_child0_eqm.
  move=> Hcoeff.
  rewrite [320 + i]addrC [352 + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_32_segment_352_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_algebra input output =>
  segment_poly output 352 32 = radix2_32_eval_poly input 320 536.
proof.
  move=> Halg.
  apply segment_poly_radix2_32_evalE; first done.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 352) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_math
          /NTRUPlus768NTTRadix2_32Algebra.radix2_32_pair_math_at
          /NTRUPlus768NTTRadix2_32Proof.block
          /NTRUPlus768NTTRadix2_32Proof.double_block
          /NTRUPlus768NTTRadix2_32Algebra.second_base
          ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/#
          ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifT 1:/# /=.
  rewrite radix2_32_zeta6_scheduleE.
  rewrite radix2_32_pair_child1_eqm 1://.
  move=> Hcoeff.
  rewrite [320 + i]addrC [352 + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_32_segment_384_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_algebra input output =>
  segment_poly output 384 32 = radix2_32_eval_poly input 384 40.
proof.
  move=> Halg.
  apply segment_poly_radix2_32_evalE; first done.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 384) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_math
          /NTRUPlus768NTTRadix2_32Algebra.radix2_32_pair_math_at
          /NTRUPlus768NTTRadix2_32Proof.block
          /NTRUPlus768NTTRadix2_32Proof.double_block
          /NTRUPlus768NTTRadix2_32Algebra.second_base.
  do 12!(rewrite ifF 1:/#).
  rewrite ifT 1:/# /=.
  rewrite radix2_32_zeta7_scheduleE radix2_32_pair_child0_eqm.
  move=> Hcoeff.
  rewrite [384 + i]addrC [416 + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_32_segment_416_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_algebra input output =>
  segment_poly output 416 32 = radix2_32_eval_poly input 384 328.
proof.
  move=> Halg.
  apply segment_poly_radix2_32_evalE; first done.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 416) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_math
          /NTRUPlus768NTTRadix2_32Algebra.radix2_32_pair_math_at
          /NTRUPlus768NTTRadix2_32Proof.block
          /NTRUPlus768NTTRadix2_32Proof.double_block
          /NTRUPlus768NTTRadix2_32Algebra.second_base.
  do 13!(rewrite ifF 1:/#).
  rewrite ifT 1:/# /=.
  rewrite radix2_32_zeta7_scheduleE.
  rewrite radix2_32_pair_child1_eqm 1://.
  move=> Hcoeff.
  rewrite [384 + i]addrC [416 + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_32_segment_448_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_algebra input output =>
  segment_poly output 448 32 = radix2_32_eval_poly input 448 184.
proof.
  move=> Halg.
  apply segment_poly_radix2_32_evalE; first done.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 448) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_math
          /NTRUPlus768NTTRadix2_32Algebra.radix2_32_pair_math_at
          /NTRUPlus768NTTRadix2_32Proof.block
          /NTRUPlus768NTTRadix2_32Proof.double_block
          /NTRUPlus768NTTRadix2_32Algebra.second_base.
  do 14!(rewrite ifF 1:/#).
  rewrite ifT 1:/# /=.
  rewrite radix2_32_zeta8_scheduleE radix2_32_pair_child0_eqm.
  move=> Hcoeff.
  rewrite [448 + i]addrC [480 + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_32_segment_480_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_algebra input output =>
  segment_poly output 480 32 = radix2_32_eval_poly input 448 472.
proof.
  move=> Halg.
  apply segment_poly_radix2_32_evalE; first done.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 480) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_math
          /NTRUPlus768NTTRadix2_32Algebra.radix2_32_pair_math_at
          /NTRUPlus768NTTRadix2_32Proof.block
          /NTRUPlus768NTTRadix2_32Proof.double_block
          /NTRUPlus768NTTRadix2_32Algebra.second_base.
  do 15!(rewrite ifF 1:/#).
  rewrite ifT 1:/# /=.
  rewrite radix2_32_zeta8_scheduleE.
  rewrite radix2_32_pair_child1_eqm 1://.
  move=> Hcoeff.
  rewrite [448 + i]addrC [480 + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_32_segment_512_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_algebra input output =>
  segment_poly output 512 32 = radix2_32_eval_poly input 512 88.
proof.
  move=> Halg.
  apply segment_poly_radix2_32_evalE; first done.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 512) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_math
          /NTRUPlus768NTTRadix2_32Algebra.radix2_32_pair_math_at
          /NTRUPlus768NTTRadix2_32Proof.block
          /NTRUPlus768NTTRadix2_32Proof.double_block
          /NTRUPlus768NTTRadix2_32Algebra.second_base.
  do 16!(rewrite ifF 1:/#).
  rewrite ifT 1:/# /=.
  rewrite radix2_32_zeta9_scheduleE radix2_32_pair_child0_eqm.
  move=> Hcoeff.
  rewrite [512 + i]addrC [544 + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_32_segment_544_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_algebra input output =>
  segment_poly output 544 32 = radix2_32_eval_poly input 512 376.
proof.
  move=> Halg.
  apply segment_poly_radix2_32_evalE; first done.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 544) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_math
          /NTRUPlus768NTTRadix2_32Algebra.radix2_32_pair_math_at
          /NTRUPlus768NTTRadix2_32Proof.block
          /NTRUPlus768NTTRadix2_32Proof.double_block
          /NTRUPlus768NTTRadix2_32Algebra.second_base.
  do 17!(rewrite ifF 1:/#).
  rewrite ifT 1:/# /=.
  rewrite radix2_32_zeta9_scheduleE.
  rewrite radix2_32_pair_child1_eqm 1://.
  move=> Hcoeff.
  rewrite [512 + i]addrC [544 + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_32_segment_576_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_algebra input output =>
  segment_poly output 576 32 = radix2_32_eval_poly input 576 232.
proof.
  move=> Halg.
  apply segment_poly_radix2_32_evalE; first done.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 576) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_math
          /NTRUPlus768NTTRadix2_32Algebra.radix2_32_pair_math_at
          /NTRUPlus768NTTRadix2_32Proof.block
          /NTRUPlus768NTTRadix2_32Proof.double_block
          /NTRUPlus768NTTRadix2_32Algebra.second_base.
  do 18!(rewrite ifF 1:/#).
  rewrite ifT 1:/# /=.
  rewrite radix2_32_zeta10_scheduleE radix2_32_pair_child0_eqm.
  move=> Hcoeff.
  rewrite [576 + i]addrC [608 + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_32_segment_608_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_algebra input output =>
  segment_poly output 608 32 = radix2_32_eval_poly input 576 520.
proof.
  move=> Halg.
  apply segment_poly_radix2_32_evalE; first done.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 608) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_math
          /NTRUPlus768NTTRadix2_32Algebra.radix2_32_pair_math_at
          /NTRUPlus768NTTRadix2_32Proof.block
          /NTRUPlus768NTTRadix2_32Proof.double_block
          /NTRUPlus768NTTRadix2_32Algebra.second_base.
  do 19!(rewrite ifF 1:/#).
  rewrite ifT 1:/# /=.
  rewrite radix2_32_zeta10_scheduleE.
  rewrite radix2_32_pair_child1_eqm 1://.
  move=> Hcoeff.
  rewrite [576 + i]addrC [608 + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_32_segment_640_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_algebra input output =>
  segment_poly output 640 32 = radix2_32_eval_poly input 640 136.
proof.
  move=> Halg.
  apply segment_poly_radix2_32_evalE; first done.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 640) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_math
          /NTRUPlus768NTTRadix2_32Algebra.radix2_32_pair_math_at
          /NTRUPlus768NTTRadix2_32Proof.block
          /NTRUPlus768NTTRadix2_32Proof.double_block
          /NTRUPlus768NTTRadix2_32Algebra.second_base.
  do 20!(rewrite ifF 1:/#).
  rewrite ifT 1:/# /=.
  rewrite radix2_32_zeta11_scheduleE radix2_32_pair_child0_eqm.
  move=> Hcoeff.
  rewrite [640 + i]addrC [672 + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_32_segment_672_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_algebra input output =>
  segment_poly output 672 32 = radix2_32_eval_poly input 640 424.
proof.
  move=> Halg.
  apply segment_poly_radix2_32_evalE; first done.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 672) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_math
          /NTRUPlus768NTTRadix2_32Algebra.radix2_32_pair_math_at
          /NTRUPlus768NTTRadix2_32Proof.block
          /NTRUPlus768NTTRadix2_32Proof.double_block
          /NTRUPlus768NTTRadix2_32Algebra.second_base.
  do 21!(rewrite ifF 1:/#).
  rewrite ifT 1:/# /=.
  rewrite radix2_32_zeta11_scheduleE.
  rewrite radix2_32_pair_child1_eqm 1://.
  move=> Hcoeff.
  rewrite [640 + i]addrC [672 + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_32_segment_704_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_algebra input output =>
  segment_poly output 704 32 = radix2_32_eval_poly input 704 280.
proof.
  move=> Halg.
  apply segment_poly_radix2_32_evalE; first done.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 704) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_math
          /NTRUPlus768NTTRadix2_32Algebra.radix2_32_pair_math_at
          /NTRUPlus768NTTRadix2_32Proof.block
          /NTRUPlus768NTTRadix2_32Proof.double_block
          /NTRUPlus768NTTRadix2_32Algebra.second_base.
  do 22!(rewrite ifF 1:/#).
  rewrite ifT 1:/# /=.
  rewrite radix2_32_zeta12_scheduleE radix2_32_pair_child0_eqm.
  move=> Hcoeff.
  rewrite [704 + i]addrC [736 + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_32_segment_736_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_algebra input output =>
  segment_poly output 736 32 = radix2_32_eval_poly input 704 568.
proof.
  move=> Halg.
  apply segment_poly_radix2_32_evalE; first done.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 736) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_32Algebra.radix2_32_math
          /NTRUPlus768NTTRadix2_32Algebra.radix2_32_pair_math_at
          /NTRUPlus768NTTRadix2_32Proof.block
          /NTRUPlus768NTTRadix2_32Proof.double_block
          /NTRUPlus768NTTRadix2_32Algebra.second_base.
  do 23!(rewrite ifF 1:/#).
  rewrite ifT 1:/# /=.
  rewrite radix2_32_zeta12_scheduleE.
  rewrite radix2_32_pair_child1_eqm 1://.
  move=> Hcoeff.
  rewrite [704 + i]addrC [736 + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_32_segment_factor_eqm
    (input output : W16.t Array768.t)
    (input_base output_base e : int) :
  segment_poly output output_base 32 =
    radix2_32_eval_poly input input_base e =>
  factor_eqm 32 e
    (segment_poly input input_base 64)
    (segment_poly output output_base 32).
proof.
  move=> Houtput.
  rewrite segment_poly_split2_32 Houtput.
  exact (radix2_32_eval_factor_eqm input input_base e).
qed.

lemma radix2_32_refine_left
    (original input output : W16.t Array768.t)
    (input_base output_base r : int) :
  0 <= r =>
  factor_eqm 64 (2 * r)
    (input_poly original) (segment_poly input input_base 64) =>
  segment_poly output output_base 32 =
    radix2_32_eval_poly input input_base r =>
  factor_eqm 32 r
    (input_poly original) (segment_poly output output_base 32).
proof.
  move=> Hr Hparent HlocalE.
  have Hparent' : factor_eqm 32 r
      (input_poly original) (segment_poly input input_base 64).
  + apply factor_eqm_split2_32_left; first exact Hr.
    exact Hparent.
  have Hlocal : factor_eqm 32 r
      (segment_poly input input_base 64)
      (segment_poly output output_base 32).
  + apply radix2_32_segment_factor_eqm.
    exact HlocalE.
  apply (factor_eqm_trans 32 r
    (input_poly original) (segment_poly input input_base 64)
    (segment_poly output output_base 32)).
  + exact Hparent'.
  + exact Hlocal.
qed.

lemma radix2_32_refine_right
    (original input output : W16.t Array768.t)
    (input_base output_base r : int) :
  0 <= r =>
  factor_eqm 64 (2 * r)
    (input_poly original) (segment_poly input input_base 64) =>
  segment_poly output output_base 32 =
    radix2_32_eval_poly input input_base (r + 288) =>
  factor_eqm 32 (r + 288)
    (input_poly original) (segment_poly output output_base 32).
proof.
  move=> Hr Hparent HlocalE.
  have Hparent' : factor_eqm 32 (r + 288)
      (input_poly original) (segment_poly input input_base 64).
  + apply factor_eqm_split2_32_right; first exact Hr.
    exact Hparent.
  have Hlocal : factor_eqm 32 (r + 288)
      (segment_poly input input_base 64)
      (segment_poly output output_base 32).
  + apply radix2_32_segment_factor_eqm.
    exact HlocalE.
  apply (factor_eqm_trans 32 (r + 288)
    (input_poly original) (segment_poly input input_base 64)
    (segment_poly output output_base 32)).
  + exact Hparent'.
  + exact Hlocal.
qed.

op radix2_32_semantics
    (original output : W16.t Array768.t) : bool =
  factor_eqm 32 8
    (input_poly original) (segment_poly output 0 32) /\
  factor_eqm 32 296
    (input_poly original) (segment_poly output 32 32) /\
  factor_eqm 32 152
    (input_poly original) (segment_poly output 64 32) /\
  factor_eqm 32 440
    (input_poly original) (segment_poly output 96 32) /\
  factor_eqm 32 56
    (input_poly original) (segment_poly output 128 32) /\
  factor_eqm 32 344
    (input_poly original) (segment_poly output 160 32) /\
  factor_eqm 32 200
    (input_poly original) (segment_poly output 192 32) /\
  factor_eqm 32 488
    (input_poly original) (segment_poly output 224 32) /\
  factor_eqm 32 104
    (input_poly original) (segment_poly output 256 32) /\
  factor_eqm 32 392
    (input_poly original) (segment_poly output 288 32) /\
  factor_eqm 32 248
    (input_poly original) (segment_poly output 320 32) /\
  factor_eqm 32 536
    (input_poly original) (segment_poly output 352 32) /\
  factor_eqm 32 40
    (input_poly original) (segment_poly output 384 32) /\
  factor_eqm 32 328
    (input_poly original) (segment_poly output 416 32) /\
  factor_eqm 32 184
    (input_poly original) (segment_poly output 448 32) /\
  factor_eqm 32 472
    (input_poly original) (segment_poly output 480 32) /\
  factor_eqm 32 88
    (input_poly original) (segment_poly output 512 32) /\
  factor_eqm 32 376
    (input_poly original) (segment_poly output 544 32) /\
  factor_eqm 32 232
    (input_poly original) (segment_poly output 576 32) /\
  factor_eqm 32 520
    (input_poly original) (segment_poly output 608 32) /\
  factor_eqm 32 136
    (input_poly original) (segment_poly output 640 32) /\
  factor_eqm 32 424
    (input_poly original) (segment_poly output 672 32) /\
  factor_eqm 32 280
    (input_poly original) (segment_poly output 704 32) /\
  factor_eqm 32 568
    (input_poly original) (segment_poly output 736 32).

lemma radix2_32_algebra_refines_radix2_64_semantics
    (original input output : W16.t Array768.t) :
  radix2_64_semantics original input =>
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_algebra input output =>
  radix2_32_semantics original output.
proof.
  rewrite /radix2_64_semantics.
  move=> [H16 [H304 [H112 [H400 [H208 [H496 [H80 [H368
          [H176 [H464 [H272 H560]]]]]]]]]]] Halg.
  rewrite /radix2_32_semantics.
  split.
  + apply (radix2_32_refine_left original input output 0 0 8).
    - done.
    - exact H16.
    - apply radix2_32_segment_0_evalE; exact Halg.
  split.
  + apply (radix2_32_refine_right original input output 0 32 8).
    - done.
    - exact H16.
    - apply radix2_32_segment_32_evalE; exact Halg.
  split.
  + apply (radix2_32_refine_left original input output 64 64 152).
    - done.
    - exact H304.
    - apply radix2_32_segment_64_evalE; exact Halg.
  split.
  + apply (radix2_32_refine_right original input output 64 96 152).
    - done.
    - exact H304.
    - apply radix2_32_segment_96_evalE; exact Halg.
  split.
  + apply (radix2_32_refine_left original input output 128 128 56).
    - done.
    - exact H112.
    - apply radix2_32_segment_128_evalE; exact Halg.
  split.
  + apply (radix2_32_refine_right original input output 128 160 56).
    - done.
    - exact H112.
    - apply radix2_32_segment_160_evalE; exact Halg.
  split.
  + apply (radix2_32_refine_left original input output 192 192 200).
    - done.
    - exact H400.
    - apply radix2_32_segment_192_evalE; exact Halg.
  split.
  + apply (radix2_32_refine_right original input output 192 224 200).
    - done.
    - exact H400.
    - apply radix2_32_segment_224_evalE; exact Halg.
  split.
  + apply (radix2_32_refine_left original input output 256 256 104).
    - done.
    - exact H208.
    - apply radix2_32_segment_256_evalE; exact Halg.
  split.
  + apply (radix2_32_refine_right original input output 256 288 104).
    - done.
    - exact H208.
    - apply radix2_32_segment_288_evalE; exact Halg.
  split.
  + apply (radix2_32_refine_left original input output 320 320 248).
    - done.
    - exact H496.
    - apply radix2_32_segment_320_evalE; exact Halg.
  split.
  + apply (radix2_32_refine_right original input output 320 352 248).
    - done.
    - exact H496.
    - apply radix2_32_segment_352_evalE; exact Halg.
  split.
  + apply (radix2_32_refine_left original input output 384 384 40).
    - done.
    - exact H80.
    - apply radix2_32_segment_384_evalE; exact Halg.
  split.
  + apply (radix2_32_refine_right original input output 384 416 40).
    - done.
    - exact H80.
    - apply radix2_32_segment_416_evalE; exact Halg.
  split.
  + apply (radix2_32_refine_left original input output 448 448 184).
    - done.
    - exact H368.
    - apply radix2_32_segment_448_evalE; exact Halg.
  split.
  + apply (radix2_32_refine_right original input output 448 480 184).
    - done.
    - exact H368.
    - apply radix2_32_segment_480_evalE; exact Halg.
  split.
  + apply (radix2_32_refine_left original input output 512 512 88).
    - done.
    - exact H176.
    - apply radix2_32_segment_512_evalE; exact Halg.
  split.
  + apply (radix2_32_refine_right original input output 512 544 88).
    - done.
    - exact H176.
    - apply radix2_32_segment_544_evalE; exact Halg.
  split.
  + apply (radix2_32_refine_left original input output 576 576 232).
    - done.
    - exact H464.
    - apply radix2_32_segment_576_evalE; exact Halg.
  split.
  + apply (radix2_32_refine_right original input output 576 608 232).
    - done.
    - exact H464.
    - apply radix2_32_segment_608_evalE; exact Halg.
  split.
  + apply (radix2_32_refine_left original input output 640 640 136).
    - done.
    - exact H272.
    - apply radix2_32_segment_640_evalE; exact Halg.
  split.
  + apply (radix2_32_refine_right original input output 640 672 136).
    - done.
    - exact H272.
    - apply radix2_32_segment_672_evalE; exact Halg.
  split.
  + apply (radix2_32_refine_left original input output 704 704 280).
    - done.
    - exact H560.
    - apply radix2_32_segment_704_evalE; exact Halg.
  apply (radix2_32_refine_right original input output 704 736 280).
  + done.
  + exact H560.
  + apply radix2_32_segment_736_evalE; exact Halg.
qed.

lemma radix2_32_spec_semantics
    (original input : W16.t Array768.t) :
  radix2_64_semantics original input =>
  NTRUPlus768NTTRadix2_32Algebra.radix2_64_output_shape input =>
  radix2_32_semantics original
    (NTRUPlus768NTTRadix2_32Proof.radix2_32_spec input).
proof.
  move=> Hsem Hshape.
  apply (radix2_32_algebra_refines_radix2_64_semantics
    original input (NTRUPlus768NTTRadix2_32Proof.radix2_32_spec input)).
  + exact Hsem.
  + exact
      (NTRUPlus768NTTRadix2_32Algebra.radix2_32_spec_algebra input Hshape).
qed.

lemma ntt_radix2_32_semantics_functional
    (original rp0 : W16.t Array768.t) :
  radix2_64_semantics original rp0 =>
  NTRUPlus768NTTRadix2_32Algebra.radix2_64_output_shape rp0 =>
  hoare [NTRUPlus768NTTRadix2_32.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_32 :
    rp = rp0 ==> radix2_32_semantics original res].
proof.
  move=> Hsem Hshape.
  conseq
    (NTRUPlus768NTTRadix2_32Algebra.ntt_radix2_32_algebra_functional
      rp0 Hshape) => />.
  move=> result Halg.
  apply (radix2_32_algebra_refines_radix2_64_semantics original rp0 result).
  + exact Hsem.
  + exact Halg.
qed.

lemma ntt_radix2_32_correct_semantics
    (original rp0 : W16.t Array768.t) :
  radix2_64_semantics original rp0 =>
  NTRUPlus768NTTRadix2_32Algebra.radix2_64_output_shape rp0 =>
  phoare [NTRUPlus768NTTRadix2_32.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_32 :
    rp = rp0 ==> radix2_32_semantics original res] = 1%r.
proof.
  move=> Hsem Hshape.
  have Hfunctional :
      hoare [NTRUPlus768NTTRadix2_32.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_32 :
        rp = rp0 ==> radix2_32_semantics original res].
  + apply ntt_radix2_32_semantics_functional.
    - exact Hsem.
    - exact Hshape.
  by conseq NTRUPlus768NTTRadix2_32Proof.ntt_radix2_32_lossless Hfunctional.
qed.
