require import AllCore IntDiv List Ring StdBigop StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array768.
require import NTRUPlus768BasemulAlgebra NTRUPlus768NTTSchedule.
require import NTRUPlus768CyclotomicFactorization.
require import NTRUPlus768EvaluationSemantics.
require import NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768ForwardNTTRadix3Semantics.
require import NTRUPlus768PolyBasemulAlgebra.
require import NTRUPlus768NTTRadix2_64.
require import NTRUPlus768NTTRadix2_64Algebra NTRUPlus768NTTRadix2_64Proof.

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

(* The first binary layer refines each degree-128 radix-3 representative into
   two degree-64 representatives. *)

op segment2_poly (a : W16.t Array768.t) (base : int) : NTRUPoly.poly =
  segment_poly a base 64 +
  segment_poly a (base + 64) 64 * exp X 64.

op radix2_eval_poly
    (a : W16.t Array768.t) (base e : int) : NTRUPoly.poly =
  segment_poly a base 64 +
  segment_poly a (base + 64) 64 * root_poly e.

lemma segment_poly_split2 (a : W16.t Array768.t) (base : int) :
  segment_poly a base 128 = segment2_poly a base.
proof.
  rewrite /segment2_poly.
  rewrite (segment_poly_split a base 64 64) 1:// 1://.
  done.
qed.

lemma radix2_eval_factor_eqm
    (a : W16.t Array768.t) (base e : int) :
  factor_eqm 64 e (segment2_poly a base) (radix2_eval_poly a base e).
proof.
  rewrite /factor_eqm /schedule_factor_modulus.
  exists (-(segment_poly a (base + 64) 64)).
  rewrite /segment2_poly /radix2_eval_poly /root_poly.
  ring.
qed.

lemma schedule_modulus_split2 (r : int) :
  0 <= r =>
  schedule_factor_modulus 128 (2 * r) =
  schedule_factor_modulus 64 r *
    schedule_factor_modulus 64 (r + 288).
proof.
  move=> Hr.
  move: (factor_split2 X 64 r _ Hr); first smt().
  rewrite /factor /schedule_factor_modulus /=.
  done.
qed.

lemma factor_eqm_split2_left
    (r : int) (p q : NTRUPoly.poly) :
  0 <= r =>
  factor_eqm 128 (2 * r) p q =>
  factor_eqm 64 r p q.
proof.
  move=> Hr.
  apply factor_eqm_weaken.
  exists (schedule_factor_modulus 64 (r + 288)).
  exact (schedule_modulus_split2 r Hr).
qed.

lemma factor_eqm_split2_right
    (r : int) (p q : NTRUPoly.poly) :
  0 <= r =>
  factor_eqm 128 (2 * r) p q =>
  factor_eqm 64 (r + 288) p q.
proof.
  move=> Hr.
  apply factor_eqm_weaken.
  exists (schedule_factor_modulus 64 r).
  rewrite schedule_modulus_split2 1:Hr.
  ring.
qed.

lemma schedule_root_shift_288_eqm (r : int) :
  0 <= r =>
  (- schedule_root r) %% q = schedule_root (r + 288) %% q.
proof.
  move=> Hr.
  rewrite /schedule_root.
  rewrite (zeta_root_shift_288 r Hr).
  by rewrite modz_mod.
qed.

lemma radix2_pair_child0_eqm (a0 a1 r : int) :
  (NTRUPlus768NTTRadix2_64Algebra.radix2_64_pair_math
     a0 a1 (schedule_root r)).`1 %% q =
  (a0 + a1 * schedule_root r) %% q.
proof.
  by rewrite /NTRUPlus768NTTRadix2_64Algebra.radix2_64_pair_math.
qed.

lemma radix2_pair_child1_eqm (a0 a1 r : int) :
  0 <= r =>
  (NTRUPlus768NTTRadix2_64Algebra.radix2_64_pair_math
     a0 a1 (schedule_root r)).`2 %% q =
  (a0 + a1 * schedule_root (r + 288)) %% q.
proof.
  move=> Hr.
  rewrite /NTRUPlus768NTTRadix2_64Algebra.radix2_64_pair_math.
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

op linear2_remainder_poly
    (a : W16.t Array768.t) (base c : int) : NTRUPoly.poly =
  PCA.bigi predT
    (fun i =>
      polyC
        (lift_int
          (coeff a.[i + base] +
           coeff a.[i + base + 64] * c)) *
      exp X i)
    0 64.

lemma linear2_remainder_polyE
    (a : W16.t Array768.t) (base c : int) :
  linear2_remainder_poly a base c =
  segment_poly a base 64 +
  polyC (lift_int c) * segment_poly a (base + 64) 64.
proof.
  rewrite /linear2_remainder_poly /segment_poly.
  have Hdist :
      polyC (lift_int c) *
        PCA.bigi predT
          (fun i => polyC (lift_word a.[i + (base + 64)]) * exp X i)
          0 64 =
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c) *
            (polyC (lift_word a.[i + (base + 64)]) * exp X i))
        0 64.
  + exact
      (PCA.mulr_sumr predT
        (fun i => polyC (lift_word a.[i + (base + 64)]) * exp X i)
        (range 0 64) (polyC (lift_int c))).
  have Hsplit :
      PCA.bigi predT
        (fun i => polyC (lift_word a.[i + base]) * exp X i)
        0 64 +
      PCA.bigi predT
        (fun i =>
          polyC (lift_int c) *
            (polyC (lift_word a.[i + (base + 64)]) * exp X i))
        0 64 =
      PCA.bigi predT
        (fun i =>
          polyC (lift_word a.[i + base]) * exp X i +
          polyC (lift_int c) *
            (polyC (lift_word a.[i + (base + 64)]) * exp X i))
        0 64.
  + apply/eq_sym.
    exact
      (PCA.big_split predT
        (fun i => polyC (lift_word a.[i + base]) * exp X i)
        (fun i =>
          polyC (lift_int c) *
            (polyC (lift_word a.[i + (base + 64)]) * exp X i))
        (range 0 64)).
  rewrite Hdist Hsplit.
  apply PCA.eq_big_int => i Hi.
  rewrite /lift_word /lift_int /=.
  rewrite CycloFq.incyclocoeffD CycloFq.incyclocoeffM.
  rewrite NTRUPoly.polyCD NTRUPoly.polyCM.
  rewrite poly_mul_add_right.
  congr.
  have Hidx : i + base + 64 = i + (base + 64) by ring.
  rewrite Hidx.
  apply poly_mul_reorder.
qed.

lemma segment_poly_linear2E
    (input output : W16.t Array768.t)
    (input_base output_base c : int) :
  (forall i, 0 <= i < 64 =>
    coeff output.[i + output_base] %% q =
    (coeff input.[i + input_base] +
     coeff input.[i + input_base + 64] * c) %% q) =>
  segment_poly output output_base 64 =
  linear2_remainder_poly input input_base c.
proof.
  move=> Hcoeff.
  rewrite /segment_poly /linear2_remainder_poly.
  apply PCA.eq_big_int => i Hi.
  have Hmod := Hcoeff i Hi.
  have Elift :
      lift_word output.[i + output_base] =
      lift_int
        (coeff input.[i + input_base] +
         coeff input.[i + input_base + 64] * c).
  + rewrite /lift_word.
    apply lift_int_eq.
    exact Hmod.
  by rewrite /= Elift.
qed.

lemma linear2_remainder_radix2_evalE
    (a : W16.t Array768.t) (base e : int) :
  0 <= e =>
  linear2_remainder_poly a base (schedule_root e) =
  radix2_eval_poly a base e.
proof.
  move=> He.
  rewrite linear2_remainder_polyE /radix2_eval_poly /root_poly.
  rewrite schedule_root_fieldE 1:He.
  ring.
qed.

lemma segment_poly_radix2_evalE
    (input output : W16.t Array768.t)
    (input_base output_base e : int) :
  0 <= e =>
  (forall i, 0 <= i < 64 =>
    coeff output.[i + output_base] %% q =
    (coeff input.[i + input_base] +
     coeff input.[i + input_base + 64] * schedule_root e) %% q) =>
  segment_poly output output_base 64 =
  radix2_eval_poly input input_base e.
proof.
  move=> He Hcoeff.
  have Hsegment :
      segment_poly output output_base 64 =
      linear2_remainder_poly input input_base (schedule_root e).
  + apply segment_poly_linear2E.
    exact Hcoeff.
  rewrite Hsegment.
  apply linear2_remainder_radix2_evalE.
  exact He.
qed.

lemma radix2_64_zeta1_scheduleE :
  NTRUPlus768NTTRadix2_64Algebra.radix2_64_zeta1_root = schedule_root 16.
proof.
  by rewrite /NTRUPlus768NTTRadix2_64Algebra.radix2_64_zeta1_root
             /schedule_root.
qed.

lemma radix2_64_zeta2_scheduleE :
  NTRUPlus768NTTRadix2_64Algebra.radix2_64_zeta2_root = schedule_root 112.
proof.
  by rewrite /NTRUPlus768NTTRadix2_64Algebra.radix2_64_zeta2_root
             /schedule_root.
qed.

lemma radix2_64_zeta3_scheduleE :
  NTRUPlus768NTTRadix2_64Algebra.radix2_64_zeta3_root = schedule_root 208.
proof.
  by rewrite /NTRUPlus768NTTRadix2_64Algebra.radix2_64_zeta3_root
             /schedule_root.
qed.

lemma radix2_64_zeta4_scheduleE :
  NTRUPlus768NTTRadix2_64Algebra.radix2_64_zeta4_root = schedule_root 80.
proof.
  by rewrite /NTRUPlus768NTTRadix2_64Algebra.radix2_64_zeta4_root
             /schedule_root.
qed.

lemma radix2_64_zeta5_scheduleE :
  NTRUPlus768NTTRadix2_64Algebra.radix2_64_zeta5_root = schedule_root 176.
proof.
  by rewrite /NTRUPlus768NTTRadix2_64Algebra.radix2_64_zeta5_root
             /schedule_root.
qed.

lemma radix2_64_zeta6_scheduleE :
  NTRUPlus768NTTRadix2_64Algebra.radix2_64_zeta6_root = schedule_root 272.
proof.
  by rewrite /NTRUPlus768NTTRadix2_64Algebra.radix2_64_zeta6_root
             /schedule_root.
qed.

lemma radix2_64_segment_0_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_64Algebra.radix2_64_algebra input output =>
  segment_poly output 0 64 = radix2_eval_poly input 0 16.
proof.
  move=> Halg.
  apply segment_poly_radix2_evalE; first done.
  move=> i Hi.
  have [_ Hcoeff] := Halg i _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_64Algebra.radix2_64_math
          /NTRUPlus768NTTRadix2_64Algebra.radix2_64_pair_math_at
          /NTRUPlus768NTTRadix2_64Proof.block
          /NTRUPlus768NTTRadix2_64Proof.double_block
          /NTRUPlus768NTTRadix2_64Algebra.second_base
          ifT 1:/# /=.
  rewrite radix2_64_zeta1_scheduleE radix2_pair_child0_eqm.
  done.
qed.

lemma radix2_64_segment_64_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_64Algebra.radix2_64_algebra input output =>
  segment_poly output 64 64 = radix2_eval_poly input 0 304.
proof.
  move=> Halg.
  apply segment_poly_radix2_evalE; first done.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 64) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_64Algebra.radix2_64_math
          /NTRUPlus768NTTRadix2_64Algebra.radix2_64_pair_math_at
          /NTRUPlus768NTTRadix2_64Proof.block
          /NTRUPlus768NTTRadix2_64Proof.double_block
          /NTRUPlus768NTTRadix2_64Algebra.second_base
          ifF 1:/# ifT 1:/# /=.
  rewrite radix2_64_zeta1_scheduleE.
  rewrite (radix2_pair_child1_eqm
    (coeff input.[i]) (coeff input.[i + 64]) 16) 1://.
  done.
qed.

lemma radix2_64_segment_128_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_64Algebra.radix2_64_algebra input output =>
  segment_poly output 128 64 = radix2_eval_poly input 128 112.
proof.
  move=> Halg.
  apply segment_poly_radix2_evalE; first done.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 128) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_64Algebra.radix2_64_math
          /NTRUPlus768NTTRadix2_64Algebra.radix2_64_pair_math_at
          /NTRUPlus768NTTRadix2_64Proof.block
          /NTRUPlus768NTTRadix2_64Proof.double_block
          /NTRUPlus768NTTRadix2_64Algebra.second_base
          ifF 1:/# ifF 1:/# ifT 1:/# /=.
  rewrite radix2_64_zeta2_scheduleE radix2_pair_child0_eqm.
  move=> Hcoeff.
  rewrite [128 + i]addrC [192 + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_64_segment_192_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_64Algebra.radix2_64_algebra input output =>
  segment_poly output 192 64 = radix2_eval_poly input 128 400.
proof.
  move=> Halg.
  apply segment_poly_radix2_evalE; first done.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 192) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_64Algebra.radix2_64_math
          /NTRUPlus768NTTRadix2_64Algebra.radix2_64_pair_math_at
          /NTRUPlus768NTTRadix2_64Proof.block
          /NTRUPlus768NTTRadix2_64Proof.double_block
          /NTRUPlus768NTTRadix2_64Algebra.second_base
          ifF 1:/# ifF 1:/# ifF 1:/# ifT 1:/# /=.
  rewrite radix2_64_zeta2_scheduleE.
  rewrite radix2_pair_child1_eqm 1://.
  move=> Hcoeff.
  rewrite [128 + i]addrC [192 + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_64_segment_256_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_64Algebra.radix2_64_algebra input output =>
  segment_poly output 256 64 = radix2_eval_poly input 256 208.
proof.
  move=> Halg.
  apply segment_poly_radix2_evalE; first done.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 256) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_64Algebra.radix2_64_math
          /NTRUPlus768NTTRadix2_64Algebra.radix2_64_pair_math_at
          /NTRUPlus768NTTRadix2_64Proof.block
          /NTRUPlus768NTTRadix2_64Proof.double_block
          /NTRUPlus768NTTRadix2_64Algebra.second_base
          ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifT 1:/# /=.
  rewrite radix2_64_zeta3_scheduleE radix2_pair_child0_eqm.
  move=> Hcoeff.
  rewrite [256 + i]addrC [320 + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_64_segment_320_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_64Algebra.radix2_64_algebra input output =>
  segment_poly output 320 64 = radix2_eval_poly input 256 496.
proof.
  move=> Halg.
  apply segment_poly_radix2_evalE; first done.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 320) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_64Algebra.radix2_64_math
          /NTRUPlus768NTTRadix2_64Algebra.radix2_64_pair_math_at
          /NTRUPlus768NTTRadix2_64Proof.block
          /NTRUPlus768NTTRadix2_64Proof.double_block
          /NTRUPlus768NTTRadix2_64Algebra.second_base
          ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifT 1:/# /=.
  rewrite radix2_64_zeta3_scheduleE.
  rewrite radix2_pair_child1_eqm 1://.
  move=> Hcoeff.
  rewrite [256 + i]addrC [320 + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_64_segment_384_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_64Algebra.radix2_64_algebra input output =>
  segment_poly output 384 64 = radix2_eval_poly input 384 80.
proof.
  move=> Halg.
  apply segment_poly_radix2_evalE; first done.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 384) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_64Algebra.radix2_64_math
          /NTRUPlus768NTTRadix2_64Algebra.radix2_64_pair_math_at
          /NTRUPlus768NTTRadix2_64Proof.block
          /NTRUPlus768NTTRadix2_64Proof.double_block
          /NTRUPlus768NTTRadix2_64Algebra.second_base
          ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/#
          ifT 1:/# /=.
  rewrite radix2_64_zeta4_scheduleE radix2_pair_child0_eqm.
  move=> Hcoeff.
  rewrite [384 + i]addrC [448 + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_64_segment_448_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_64Algebra.radix2_64_algebra input output =>
  segment_poly output 448 64 = radix2_eval_poly input 384 368.
proof.
  move=> Halg.
  apply segment_poly_radix2_evalE; first done.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 448) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_64Algebra.radix2_64_math
          /NTRUPlus768NTTRadix2_64Algebra.radix2_64_pair_math_at
          /NTRUPlus768NTTRadix2_64Proof.block
          /NTRUPlus768NTTRadix2_64Proof.double_block
          /NTRUPlus768NTTRadix2_64Algebra.second_base
          ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/#
          ifF 1:/# ifT 1:/# /=.
  rewrite radix2_64_zeta4_scheduleE.
  rewrite radix2_pair_child1_eqm 1://.
  move=> Hcoeff.
  rewrite [384 + i]addrC [448 + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_64_segment_512_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_64Algebra.radix2_64_algebra input output =>
  segment_poly output 512 64 = radix2_eval_poly input 512 176.
proof.
  move=> Halg.
  apply segment_poly_radix2_evalE; first done.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 512) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_64Algebra.radix2_64_math
          /NTRUPlus768NTTRadix2_64Algebra.radix2_64_pair_math_at
          /NTRUPlus768NTTRadix2_64Proof.block
          /NTRUPlus768NTTRadix2_64Proof.double_block
          /NTRUPlus768NTTRadix2_64Algebra.second_base
          ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/#
          ifF 1:/# ifF 1:/# ifT 1:/# /=.
  rewrite radix2_64_zeta5_scheduleE radix2_pair_child0_eqm.
  move=> Hcoeff.
  rewrite [512 + i]addrC [576 + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_64_segment_576_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_64Algebra.radix2_64_algebra input output =>
  segment_poly output 576 64 = radix2_eval_poly input 512 464.
proof.
  move=> Halg.
  apply segment_poly_radix2_evalE; first done.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 576) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_64Algebra.radix2_64_math
          /NTRUPlus768NTTRadix2_64Algebra.radix2_64_pair_math_at
          /NTRUPlus768NTTRadix2_64Proof.block
          /NTRUPlus768NTTRadix2_64Proof.double_block
          /NTRUPlus768NTTRadix2_64Algebra.second_base
          ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/#
          ifF 1:/# ifF 1:/# ifF 1:/# ifT 1:/# /=.
  rewrite radix2_64_zeta5_scheduleE.
  rewrite radix2_pair_child1_eqm 1://.
  move=> Hcoeff.
  rewrite [512 + i]addrC [576 + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_64_segment_640_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_64Algebra.radix2_64_algebra input output =>
  segment_poly output 640 64 = radix2_eval_poly input 640 272.
proof.
  move=> Halg.
  apply segment_poly_radix2_evalE; first done.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 640) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_64Algebra.radix2_64_math
          /NTRUPlus768NTTRadix2_64Algebra.radix2_64_pair_math_at
          /NTRUPlus768NTTRadix2_64Proof.block
          /NTRUPlus768NTTRadix2_64Proof.double_block
          /NTRUPlus768NTTRadix2_64Algebra.second_base
          ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/#
          ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifT 1:/# /=.
  rewrite radix2_64_zeta6_scheduleE radix2_pair_child0_eqm.
  move=> Hcoeff.
  rewrite [640 + i]addrC [704 + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_64_segment_704_evalE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix2_64Algebra.radix2_64_algebra input output =>
  segment_poly output 704 64 = radix2_eval_poly input 640 560.
proof.
  move=> Halg.
  apply segment_poly_radix2_evalE; first done.
  move=> i Hi.
  have [_ Hcoeff] := Halg (i + 704) _; first smt().
  move: Hcoeff.
  rewrite /NTRUPlus768NTTRadix2_64Algebra.radix2_64_math
          /NTRUPlus768NTTRadix2_64Algebra.radix2_64_pair_math_at
          /NTRUPlus768NTTRadix2_64Proof.block
          /NTRUPlus768NTTRadix2_64Proof.double_block
          /NTRUPlus768NTTRadix2_64Algebra.second_base
          ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/#
          ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# /=.
  rewrite radix2_64_zeta6_scheduleE.
  rewrite radix2_pair_child1_eqm 1://.
  move=> Hcoeff.
  rewrite [640 + i]addrC [704 + i]addrC in Hcoeff.
  exact Hcoeff.
qed.

lemma radix2_64_segment_factor_eqm
    (input output : W16.t Array768.t)
    (input_base output_base e : int) :
  segment_poly output output_base 64 =
    radix2_eval_poly input input_base e =>
  factor_eqm 64 e
    (segment_poly input input_base 128)
    (segment_poly output output_base 64).
proof.
  move=> Houtput.
  rewrite segment_poly_split2 Houtput.
  exact (radix2_eval_factor_eqm input input_base e).
qed.

lemma radix2_64_refine_left
    (original input output : W16.t Array768.t)
    (input_base output_base r : int) :
  0 <= r =>
  factor_eqm 128 (2 * r)
    (input_poly original) (segment_poly input input_base 128) =>
  segment_poly output output_base 64 =
    radix2_eval_poly input input_base r =>
  factor_eqm 64 r
    (input_poly original) (segment_poly output output_base 64).
proof.
  move=> Hr Hparent HlocalE.
  have Hparent' : factor_eqm 64 r
      (input_poly original) (segment_poly input input_base 128).
  + apply factor_eqm_split2_left; first exact Hr.
    exact Hparent.
  have Hlocal : factor_eqm 64 r
      (segment_poly input input_base 128)
      (segment_poly output output_base 64).
  + apply radix2_64_segment_factor_eqm.
    exact HlocalE.
  apply (factor_eqm_trans 64 r
    (input_poly original) (segment_poly input input_base 128)
    (segment_poly output output_base 64)).
  + exact Hparent'.
  + exact Hlocal.
qed.

lemma radix2_64_refine_right
    (original input output : W16.t Array768.t)
    (input_base output_base r : int) :
  0 <= r =>
  factor_eqm 128 (2 * r)
    (input_poly original) (segment_poly input input_base 128) =>
  segment_poly output output_base 64 =
    radix2_eval_poly input input_base (r + 288) =>
  factor_eqm 64 (r + 288)
    (input_poly original) (segment_poly output output_base 64).
proof.
  move=> Hr Hparent HlocalE.
  have Hparent' : factor_eqm 64 (r + 288)
      (input_poly original) (segment_poly input input_base 128).
  + apply factor_eqm_split2_right; first exact Hr.
    exact Hparent.
  have Hlocal : factor_eqm 64 (r + 288)
      (segment_poly input input_base 128)
      (segment_poly output output_base 64).
  + apply radix2_64_segment_factor_eqm.
    exact HlocalE.
  apply (factor_eqm_trans 64 (r + 288)
    (input_poly original) (segment_poly input input_base 128)
    (segment_poly output output_base 64)).
  + exact Hparent'.
  + exact Hlocal.
qed.

op radix2_64_semantics
    (original output : W16.t Array768.t) : bool =
  factor_eqm 64 16
    (input_poly original) (segment_poly output 0 64) /\
  factor_eqm 64 304
    (input_poly original) (segment_poly output 64 64) /\
  factor_eqm 64 112
    (input_poly original) (segment_poly output 128 64) /\
  factor_eqm 64 400
    (input_poly original) (segment_poly output 192 64) /\
  factor_eqm 64 208
    (input_poly original) (segment_poly output 256 64) /\
  factor_eqm 64 496
    (input_poly original) (segment_poly output 320 64) /\
  factor_eqm 64 80
    (input_poly original) (segment_poly output 384 64) /\
  factor_eqm 64 368
    (input_poly original) (segment_poly output 448 64) /\
  factor_eqm 64 176
    (input_poly original) (segment_poly output 512 64) /\
  factor_eqm 64 464
    (input_poly original) (segment_poly output 576 64) /\
  factor_eqm 64 272
    (input_poly original) (segment_poly output 640 64) /\
  factor_eqm 64 560
    (input_poly original) (segment_poly output 704 64).

lemma radix2_64_algebra_refines_radix3_semantics
    (original input output : W16.t Array768.t) :
  radix3_semantics original input =>
  NTRUPlus768NTTRadix2_64Algebra.radix2_64_algebra input output =>
  radix2_64_semantics original output.
proof.
  rewrite /radix3_semantics.
  move=> [H32 [H224 [H416 [H160 [H352 H544]]]]] Halg.
  rewrite /radix2_64_semantics.
  split.
  + apply (radix2_64_refine_left original input output 0 0 16).
    - done.
    - exact H32.
    - apply radix2_64_segment_0_evalE; exact Halg.
  split.
  + apply (radix2_64_refine_right original input output 0 64 16).
    - done.
    - exact H32.
    - apply radix2_64_segment_64_evalE; exact Halg.
  split.
  + apply (radix2_64_refine_left original input output 128 128 112).
    - done.
    - exact H224.
    - apply radix2_64_segment_128_evalE; exact Halg.
  split.
  + apply (radix2_64_refine_right original input output 128 192 112).
    - done.
    - exact H224.
    - apply radix2_64_segment_192_evalE; exact Halg.
  split.
  + apply (radix2_64_refine_left original input output 256 256 208).
    - done.
    - exact H416.
    - apply radix2_64_segment_256_evalE; exact Halg.
  split.
  + apply (radix2_64_refine_right original input output 256 320 208).
    - done.
    - exact H416.
    - apply radix2_64_segment_320_evalE; exact Halg.
  split.
  + apply (radix2_64_refine_left original input output 384 384 80).
    - done.
    - exact H160.
    - apply radix2_64_segment_384_evalE; exact Halg.
  split.
  + apply (radix2_64_refine_right original input output 384 448 80).
    - done.
    - exact H160.
    - apply radix2_64_segment_448_evalE; exact Halg.
  split.
  + apply (radix2_64_refine_left original input output 512 512 176).
    - done.
    - exact H352.
    - apply radix2_64_segment_512_evalE; exact Halg.
  split.
  + apply (radix2_64_refine_right original input output 512 576 176).
    - done.
    - exact H352.
    - apply radix2_64_segment_576_evalE; exact Halg.
  split.
  + apply (radix2_64_refine_left original input output 640 640 272).
    - done.
    - exact H544.
    - apply radix2_64_segment_640_evalE; exact Halg.
  apply (radix2_64_refine_right original input output 640 704 272).
  + done.
  + exact H544.
  + apply radix2_64_segment_704_evalE; exact Halg.
qed.

lemma radix2_64_spec_semantics
    (original input : W16.t Array768.t) :
  radix3_semantics original input =>
  NTRUPlus768NTTRadix2_64Algebra.radix3_output_shape input =>
  radix2_64_semantics original
    (NTRUPlus768NTTRadix2_64Proof.radix2_64_spec input).
proof.
  move=> Hsem Hshape.
  apply (radix2_64_algebra_refines_radix3_semantics
    original input (NTRUPlus768NTTRadix2_64Proof.radix2_64_spec input)).
  + exact Hsem.
  + exact
      (NTRUPlus768NTTRadix2_64Algebra.radix2_64_spec_algebra input Hshape).
qed.

lemma ntt_radix2_64_semantics_functional
    (original rp0 : W16.t Array768.t) :
  radix3_semantics original rp0 =>
  NTRUPlus768NTTRadix2_64Algebra.radix3_output_shape rp0 =>
  hoare [NTRUPlus768NTTRadix2_64.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_64 :
    rp = rp0 ==> radix2_64_semantics original res].
proof.
  move=> Hsem Hshape.
  conseq
    (NTRUPlus768NTTRadix2_64Algebra.ntt_radix2_64_algebra_functional
      rp0 Hshape) => />.
  move=> result Halg.
  apply (radix2_64_algebra_refines_radix3_semantics original rp0 result).
  + exact Hsem.
  + exact Halg.
qed.

lemma ntt_radix2_64_correct_semantics
    (original rp0 : W16.t Array768.t) :
  radix3_semantics original rp0 =>
  NTRUPlus768NTTRadix2_64Algebra.radix3_output_shape rp0 =>
  phoare [NTRUPlus768NTTRadix2_64.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_64 :
    rp = rp0 ==> radix2_64_semantics original res] = 1%r.
proof.
  move=> Hsem Hshape.
  have Hfunctional :
      hoare [NTRUPlus768NTTRadix2_64.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_64 :
        rp = rp0 ==> radix2_64_semantics original res].
  + apply ntt_radix2_64_semantics_functional.
    - exact Hsem.
    - exact Hshape.
  by conseq NTRUPlus768NTTRadix2_64Proof.ntt_radix2_64_lossless Hfunctional.
qed.
