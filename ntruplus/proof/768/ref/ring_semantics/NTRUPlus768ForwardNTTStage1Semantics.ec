require import AllCore IntDiv List Ring StdBigop StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array768.
require import NTRUPlus768CyclotomicFactorization.
require import NTRUPlus768EvaluationSemantics.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768NTTStage1.
require import NTRUPlus768NTTStage1Algebra NTRUPlus768NTTStage1Proof.

import NTRUPoly.BigPoly.

(* The first forward NTT layer splits the global polynomial into two
   degree-384 quotient representatives.  This theory states only that first
   semantic split; later radix layers will refine the same invariant. *)

op segment_poly
    (a : W16.t Array768.t) (base length : int) : poly =
  PCA.bigi predT
    (fun i => polyC (lift_word a.[i + base]) * exp X i)
    0 length.

op input_poly (a : W16.t Array768.t) : poly =
  segment_poly a 0 384 + segment_poly a 384 384 * exp X 384.

op stage1_remainder_poly
    (a : W16.t Array768.t) (root : int) : poly =
  PCA.bigi predT
    (fun i =>
      polyC
        (lift_int
          (coeff a.[i] + coeff a.[i + 384] * root)) *
      exp X i)
    0 384.

op schedule_factor_modulus (m e : int) : poly =
  exp X m - polyC (CycloFq.exp zeta_field e).

op factor_eqm (m e : int) (p q : poly) : bool =
  exists h, q - p = h * schedule_factor_modulus m e.

lemma poly_mul_add_right (a b c : poly) :
  (a + b) * c = a * c + b * c.
proof. ring. qed.

lemma poly_mul_reorder (a b c : poly) :
  (a * b) * c = b * (a * c).
proof. ring. qed.

lemma exp_X4_96 :
  exp (exp X 4) 96 = exp X 384.
proof.
  change (exp (exp X 4) 96 = exp X (4 * 96)).
  apply/eq_sym.
  exact (NTRUPoly.PolyComRing.exprM X 4 96).
qed.

lemma exp_X4_192 :
  exp (exp X 4) 192 = exp X 768.
proof.
  change (exp (exp X 4) 192 = exp X (4 * 192)).
  apply/eq_sym.
  exact (NTRUPoly.PolyComRing.exprM X 4 192).
qed.

lemma factor_eqm_refl (m e : int) (p : poly) :
  factor_eqm m e p p.
proof.
  rewrite /factor_eqm.
  exists poly0.
  ring.
qed.

lemma factor_eqm_sym (m e : int) (p q : poly) :
  factor_eqm m e p q => factor_eqm m e q p.
proof.
  rewrite /factor_eqm.
  move=> [h Hh].
  exists (-h).
  have -> : p - q = -(q - p) by ring.
  rewrite Hh.
  ring.
qed.

lemma factor_eqm_trans (m e : int) (p q r : poly) :
  factor_eqm m e p q => factor_eqm m e q r => factor_eqm m e p r.
proof.
  rewrite /factor_eqm.
  move=> [h Hh] [j Hj].
  exists (h + j).
  have -> : r - p = (q - p) + (r - q) by ring.
  rewrite Hh Hj.
  ring.
qed.

lemma factor_eqm_add (m e : int) (p q r s : poly) :
  factor_eqm m e p q => factor_eqm m e r s =>
  factor_eqm m e (p + r) (q + s).
proof.
  rewrite /factor_eqm.
  move=> [h Hh] [j Hj].
  exists (h + j).
  have -> : q + s - (p + r) = (q - p) + (s - r) by ring.
  rewrite Hh Hj.
  ring.
qed.

lemma factor_eqm_mul (m e : int) (p q r s : poly) :
  factor_eqm m e p q => factor_eqm m e r s =>
  factor_eqm m e (p * r) (q * s).
proof.
  rewrite /factor_eqm.
  move=> [h Hh] [j Hj].
  exists (h * s + p * j).
  have -> : q * s - p * r = (q - p) * s + p * (s - r) by ring.
  rewrite Hh Hj.
  ring.
qed.

lemma stage1_root_value :
  NTRUPlus768NTTStage1Algebra.stage1_root = 2735.
proof.
  by rewrite /NTRUPlus768NTTStage1Algebra.stage1_root /zeta_root /q /=.
qed.

lemma stage1_root_field_96 :
  lift_int NTRUPlus768NTTStage1Algebra.stage1_root =
  CycloFq.exp zeta_field 96.
proof.
  rewrite stage1_root_value /lift_int.
  by rewrite zeta96E.
qed.

lemma stage1_other_root_field_480 :
  lift_int (1 - NTRUPlus768NTTStage1Algebra.stage1_root) =
  CycloFq.exp zeta_field 480.
proof.
  rewrite stage1_root_value /lift_int.
  rewrite zeta480E.
  apply/CycloFq.eq_incyclocoeff.
  by rewrite /q /=.
qed.

lemma stage1_factor_moduli_global :
  schedule_factor_modulus 384 96 *
    schedule_factor_modulus 384 480 = global_modulus.
proof.
  move: (initial_factorization (exp X 4)).
  rewrite /factor_product /roots_initial /ell /=.
  rewrite /factor !PCM.big_cons /predT /=.
  move=> Hfactor.
  rewrite PCM.big_nil in Hfactor.
  rewrite NTRUPoly.PolyComRing.mulr1 in Hfactor.
  rewrite exp_X4_96 exp_X4_192 in Hfactor.
  rewrite /schedule_factor_modulus /global_modulus.
  exact Hfactor.
qed.

lemma stage1_remainder_polyE
    (a : W16.t Array768.t) (root : int) :
  stage1_remainder_poly a root =
  segment_poly a 0 384 +
  polyC (lift_int root) * segment_poly a 384 384.
proof.
  rewrite /stage1_remainder_poly /segment_poly.
  have Hdist :
      polyC (lift_int root) *
        PCA.bigi predT
          (fun i => polyC (lift_word a.[i + 384]) * exp X i)
          0 384 =
      PCA.bigi predT
        (fun i =>
          polyC (lift_int root) *
            (polyC (lift_word a.[i + 384]) * exp X i))
        0 384.
  + exact
      (PCA.mulr_sumr predT
        (fun i => polyC (lift_word a.[i + 384]) * exp X i)
        (range 0 384) (polyC (lift_int root))).
  have Hsplit :
      PCA.bigi predT
        (fun i => polyC (lift_word a.[i + 0]) * exp X i)
        0 384 +
      PCA.bigi predT
        (fun i =>
          polyC (lift_int root) *
            (polyC (lift_word a.[i + 384]) * exp X i))
        0 384 =
      PCA.bigi predT
        (fun i =>
          polyC (lift_word a.[i + 0]) * exp X i +
          polyC (lift_int root) *
            (polyC (lift_word a.[i + 384]) * exp X i))
        0 384.
  + apply/eq_sym.
    exact
      (PCA.big_split predT
        (fun i => polyC (lift_word a.[i + 0]) * exp X i)
        (fun i =>
          polyC (lift_int root) *
            (polyC (lift_word a.[i + 384]) * exp X i))
        (range 0 384)).
  rewrite Hdist Hsplit.
  apply PCA.eq_big_int => i Hi.
  rewrite /lift_word /lift_int /=.
  rewrite CycloFq.incyclocoeffD CycloFq.incyclocoeffM.
  rewrite NTRUPoly.polyCD NTRUPoly.polyCM.
  rewrite poly_mul_add_right.
  congr.
  apply poly_mul_reorder.
qed.

lemma stage1_low_segment_polyE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTStage1Algebra.stage1_algebra input output =>
  segment_poly output 0 384 =
  stage1_remainder_poly input NTRUPlus768NTTStage1Algebra.stage1_root.
proof.
  move=> Halg.
  rewrite /NTRUPlus768NTTStage1Algebra.stage1_algebra in Halg.
  rewrite /segment_poly /stage1_remainder_poly.
  apply PCA.eq_big_int => i Hi.
  have [_ Hcoeff] := Halg i _; first smt().
  have Hmod :
      coeff output.[i] %% q =
      (coeff input.[i] +
       coeff input.[i + 384] *
         NTRUPlus768NTTStage1Algebra.stage1_root) %% q.
  + move: Hcoeff.
    rewrite /NTRUPlus768NTTStage1Algebra.stage1_math.
    rewrite /NTRUPlus768NTTStage1Proof.half ifT 1:/#.
    done.
  have Elift :
      lift_word output.[i] =
      lift_int
        (coeff input.[i] +
         coeff input.[i + 384] *
           NTRUPlus768NTTStage1Algebra.stage1_root).
  + rewrite /= /lift_word.
    apply lift_int_eq.
    exact Hmod.
  by rewrite /= Elift.
qed.

lemma stage1_high_segment_polyE
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTStage1Algebra.stage1_algebra input output =>
  segment_poly output 384 384 =
  stage1_remainder_poly input
    (1 - NTRUPlus768NTTStage1Algebra.stage1_root).
proof.
  move=> Halg.
  rewrite /NTRUPlus768NTTStage1Algebra.stage1_algebra in Halg.
  rewrite /segment_poly /stage1_remainder_poly.
  apply PCA.eq_big_int => i Hi.
  have Hj : 0 <= i + 384 < 768 by smt().
  have [_ Hcoeff] := Halg (i + 384) Hj.
  have Hexpr :
      coeff input.[i] + coeff input.[i + 384] -
        coeff input.[i + 384] *
          NTRUPlus768NTTStage1Algebra.stage1_root =
      coeff input.[i] +
        coeff input.[i + 384] *
          (1 - NTRUPlus768NTTStage1Algebra.stage1_root) by ring.
  have Hmod :
      coeff output.[i + 384] %% q =
      (coeff input.[i] +
       coeff input.[i + 384] *
         (1 - NTRUPlus768NTTStage1Algebra.stage1_root)) %% q.
  + move: Hcoeff.
    rewrite /NTRUPlus768NTTStage1Algebra.stage1_math.
    rewrite /NTRUPlus768NTTStage1Proof.half ifF 1:/#.
    rewrite (_ : i + 384 - 384 = i) 1:/# Hexpr.
    done.
  have Elift :
      lift_word output.[i + 384] =
      lift_int
        (coeff input.[i] +
         coeff input.[i + 384] *
           (1 - NTRUPlus768NTTStage1Algebra.stage1_root)).
  + rewrite /lift_word.
    apply lift_int_eq.
    exact Hmod.
  by rewrite /= Elift.
qed.

lemma stage1_remainder_factor_eqm
    (a : W16.t Array768.t) (root e : int) :
  lift_int root = CycloFq.exp zeta_field e =>
  factor_eqm 384 e (input_poly a) (stage1_remainder_poly a root).
proof.
  move=> Hroot.
  rewrite /factor_eqm.
  exists (-(segment_poly a 384 384)).
  rewrite stage1_remainder_polyE /input_poly /schedule_factor_modulus Hroot.
  ring.
qed.

lemma stage1_low_factor_eqm
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTStage1Algebra.stage1_algebra input output =>
  factor_eqm 384 96 (input_poly input) (segment_poly output 0 384).
proof.
  move=> Halg.
  rewrite (stage1_low_segment_polyE input output Halg).
  exact
    (stage1_remainder_factor_eqm input
      NTRUPlus768NTTStage1Algebra.stage1_root 96
      stage1_root_field_96).
qed.

lemma stage1_high_factor_eqm
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTStage1Algebra.stage1_algebra input output =>
  factor_eqm 384 480 (input_poly input) (segment_poly output 384 384).
proof.
  move=> Halg.
  rewrite (stage1_high_segment_polyE input output Halg).
  exact
    (stage1_remainder_factor_eqm input
      (1 - NTRUPlus768NTTStage1Algebra.stage1_root) 480
      stage1_other_root_field_480).
qed.

op stage1_semantics
    (input output : W16.t Array768.t) : bool =
  factor_eqm 384 96
    (input_poly input) (segment_poly output 0 384) /\
  factor_eqm 384 480
    (input_poly input) (segment_poly output 384 384).

lemma stage1_algebra_implies_semantics
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTStage1Algebra.stage1_algebra input output =>
  stage1_semantics input output.
proof.
  move=> Halg.
  rewrite /stage1_semantics.
  split.
  + exact (stage1_low_factor_eqm input output Halg).
  exact (stage1_high_factor_eqm input output Halg).
qed.

lemma stage1_spec_semantics (input : W16.t Array768.t) :
  NTRUPlus768NTTStage1Algebra.input_qrange input =>
  stage1_semantics input (NTRUPlus768NTTStage1Proof.stage1_spec input).
proof.
  move=> Hinput.
  apply stage1_algebra_implies_semantics.
  exact (stage1_spec_algebra input Hinput).
qed.

lemma ntt_stage1_semantics_functional
    (rp0 ap0 : W16.t Array768.t) :
  NTRUPlus768NTTStage1Algebra.input_qrange ap0 =>
  hoare [NTRUPlus768NTTStage1.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_stage1 :
    rp = rp0 /\ ap = ap0 ==> stage1_semantics ap0 res].
proof.
  move=> Hinput.
  conseq (ntt_stage1_algebra_functional rp0 ap0 Hinput) => />.
  move=> &hr Hap result Halg.
  rewrite Hap in Halg.
  rewrite Hap.
  exact (stage1_algebra_implies_semantics ap0 result Halg).
qed.

lemma ntt_stage1_correct_semantics
    (rp0 ap0 : W16.t Array768.t) :
  NTRUPlus768NTTStage1Algebra.input_qrange ap0 =>
  phoare [NTRUPlus768NTTStage1.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_stage1 :
    rp = rp0 /\ ap = ap0 ==> stage1_semantics ap0 res] = 1%r.
proof.
  move=> Hinput.
  have Hfunctional := ntt_stage1_semantics_functional rp0 ap0 Hinput.
  by conseq ntt_stage1_lossless Hfunctional.
qed.
