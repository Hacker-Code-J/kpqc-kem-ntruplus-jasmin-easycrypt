require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array768.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768NTTStage1Algebra.
require import NTRUPlus768Crepmod3Algebra.
require import NTRUPlus768PolySub.
require import NTRUPlus768PolySubProof.
require import W16extra.

import Ring.IntID IntOrder.

op decoder_range (p : W16.t Array768.t) : bool =
  forall j, 0 <= j < 768 => 0 <= coeff p.[j] < 4096.

op poly_sub_algebra
    (input_a input_b output : W16.t Array768.t) : bool =
  forall j, 0 <= j < 768 =>
    coeff output.[j] = coeff input_a.[j] - coeff input_b.[j] /\
    -3456 <= coeff output.[j] <= 7552 /\
    coeff output.[j] %% q =
      (coeff input_a.[j] - coeff input_b.[j]) %% q.

lemma word_from_coeff (w : W16.t) :
  w = W16.of_int (coeff w).
proof.
  exact (NTRUPlus768Crepmod3Algebra.word_from_coeff w).
qed.

lemma coeff_of_word_small (x : int) :
  W16.min_sint <= x <= W16.max_sint =>
  coeff (W16.of_int x) = x.
proof.
  exact NTRUPlus768Crepmod3Algebra.coeff_of_word_small.
qed.

lemma decoder_range_coeff
    (p : W16.t Array768.t) (j : int) :
  decoder_range p =>
  0 <= j < 768 =>
  0 <= coeff p.[j] < 4096.
proof.
  move=> Hp Hj.
  exact (Hp j Hj).
qed.

lemma poly_sub_word_range
    (a b : W16.t) :
  0 <= coeff a < 4096 =>
  -q <= coeff b < q =>
  -3456 <= coeff a - coeff b <= 7552.
proof.
  move=> Ha Hb.
  rewrite /q /= in Hb.
  smt().
qed.

lemma poly_sub_word_coeffE
    (a b : W16.t) :
  0 <= coeff a < 4096 =>
  -q <= coeff b < q =>
  coeff (a - b) = coeff a - coeff b.
proof.
  move=> Ha Hb.
  rewrite /coeff.
  apply to_sintB_small.
  move: Ha Hb; rewrite /q /=.
  smt().
qed.

lemma poly_sub_wordE
    (a b : W16.t) :
  0 <= coeff a < 4096 =>
  -q <= coeff b < q =>
  a - b = W16.of_int (coeff a - coeff b).
proof.
  move=> Ha Hb.
  rewrite (word_from_coeff (a - b)).
  by rewrite poly_sub_word_coeffE.
qed.

lemma poly_sub_word_mod_q
    (a b : W16.t) :
  0 <= coeff a < 4096 =>
  -q <= coeff b < q =>
  coeff (a - b) %% q = (coeff a - coeff b) %% q.
proof.
  move=> Ha Hb.
  by rewrite poly_sub_word_coeffE.
qed.

lemma poly_sub_spec_algebra
    (input_a input_b : W16.t Array768.t) :
  decoder_range input_a =>
  NTRUPlus768NTTStage1Algebra.input_qrange input_b =>
  poly_sub_algebra input_a input_b
    (NTRUPlus768PolySubProof.poly_sub_spec input_a input_b).
proof.
  move=> Ha Hb j Hj.
  have Haj := decoder_range_coeff input_a j Ha Hj.
  have Hbj : -q <= coeff input_b.[j] < q by exact (Hb j Hj).
  have Hcoeff :=
    poly_sub_word_coeffE input_a.[j] input_b.[j] Haj Hbj.
  rewrite /NTRUPlus768PolySubProof.poly_sub_spec Array768.initiE 1:/#.
  split.
  + exact Hcoeff.
  split.
  + rewrite Hcoeff.
    exact (poly_sub_word_range input_a.[j] input_b.[j] Haj Hbj).
  exact (poly_sub_word_mod_q input_a.[j] input_b.[j] Haj Hbj).
qed.

lemma poly_sub_spec_decoder_forward_range
    (input_a input_b : W16.t Array768.t) (j : int) :
  decoder_range input_a =>
  NTRUPlus768NTTStage1Algebra.input_qrange input_b =>
  0 <= j < 768 =>
  -3456 <=
    coeff (NTRUPlus768PolySubProof.poly_sub_spec input_a input_b).[j] <=
    7552.
proof.
  move=> Ha Hb Hj.
  have Halg := poly_sub_spec_algebra input_a input_b Ha Hb j Hj.
  by move: Halg => [_ [Hrange _]].
qed.

lemma poly_sub_spec_decoder_forward_modq
    (input_a input_b : W16.t Array768.t) (j : int) :
  decoder_range input_a =>
  NTRUPlus768NTTStage1Algebra.input_qrange input_b =>
  0 <= j < 768 =>
  coeff (NTRUPlus768PolySubProof.poly_sub_spec input_a input_b).[j] %% q =
    (coeff input_a.[j] - coeff input_b.[j]) %% q.
proof.
  move=> Ha Hb Hj.
  have Halg := poly_sub_spec_algebra input_a input_b Ha Hb j Hj.
  by move: Halg => [_ [_ Hmodq]].
qed.

lemma poly_sub_functional_algebra
    (rp0 ap0 bp0 : W16.t Array768.t) :
  decoder_range ap0 =>
  NTRUPlus768NTTStage1Algebra.input_qrange bp0 =>
  hoare [NTRUPlus768PolySub.M.jade_ntruplus_ntruplus768_amd64_ref_poly_sub :
    rp = rp0 /\ ap = ap0 /\ bp = bp0 ==>
    poly_sub_algebra ap0 bp0 res].
proof.
  move=> Ha Hb.
  have Hspec := poly_sub_spec_algebra ap0 bp0 Ha Hb.
  conseq (NTRUPlus768PolySubProof.poly_sub_functional rp0 ap0 bp0).
  auto.
qed.

lemma poly_sub_correct_algebra
    (rp0 ap0 bp0 : W16.t Array768.t) :
  decoder_range ap0 =>
  NTRUPlus768NTTStage1Algebra.input_qrange bp0 =>
  phoare [NTRUPlus768PolySub.M.jade_ntruplus_ntruplus768_amd64_ref_poly_sub :
    rp = rp0 /\ ap = ap0 /\ bp = bp0 ==>
    poly_sub_algebra ap0 bp0 res] = 1%r.
proof.
  move=> Ha Hb.
  have Hfunctional := poly_sub_functional_algebra rp0 ap0 bp0 Ha Hb.
  by conseq NTRUPlus768PolySubProof.poly_sub_lossless Hfunctional.
qed.
