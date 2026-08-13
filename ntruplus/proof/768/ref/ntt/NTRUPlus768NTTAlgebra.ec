require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array768.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768NTTProof.
require import NTRUPlus768NTTStage1Proof NTRUPlus768NTTRadix3Proof.
require import NTRUPlus768NTTRadix2_64Proof NTRUPlus768NTTRadix2_32Proof.
require import NTRUPlus768NTTRadix2_16Proof NTRUPlus768NTTRadix2_8Proof.
require import NTRUPlus768NTTRadix2_4Proof.
require import NTRUPlus768NTTStage1Algebra NTRUPlus768NTTRadix3Algebra.
require import NTRUPlus768NTTRadix2_64Algebra NTRUPlus768NTTRadix2_32Algebra.
require import NTRUPlus768NTTRadix2_16Algebra NTRUPlus768NTTRadix2_8Algebra.
require import NTRUPlus768NTTRadix2_4Algebra.

import Ring.IntID IntOrder.

op forward_stage1_spec (p : W16.t Array768.t) : W16.t Array768.t =
  NTRUPlus768NTTStage1Proof.stage1_spec p.

op forward_radix3_spec (p : W16.t Array768.t) : W16.t Array768.t =
  NTRUPlus768NTTRadix3Proof.radix3_spec (forward_stage1_spec p).

op forward_radix2_64_spec (p : W16.t Array768.t) : W16.t Array768.t =
  NTRUPlus768NTTRadix2_64Proof.radix2_64_spec (forward_radix3_spec p).

op forward_radix2_32_spec (p : W16.t Array768.t) : W16.t Array768.t =
  NTRUPlus768NTTRadix2_32Proof.radix2_32_spec (forward_radix2_64_spec p).

op forward_radix2_16_spec (p : W16.t Array768.t) : W16.t Array768.t =
  NTRUPlus768NTTRadix2_16Algebra.radix2_16_spec (forward_radix2_32_spec p).

op forward_radix2_8_spec (p : W16.t Array768.t) : W16.t Array768.t =
  NTRUPlus768NTTRadix2_8Algebra.radix2_8_spec (forward_radix2_16_spec p).

op forward_ntt_spec (p : W16.t Array768.t) : W16.t Array768.t =
  NTRUPlus768NTTRadix2_4Algebra.radix2_4_spec (forward_radix2_8_spec p).

op forward_ntt_algebra
    (input output : W16.t Array768.t) : bool =
  NTRUPlus768NTTStage1Algebra.input_qrange input /\
  NTRUPlus768NTTStage1Algebra.stage1_algebra input (forward_stage1_spec input) /\
  NTRUPlus768NTTRadix3Algebra.radix3_algebra
    (forward_stage1_spec input) (forward_radix3_spec input) /\
  NTRUPlus768NTTRadix2_64Algebra.radix2_64_algebra
    (forward_radix3_spec input) (forward_radix2_64_spec input) /\
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_algebra
    (forward_radix2_64_spec input) (forward_radix2_32_spec input) /\
  NTRUPlus768NTTRadix2_16Algebra.radix2_16_algebra
    (forward_radix2_32_spec input) (forward_radix2_16_spec input) /\
  NTRUPlus768NTTRadix2_8Algebra.radix2_8_algebra
    (forward_radix2_16_spec input) (forward_radix2_8_spec input) /\
  NTRUPlus768NTTRadix2_4Algebra.radix2_4_algebra
    (forward_radix2_8_spec input) output /\
  output = forward_ntt_spec input.

lemma stage1_algebra_stage1_output_shape
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTStage1Algebra.stage1_algebra input output =>
  NTRUPlus768NTTRadix3Algebra.stage1_output_shape output.
proof.
  move=> Halg j Hj.
  have Hjalg := Halg j Hj.
  rewrite /NTRUPlus768NTTRadix3Algebra.stage1_output_shape.
  by move: Hjalg => [Hrange _]; smt().
qed.

lemma radix3_algebra_radix3_output_shape
    (input output : W16.t Array768.t) :
  NTRUPlus768NTTRadix3Algebra.radix3_algebra input output =>
  NTRUPlus768NTTRadix2_64Algebra.radix3_output_shape output.
proof.
  move=> Halg j Hj.
  have Hjalg := Halg j Hj.
  rewrite /NTRUPlus768NTTRadix2_64Algebra.radix3_output_shape.
  by move: Hjalg => [Hrange _]; smt().
qed.

lemma forward_stage1_spec_algebra (input : W16.t Array768.t) :
  NTRUPlus768NTTStage1Algebra.input_qrange input =>
  NTRUPlus768NTTStage1Algebra.stage1_algebra input (forward_stage1_spec input).
proof.
  move=> Hinput.
  rewrite /forward_stage1_spec.
  exact (NTRUPlus768NTTStage1Algebra.stage1_spec_algebra input Hinput).
qed.

lemma forward_radix3_spec_algebra (input : W16.t Array768.t) :
  NTRUPlus768NTTStage1Algebra.input_qrange input =>
  NTRUPlus768NTTRadix3Algebra.radix3_algebra
    (forward_stage1_spec input) (forward_radix3_spec input).
proof.
  move=> Hinput.
  rewrite /forward_radix3_spec.
  apply NTRUPlus768NTTRadix3Algebra.radix3_spec_algebra.
  exact
    (stage1_algebra_stage1_output_shape
      input (forward_stage1_spec input)
      (forward_stage1_spec_algebra input Hinput)).
qed.

lemma forward_radix2_64_spec_algebra (input : W16.t Array768.t) :
  NTRUPlus768NTTStage1Algebra.input_qrange input =>
  NTRUPlus768NTTRadix2_64Algebra.radix2_64_algebra
    (forward_radix3_spec input) (forward_radix2_64_spec input).
proof.
  move=> Hinput.
  rewrite /forward_radix2_64_spec.
  apply NTRUPlus768NTTRadix2_64Algebra.radix2_64_spec_algebra.
  exact
    (radix3_algebra_radix3_output_shape
      (forward_stage1_spec input) (forward_radix3_spec input)
      (forward_radix3_spec_algebra input Hinput)).
qed.

lemma forward_radix2_32_spec_algebra (input : W16.t Array768.t) :
  NTRUPlus768NTTStage1Algebra.input_qrange input =>
  NTRUPlus768NTTRadix2_32Algebra.radix2_32_algebra
    (forward_radix2_64_spec input) (forward_radix2_32_spec input).
proof.
  move=> Hinput.
  rewrite /forward_radix2_32_spec.
  apply NTRUPlus768NTTRadix2_32Algebra.radix2_32_spec_algebra.
  exact
    (NTRUPlus768NTTRadix2_32Algebra.radix2_64_algebra_output_shape
      (forward_radix3_spec input) (forward_radix2_64_spec input)
      (forward_radix2_64_spec_algebra input Hinput)).
qed.

lemma forward_radix2_16_spec_algebra (input : W16.t Array768.t) :
  NTRUPlus768NTTStage1Algebra.input_qrange input =>
  NTRUPlus768NTTRadix2_16Algebra.radix2_16_algebra
    (forward_radix2_32_spec input) (forward_radix2_16_spec input).
proof.
  move=> Hinput.
  rewrite /forward_radix2_16_spec.
  exact
    (NTRUPlus768NTTRadix2_16Algebra.radix2_16_from_radix2_32_algebra
      (forward_radix2_64_spec input) (forward_radix2_32_spec input)
      (forward_radix2_32_spec_algebra input Hinput)).
qed.

lemma forward_radix2_8_spec_algebra (input : W16.t Array768.t) :
  NTRUPlus768NTTStage1Algebra.input_qrange input =>
  NTRUPlus768NTTRadix2_8Algebra.radix2_8_algebra
    (forward_radix2_16_spec input) (forward_radix2_8_spec input).
proof.
  move=> Hinput.
  rewrite /forward_radix2_8_spec.
  exact
    (NTRUPlus768NTTRadix2_8Algebra.radix2_8_from_radix2_16_algebra
      (forward_radix2_32_spec input) (forward_radix2_16_spec input)
      (forward_radix2_16_spec_algebra input Hinput)).
qed.

lemma forward_radix2_4_spec_algebra (input : W16.t Array768.t) :
  NTRUPlus768NTTStage1Algebra.input_qrange input =>
  NTRUPlus768NTTRadix2_4Algebra.radix2_4_algebra
    (forward_radix2_8_spec input) (forward_ntt_spec input).
proof.
  move=> Hinput.
  rewrite /forward_ntt_spec.
  exact
    (NTRUPlus768NTTRadix2_4Algebra.radix2_4_from_radix2_8_algebra
      (forward_radix2_16_spec input) (forward_radix2_8_spec input)
      (forward_radix2_8_spec_algebra input Hinput)).
qed.

lemma forward_ntt_spec_algebra (input : W16.t Array768.t) :
  NTRUPlus768NTTStage1Algebra.input_qrange input =>
  forward_ntt_algebra input (forward_ntt_spec input).
proof.
  move=> Hinput.
  rewrite /forward_ntt_algebra.
  split; first exact Hinput.
  split; first exact (forward_stage1_spec_algebra input Hinput).
  split; first exact (forward_radix3_spec_algebra input Hinput).
  split; first exact (forward_radix2_64_spec_algebra input Hinput).
  split; first exact (forward_radix2_32_spec_algebra input Hinput).
  split; first exact (forward_radix2_16_spec_algebra input Hinput).
  split; first exact (forward_radix2_8_spec_algebra input Hinput).
  split; first exact (forward_radix2_4_spec_algebra input Hinput).
  done.
qed.

lemma forward_ntt_centered_output_shape (input : W16.t Array768.t) :
  NTRUPlus768NTTStage1Algebra.input_qrange input =>
  NTRUPlus768NTTRadix2_4Algebra.centered_input_shape (forward_ntt_spec input).
proof.
  move=> Hinput.
  rewrite /NTRUPlus768NTTRadix2_4Algebra.centered_input_shape.
  move=> j Hj.
  have Hjalg :=
    forward_radix2_4_spec_algebra input Hinput j Hj.
  move: Hjalg => [Hrange _].
  rewrite /q /= in Hrange.
  smt().
qed.

lemma forward_ntt_centered_coeff_range
    (input : W16.t Array768.t) (j : int) :
  NTRUPlus768NTTStage1Algebra.input_qrange input =>
  0 <= j < 768 =>
  -q <= coeff (forward_ntt_spec input).[j] < q.
proof.
  move=> Hinput Hj.
  have Hjshape := forward_ntt_centered_output_shape input Hinput j Hj.
  rewrite /q /= in Hjshape.
  smt().
qed.

lemma ntt_specE (p : W16.t Array768.t) :
  NTRUPlus768NTTProof.ntt_spec p = forward_ntt_spec p.
proof.
  rewrite /NTRUPlus768NTTProof.ntt_spec.
  rewrite /forward_ntt_spec /forward_radix2_8_spec /forward_radix2_16_spec.
  rewrite /forward_radix2_32_spec /forward_radix2_64_spec.
  rewrite /forward_radix3_spec /forward_stage1_spec.
  rewrite NTRUPlus768NTTRadix2_16Algebra.radix2_16_word_specE.
  rewrite NTRUPlus768NTTRadix2_8Algebra.radix2_8_word_specE.
  rewrite NTRUPlus768NTTRadix2_4Algebra.radix2_4_word_specE.
  done.
qed.

lemma ntt_algebra_functional
    (rp0 ap0 : W16.t Array768.t) :
  NTRUPlus768NTTStage1Algebra.input_qrange ap0 =>
  hoare [NTRUPlus768NTT.M.jade_ntruplus_ntruplus768_amd64_ref_ntt :
    rp = rp0 /\ ap = ap0 ==> forward_ntt_algebra ap0 res].
proof.
  move=> Hinput.
  conseq (NTRUPlus768NTTProof.ntt_functional rp0 ap0) => /> &hr Hap.
  rewrite Hap ntt_specE.
  have Halg := forward_ntt_spec_algebra ap0 Hinput.
  rewrite /forward_ntt_algebra in Halg.
  move: Halg => [_ Halg].
  exact Halg.
qed.

lemma ntt_correct_algebra
    (rp0 ap0 : W16.t Array768.t) :
  NTRUPlus768NTTStage1Algebra.input_qrange ap0 =>
  phoare [NTRUPlus768NTT.M.jade_ntruplus_ntruplus768_amd64_ref_ntt :
    rp = rp0 /\ ap = ap0 ==> forward_ntt_algebra ap0 res] = 1%r.
proof.
  move=> Hinput.
  have Hfunctional := ntt_algebra_functional rp0 ap0 Hinput.
  by conseq NTRUPlus768NTTProof.ntt_lossless Hfunctional.
qed.
