require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array768.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768InvNTTProof.
require import NTRUPlus768InvNTTRadix2_4Proof NTRUPlus768InvNTTRadix2_8Proof.
require import NTRUPlus768InvNTTRadix2_16Proof NTRUPlus768InvNTTRadix2_32Proof.
require import NTRUPlus768InvNTTRadix2_64Proof NTRUPlus768InvNTTRadix3Proof.
require import NTRUPlus768InvNTTFinalProof.
require import NTRUPlus768InvNTTRadix2_4Algebra NTRUPlus768InvNTTRadix2_8Algebra.
require import NTRUPlus768InvNTTRadix2_16Algebra NTRUPlus768InvNTTRadix2_32Algebra.
require import NTRUPlus768InvNTTRadix2_64Algebra NTRUPlus768InvNTTRadix3Algebra.
require import NTRUPlus768InvNTTFinalAlgebra.

import Ring.IntID IntOrder.

op inverse_radix2_4_spec (p : W16.t Array768.t) : W16.t Array768.t =
  NTRUPlus768InvNTTRadix2_4Proof.invntt_radix2_4_spec p.

op inverse_radix2_8_spec (p : W16.t Array768.t) : W16.t Array768.t =
  NTRUPlus768InvNTTRadix2_8Proof.invntt_radix2_8_spec
    (inverse_radix2_4_spec p).

op inverse_radix2_16_spec (p : W16.t Array768.t) : W16.t Array768.t =
  NTRUPlus768InvNTTRadix2_16Proof.invntt_radix2_16_spec
    (inverse_radix2_8_spec p).

op inverse_radix2_32_spec (p : W16.t Array768.t) : W16.t Array768.t =
  NTRUPlus768InvNTTRadix2_32Proof.invntt_radix2_32_spec
    (inverse_radix2_16_spec p).

op inverse_radix2_64_spec (p : W16.t Array768.t) : W16.t Array768.t =
  NTRUPlus768InvNTTRadix2_64Proof.invntt_radix2_64_spec
    (inverse_radix2_32_spec p).

op inverse_radix3_spec (p : W16.t Array768.t) : W16.t Array768.t =
  NTRUPlus768InvNTTRadix3Proof.invntt_radix3_spec
    (inverse_radix2_64_spec p).

op inverse_invntt_spec (p : W16.t Array768.t) : W16.t Array768.t =
  NTRUPlus768InvNTTFinalProof.invntt_final_spec (inverse_radix3_spec p).

op inverse_invntt_algebra
    (input output : W16.t Array768.t) : bool =
  NTRUPlus768InvNTTRadix2_4Algebra.qrange_input_shape input /\
  NTRUPlus768InvNTTRadix2_4Algebra.invntt_radix2_4_algebra
    input (inverse_radix2_4_spec input) /\
  NTRUPlus768InvNTTRadix2_8Algebra.invntt_radix2_8_algebra
    (inverse_radix2_4_spec input) (inverse_radix2_8_spec input) /\
  NTRUPlus768InvNTTRadix2_16Algebra.invntt_radix2_16_algebra
    (inverse_radix2_8_spec input) (inverse_radix2_16_spec input) /\
  NTRUPlus768InvNTTRadix2_32Algebra.invntt_radix2_32_algebra
    (inverse_radix2_16_spec input) (inverse_radix2_32_spec input) /\
  NTRUPlus768InvNTTRadix2_64Algebra.invntt_radix2_64_algebra
    (inverse_radix2_32_spec input) (inverse_radix2_64_spec input) /\
  NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_algebra
    (inverse_radix2_64_spec input) (inverse_radix3_spec input) /\
  NTRUPlus768InvNTTFinalAlgebra.invntt_final_algebra
    (inverse_radix3_spec input) output /\
  output = inverse_invntt_spec input.

lemma inverse_radix2_4_spec_algebra (input : W16.t Array768.t) :
  NTRUPlus768InvNTTRadix2_4Algebra.qrange_input_shape input =>
  NTRUPlus768InvNTTRadix2_4Algebra.invntt_radix2_4_algebra
    input (inverse_radix2_4_spec input).
proof.
  move=> Hinput.
  rewrite /inverse_radix2_4_spec.
  exact
    (NTRUPlus768InvNTTRadix2_4Algebra.invntt_radix2_4_spec_algebra
      input Hinput).
qed.

lemma inverse_radix2_8_spec_algebra (input : W16.t Array768.t) :
  NTRUPlus768InvNTTRadix2_4Algebra.qrange_input_shape input =>
  NTRUPlus768InvNTTRadix2_8Algebra.invntt_radix2_8_algebra
    (inverse_radix2_4_spec input) (inverse_radix2_8_spec input).
proof.
  move=> Hinput.
  rewrite /inverse_radix2_8_spec.
  exact
    (NTRUPlus768InvNTTRadix2_8Algebra.invntt_radix2_8_from_invntt_radix2_4_algebra
      input (inverse_radix2_4_spec input)
      (inverse_radix2_4_spec_algebra input Hinput)).
qed.

lemma inverse_radix2_16_spec_algebra (input : W16.t Array768.t) :
  NTRUPlus768InvNTTRadix2_4Algebra.qrange_input_shape input =>
  NTRUPlus768InvNTTRadix2_16Algebra.invntt_radix2_16_algebra
    (inverse_radix2_8_spec input) (inverse_radix2_16_spec input).
proof.
  move=> Hinput.
  rewrite /inverse_radix2_16_spec.
  exact
    (NTRUPlus768InvNTTRadix2_16Algebra.invntt_radix2_16_from_invntt_radix2_8_algebra
      (inverse_radix2_4_spec input) (inverse_radix2_8_spec input)
      (inverse_radix2_8_spec_algebra input Hinput)).
qed.

lemma inverse_radix2_32_spec_algebra (input : W16.t Array768.t) :
  NTRUPlus768InvNTTRadix2_4Algebra.qrange_input_shape input =>
  NTRUPlus768InvNTTRadix2_32Algebra.invntt_radix2_32_algebra
    (inverse_radix2_16_spec input) (inverse_radix2_32_spec input).
proof.
  move=> Hinput.
  rewrite /inverse_radix2_32_spec.
  exact
    (NTRUPlus768InvNTTRadix2_32Algebra.invntt_radix2_32_from_invntt_radix2_16_algebra
      (inverse_radix2_8_spec input) (inverse_radix2_16_spec input)
      (inverse_radix2_16_spec_algebra input Hinput)).
qed.

lemma inverse_radix2_64_spec_algebra (input : W16.t Array768.t) :
  NTRUPlus768InvNTTRadix2_4Algebra.qrange_input_shape input =>
  NTRUPlus768InvNTTRadix2_64Algebra.invntt_radix2_64_algebra
    (inverse_radix2_32_spec input) (inverse_radix2_64_spec input).
proof.
  move=> Hinput.
  rewrite /inverse_radix2_64_spec.
  exact
    (NTRUPlus768InvNTTRadix2_64Algebra.invntt_radix2_64_from_invntt_radix2_32_algebra
      (inverse_radix2_16_spec input) (inverse_radix2_32_spec input)
      (inverse_radix2_32_spec_algebra input Hinput)).
qed.

lemma inverse_radix3_spec_algebra (input : W16.t Array768.t) :
  NTRUPlus768InvNTTRadix2_4Algebra.qrange_input_shape input =>
  NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_algebra
    (inverse_radix2_64_spec input) (inverse_radix3_spec input).
proof.
  move=> Hinput.
  rewrite /inverse_radix3_spec.
  exact
    (NTRUPlus768InvNTTRadix3Algebra.invntt_radix3_from_invntt_radix2_64_algebra
      (inverse_radix2_32_spec input) (inverse_radix2_64_spec input)
      (inverse_radix2_64_spec_algebra input Hinput)).
qed.

lemma inverse_final_spec_algebra (input : W16.t Array768.t) :
  NTRUPlus768InvNTTRadix2_4Algebra.qrange_input_shape input =>
  NTRUPlus768InvNTTFinalAlgebra.invntt_final_algebra
    (inverse_radix3_spec input) (inverse_invntt_spec input).
proof.
  move=> Hinput.
  rewrite /inverse_invntt_spec.
  exact
    (NTRUPlus768InvNTTFinalAlgebra.invntt_final_from_invntt_radix3_algebra
      (inverse_radix2_64_spec input) (inverse_radix3_spec input)
      (inverse_radix3_spec_algebra input Hinput)).
qed.

lemma inverse_invntt_spec_algebra (input : W16.t Array768.t) :
  NTRUPlus768InvNTTRadix2_4Algebra.qrange_input_shape input =>
  inverse_invntt_algebra input (inverse_invntt_spec input).
proof.
  move=> Hinput.
  rewrite /inverse_invntt_algebra.
  split; first exact Hinput.
  split; first exact (inverse_radix2_4_spec_algebra input Hinput).
  split; first exact (inverse_radix2_8_spec_algebra input Hinput).
  split; first exact (inverse_radix2_16_spec_algebra input Hinput).
  split; first exact (inverse_radix2_32_spec_algebra input Hinput).
  split; first exact (inverse_radix2_64_spec_algebra input Hinput).
  split; first exact (inverse_radix3_spec_algebra input Hinput).
  split; first exact (inverse_final_spec_algebra input Hinput).
  done.
qed.

lemma inverse_invntt_output_qrange
    (input : W16.t Array768.t) (j : int) :
  NTRUPlus768InvNTTRadix2_4Algebra.qrange_input_shape input =>
  0 <= j < 768 =>
  -q <= coeff (inverse_invntt_spec input).[j] < q.
proof.
  move=> Hinput Hj.
  have Hjalg := inverse_final_spec_algebra input Hinput j Hj.
  by move: Hjalg => [Hrange _].
qed.

lemma invntt_specE (p : W16.t Array768.t) :
  NTRUPlus768InvNTTProof.invntt_spec p = inverse_invntt_spec p.
proof.
  rewrite /NTRUPlus768InvNTTProof.invntt_spec.
  rewrite /inverse_invntt_spec /inverse_radix3_spec /inverse_radix2_64_spec.
  rewrite /inverse_radix2_32_spec /inverse_radix2_16_spec.
  rewrite /inverse_radix2_8_spec /inverse_radix2_4_spec.
  done.
qed.

lemma invntt_algebra_functional
    (rp0 ap0 : W16.t Array768.t) :
  NTRUPlus768InvNTTRadix2_4Algebra.qrange_input_shape ap0 =>
  hoare [NTRUPlus768InvNTT.M.jade_ntruplus_ntruplus768_amd64_ref_invntt :
    rp = rp0 /\ ap = ap0 ==> inverse_invntt_algebra ap0 res].
proof.
  move=> Hinput.
  conseq (NTRUPlus768InvNTTProof.invntt_functional rp0 ap0) => /> &hr Hap.
  rewrite Hap invntt_specE.
  have Halg := inverse_invntt_spec_algebra ap0 Hinput.
  rewrite /inverse_invntt_algebra in Halg.
  move: Halg => [_ Halg].
  exact Halg.
qed.

lemma invntt_correct_algebra
    (rp0 ap0 : W16.t Array768.t) :
  NTRUPlus768InvNTTRadix2_4Algebra.qrange_input_shape ap0 =>
  phoare [NTRUPlus768InvNTT.M.jade_ntruplus_ntruplus768_amd64_ref_invntt :
    rp = rp0 /\ ap = ap0 ==> inverse_invntt_algebra ap0 res] = 1%r.
proof.
  move=> Hinput.
  have Hfunctional := invntt_algebra_functional rp0 ap0 Hinput.
  by conseq NTRUPlus768InvNTTProof.invntt_lossless Hfunctional.
qed.
