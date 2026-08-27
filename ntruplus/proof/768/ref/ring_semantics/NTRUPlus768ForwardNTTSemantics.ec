require import AllCore.
from Jasmin require import JWord.

require import Array768.
require import NTRUPlus768NTTAlgebra.
require import NTRUPlus768TerminalRepresentation.
require import NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768ForwardNTTRadix3Semantics.
require import NTRUPlus768ForwardNTTRadix2_64Semantics.
require import NTRUPlus768ForwardNTTRadix2_32Semantics.
require import NTRUPlus768ForwardNTTRadix2_16Semantics.
require import NTRUPlus768ForwardNTTRadix2_8Semantics.
require import NTRUPlus768ForwardNTTRadix2_4Semantics.

lemma forward_ntt_algebra_terminal_represents
    (original output : W16.t Array768.t) :
  NTRUPlus768NTTAlgebra.forward_ntt_algebra original output =>
  terminal_represents output (input_poly original).
proof.
  rewrite /NTRUPlus768NTTAlgebra.forward_ntt_algebra.
  move=> [_ [Hstage1 [Hradix3 [Hradix2_64 [Hradix2_32
           [Hradix2_16 [Hradix2_8 [Hradix2_4 _]]]]]]]].

  have Hstage1_sem :=
    NTRUPlus768ForwardNTTStage1Semantics.stage1_algebra_implies_semantics
      original
      (NTRUPlus768NTTAlgebra.forward_stage1_spec original)
      Hstage1.
  have Hradix3_sem :=
    NTRUPlus768ForwardNTTRadix3Semantics.radix3_algebra_refines_stage1_semantics
      original
      (NTRUPlus768NTTAlgebra.forward_stage1_spec original)
      (NTRUPlus768NTTAlgebra.forward_radix3_spec original)
      Hstage1_sem Hradix3.
  have Hradix2_64_sem :=
    NTRUPlus768ForwardNTTRadix2_64Semantics.radix2_64_algebra_refines_radix3_semantics
      original
      (NTRUPlus768NTTAlgebra.forward_radix3_spec original)
      (NTRUPlus768NTTAlgebra.forward_radix2_64_spec original)
      Hradix3_sem Hradix2_64.
  have Hradix2_32_sem :=
    NTRUPlus768ForwardNTTRadix2_32Semantics.radix2_32_algebra_refines_radix2_64_semantics
      original
      (NTRUPlus768NTTAlgebra.forward_radix2_64_spec original)
      (NTRUPlus768NTTAlgebra.forward_radix2_32_spec original)
      Hradix2_64_sem Hradix2_32.
  have Hradix2_16_sem :=
    NTRUPlus768ForwardNTTRadix2_16Semantics.radix2_16_algebra_refines_radix2_32_semantics
      original
      (NTRUPlus768NTTAlgebra.forward_radix2_32_spec original)
      (NTRUPlus768NTTAlgebra.forward_radix2_16_spec original)
      Hradix2_32_sem Hradix2_16.
  have Hradix2_8_sem :=
    NTRUPlus768ForwardNTTRadix2_8Semantics.radix2_8_algebra_refines_radix2_16_semantics
      original
      (NTRUPlus768NTTAlgebra.forward_radix2_16_spec original)
      (NTRUPlus768NTTAlgebra.forward_radix2_8_spec original)
      Hradix2_16_sem Hradix2_8.

  exact
    (NTRUPlus768ForwardNTTRadix2_4Semantics.radix2_4_algebra_refines_terminal_representation
      original
      (NTRUPlus768NTTAlgebra.forward_radix2_8_spec original)
      output Hradix2_8_sem Hradix2_4).
qed.

lemma forward_ntt_spec_terminal_represents
    (input : W16.t Array768.t) :
  NTRUPlus768NTTStage1Algebra.input_qrange input =>
  terminal_represents
    (NTRUPlus768NTTAlgebra.forward_ntt_spec input)
    (input_poly input).
proof.
  move=> Hinput.
  apply
    (forward_ntt_algebra_terminal_represents
      input (NTRUPlus768NTTAlgebra.forward_ntt_spec input)).
  exact (NTRUPlus768NTTAlgebra.forward_ntt_spec_algebra input Hinput).
qed.

lemma ntt_terminal_represents_functional
    (rp0 ap0 : W16.t Array768.t) :
  NTRUPlus768NTTStage1Algebra.input_qrange ap0 =>
  hoare [NTRUPlus768NTT.M.jade_ntruplus_ntruplus768_amd64_ref_ntt :
    rp = rp0 /\ ap = ap0 ==>
    terminal_represents res (input_poly ap0)].
proof.
  move=> Hinput.
  conseq (NTRUPlus768NTTProof.ntt_functional rp0 ap0) => /> &hr Hap.
  rewrite Hap NTRUPlus768NTTAlgebra.ntt_specE.
  exact (forward_ntt_spec_terminal_represents ap0 Hinput).
qed.

lemma ntt_correct_terminal_represents
    (rp0 ap0 : W16.t Array768.t) :
  NTRUPlus768NTTStage1Algebra.input_qrange ap0 =>
  phoare [NTRUPlus768NTT.M.jade_ntruplus_ntruplus768_amd64_ref_ntt :
    rp = rp0 /\ ap = ap0 ==>
    terminal_represents res (input_poly ap0)] = 1%r.
proof.
  move=> Hinput.
  have Hfunctional :
      hoare [NTRUPlus768NTT.M.jade_ntruplus_ntruplus768_amd64_ref_ntt :
        rp = rp0 /\ ap = ap0 ==>
        terminal_represents res (input_poly ap0)].
  + exact (ntt_terminal_represents_functional rp0 ap0 Hinput).
  by conseq NTRUPlus768NTTProof.ntt_lossless Hfunctional.
qed.
