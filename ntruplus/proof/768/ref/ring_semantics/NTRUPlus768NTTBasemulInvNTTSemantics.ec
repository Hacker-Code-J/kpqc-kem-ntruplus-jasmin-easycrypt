(* Forward NTT, basemul, then inverse NTT yields the product polynomial. *)
require import AllCore.
from Jasmin require import JWord.

require import Array4 Array768.
require import NTRUPlus768EvaluationSemantics.
require import NTRUPlus768TerminalRepresentation.
require import NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768ForwardNTTSemantics.
require import NTRUPlus768NTTAlgebra.
require import NTRUPlus768NTTStage1Algebra.
require import NTRUPlus768PolyBasemulProof.
require import NTRUPlus768PolyBasemulAlgebra.
require import NTRUPlus768PolyBasemulInvNTTAlgebra.
require import NTRUPlus768InvNTTAlgebra.
require import NTRUPlus768InverseNTTSemantics.

op ntt_basemul_invntt_semantics
    (a b output : W16.t Array768.t) : bool =
  eqm_global (input_poly a * input_poly b) (input_poly output).

lemma forward_ntt_spec_poly_basemul_input_shape
    (input : W16.t Array768.t) :
  NTRUPlus768NTTStage1Algebra.input_qrange input =>
  NTRUPlus768PolyBasemulAlgebra.in_qrange768
    (NTRUPlus768NTTAlgebra.forward_ntt_spec input).
proof.
  move=> Hinput.
  rewrite /NTRUPlus768PolyBasemulAlgebra.in_qrange768
          /in_qrange4 /in_qrange.
  move=> k Hk.
  split.
  + rewrite /block4 Array4.initiE 1:/#.
    have H0 : 0 <= 4 * k < 768 by smt().
    exact
      (NTRUPlus768NTTAlgebra.forward_ntt_centered_coeff_range
        input (4 * k) Hinput H0).
  split.
  + rewrite /block4 Array4.initiE 1:/#.
    have H1 : 0 <= 4 * k + 1 < 768 by smt().
    exact
      (NTRUPlus768NTTAlgebra.forward_ntt_centered_coeff_range
        input (4 * k + 1) Hinput H1).
  split.
  + rewrite /block4 Array4.initiE 1:/#.
    have H2 : 0 <= 4 * k + 2 < 768 by smt().
    exact
      (NTRUPlus768NTTAlgebra.forward_ntt_centered_coeff_range
        input (4 * k + 2) Hinput H2).
  rewrite /block4 Array4.initiE 1:/#.
  have H3 : 0 <= 4 * k + 3 < 768 by smt().
  exact
    (NTRUPlus768NTTAlgebra.forward_ntt_centered_coeff_range
      input (4 * k + 3) Hinput H3).
qed.

lemma terminal_product_inverse_spec_semantics
    (ap bp rp : W16.t Array768.t) (p q : poly) :
  terminal_represents ap p =>
  terminal_represents bp q =>
  NTRUPlus768PolyBasemulAlgebra.poly_basemul_qring ap bp rp 192 =>
  NTRUPlus768InverseNTTSemantics.invntt_semantics
    (p * q)
    (NTRUPlus768InvNTTAlgebra.inverse_invntt_spec rp).
proof.
  move=> Hap Hbp Hqring.
  apply
    (NTRUPlus768InverseNTTSemantics.inverse_invntt_spec_semantics
      (p * q) rp).
  + exact
      (poly_basemul_qring_represents_product ap bp rp p q
        Hap Hbp Hqring).
  have Hready :=
    NTRUPlus768PolyBasemulInvNTTAlgebra.poly_basemul_qring_implies_invntt_ready
      ap bp rp Hqring.
  by move: Hready => [_ Hshape].
qed.

lemma ntt_basemul_invntt_spec_product
    (a b product_ntt : W16.t Array768.t) :
  NTRUPlus768NTTStage1Algebra.input_qrange a =>
  NTRUPlus768NTTStage1Algebra.input_qrange b =>
  is_poly_basemul
    (NTRUPlus768NTTAlgebra.forward_ntt_spec a)
    (NTRUPlus768NTTAlgebra.forward_ntt_spec b)
    product_ntt 192 =>
  ntt_basemul_invntt_semantics a b
    (NTRUPlus768InvNTTAlgebra.inverse_invntt_spec product_ntt).
proof.
  move=> Ha Hb Hword.
  rewrite /ntt_basemul_invntt_semantics.
  have Ha_term :=
    NTRUPlus768ForwardNTTSemantics.forward_ntt_spec_terminal_represents a Ha.
  have Hb_term :=
    NTRUPlus768ForwardNTTSemantics.forward_ntt_spec_terminal_represents b Hb.
  have Ha_shape := forward_ntt_spec_poly_basemul_input_shape a Ha.
  have Hb_shape := forward_ntt_spec_poly_basemul_input_shape b Hb.
  have Hqring :=
    NTRUPlus768PolyBasemulAlgebra.poly_basemul_word_to_qring
      (NTRUPlus768NTTAlgebra.forward_ntt_spec a)
      (NTRUPlus768NTTAlgebra.forward_ntt_spec b)
      product_ntt
      Ha_shape Hb_shape Hword.
  exact
    (terminal_product_inverse_spec_semantics
      (NTRUPlus768NTTAlgebra.forward_ntt_spec a)
      (NTRUPlus768NTTAlgebra.forward_ntt_spec b)
      product_ntt
      (input_poly a) (input_poly b)
      Ha_term Hb_term Hqring).
qed.
