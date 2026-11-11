require import AllCore.
from Jasmin require import JWord.
require import Array768 NTTComposition.
require import NTRUPlus768CyclotomicFactorization NTRUPlus768BasemulAlgebra.
require import NTRUPlus768EvaluationSemantics NTRUPlus768TerminalRepresentation.
require import NTRUPlus768ForwardNTTStage1Semantics NTRUPlus768ForwardNTTSemantics.
require import NTRUPlus768InverseNTTSemantics NTRUPlus768NTTBasemulInvNTTSemantics.
require import NTRUPlus768NTTAlgebra NTRUPlus768NTTProof NTRUPlus768NTTStage1Algebra.
require import NTRUPlus768PolyBasemulProof NTRUPlus768PolyBasemulAlgebra NTRUPlus768PolyBasemulInvNTTAlgebra.
require import NTRUPlus768InvNTTAlgebra NTRUPlus768InvNTTProof NTRUPlus768InvNTTRadix2_4Algebra.

type buffer = W16.t Array768.t.
op coefficient_input (x:buffer) (p:NTRUPoly.poly) = input_poly x=p.
op coefficient_output (x:buffer) (p:NTRUPoly.poly) = eqm_global p (input_poly x).
op coefficient_output_bound (x:buffer) =
  forall j, 0<=j<768 => -NTRUPlus768BasemulAlgebra.q <= coeff x.[j] < NTRUPlus768BasemulAlgebra.q.

clone NTTComposition as Common with
  type polynomial <- NTRUPoly.poly,
  type coefficient_buffer <- buffer,
  type transform_buffer <- buffer,
  op polynomial_product <- NTRUPoly.PolyComRing.( * ),
  op input_rep <- coefficient_input,
  op forward_rep <- terminal_represents,
  op product_rep <- terminal_represents,
  op output_rep <- coefficient_output,
  op input_bound <- NTRUPlus768NTTStage1Algebra.input_qrange,
  op forward_bound <- NTRUPlus768PolyBasemulAlgebra.in_qrange768,
  op inverse_bound <- NTRUPlus768InvNTTRadix2_4Algebra.qrange_input_shape,
  op output_bound <- coefficient_output_bound.

(* These adapters call the extracted kernels. The witness is an arbitrary
   initial output buffer; every imported kernel theorem quantifies over it. *)
module Kernels = {
  proc forward(x:buffer) : buffer = {
    var r:buffer;
    r <@ NTRUPlus768NTT.M.jade_ntruplus_ntruplus768_amd64_ref_ntt(witness,x);
    return r;
  }
  proc multiply(x:buffer,y:buffer) : buffer = {
    var r:buffer;
    r <@ NTRUPlus768PolyBasemul.M.jade_ntruplus_ntruplus768_amd64_ref_poly_basemul(witness,x,y);
    return r;
  }
  proc inverse(x:buffer) : buffer = {
    var r:buffer;
    r <@ NTRUPlus768InvNTT.M.jade_ntruplus_ntruplus768_amd64_ref_invntt(witness,x);
    return r;
  }
}.

lemma forward_ll : islossless Kernels.forward.
proof. proc; call NTRUPlus768NTTProof.ntt_lossless; auto. qed.
lemma multiply_ll : islossless Kernels.multiply.
proof. proc; call NTRUPlus768PolyBasemulProof.poly_basemul_lossless; auto. qed.
lemma inverse_ll : islossless Kernels.inverse.
proof. proc; call NTRUPlus768InvNTTProof.invntt_lossless; auto. qed.

lemma forward_functional p :
  hoare[Kernels.forward : coefficient_input x p /\ NTRUPlus768NTTStage1Algebra.input_qrange x ==>
    terminal_represents res p /\ NTRUPlus768PolyBasemulAlgebra.in_qrange768 res].
proof.
proc.
ecall (NTRUPlus768NTTProof.ntt_functional witness x).
skip.
move=> &hr [hp hb].
split; first trivial.
move=> _ result hresult.
rewrite hresult NTRUPlus768NTTAlgebra.ntt_specE.
split.
+ move: hp; rewrite /coefficient_input => <-.
  exact (NTRUPlus768ForwardNTTSemantics.forward_ntt_spec_terminal_represents x{hr} hb).
exact (NTRUPlus768NTTBasemulInvNTTSemantics.forward_ntt_spec_poly_basemul_input_shape x{hr} hb).
qed.

lemma forward_total p :
  phoare[Kernels.forward : coefficient_input x p /\ NTRUPlus768NTTStage1Algebra.input_qrange x ==>
    terminal_represents res p /\ NTRUPlus768PolyBasemulAlgebra.in_qrange768 res] = 1%r.
proof. by conseq forward_ll (forward_functional p). qed.

lemma multiply_functional p q :
  hoare[Kernels.multiply : terminal_represents x p /\ NTRUPlus768PolyBasemulAlgebra.in_qrange768 x /\
    terminal_represents y q /\ NTRUPlus768PolyBasemulAlgebra.in_qrange768 y ==>
    terminal_represents res (p*q) /\ NTRUPlus768InvNTTRadix2_4Algebra.qrange_input_shape res].
proof.
proc.
ecall (NTRUPlus768PolyBasemulProof.poly_basemul_functional witness x y).
skip.
move=> &hr [hxp [hxb [hyp hyb]]].
split; first trivial.
move=> _ result hw.
have hring := NTRUPlus768PolyBasemulAlgebra.poly_basemul_word_to_qring x{hr} y{hr} result hxb hyb hw.
have hready := NTRUPlus768PolyBasemulInvNTTAlgebra.poly_basemul_qring_implies_invntt_ready x{hr} y{hr} result hring.
split.
+ exact (NTRUPlus768TerminalRepresentation.poly_basemul_qring_represents_product x{hr} y{hr} result p q hxp hyp hring).
by move: hready => [_ hshape].
qed.

lemma multiply_total p q :
  phoare[Kernels.multiply : terminal_represents x p /\ NTRUPlus768PolyBasemulAlgebra.in_qrange768 x /\
    terminal_represents y q /\ NTRUPlus768PolyBasemulAlgebra.in_qrange768 y ==>
    terminal_represents res (p*q) /\ NTRUPlus768InvNTTRadix2_4Algebra.qrange_input_shape res] = 1%r.
proof. by conseq multiply_ll (multiply_functional p q). qed.

lemma inverse_functional p :
  hoare[Kernels.inverse : terminal_represents x p /\ NTRUPlus768InvNTTRadix2_4Algebra.qrange_input_shape x ==>
    coefficient_output res p /\ coefficient_output_bound res].
proof.
proc.
ecall (NTRUPlus768InvNTTProof.invntt_functional witness x).
skip.
move=> &hr [hp hb].
split; first trivial.
move=> _ result hresult.
rewrite hresult NTRUPlus768InvNTTAlgebra.invntt_specE.
split.
+ exact (NTRUPlus768InverseNTTSemantics.inverse_invntt_spec_semantics p x{hr} hp hb).
rewrite /coefficient_output_bound => j hj.
exact (NTRUPlus768InvNTTAlgebra.inverse_invntt_output_qrange x{hr} j hb hj).
qed.

lemma inverse_total p :
  phoare[Kernels.inverse : terminal_represents x p /\ NTRUPlus768InvNTTRadix2_4Algebra.qrange_input_shape x ==>
    coefficient_output res p /\ coefficient_output_bound res] = 1%r.
proof. by conseq inverse_ll (inverse_functional p). qed.

lemma ntruplus768_ntt_product_total (p q:NTRUPoly.poly) :
  phoare[Common.Product(Kernels).run :
    coefficient_input x p /\ NTRUPlus768NTTStage1Algebra.input_qrange x /\
    coefficient_input y q /\ NTRUPlus768NTTStage1Algebra.input_qrange y ==>
    coefficient_output res (p*q) /\ coefficient_output_bound res] = 1%r.
proof.
apply (Common.composition_total Kernels p q).
+ exact forward_total.
+ exact multiply_total.
+ exact inverse_total.
qed.
