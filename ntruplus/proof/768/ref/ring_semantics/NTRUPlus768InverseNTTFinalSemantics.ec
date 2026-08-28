(* Global polynomial semantics for inverse-NTT finalization. *)
require import AllCore IntDiv List Ring StdBigop StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array768.
require import NTRUPlus768CyclotomicFactorization.
require import NTRUPlus768EvaluationSemantics.
require import NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768TerminalRepresentation.
require import NTRUPlus768InvNTTFinal.
require import NTRUPlus768InvNTTFinalAlgebra NTRUPlus768InvNTTFinalProof.
require import NTRUPlus768InverseNTTRadix3Semantics.
require import NTRUPlus768InverseNTTFinalRecombination.
require import NTRUPlus768InverseNTTFinalInterpolation.

op invntt_final_semantics
    (p : NTRUPoly.poly) (output : W16.t Array768.t) : bool =
  eqm_global p (input_poly output).

lemma invntt_final_algebra_refines_invntt_radix3_semantics
    (p : NTRUPoly.poly) (input output : W16.t Array768.t) :
  invntt_radix3_semantics p input =>
  NTRUPlus768InvNTTFinalAlgebra.invntt_final_algebra input output =>
  invntt_final_semantics p output.
proof.
  move=> [Hlow Hhigh] Halg.
  rewrite /invntt_final_semantics
          (invntt_final_input_polyE input output Halg).
  apply invntt_final_recombine_eqm_global.
  + exact Hlow.
  + exact Hhigh.
qed.

lemma invntt_final_spec_semantics
    (p : NTRUPoly.poly) (input : W16.t Array768.t) :
  invntt_radix3_semantics p input =>
  NTRUPlus768InvNTTFinalAlgebra.invntt_final_input_shape input =>
  invntt_final_semantics p
    (NTRUPlus768InvNTTFinalProof.invntt_final_spec input).
proof.
  move=> Hsem Hshape.
  apply (invntt_final_algebra_refines_invntt_radix3_semantics
    p input (NTRUPlus768InvNTTFinalProof.invntt_final_spec input)).
  + exact Hsem.
  + exact (NTRUPlus768InvNTTFinalAlgebra.invntt_final_spec_algebra
      input Hshape).
qed.

lemma invntt_final_semantics_functional
    (p : NTRUPoly.poly) (rp0 : W16.t Array768.t) :
  invntt_radix3_semantics p rp0 =>
  NTRUPlus768InvNTTFinalAlgebra.invntt_final_input_shape rp0 =>
  hoare [NTRUPlus768InvNTTFinal.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_final :
    rp = rp0 ==> invntt_final_semantics p res].
proof.
  move=> Hsem Hshape.
  conseq
    (NTRUPlus768InvNTTFinalAlgebra.invntt_final_algebra_functional
      rp0 Hshape) => />.
  move=> result Halg.
  apply (invntt_final_algebra_refines_invntt_radix3_semantics
    p rp0 result).
  + exact Hsem.
  + exact Halg.
qed.

lemma invntt_final_correct_semantics
    (p : NTRUPoly.poly) (rp0 : W16.t Array768.t) :
  invntt_radix3_semantics p rp0 =>
  NTRUPlus768InvNTTFinalAlgebra.invntt_final_input_shape rp0 =>
  phoare [NTRUPlus768InvNTTFinal.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_final :
    rp = rp0 ==> invntt_final_semantics p res] = 1%r.
proof.
  move=> Hsem Hshape.
  have Hfunctional :
      hoare [NTRUPlus768InvNTTFinal.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_final :
        rp = rp0 ==> invntt_final_semantics p res].
  + apply invntt_final_semantics_functional.
    - exact Hsem.
    - exact Hshape.
  by conseq NTRUPlus768InvNTTFinalProof.invntt_final_lossless Hfunctional.
qed.
