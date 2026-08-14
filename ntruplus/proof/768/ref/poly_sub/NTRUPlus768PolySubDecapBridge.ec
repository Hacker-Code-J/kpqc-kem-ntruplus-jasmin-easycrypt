require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array768 Array1152.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768PolyBasemul.
require import NTRUPlus768PolyBasemulProof.
require import NTRUPlus768PolyBasemulAlgebra.
require import NTRUPlus768PolyBasemulInvNTTAlgebra.
require import NTRUPlus768PolyFromBytesAlgebra.
require import NTRUPlus768InvNTTRadix2_4Algebra.
require import NTRUPlus768NTTAlgebra.
require import NTRUPlus768NTTStage1Algebra.
require import NTRUPlus768Crepmod3DecapBridge.
require import NTRUPlus768PolySubProof.
require import NTRUPlus768PolySubAlgebra.

import Ring.IntID IntOrder.

op decap_m1_poly_sub_value_flow
    (ciphertext basemul_output poly_sub_output : W16.t Array768.t) : bool =
  NTRUPlus768Crepmod3DecapBridge.decap_m1_crepmod3_value_flow
    basemul_output
    (NTRUPlus768Crepmod3DecapBridge.inverse_invntt_crepmod3_spec basemul_output) /\
  NTRUPlus768NTTAlgebra.forward_ntt_algebra
    (NTRUPlus768Crepmod3DecapBridge.inverse_invntt_crepmod3_spec basemul_output)
    (NTRUPlus768NTTAlgebra.forward_ntt_spec
      (NTRUPlus768Crepmod3DecapBridge.inverse_invntt_crepmod3_spec
        basemul_output)) /\
  NTRUPlus768PolySubAlgebra.poly_sub_algebra
    ciphertext
    (NTRUPlus768NTTAlgebra.forward_ntt_spec
      (NTRUPlus768Crepmod3DecapBridge.inverse_invntt_crepmod3_spec
        basemul_output))
    poly_sub_output /\
  poly_sub_output =
    NTRUPlus768PolySubProof.poly_sub_spec ciphertext
      (NTRUPlus768NTTAlgebra.forward_ntt_spec
        (NTRUPlus768Crepmod3DecapBridge.inverse_invntt_crepmod3_spec
          basemul_output)).

lemma poly_frombytes_spec_decoder_range
    (a : W8.t Array1152.t) :
  NTRUPlus768PolySubAlgebra.decoder_range
    (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec a).
proof.
  move=> j Hj.
  have Huint :=
    NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec_coeff_range a j Hj.
  have Hcoeff :
      coeff (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec a).[j] =
      W16.to_uint (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec a).[j].
  + apply NTRUPlus768PolyFromBytesAlgebra.coeff_uint_small.
    move: Huint; smt().
  by rewrite Hcoeff.
qed.

lemma inverse_invntt_crepmod3_spec_forward_ntt_algebra
    (input : W16.t Array768.t) :
  NTRUPlus768InvNTTRadix2_4Algebra.qrange_input_shape input =>
  NTRUPlus768NTTAlgebra.forward_ntt_algebra
    (NTRUPlus768Crepmod3DecapBridge.inverse_invntt_crepmod3_spec input)
    (NTRUPlus768NTTAlgebra.forward_ntt_spec
      (NTRUPlus768Crepmod3DecapBridge.inverse_invntt_crepmod3_spec input)).
proof.
  move=> Hinput.
  apply NTRUPlus768NTTAlgebra.forward_ntt_spec_algebra.
  exact
    (NTRUPlus768Crepmod3DecapBridge.inverse_invntt_spec_crepmod3_input_qrange
      input Hinput).
qed.

lemma inverse_invntt_crepmod3_spec_forward_ntt_qrange
    (input : W16.t Array768.t) :
  NTRUPlus768InvNTTRadix2_4Algebra.qrange_input_shape input =>
  NTRUPlus768NTTStage1Algebra.input_qrange
    (NTRUPlus768NTTAlgebra.forward_ntt_spec
      (NTRUPlus768Crepmod3DecapBridge.inverse_invntt_crepmod3_spec input)).
proof.
  move=> Hinput j Hj.
  exact
    (NTRUPlus768NTTAlgebra.forward_ntt_centered_coeff_range
      (NTRUPlus768Crepmod3DecapBridge.inverse_invntt_crepmod3_spec input) j
      (NTRUPlus768Crepmod3DecapBridge.inverse_invntt_spec_crepmod3_input_qrange
        input Hinput) Hj).
qed.

lemma poly_basemul_qring_decap_m1_poly_sub_value_flow
    (ciphertext ap bp rp : W16.t Array768.t) :
  NTRUPlus768PolySubAlgebra.decoder_range ciphertext =>
  poly_basemul_qring ap bp rp 192 =>
  decap_m1_poly_sub_value_flow ciphertext rp
    (NTRUPlus768PolySubProof.poly_sub_spec ciphertext
      (NTRUPlus768NTTAlgebra.forward_ntt_spec
        (NTRUPlus768Crepmod3DecapBridge.inverse_invntt_crepmod3_spec rp))).
proof.
  move=> Hcipher Hqring.
  have Hready :=
    poly_basemul_qring_implies_invntt_ready ap bp rp Hqring.
  move: Hready => [_ Hshape].
  rewrite /decap_m1_poly_sub_value_flow.
  split.
  + exact
      (NTRUPlus768Crepmod3DecapBridge.poly_basemul_qring_decap_m1_crepmod3_value_flow
        ap bp rp Hqring).
  split.
  + exact (inverse_invntt_crepmod3_spec_forward_ntt_algebra rp Hshape).
  split.
  + apply NTRUPlus768PolySubAlgebra.poly_sub_spec_algebra.
    - exact Hcipher.
    exact (inverse_invntt_crepmod3_spec_forward_ntt_qrange rp Hshape).
  done.
qed.

(* This terminal theorem composes decoder, inverse_invntt, crepmod3, forward_ntt,
   and poly_sub at the array-value level. It does not claim concrete caller
   pointers, shared-memory aliasing, C-AST equivalence, or full-KEM security. *)
lemma poly_frombytes_two_decoder_specs_decap_ciphertext_sub_value_flow
    (f ciphertext : W8.t Array1152.t) (rp0 : W16.t Array768.t) :
  phoare [NTRUPlus768PolyBasemul.M.jade_ntruplus_ntruplus768_amd64_ref_poly_basemul :
    rp = rp0 /\
    ap = NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec ciphertext /\
    bp = NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec f ==>
    decap_m1_poly_sub_value_flow
      (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec ciphertext)
      res
      (NTRUPlus768PolySubProof.poly_sub_spec
        (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec ciphertext)
        (NTRUPlus768NTTAlgebra.forward_ntt_spec
          (NTRUPlus768Crepmod3DecapBridge.inverse_invntt_crepmod3_spec res)))] = 1%r.
proof.
  have Hf : in_s12range768
      (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec f)
    by exact
      (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec_in_s12range768 f).
  have Hcipher_dec :
      NTRUPlus768PolySubAlgebra.decoder_range
      (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec ciphertext)
    by exact (poly_frombytes_spec_decoder_range ciphertext).
  have Hcipher_s12 : in_s12range768
      (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec ciphertext)
    by exact
      (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec_in_s12range768
        ciphertext).
  conseq NTRUPlus768PolyBasemulProof.poly_basemul_lossless
    (NTRUPlus768PolyBasemulProof.poly_basemul_functional rp0
      (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec ciphertext)
      (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec f)).
  move=> &hr _ result; split.
  + move=> [_ Hword].
    split.
    + trivial.
    exact Hword.
  move=> [_ Hword]; split.
  + have Hqring :=
      NTRUPlus768PolyBasemulAlgebra.poly_basemul_word_to_qring_s12
        (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec ciphertext)
        (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec f)
        result Hcipher_s12 Hf Hword.
    exact
      (poly_basemul_qring_decap_m1_poly_sub_value_flow
        (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec ciphertext)
        (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec ciphertext)
        (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec f)
        result Hcipher_dec Hqring).
  exact Hword.
qed.
