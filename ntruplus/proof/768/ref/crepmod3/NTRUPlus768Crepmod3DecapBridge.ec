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
require import NTRUPlus768InvNTTAlgebra.
require import NTRUPlus768NTTStage1Algebra.
require import NTRUPlus768Crepmod3Proof.
require import NTRUPlus768Crepmod3Algebra.

import Ring.IntID IntOrder.

op inverse_invntt_crepmod3_spec
    (input : W16.t Array768.t) : W16.t Array768.t =
  NTRUPlus768Crepmod3Proof.poly_crepmod3_spec
    (NTRUPlus768InvNTTAlgebra.inverse_invntt_spec input).

op decap_m1_crepmod3_value_flow
    (basemul_output crepmod3_output : W16.t Array768.t) : bool =
  NTRUPlus768InvNTTAlgebra.inverse_invntt_algebra basemul_output
    (NTRUPlus768InvNTTAlgebra.inverse_invntt_spec basemul_output) /\
  NTRUPlus768Crepmod3Algebra.poly_crepmod3_algebra
    (NTRUPlus768InvNTTAlgebra.inverse_invntt_spec basemul_output)
    crepmod3_output /\
  NTRUPlus768NTTStage1Algebra.input_qrange crepmod3_output.

lemma inverse_invntt_spec_ntt_input_qrange
    (input : W16.t Array768.t) :
  NTRUPlus768InvNTTRadix2_4Algebra.qrange_input_shape input =>
  NTRUPlus768NTTStage1Algebra.input_qrange
    (NTRUPlus768InvNTTAlgebra.inverse_invntt_spec input).
proof.
  move=> Hinput j Hj.
  exact
    (NTRUPlus768InvNTTAlgebra.inverse_invntt_output_qrange
      input j Hinput Hj).
qed.

lemma inverse_invntt_spec_crepmod3_algebra
    (input : W16.t Array768.t) :
  NTRUPlus768InvNTTRadix2_4Algebra.qrange_input_shape input =>
  NTRUPlus768Crepmod3Algebra.poly_crepmod3_algebra
    (NTRUPlus768InvNTTAlgebra.inverse_invntt_spec input)
    (inverse_invntt_crepmod3_spec input).
proof.
  move=> Hinput.
  rewrite /inverse_invntt_crepmod3_spec.
  apply NTRUPlus768Crepmod3Algebra.poly_crepmod3_spec_algebra.
  exact (inverse_invntt_spec_ntt_input_qrange input Hinput).
qed.

lemma inverse_invntt_spec_crepmod3_input_qrange
    (input : W16.t Array768.t) :
  NTRUPlus768InvNTTRadix2_4Algebra.qrange_input_shape input =>
  NTRUPlus768NTTStage1Algebra.input_qrange
    (inverse_invntt_crepmod3_spec input).
proof.
  move=> Hinput.
  rewrite /inverse_invntt_crepmod3_spec.
  apply NTRUPlus768Crepmod3Algebra.poly_crepmod3_spec_input_qrange.
  exact (inverse_invntt_spec_ntt_input_qrange input Hinput).
qed.

lemma poly_basemul_qring_decap_m1_crepmod3_value_flow
    (ap bp rp : W16.t Array768.t) :
  poly_basemul_qring ap bp rp 192 =>
  decap_m1_crepmod3_value_flow rp (inverse_invntt_crepmod3_spec rp).
proof.
  move=> Hqring.
  have Hready :=
    poly_basemul_qring_implies_invntt_ready ap bp rp Hqring.
  move: Hready => [_ Hshape].
  rewrite /decap_m1_crepmod3_value_flow.
  split.
  + exact
      (NTRUPlus768InvNTTAlgebra.inverse_invntt_spec_algebra rp Hshape).
  split.
  + exact (inverse_invntt_spec_crepmod3_algebra rp Hshape).
  exact (inverse_invntt_spec_crepmod3_input_qrange rp Hshape).
qed.

(* This terminal theorem composes array values. It does not model the
   concrete C caller's pointer identity, shared storage, or partial overlap. *)
lemma poly_frombytes_two_decoder_specs_decap_m1_crepmod3_value_flow
    (a b : W8.t Array1152.t) (rp0 : W16.t Array768.t) :
  phoare [NTRUPlus768PolyBasemul.M.jade_ntruplus_ntruplus768_amd64_ref_poly_basemul :
    rp = rp0 /\
    ap = NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec a /\
    bp = NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec b ==>
    decap_m1_crepmod3_value_flow res
      (inverse_invntt_crepmod3_spec res)] = 1%r.
proof.
  have Ha : in_s12range768
      (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec a)
    by exact
      (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec_in_s12range768 a).
  have Hb : in_s12range768
      (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec b)
    by exact
      (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec_in_s12range768 b).
  conseq NTRUPlus768PolyBasemulProof.poly_basemul_lossless
    (NTRUPlus768PolyBasemulProof.poly_basemul_functional rp0
      (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec a)
      (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec b)).
  move=> &hr _ result; split.
  + move=> [_ Hword].
    split.
    + trivial.
    exact Hword.
  move=> [_ Hword]; split.
  + have Hqring :=
      NTRUPlus768PolyBasemulAlgebra.poly_basemul_word_to_qring_s12
        (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec a)
        (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec b)
        result Ha Hb Hword.
    exact
      (poly_basemul_qring_decap_m1_crepmod3_value_flow
        (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec a)
        (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec b)
        result Hqring).
  exact Hword.
qed.
