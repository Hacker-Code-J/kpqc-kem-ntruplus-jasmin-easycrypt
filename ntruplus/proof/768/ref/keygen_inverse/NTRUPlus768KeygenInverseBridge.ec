require import AllCore.
from Jasmin require import JWord.

require import Array4 Array192 Array768.
require import NTRUPlus768NTTRadix2_4Algebra.
require import NTRUPlus768KeygenSamplerBridge.
require import NTRUPlus768PolyBasemulAlgebra.
require import NTRUPlus768PolyBasemulProof.
require import NTRUPlus768PolyBaseInvBridge.
require import NTRUPlus768PolyBaseInvProof.

(* Scope: this theory only composes the verified keygen sampler/NTT value flow
   with the verified exact poly_baseinv core contract.  It proves finv/ginv
   provenance when the core returns zero and fail-closed zeroization when it
   returns one.  It does not claim production-C semantics, retry termination or
   success probability, h = g * finv, hinv = f * ginv, serialization, CT/SCT,
   or full-KEM correctness. *)

lemma keygen_f_ntt_qrange (buf : W8.t Array192.t) :
  in_qrange768 (keygen_f_ntt_spec buf).
proof.
  rewrite /in_qrange768 /in_qrange4 /in_qrange.
  move=> k Hk.
  have Hshape := keygen_f_ntt_centered_output buf.
  split.
  + rewrite /block4 Array4.initiE 1:/#.
    have H0 : 0 <= 4 * k < 768 by smt().
    exact
      (NTRUPlus768NTTRadix2_4Algebra.centered_input_shape_qrange
        (keygen_f_ntt_spec buf) (4 * k) Hshape H0).
  split.
  + rewrite /block4 Array4.initiE 1:/#.
    have H1 : 0 <= 4 * k + 1 < 768 by smt().
    exact
      (NTRUPlus768NTTRadix2_4Algebra.centered_input_shape_qrange
        (keygen_f_ntt_spec buf) (4 * k + 1) Hshape H1).
  split.
  + rewrite /block4 Array4.initiE 1:/#.
    have H2 : 0 <= 4 * k + 2 < 768 by smt().
    exact
      (NTRUPlus768NTTRadix2_4Algebra.centered_input_shape_qrange
        (keygen_f_ntt_spec buf) (4 * k + 2) Hshape H2).
  rewrite /block4 Array4.initiE 1:/#.
  have H3 : 0 <= 4 * k + 3 < 768 by smt().
  exact
    (NTRUPlus768NTTRadix2_4Algebra.centered_input_shape_qrange
      (keygen_f_ntt_spec buf) (4 * k + 3) Hshape H3).
qed.

lemma keygen_g_ntt_qrange (buf : W8.t Array192.t) :
  in_qrange768 (keygen_g_ntt_spec buf).
proof.
  rewrite /in_qrange768 /in_qrange4 /in_qrange.
  move=> k Hk.
  have Hshape := keygen_g_ntt_centered_output buf.
  split.
  + rewrite /block4 Array4.initiE 1:/#.
    have H0 : 0 <= 4 * k < 768 by smt().
    exact
      (NTRUPlus768NTTRadix2_4Algebra.centered_input_shape_qrange
        (keygen_g_ntt_spec buf) (4 * k) Hshape H0).
  split.
  + rewrite /block4 Array4.initiE 1:/#.
    have H1 : 0 <= 4 * k + 1 < 768 by smt().
    exact
      (NTRUPlus768NTTRadix2_4Algebra.centered_input_shape_qrange
        (keygen_g_ntt_spec buf) (4 * k + 1) Hshape H1).
  split.
  + rewrite /block4 Array4.initiE 1:/#.
    have H2 : 0 <= 4 * k + 2 < 768 by smt().
    exact
      (NTRUPlus768NTTRadix2_4Algebra.centered_input_shape_qrange
        (keygen_g_ntt_spec buf) (4 * k + 2) Hshape H2).
  rewrite /block4 Array4.initiE 1:/#.
  have H3 : 0 <= 4 * k + 3 < 768 by smt().
  exact
    (NTRUPlus768NTTRadix2_4Algebra.centered_input_shape_qrange
      (keygen_g_ntt_spec buf) (4 * k + 3) Hshape H3).
qed.

lemma keygen_f_inverse_success_bridge
    (buf : W8.t Array192.t) (rp0 : W16.t Array768.t) :
  hoare [NTRUPlus768PolyBaseInv.M.__poly_baseinv_core :
    rp = rp0 /\ ap = keygen_f_ntt_spec buf ==>
    res.`2 = W64.of_int 0 =>
    poly_baseinv_success (keygen_f_ntt_spec buf) res.`1].
proof.
  exact
    (poly_baseinv_success_bridge rp0 (keygen_f_ntt_spec buf)
      (keygen_f_ntt_qrange buf)).
qed.

lemma keygen_g_inverse_success_bridge
    (buf : W8.t Array192.t) (rp0 : W16.t Array768.t) :
  hoare [NTRUPlus768PolyBaseInv.M.__poly_baseinv_core :
    rp = rp0 /\ ap = keygen_g_ntt_spec buf ==>
    res.`2 = W64.of_int 0 =>
    poly_baseinv_success (keygen_g_ntt_spec buf) res.`1].
proof.
  exact
    (poly_baseinv_success_bridge rp0 (keygen_g_ntt_spec buf)
      (keygen_g_ntt_qrange buf)).
qed.

lemma keygen_f_inverse_qrange_on_success
    (buf : W8.t Array192.t) (rp0 : W16.t Array768.t) :
  hoare [NTRUPlus768PolyBaseInv.M.__poly_baseinv_core :
    rp = rp0 /\ ap = keygen_f_ntt_spec buf ==>
    res.`2 = W64.of_int 0 =>
    in_qrange768 res.`1].
proof.
  exact
    (poly_baseinv_output_qrange_on_success rp0 (keygen_f_ntt_spec buf)
      (keygen_f_ntt_qrange buf)).
qed.

lemma keygen_g_inverse_qrange_on_success
    (buf : W8.t Array192.t) (rp0 : W16.t Array768.t) :
  hoare [NTRUPlus768PolyBaseInv.M.__poly_baseinv_core :
    rp = rp0 /\ ap = keygen_g_ntt_spec buf ==>
    res.`2 = W64.of_int 0 =>
    in_qrange768 res.`1].
proof.
  exact
    (poly_baseinv_output_qrange_on_success rp0 (keygen_g_ntt_spec buf)
      (keygen_g_ntt_qrange buf)).
qed.

lemma keygen_f_inverse_product_identity_on_success
    (buf : W8.t Array192.t) (rp0 : W16.t Array768.t) :
  hoare [NTRUPlus768PolyBaseInv.M.__poly_baseinv_core :
    rp = rp0 /\ ap = keygen_f_ntt_spec buf ==>
    res.`2 = W64.of_int 0 =>
    poly_basemul_qring
      (keygen_f_ntt_spec buf) res.`1 ntt_block_identity 192].
proof.
  exact
    (poly_baseinv_product_identity_on_success rp0 (keygen_f_ntt_spec buf)
      (keygen_f_ntt_qrange buf)).
qed.

lemma keygen_g_inverse_product_identity_on_success
    (buf : W8.t Array192.t) (rp0 : W16.t Array768.t) :
  hoare [NTRUPlus768PolyBaseInv.M.__poly_baseinv_core :
    rp = rp0 /\ ap = keygen_g_ntt_spec buf ==>
    res.`2 = W64.of_int 0 =>
    poly_basemul_qring
      (keygen_g_ntt_spec buf) res.`1 ntt_block_identity 192].
proof.
  exact
    (poly_baseinv_product_identity_on_success rp0 (keygen_g_ntt_spec buf)
      (keygen_g_ntt_qrange buf)).
qed.

lemma keygen_f_inverse_zero_on_failure
    (buf : W8.t Array192.t) (rp0 : W16.t Array768.t) :
  hoare [NTRUPlus768PolyBaseInv.M.__poly_baseinv_core :
    rp = rp0 /\ ap = keygen_f_ntt_spec buf ==>
    res.`2 = W64.of_int 1 =>
    poly_has_failed (keygen_f_ntt_spec buf) 192 /\ res.`1 = poly_zero].
proof.
  conseq (poly_baseinv_functional rp0 (keygen_f_ntt_spec buf)) => />.
  move=> &hr _ result Hpost Hfail.
  move: Hpost => [[Hzero _] | [Hone [Hfailed Hzero_poly]]].
  + smt(poly_baseinv_w64_zero_neq_one).
  split; [exact Hfailed | exact Hzero_poly].
qed.

lemma keygen_g_inverse_zero_on_failure
    (buf : W8.t Array192.t) (rp0 : W16.t Array768.t) :
  hoare [NTRUPlus768PolyBaseInv.M.__poly_baseinv_core :
    rp = rp0 /\ ap = keygen_g_ntt_spec buf ==>
    res.`2 = W64.of_int 1 =>
    poly_has_failed (keygen_g_ntt_spec buf) 192 /\ res.`1 = poly_zero].
proof.
  conseq (poly_baseinv_functional rp0 (keygen_g_ntt_spec buf)) => />.
  move=> &hr _ result Hpost Hfail.
  move: Hpost => [[Hzero _] | [Hone [Hfailed Hzero_poly]]].
  + smt(poly_baseinv_w64_zero_neq_one).
  split; [exact Hfailed | exact Hzero_poly].
qed.
