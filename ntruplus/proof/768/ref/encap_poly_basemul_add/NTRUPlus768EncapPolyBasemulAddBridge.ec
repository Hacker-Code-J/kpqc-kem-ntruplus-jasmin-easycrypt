require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array96 Array192 Array768 Array1152.
require import NTRUPlus768PolyCBD1Algebra.
require import NTRUPlus768PolySOTPEncodeAlgebra.
require import NTRUPlus768PolyBasemulAlgebra.
require import NTRUPlus768NTTAlgebra.
require import NTRUPlus768PolyFromBytesAlgebra.
require import NTRUPlus768EncapPolyBasemulAddAlgebra.

import Ring.IntID IntOrder.

(* Encapsulation-side typed value flow only.  Key-generation inverse
   provenance, valid-key m1 recovery, r2 recovery, and KEM agreement remain
   separate obligations. *)

op encap_encoded_m_spec
    (msg : W8.t Array96.t)
    (pad : W8.t Array192.t) : W16.t Array768.t =
  NTRUPlus768PolySOTPEncodeAlgebra.poly_sotp_encode_spec msg pad.

op encap_m_ntt_spec
    (msg : W8.t Array96.t)
    (pad : W8.t Array192.t) : W16.t Array768.t =
  NTRUPlus768NTTAlgebra.forward_ntt_spec (encap_encoded_m_spec msg pad).

op encap_ciphertext_spec
    (product : W16.t Array768.t)
    (msg : W8.t Array96.t)
    (pad : W8.t Array192.t) : W16.t Array768.t =
  poly_centered_add_spec product (encap_m_ntt_spec msg pad).

op encap_poly_basemul_add_value_flow
    (pk : W8.t Array1152.t)
    (msg : W8.t Array96.t)
    (pad : W8.t Array192.t)
    (h r_ntt encoded_m m_ntt product ciphertext : W16.t Array768.t) : bool =
  h = NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec pk /\
  encoded_m = encap_encoded_m_spec msg pad /\
  m_ntt = NTRUPlus768NTTAlgebra.forward_ntt_spec encoded_m /\
  NTRUPlus768NTTAlgebra.forward_ntt_algebra encoded_m m_ntt /\
  poly_basemul_qring h r_ntt product 192 /\
  poly_basemul_add_qring h r_ntt m_ntt ciphertext 192.

lemma encap_encoded_m_trit_output
    (msg : W8.t Array96.t)
    (pad : W8.t Array192.t) :
  NTRUPlus768PolyCBD1Algebra.poly_cbd1_trit_output
    (encap_encoded_m_spec msg pad).
proof.
  rewrite /encap_encoded_m_spec /NTRUPlus768PolySOTPEncodeAlgebra.poly_sotp_encode_spec.
  exact
    (NTRUPlus768PolyCBD1Algebra.poly_cbd1_spec_trit_output
      (NTRUPlus768PolySOTPEncodeAlgebra.poly_sotp_encode_input msg pad)).
qed.

lemma encap_encoded_m_input_qrange
    (msg : W8.t Array96.t)
    (pad : W8.t Array192.t) :
  NTRUPlus768NTTStage1Algebra.input_qrange
    (encap_encoded_m_spec msg pad).
proof.
  rewrite /encap_encoded_m_spec /NTRUPlus768PolySOTPEncodeAlgebra.poly_sotp_encode_spec.
  exact
    (NTRUPlus768PolyCBD1Algebra.poly_cbd1_spec_input_qrange
      (NTRUPlus768PolySOTPEncodeAlgebra.poly_sotp_encode_input msg pad)).
qed.

lemma encap_m_ntt_algebra
    (msg : W8.t Array96.t)
    (pad : W8.t Array192.t) :
  NTRUPlus768NTTAlgebra.forward_ntt_algebra
    (encap_encoded_m_spec msg pad)
    (encap_m_ntt_spec msg pad).
proof.
  exact
    (NTRUPlus768NTTAlgebra.forward_ntt_spec_algebra
      (encap_encoded_m_spec msg pad)
      (encap_encoded_m_input_qrange msg pad)).
qed.

lemma encap_m_ntt_centered_output
    (msg : W8.t Array96.t)
    (pad : W8.t Array192.t) :
  NTRUPlus768NTTRadix2_4Algebra.centered_input_shape
    (encap_m_ntt_spec msg pad).
proof.
  exact
    (NTRUPlus768NTTAlgebra.forward_ntt_centered_output_shape
      (encap_encoded_m_spec msg pad)
      (encap_encoded_m_input_qrange msg pad)).
qed.

lemma encap_ciphertext_spec_qring
    (ap bp product : W16.t Array768.t)
    (msg : W8.t Array96.t)
    (pad : W8.t Array192.t) :
  poly_basemul_qring ap bp product 192 =>
  poly_basemul_add_qring ap bp (encap_m_ntt_spec msg pad)
    (encap_ciphertext_spec product msg pad) 192.
proof.
  move=> Hprod.
  rewrite /encap_ciphertext_spec /encap_m_ntt_spec.
  exact
    (poly_basemul_add_spec_qring ap bp product
      (NTRUPlus768NTTAlgebra.forward_ntt_spec
        (encap_encoded_m_spec msg pad))
      Hprod
      (encap_m_ntt_centered_output msg pad)).
qed.

lemma encap_poly_basemul_add_value_flow_intro
    (pk : W8.t Array1152.t)
    (msg : W8.t Array96.t)
    (pad : W8.t Array192.t)
    (r_ntt product : W16.t Array768.t) :
  poly_basemul_qring
    (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec pk)
    r_ntt product 192 =>
  encap_poly_basemul_add_value_flow
    pk msg pad
    (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec pk)
    r_ntt
    (encap_encoded_m_spec msg pad)
    (encap_m_ntt_spec msg pad)
    product
    (encap_ciphertext_spec product msg pad).
proof.
  move=> Hprod.
  rewrite /encap_poly_basemul_add_value_flow.
  split; first done.
  split; first done.
  split; first done.
  split.
  + exact (encap_m_ntt_algebra msg pad).
  split; first exact Hprod.
  exact (encap_ciphertext_spec_qring
    (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec pk)
    r_ntt product msg pad Hprod).
qed.

lemma encap_poly_basemul_add_value_flow_outcome
    (pk : W8.t Array1152.t)
    (msg : W8.t Array96.t)
    (pad : W8.t Array192.t)
    (h r_ntt encoded_m m_ntt product ciphertext : W16.t Array768.t) :
  encap_poly_basemul_add_value_flow
    pk msg pad h r_ntt encoded_m m_ntt product ciphertext =>
  h = NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec pk /\
  encoded_m = encap_encoded_m_spec msg pad /\
  m_ntt = NTRUPlus768NTTAlgebra.forward_ntt_spec encoded_m /\
  NTRUPlus768NTTAlgebra.forward_ntt_algebra encoded_m m_ntt /\
  poly_basemul_qring h r_ntt product 192 /\
  poly_basemul_add_qring h r_ntt m_ntt ciphertext 192.
proof. by rewrite /encap_poly_basemul_add_value_flow. qed.

lemma encap_ciphertext_spec_in_qrange768
    (product : W16.t Array768.t)
    (msg : W8.t Array96.t)
    (pad : W8.t Array192.t) :
  in_qrange768 product =>
  in_qrange768 (encap_ciphertext_spec product msg pad).
proof.
  move=> Hproduct.
  have Hqring :=
    poly_centered_add_spec_qring product (encap_m_ntt_spec msg pad)
      Hproduct (encap_m_ntt_centered_output msg pad).
  exact
    (poly_centered_add_qring_output_in_qrange768
      product (encap_m_ntt_spec msg pad)
      (encap_ciphertext_spec product msg pad) Hqring).
qed.
