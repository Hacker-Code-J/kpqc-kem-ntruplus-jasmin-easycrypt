require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array96 Array192 Array768 Array1152.
require import NTRUPlus768PolyFromBytesAlgebra.
require import NTRUPlus768PolyToBytesProof.
require import NTRUPlus768PolySubAlgebra.
require import NTRUPlus768PolySubDecapBridge.
require import NTRUPlus768PolyBasemulAlgebra.
require import NTRUPlus768Crepmod3Algebra.
require import NTRUPlus768Crepmod3DecapBridge.
require import NTRUPlus768DecapR2Bridge.
require import NTRUPlus768DecapHashGBridge.
require import NTRUPlus768InvNTTAlgebra.
require import NTRUPlus768PolySOTPDecodeAlgebra.

import Ring.IntID IntOrder.

op inverse_invntt_crepmod3_trit_input
    (first_basemul_output : W16.t Array768.t) : bool =
  NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_trit_input
    (NTRUPlus768Crepmod3DecapBridge.inverse_invntt_crepmod3_spec
      first_basemul_output).

op decap_poly_sotp_decode_value_flow
    (ciphertext first_ap first_bp first_basemul_output hinv r2_output :
      W16.t Array768.t)
    (buf1 : W8.t Array1152.t)
    (buf2 : W8.t Array192.t)
    (msg : W8.t Array96.t) (fail_flag : bool) : bool =
  NTRUPlus768Crepmod3DecapBridge.decap_m1_crepmod3_value_flow
    first_basemul_output
    (NTRUPlus768Crepmod3DecapBridge.inverse_invntt_crepmod3_spec
      first_basemul_output) /\
  inverse_invntt_crepmod3_trit_input first_basemul_output /\
  NTRUPlus768DecapHashGBridge.decap_hash_g_value_flow
    ciphertext first_ap first_bp first_basemul_output hinv r2_output buf1 buf2 /\
  (msg, fail_flag) =
    NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_decode_spec
      (NTRUPlus768Crepmod3DecapBridge.inverse_invntt_crepmod3_spec
        first_basemul_output)
      buf2.

lemma inverse_invntt_crepmod3_spec_trit_input
    (input : W16.t Array768.t) :
  NTRUPlus768Crepmod3Algebra.poly_crepmod3_algebra
    (NTRUPlus768InvNTTAlgebra.inverse_invntt_spec input)
    (NTRUPlus768Crepmod3DecapBridge.inverse_invntt_crepmod3_spec input) =>
  inverse_invntt_crepmod3_trit_input input.
proof.
  move=> Halg k Hk.
  have Hcoeff := Halg k Hk.
  by move: Hcoeff => [Htrit _].
qed.

lemma poly_basemul_qring_inverse_invntt_crepmod3_trit_input
    (ap bp rp : W16.t Array768.t) :
  poly_basemul_qring ap bp rp 192 =>
  inverse_invntt_crepmod3_trit_input rp.
proof.
  move=> Hqring.
  have Hflow :=
    NTRUPlus768Crepmod3DecapBridge.poly_basemul_qring_decap_m1_crepmod3_value_flow
      ap bp rp Hqring.
  move: Hflow => [_ [Hcrep _]].
  exact (inverse_invntt_crepmod3_spec_trit_input rp Hcrep).
qed.

(* This terminal theorem composes decapsulation values only.
   It is not a proof of the concrete C/Jasmin caller, pointer aliasing,
   memory safety, or any poly_sotp_encode/poly_sotp_decode inverse property. *)
lemma decap_terminal_poly_sotp_decode_value_flow
    (f_bytes ciphertext_bytes : W8.t Array1152.t)
    (first_basemul_output hinv r2_output : W16.t Array768.t) :
  poly_basemul_qring
    (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec ciphertext_bytes)
    (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec f_bytes)
    first_basemul_output 192 =>
  NTRUPlus768PolyBasemulAlgebra.in_qrange768 hinv =>
  poly_basemul_qring
    (NTRUPlus768DecapR2Bridge.decap_sub_spec
      (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec ciphertext_bytes)
      first_basemul_output)
    (NTRUPlus768DecapR2Bridge.decoded_hinv_spec hinv)
    r2_output 192 =>
  decap_poly_sotp_decode_value_flow
    (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec ciphertext_bytes)
    (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec ciphertext_bytes)
    (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec f_bytes)
    first_basemul_output hinv r2_output
    (NTRUPlus768PolyToBytesProof.poly_tobytes_spec r2_output)
    (NTRUPlus768DecapHashGBridge.hash_g_spec
      (NTRUPlus768PolyToBytesProof.poly_tobytes_spec r2_output))
    (NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_decode_msg_spec
      (NTRUPlus768Crepmod3DecapBridge.inverse_invntt_crepmod3_spec
        first_basemul_output)
      (NTRUPlus768DecapHashGBridge.hash_g_spec
        (NTRUPlus768PolyToBytesProof.poly_tobytes_spec r2_output)))
    (NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_decode_fail_spec
      (NTRUPlus768Crepmod3DecapBridge.inverse_invntt_crepmod3_spec
        first_basemul_output)
      (NTRUPlus768DecapHashGBridge.hash_g_spec
        (NTRUPlus768PolyToBytesProof.poly_tobytes_spec r2_output))).
proof.
  move=> Hfirst Hhinv Hr2.
  rewrite /decap_poly_sotp_decode_value_flow.
  split.
  + exact
      (NTRUPlus768Crepmod3DecapBridge.poly_basemul_qring_decap_m1_crepmod3_value_flow
        (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec ciphertext_bytes)
        (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec f_bytes)
        first_basemul_output Hfirst).
  split.
  + exact
      (poly_basemul_qring_inverse_invntt_crepmod3_trit_input
        (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec ciphertext_bytes)
        (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec f_bytes)
        first_basemul_output Hfirst).
  split.
  + exact
      (NTRUPlus768DecapHashGBridge.decap_r2_hash_g_value_flow
        f_bytes ciphertext_bytes first_basemul_output hinv r2_output
        Hfirst Hhinv Hr2).
  done.
qed.
