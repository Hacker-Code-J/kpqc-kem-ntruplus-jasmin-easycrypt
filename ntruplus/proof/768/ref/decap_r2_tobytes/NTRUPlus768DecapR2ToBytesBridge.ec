require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array768 Array1152.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768PolyBasemulAlgebra.
require import NTRUPlus768PolyFromBytesAlgebra.
require import NTRUPlus768PolySubAlgebra.
require import NTRUPlus768PolySubDecapBridge.
require import NTRUPlus768PolyToBytes.
require import NTRUPlus768PolyToBytesProof.
require import NTRUPlus768PolyToBytesAlgebra.
require import NTRUPlus768DecapR2Bridge.

import Ring.IntID IntOrder.

op decap_r2_tobytes_value_flow
    (ciphertext first_ap first_bp first_basemul_output hinv r2_output :
      W16.t Array768.t)
    (buf1 : W8.t Array1152.t) : bool =
  NTRUPlus768DecapR2Bridge.decap_r2_value_flow
    ciphertext first_ap first_bp first_basemul_output hinv r2_output /\
  buf1 = NTRUPlus768PolyToBytesProof.poly_tobytes_spec r2_output.

lemma decap_r2_qring_poly_tobytes_input_qrange
    (ap bp r2_output : W16.t Array768.t) :
  poly_basemul_qring ap bp r2_output 192 =>
  NTRUPlus768PolyToBytesProof.poly_tobytes_input_qrange r2_output.
proof.
  move=> Hr2.
  apply NTRUPlus768DecapR2Bridge.in_qrange768_poly_tobytes_input_qrange.
  exact
    (NTRUPlus768DecapR2Bridge.poly_basemul_qring_output_in_qrange768
      ap bp r2_output Hr2).
qed.

lemma valid_hinv_decap_r2_serialized_value_flow
    (ciphertext first_ap first_bp first_basemul_output hinv r2_output :
      W16.t Array768.t) :
  NTRUPlus768PolySubAlgebra.decoder_range ciphertext =>
  poly_basemul_qring first_ap first_bp first_basemul_output 192 =>
  NTRUPlus768PolyToBytesProof.poly_tobytes_input_qrange hinv =>
  poly_basemul_qring
    (NTRUPlus768DecapR2Bridge.decap_sub_spec ciphertext first_basemul_output)
    (NTRUPlus768DecapR2Bridge.decoded_hinv_spec hinv)
    r2_output 192 =>
  decap_r2_tobytes_value_flow ciphertext first_ap first_bp
    first_basemul_output hinv r2_output
    (NTRUPlus768PolyToBytesProof.poly_tobytes_spec r2_output).
proof.
  move=> Hcipher Hfirst Hhinv Hr2.
  rewrite /decap_r2_tobytes_value_flow.
  split.
  + exact
      (NTRUPlus768DecapR2Bridge.valid_hinv_decap_r2_value_flow
        ciphertext first_ap first_bp first_basemul_output hinv r2_output
        Hcipher Hfirst Hhinv Hr2).
  done.
qed.

lemma valid_hinv_decap_r2_poly_tobytes_correct
    (ciphertext first_ap first_bp first_basemul_output hinv r2_output :
      W16.t Array768.t)
    (rp0 : W8.t Array1152.t) :
  NTRUPlus768PolySubAlgebra.decoder_range ciphertext =>
  poly_basemul_qring first_ap first_bp first_basemul_output 192 =>
  NTRUPlus768PolyToBytesProof.poly_tobytes_input_qrange hinv =>
  poly_basemul_qring
    (NTRUPlus768DecapR2Bridge.decap_sub_spec ciphertext first_basemul_output)
    (NTRUPlus768DecapR2Bridge.decoded_hinv_spec hinv)
    r2_output 192 =>
  phoare [NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes :
    rp = rp0 /\ ap = r2_output ==>
    res = NTRUPlus768PolyToBytesProof.poly_tobytes_spec r2_output] = 1%r.
proof.
  move=> _ _ _ Hr2.
  exact
    (NTRUPlus768PolyToBytesProof.poly_tobytes_correct rp0 r2_output
      (decap_r2_qring_poly_tobytes_input_qrange
        (NTRUPlus768DecapR2Bridge.decap_sub_spec ciphertext first_basemul_output)
        (NTRUPlus768DecapR2Bridge.decoded_hinv_spec hinv)
        r2_output Hr2)).
qed.

(* This terminal theorem extends the proven decapsulation flow up to the exact
   serialized bytes produced by poly_tobytes(buf1, &r2). It stops before hash_g
   and does not model caller aliasing, pointer identity, or C-AST equivalence. *)
lemma decap_r2_serialized_value_flow
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
  decap_r2_tobytes_value_flow
    (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec ciphertext_bytes)
    (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec ciphertext_bytes)
    (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec f_bytes)
    first_basemul_output hinv r2_output
    (NTRUPlus768PolyToBytesProof.poly_tobytes_spec r2_output).
proof.
  move=> Hfirst Hhinv Hr2.
  exact
    (valid_hinv_decap_r2_serialized_value_flow
      (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec ciphertext_bytes)
      (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec ciphertext_bytes)
      (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec f_bytes)
      first_basemul_output hinv r2_output
      (NTRUPlus768PolySubDecapBridge.poly_frombytes_spec_decoder_range
        ciphertext_bytes)
      Hfirst
      (NTRUPlus768DecapR2Bridge.in_qrange768_poly_tobytes_input_qrange
        hinv Hhinv)
      Hr2).
qed.

(* Procedure theorem for the concrete decapsulation seam poly_tobytes(buf1,&r2)
   once the preceding poly_basemul result is available as a q-ring array. *)
lemma decap_r2_poly_tobytes_correct
    (f_bytes ciphertext_bytes : W8.t Array1152.t)
    (first_basemul_output hinv r2_output : W16.t Array768.t)
    (buf10 : W8.t Array1152.t) :
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
  phoare [NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes :
    rp = buf10 /\ ap = r2_output ==>
    res = NTRUPlus768PolyToBytesProof.poly_tobytes_spec r2_output] = 1%r.
proof.
  move=> Hfirst Hhinv Hr2.
  exact
    (valid_hinv_decap_r2_poly_tobytes_correct
      (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec ciphertext_bytes)
      (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec ciphertext_bytes)
      (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec f_bytes)
      first_basemul_output hinv r2_output buf10
      (NTRUPlus768PolySubDecapBridge.poly_frombytes_spec_decoder_range
        ciphertext_bytes)
      Hfirst
      (NTRUPlus768DecapR2Bridge.in_qrange768_poly_tobytes_input_qrange
        hinv Hhinv)
      Hr2).
qed.
