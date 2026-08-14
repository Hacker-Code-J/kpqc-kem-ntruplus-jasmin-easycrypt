require import AllCore List Distr.
from Jasmin require import JWord.

require import Array768 Array1152 Array192.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768PolyBasemulAlgebra.
require import NTRUPlus768PolyFromBytesAlgebra.
require import NTRUPlus768PolySubAlgebra.
require import NTRUPlus768PolySubDecapBridge.
require import NTRUPlus768PolyToBytesProof.
require import NTRUPlus768DecapR2Bridge.
require import NTRUPlus768DecapR2ToBytesBridge.
require import Keccak1600_Spec.
require import EclibExtra.

op hash_g_input (buf1 : W8.t Array1152.t) : W8.t list =
  [W8.of_int 1] ++ to_list buf1.

op hash_g_output_list (buf1 : W8.t Array1152.t) : W8.t list =
  SHAKE256 (hash_g_input buf1) 192.

op hash_g_spec (buf1 : W8.t Array1152.t) : W8.t Array192.t =
  Array192.of_list W8.zero (hash_g_output_list buf1).

lemma hash_g_input_size (buf1 : W8.t Array1152.t) :
  size (hash_g_input buf1) = 1153.
proof. by rewrite /hash_g_input size_cat Array1152.size_to_list. qed.

lemma hash_g_input_domain (buf1 : W8.t Array1152.t) :
  nth W8.zero (hash_g_input buf1) 0 = W8.of_int 1.
proof. by rewrite /hash_g_input /=. qed.

lemma hash_g_input_payload (buf1 : W8.t Array1152.t) :
  drop 1 (hash_g_input buf1) = to_list buf1.
proof.
  rewrite (_ : 1 = 0 + 1) 1:/#.
  rewrite dropS 1:/# /hash_g_input /=.
  done.
qed.

lemma hash_g_output_list_size (buf1 : W8.t Array1152.t) :
  size (hash_g_output_list buf1) = 192.
proof. by rewrite /hash_g_output_list size_SHAKE256. qed.

lemma hash_g_spec_to_list (buf1 : W8.t Array1152.t) :
  to_list (hash_g_spec buf1) = hash_g_output_list buf1.
proof.
  rewrite /hash_g_spec.
  apply Array192.of_listK.
  exact (hash_g_output_list_size buf1).
qed.

module HashG = {
  proc hash_g(buf1 : W8.t Array1152.t) : W8.t Array192.t = {
    var out;

    (* Match the C call site domain separation: 0x01 || poly_tobytes(r2). *)
    out <@ Keccak1600Bytes.shake256(hash_g_input buf1, 192);
    return Array192.of_list W8.zero out;
  }
}.

hoare hash_g_h (buf10 : W8.t Array1152.t) :
  HashG.hash_g
  : buf1 = buf10
    ==> res = hash_g_spec buf10.
proof.
  proc.
  ecall (SHAKE256_h (hash_g_input buf10) 192).
  by auto => />.
qed.

lemma hash_g_ll : islossless HashG.hash_g.
proof.
  proc.
  call SHAKE256_ll.
  by auto.
qed.

phoare hash_g_abstract_correct (buf10 : W8.t Array1152.t) :
  [HashG.hash_g :
    buf1 = buf10
      ==> res = hash_g_spec buf10] = 1%r.
proof. by conseq hash_g_ll (hash_g_h buf10). qed.

op decap_hash_g_value_flow
    (ciphertext first_ap first_bp first_basemul_output hinv r2_output :
      W16.t Array768.t)
    (buf1 : W8.t Array1152.t)
    (buf2 : W8.t Array192.t) : bool =
  NTRUPlus768DecapR2ToBytesBridge.decap_r2_tobytes_value_flow
    ciphertext first_ap first_bp first_basemul_output hinv r2_output buf1 /\
  buf2 =
    hash_g_spec (NTRUPlus768PolyToBytesProof.poly_tobytes_spec r2_output).

lemma valid_hinv_decap_hash_g_value_flow
    (ciphertext first_ap first_bp first_basemul_output hinv r2_output :
      W16.t Array768.t) :
  NTRUPlus768PolySubAlgebra.decoder_range ciphertext =>
  poly_basemul_qring first_ap first_bp first_basemul_output 192 =>
  NTRUPlus768PolyToBytesProof.poly_tobytes_input_qrange hinv =>
  poly_basemul_qring
    (NTRUPlus768DecapR2Bridge.decap_sub_spec ciphertext first_basemul_output)
    (NTRUPlus768DecapR2Bridge.decoded_hinv_spec hinv)
    r2_output 192 =>
  decap_hash_g_value_flow ciphertext first_ap first_bp
    first_basemul_output hinv r2_output
    (NTRUPlus768PolyToBytesProof.poly_tobytes_spec r2_output)
    (hash_g_spec (NTRUPlus768PolyToBytesProof.poly_tobytes_spec r2_output)).
proof.
  move=> Hcipher Hfirst Hhinv Hr2.
  rewrite /decap_hash_g_value_flow.
  split.
  + exact
      (NTRUPlus768DecapR2ToBytesBridge.valid_hinv_decap_r2_serialized_value_flow
        ciphertext first_ap first_bp first_basemul_output hinv r2_output
        Hcipher Hfirst Hhinv Hr2).
  done.
qed.

(* This terminal theorem stops at the mathematical seam
   buf2 = hash_g_spec (poly_tobytes_spec r2_output). It does not prove the
   NTRU+ C code in symmetric.c or fips202.c, pointer/alias semantics, or any
   Jasmin extraction. *)
lemma decap_r2_hash_g_value_flow
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
  decap_hash_g_value_flow
    (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec ciphertext_bytes)
    (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec ciphertext_bytes)
    (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec f_bytes)
    first_basemul_output hinv r2_output
    (NTRUPlus768PolyToBytesProof.poly_tobytes_spec r2_output)
    (hash_g_spec (NTRUPlus768PolyToBytesProof.poly_tobytes_spec r2_output)).
proof.
  move=> Hfirst Hhinv Hr2.
  exact
    (valid_hinv_decap_hash_g_value_flow
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

lemma decap_hash_g_correct
    (r2_output : W16.t Array768.t) :
  phoare [HashG.hash_g :
    buf1 = NTRUPlus768PolyToBytesProof.poly_tobytes_spec r2_output
      ==> res =
        hash_g_spec (NTRUPlus768PolyToBytesProof.poly_tobytes_spec r2_output)] = 1%r.
proof.
  exact
    (hash_g_abstract_correct
      (NTRUPlus768PolyToBytesProof.poly_tobytes_spec r2_output)).
qed.
