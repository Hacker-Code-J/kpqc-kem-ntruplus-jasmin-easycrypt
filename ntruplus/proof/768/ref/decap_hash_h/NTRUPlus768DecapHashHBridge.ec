require import AllCore List Distr.
from Jasmin require import JWord.

require import Array32 Array96 Array128 Array192 Array224 Array768 Array1152.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768PolyBasemulAlgebra.
require import NTRUPlus768PolyFromBytesAlgebra.
require import NTRUPlus768PolyToBytesProof.
require import NTRUPlus768DecapR2Bridge.
require import NTRUPlus768DecapHashGBridge.
require import NTRUPlus768Crepmod3DecapBridge.
require import NTRUPlus768PolySOTPDecodeAlgebra.
require import NTRUPlus768PolySOTPDecodeDecapBridge.
require import Keccak1600_Spec.
require import EclibExtra.

(* The 32-byte suffix is an explicit value parameter. This theory does not
   prove its key-generation provenance as hash_f(pk) or the C secret-key
   memory layout. *)
op hash_h_payload_list
    (msg : W8.t Array96.t) (suffix : W8.t Array32.t) : W8.t list =
  to_list msg ++ to_list suffix.

op hash_h_payload
    (msg : W8.t Array96.t) (suffix : W8.t Array32.t) : W8.t Array128.t =
  Array128.of_list W8.zero (hash_h_payload_list msg suffix).

op hash_h_input
    (msg : W8.t Array96.t) (suffix : W8.t Array32.t) : W8.t list =
  [W8.of_int 2] ++ hash_h_payload_list msg suffix.

op hash_h_output_list
    (msg : W8.t Array96.t) (suffix : W8.t Array32.t) : W8.t list =
  SHAKE256 (hash_h_input msg suffix) 224.

op hash_h_spec
    (msg : W8.t Array96.t) (suffix : W8.t Array32.t) : W8.t Array224.t =
  Array224.of_list W8.zero (hash_h_output_list msg suffix).

(* These projections name the two live consumers of the 224-byte output:
   the candidate shared secret and the input consumed by poly_cbd1. *)
op hash_h_ss_spec
    (msg : W8.t Array96.t) (suffix : W8.t Array32.t) : W8.t Array32.t =
  Array32.init (fun i => (hash_h_spec msg suffix).[i]).

op hash_h_cbd1_input_spec
    (msg : W8.t Array96.t) (suffix : W8.t Array32.t) : W8.t Array192.t =
  Array192.init (fun i => (hash_h_spec msg suffix).[32 + i]).

lemma hash_h_payload_size
    (msg : W8.t Array96.t) (suffix : W8.t Array32.t) :
  size (hash_h_payload_list msg suffix) = 128.
proof.
  by rewrite /hash_h_payload_list size_cat
    Array96.size_to_list Array32.size_to_list.
qed.

lemma hash_h_payload_to_list
    (msg : W8.t Array96.t) (suffix : W8.t Array32.t) :
  to_list (hash_h_payload msg suffix) = hash_h_payload_list msg suffix.
proof.
  rewrite /hash_h_payload.
  apply Array128.of_listK.
  exact (hash_h_payload_size msg suffix).
qed.

lemma hash_h_input_size
    (msg : W8.t Array96.t) (suffix : W8.t Array32.t) :
  size (hash_h_input msg suffix) = 129.
proof. by rewrite /hash_h_input size_cat hash_h_payload_size. qed.

lemma hash_h_input_domain
    (msg : W8.t Array96.t) (suffix : W8.t Array32.t) :
  nth W8.zero (hash_h_input msg suffix) 0 = W8.of_int 2.
proof. by rewrite /hash_h_input /=. qed.

lemma hash_h_input_payload
    (msg : W8.t Array96.t) (suffix : W8.t Array32.t) :
  drop 1 (hash_h_input msg suffix) = to_list (hash_h_payload msg suffix).
proof.
  rewrite (_ : 1 = 0 + 1) 1:/#.
  rewrite dropS 1:/# /hash_h_input /=.
  by rewrite hash_h_payload_to_list.
qed.

lemma hash_h_output_list_size
    (msg : W8.t Array96.t) (suffix : W8.t Array32.t) :
  size (hash_h_output_list msg suffix) = 224.
proof. by rewrite /hash_h_output_list size_SHAKE256. qed.

lemma hash_h_spec_to_list
    (msg : W8.t Array96.t) (suffix : W8.t Array32.t) :
  to_list (hash_h_spec msg suffix) = hash_h_output_list msg suffix.
proof.
  rewrite /hash_h_spec.
  apply Array224.of_listK.
  exact (hash_h_output_list_size msg suffix).
qed.

module HashH = {
  proc hash_h
      (msg : W8.t Array96.t, suffix : W8.t Array32.t) : W8.t Array224.t = {
    var out;

    (* Match the C domain separation: 0x02 || msg[0..95] || suffix[0..31]. *)
    out <@ Keccak1600Bytes.shake256(hash_h_input msg suffix, 224);
    return Array224.of_list W8.zero out;
  }
}.

hoare hash_h_h
    (msg0 : W8.t Array96.t) (suffix0 : W8.t Array32.t) :
  HashH.hash_h
  : msg = msg0 /\ suffix = suffix0
    ==> res = hash_h_spec msg0 suffix0.
proof.
  proc.
  ecall (SHAKE256_h (hash_h_input msg0 suffix0) 224).
  by auto => />.
qed.

lemma hash_h_ll : islossless HashH.hash_h.
proof.
  proc.
  call SHAKE256_ll.
  by auto.
qed.

phoare hash_h_abstract_correct
    (msg0 : W8.t Array96.t) (suffix0 : W8.t Array32.t) :
  [HashH.hash_h :
    msg = msg0 /\ suffix = suffix0
      ==> res = hash_h_spec msg0 suffix0] = 1%r.
proof. by conseq hash_h_ll (hash_h_h msg0 suffix0). qed.

op decap_hash_h_value_flow
    (ciphertext first_ap first_bp first_basemul_output hinv r2_output :
      W16.t Array768.t)
    (buf1 : W8.t Array1152.t)
    (buf2 : W8.t Array192.t)
    (msg : W8.t Array96.t) (fail_flag : bool)
    (suffix : W8.t Array32.t)
    (payload : W8.t Array128.t)
    (buf3_prefix : W8.t Array224.t) : bool =
  NTRUPlus768PolySOTPDecodeDecapBridge.decap_poly_sotp_decode_value_flow
    ciphertext first_ap first_bp first_basemul_output hinv r2_output
    buf1 buf2 msg fail_flag /\
  payload = hash_h_payload msg suffix /\
  buf3_prefix = hash_h_spec msg suffix.

lemma decap_hash_h_value_flow_ss_source
    (ciphertext first_ap first_bp first_basemul_output hinv r2_output :
      W16.t Array768.t)
    (buf1 : W8.t Array1152.t)
    (buf2 : W8.t Array192.t)
    (msg : W8.t Array96.t) (fail_flag : bool)
    (suffix : W8.t Array32.t)
    (payload : W8.t Array128.t)
    (buf3_prefix : W8.t Array224.t) :
  decap_hash_h_value_flow
    ciphertext first_ap first_bp first_basemul_output hinv r2_output
    buf1 buf2 msg fail_flag suffix payload buf3_prefix =>
  Array32.init (fun i => buf3_prefix.[i]) = hash_h_ss_spec msg suffix.
proof.
  move=> [_ [_ ->]].
  by rewrite /hash_h_ss_spec.
qed.

(* This terminal theorem composes array values only. In particular, suffix is
   arbitrary: no formal hash_f/key-layout provenance, C/Jasmin equivalence,
   pointer-alias model, poly_cbd1, reencryption, comparison, fallback, or
   full-KEM correctness is claimed here. *)
lemma decap_terminal_hash_h_value_flow
    (f_bytes ciphertext_bytes : W8.t Array1152.t)
    (first_basemul_output hinv r2_output : W16.t Array768.t)
    (suffix : W8.t Array32.t) :
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
  decap_hash_h_value_flow
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
        (NTRUPlus768PolyToBytesProof.poly_tobytes_spec r2_output)))
    suffix
    (hash_h_payload
      (NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_decode_msg_spec
        (NTRUPlus768Crepmod3DecapBridge.inverse_invntt_crepmod3_spec
          first_basemul_output)
        (NTRUPlus768DecapHashGBridge.hash_g_spec
          (NTRUPlus768PolyToBytesProof.poly_tobytes_spec r2_output)))
      suffix)
    (hash_h_spec
      (NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_decode_msg_spec
        (NTRUPlus768Crepmod3DecapBridge.inverse_invntt_crepmod3_spec
          first_basemul_output)
        (NTRUPlus768DecapHashGBridge.hash_g_spec
          (NTRUPlus768PolyToBytesProof.poly_tobytes_spec r2_output)))
      suffix).
proof.
  move=> Hfirst Hhinv Hr2.
  rewrite /decap_hash_h_value_flow.
  split.
  + exact
      (NTRUPlus768PolySOTPDecodeDecapBridge.decap_terminal_poly_sotp_decode_value_flow
        f_bytes ciphertext_bytes first_basemul_output hinv r2_output
        Hfirst Hhinv Hr2).
  by split.
qed.

lemma decap_hash_h_failure_zero
    (a : W16.t Array768.t) (buf : W8.t Array192.t)
    (suffix : W8.t Array32.t) :
  NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_decode_fail_spec a buf =>
  hash_h_spec
    (NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_decode_msg_spec a buf)
    suffix =
  hash_h_spec NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_zero_msg_spec suffix.
proof.
  move=> Hfail.
  by rewrite
    (NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_decode_failure_zero a buf Hfail).
qed.

lemma decap_hash_h_correct
    (msg0 : W8.t Array96.t) (suffix0 : W8.t Array32.t) :
  phoare [HashH.hash_h :
    msg = msg0 /\ suffix = suffix0
      ==> res = hash_h_spec msg0 suffix0] = 1%r.
proof. exact (hash_h_abstract_correct msg0 suffix0). qed.
