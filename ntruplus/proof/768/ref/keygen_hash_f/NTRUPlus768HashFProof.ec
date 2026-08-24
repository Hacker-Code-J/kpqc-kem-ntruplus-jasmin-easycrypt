require import AllCore List Distr.
from Jasmin require import JWord.

require import Array32 Array1152.
require import Keccak1600_Spec.

(* Standalone FIPS202 value/procedure model of the C hash_f wrapper.  This is
   not a C pointer, heap, or binary-equivalence theorem. *)
op hash_f_payload_list
    (pk : W8.t Array1152.t) : W8.t list =
  to_list pk.

op hash_f_input
    (pk : W8.t Array1152.t) : W8.t list =
  [W8.of_int 0] ++ hash_f_payload_list pk.

op hash_f_output_list
    (pk : W8.t Array1152.t) : W8.t list =
  SHAKE256 (hash_f_input pk) 32.

op hash_f_spec
    (pk : W8.t Array1152.t) : W8.t Array32.t =
  Array32.of_list W8.zero (hash_f_output_list pk).

lemma hash_f_payload_size
    (pk : W8.t Array1152.t) :
  size (hash_f_payload_list pk) = 1152.
proof. by rewrite /hash_f_payload_list Array1152.size_to_list. qed.

lemma hash_f_input_size
    (pk : W8.t Array1152.t) :
  size (hash_f_input pk) = 1153.
proof. by rewrite /hash_f_input size_cat hash_f_payload_size. qed.

lemma hash_f_input_domain
    (pk : W8.t Array1152.t) :
  nth W8.zero (hash_f_input pk) 0 = W8.of_int 0.
proof. by rewrite /hash_f_input /=. qed.

lemma hash_f_input_payload
    (pk : W8.t Array1152.t) :
  drop 1 (hash_f_input pk) = to_list pk.
proof.
  rewrite (_ : 1 = 0 + 1) 1:/#.
  rewrite dropS 1:/# /hash_f_input /=.
  by rewrite /hash_f_payload_list.
qed.

lemma hash_f_output_list_size
    (pk : W8.t Array1152.t) :
  size (hash_f_output_list pk) = 32.
proof. by rewrite /hash_f_output_list size_SHAKE256. qed.

lemma hash_f_spec_to_list
    (pk : W8.t Array1152.t) :
  to_list (hash_f_spec pk) = hash_f_output_list pk.
proof.
  rewrite /hash_f_spec.
  apply Array32.of_listK.
  exact (hash_f_output_list_size pk).
qed.

module HashF = {
  proc hash_f(pk : W8.t Array1152.t) : W8.t Array32.t = {
    var out;

    (* Match the C domain separation: 0x00 || pk[0..1151]. *)
    out <@ Keccak1600Bytes.shake256(hash_f_input pk, 32);
    return Array32.of_list W8.zero out;
  }
}.

hoare hash_f_h
    (pk0 : W8.t Array1152.t) :
  HashF.hash_f
  : pk = pk0
    ==> res = hash_f_spec pk0.
proof.
  proc.
  ecall (SHAKE256_h (hash_f_input pk0) 32).
  by auto => />.
qed.

lemma hash_f_ll : islossless HashF.hash_f.
proof.
  proc.
  call SHAKE256_ll.
  by auto.
qed.

lemma hash_f_correct
    (pk0 : W8.t Array1152.t) :
  phoare [HashF.hash_f :
    pk = pk0 ==> res = hash_f_spec pk0] = 1%r.
proof. by conseq hash_f_ll (hash_f_h pk0). qed.
