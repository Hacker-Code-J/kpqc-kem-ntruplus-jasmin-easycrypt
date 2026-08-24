require import AllCore.
from Jasmin require import JWord.

require import Array32 Array96 Array128 Array224 Array1152 Array2304.
require import NTRUPlus768HashFProof.
require import NTRUPlus768KeygenHashFBridge.

(* Concrete instantiation of the lightweight frontier.  This file connects
   suffix to hash_f_spec(pk), but does not import the terminal proof or claim
   full keypair/decapsulation procedure equivalence. *)
op hash_f_exact_frontier
    (pk : W8.t Array1152.t)
    (suffix : W8.t Array32.t) : bool =
  suffix = hash_f_spec pk.

lemma hash_f_exact_frontier_intro
    (pk : W8.t Array1152.t) :
  hash_f_exact_frontier pk (hash_f_spec pk).
proof. by rewrite /hash_f_exact_frontier. qed.

lemma keygen_hash_f_concrete_suffix_value_flow_intro
    (pk : W8.t Array1152.t)
    (msg : W8.t Array96.t)
    (sk_prefix : W8.t Array2304.t) :
  keygen_hash_f_correlated_suffix_value_flow
    hash_f_exact_frontier
    pk msg sk_prefix
    (hash_f_spec pk)
    (keygen_hash_f_msg_payload msg (hash_f_spec pk)).
proof.
  exact (keygen_hash_f_correlated_suffix_value_flow_intro
    hash_f_exact_frontier pk msg sk_prefix
    (hash_f_spec pk)
    (hash_f_exact_frontier_intro pk)).
qed.

lemma keygen_hash_f_concrete_hash_closure_intro
    (hash_h_frontier :
      bool ->
      W8.t Array1152.t ->
      W8.t Array96.t ->
      W8.t Array32.t ->
      W8.t Array224.t -> bool)
    (pk : W8.t Array1152.t)
    (msg : W8.t Array96.t)
    (sk_prefix : W8.t Array2304.t)
    (decode_failed : bool)
    (buf1 : W8.t Array1152.t)
    (buf3_prefix : W8.t Array224.t) :
  hash_h_frontier decode_failed buf1 msg (hash_f_spec pk) buf3_prefix =>
  keygen_hash_f_correlated_hash_closure
    hash_f_exact_frontier hash_h_frontier
    pk decode_failed buf1 msg (hash_f_spec pk) buf3_prefix.
proof.
  move=> Hhash_h.
  exact (keygen_hash_f_correlated_hash_closure_intro
    hash_f_exact_frontier hash_h_frontier
    pk msg sk_prefix
    (hash_f_spec pk)
    (keygen_hash_f_msg_payload msg (hash_f_spec pk))
    decode_failed buf1 buf3_prefix
    (keygen_hash_f_concrete_suffix_value_flow_intro pk msg sk_prefix)
    Hhash_h).
qed.
