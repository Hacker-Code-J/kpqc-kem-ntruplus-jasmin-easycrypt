require import AllCore.
from Jasmin require import JWord.

require import Array32 Array96 Array128 Array1152 Array2304.
require import NTRUPlus768HashFProof.
require import NTRUPlus768KeygenHashFBridge.
require import NTRUPlus768KeygenHashFConcrete.
require import NTRUPlus768EncapHashFAgreement.

(* Concrete agreement adapter for the exact hash_f_spec(pk) suffix.  This is
   still only a value-level suffix agreement theorem; no full procedures,
   hash_h, shared-secret, or C-memory correctness is claimed here. *)

lemma encap_hash_f_concrete_agreement_intro
    (pk : W8.t Array1152.t)
    (encap_msg_prefix decap_msg_prefix : W8.t Array96.t)
    (sk_prefix : W8.t Array2304.t) :
  encap_hash_f_agreement_value_flow
    hash_f_exact_frontier
    pk encap_msg_prefix decap_msg_prefix
    sk_prefix
    (hash_f_spec pk)
    (encap_hash_f_msg_payload encap_msg_prefix (hash_f_spec pk))
    (decap_hash_f_msg_payload decap_msg_prefix (hash_f_spec pk)).
proof.
  have Hbase :=
    keygen_hash_f_concrete_suffix_value_flow_intro
      pk decap_msg_prefix sk_prefix.
  move: Hbase => [[Hhash Hproj] Hpayload].
  rewrite /encap_hash_f_agreement_value_flow.
  split.
  + split; first exact Hhash.
    exact Hproj.
  split; first done.
  rewrite /decap_hash_f_msg_payload Hproj.
  exact Hpayload.
qed.

lemma encap_hash_f_concrete_agreement_outcome
    (pk : W8.t Array1152.t)
    (encap_msg_prefix decap_msg_prefix : W8.t Array96.t)
    (sk_prefix : W8.t Array2304.t) :
  let suffix = hash_f_spec pk in
  let encap_msg = encap_hash_f_msg_payload encap_msg_prefix suffix in
  let decap_msg = decap_hash_f_msg_payload decap_msg_prefix suffix in
  encap_hash_f_msg_suffix encap_msg = suffix /\
  keygen_hash_f_secret_suffix sk_prefix suffix = suffix /\
  decap_hash_f_msg_suffix decap_msg = suffix /\
  (forall i, 0 <= i < 32 => encap_msg.[96 + i] = suffix.[i]) /\
  (forall i, 0 <= i < 32 => decap_msg.[96 + i] = suffix.[i]) /\
  encap_hash_f_msg_suffix encap_msg = decap_hash_f_msg_suffix decap_msg.
proof.
  move=> suffix encap_msg decap_msg.
  have Hflow :=
    encap_hash_f_concrete_agreement_intro
      pk encap_msg_prefix decap_msg_prefix sk_prefix.
  move: (encap_hash_f_agreement_outcome
    hash_f_exact_frontier
    pk encap_msg_prefix decap_msg_prefix
    sk_prefix suffix encap_msg decap_msg Hflow).
  by rewrite /hash_f_exact_frontier.
qed.
