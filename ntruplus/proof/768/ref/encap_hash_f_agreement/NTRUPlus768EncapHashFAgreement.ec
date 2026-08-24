require import AllCore.
from Jasmin require import JWord.

require import Array32 Array96 Array128 Array1152 Array2304.
require import NTRUPlus768KeygenHashFBridge.

(* This file only states value-level suffix agreement for the shared hash_f
   output across encap/keygen/decap layouts.  It does not prove full msg,
   hash_h, shared-secret, C-memory, or procedure equivalence. *)

op encap_hash_f_msg_payload
    (msg_prefix : W8.t Array96.t)
    (suffix : W8.t Array32.t) : W8.t Array128.t =
  keygen_hash_f_msg_payload msg_prefix suffix.

op encap_hash_f_msg_suffix
    (msg_payload : W8.t Array128.t) : W8.t Array32.t =
  keygen_hash_f_msg_suffix msg_payload.

op decap_hash_f_msg_payload
    (msg_prefix : W8.t Array96.t)
    (sk_suffix : W8.t Array32.t) : W8.t Array128.t =
  keygen_hash_f_msg_payload msg_prefix sk_suffix.

op decap_hash_f_msg_suffix
    (msg_payload : W8.t Array128.t) : W8.t Array32.t =
  keygen_hash_f_msg_suffix msg_payload.

op encap_hash_f_agreement_value_flow
    (hash_f_frontier : W8.t Array1152.t -> W8.t Array32.t -> bool)
    (pk : W8.t Array1152.t)
    (encap_msg_prefix decap_msg_prefix : W8.t Array96.t)
    (sk_prefix : W8.t Array2304.t)
    (suffix : W8.t Array32.t)
    (encap_msg decap_msg : W8.t Array128.t) : bool =
  keygen_hash_f_suffix_value_flow hash_f_frontier pk sk_prefix suffix /\
  encap_msg = encap_hash_f_msg_payload encap_msg_prefix suffix /\
  decap_msg =
    decap_hash_f_msg_payload
      decap_msg_prefix
      (keygen_hash_f_secret_suffix sk_prefix suffix).

lemma encap_hash_f_agreement_value_flow_intro
    (hash_f_frontier : W8.t Array1152.t -> W8.t Array32.t -> bool)
    (pk : W8.t Array1152.t)
    (encap_msg_prefix decap_msg_prefix : W8.t Array96.t)
    (sk_prefix : W8.t Array2304.t)
    (suffix : W8.t Array32.t) :
  hash_f_frontier pk suffix =>
  encap_hash_f_agreement_value_flow
    hash_f_frontier pk
    encap_msg_prefix decap_msg_prefix
    sk_prefix suffix
    (encap_hash_f_msg_payload encap_msg_prefix suffix)
    (decap_hash_f_msg_payload
      decap_msg_prefix
      (keygen_hash_f_secret_suffix sk_prefix suffix)).
proof.
  move=> Hhash.
  rewrite /encap_hash_f_agreement_value_flow.
  split.
  + exact (keygen_hash_f_suffix_value_flow_intro
      hash_f_frontier pk sk_prefix suffix Hhash).
  + by split.
qed.

lemma encap_hash_f_encap_suffix_exact
    (hash_f_frontier : W8.t Array1152.t -> W8.t Array32.t -> bool)
    (pk : W8.t Array1152.t)
    (encap_msg_prefix decap_msg_prefix : W8.t Array96.t)
    (sk_prefix : W8.t Array2304.t)
    (suffix : W8.t Array32.t)
    (encap_msg decap_msg : W8.t Array128.t) :
  encap_hash_f_agreement_value_flow
    hash_f_frontier pk
    encap_msg_prefix decap_msg_prefix
    sk_prefix suffix encap_msg decap_msg =>
  encap_hash_f_msg_suffix encap_msg = suffix.
proof.
  move=> [_ [-> _]].
  rewrite /encap_hash_f_msg_suffix /encap_hash_f_msg_payload.
  exact (keygen_hash_f_msg_suffix_exact encap_msg_prefix suffix).
qed.

lemma encap_hash_f_encap_suffix_byte
    (hash_f_frontier : W8.t Array1152.t -> W8.t Array32.t -> bool)
    (pk : W8.t Array1152.t)
    (encap_msg_prefix decap_msg_prefix : W8.t Array96.t)
    (sk_prefix : W8.t Array2304.t)
    (suffix : W8.t Array32.t)
    (encap_msg decap_msg : W8.t Array128.t)
    (i : int) :
  encap_hash_f_agreement_value_flow
    hash_f_frontier pk
    encap_msg_prefix decap_msg_prefix
    sk_prefix suffix encap_msg decap_msg =>
  0 <= i < 32 =>
  encap_msg.[96 + i] = suffix.[i].
proof.
  move=> [_ [-> _]] Hi.
  rewrite /encap_hash_f_msg_payload.
  exact (keygen_hash_f_msg_payload_suffix_byte
    encap_msg_prefix suffix i Hi).
qed.

lemma encap_hash_f_keygen_suffix_exact
    (hash_f_frontier : W8.t Array1152.t -> W8.t Array32.t -> bool)
    (pk : W8.t Array1152.t)
    (encap_msg_prefix decap_msg_prefix : W8.t Array96.t)
    (sk_prefix : W8.t Array2304.t)
    (suffix : W8.t Array32.t)
    (encap_msg decap_msg : W8.t Array128.t) :
  encap_hash_f_agreement_value_flow
    hash_f_frontier pk
    encap_msg_prefix decap_msg_prefix
    sk_prefix suffix encap_msg decap_msg =>
  keygen_hash_f_secret_suffix sk_prefix suffix = suffix.
proof.
  move=> [Hsuffix _].
  move: Hsuffix => [_ Hproj].
  exact Hproj.
qed.

lemma encap_hash_f_decap_suffix_exact
    (hash_f_frontier : W8.t Array1152.t -> W8.t Array32.t -> bool)
    (pk : W8.t Array1152.t)
    (encap_msg_prefix decap_msg_prefix : W8.t Array96.t)
    (sk_prefix : W8.t Array2304.t)
    (suffix : W8.t Array32.t)
    (encap_msg decap_msg : W8.t Array128.t) :
  encap_hash_f_agreement_value_flow
    hash_f_frontier pk
    encap_msg_prefix decap_msg_prefix
    sk_prefix suffix encap_msg decap_msg =>
  decap_hash_f_msg_suffix decap_msg = suffix.
proof.
  move=> [Hsuffix [_ ->]].
  move: Hsuffix => [_ Hproj].
  rewrite /decap_hash_f_msg_suffix /decap_hash_f_msg_payload Hproj.
  exact (keygen_hash_f_msg_suffix_exact decap_msg_prefix suffix).
qed.

lemma encap_hash_f_decap_suffix_byte
    (hash_f_frontier : W8.t Array1152.t -> W8.t Array32.t -> bool)
    (pk : W8.t Array1152.t)
    (encap_msg_prefix decap_msg_prefix : W8.t Array96.t)
    (sk_prefix : W8.t Array2304.t)
    (suffix : W8.t Array32.t)
    (encap_msg decap_msg : W8.t Array128.t)
    (i : int) :
  encap_hash_f_agreement_value_flow
    hash_f_frontier pk
    encap_msg_prefix decap_msg_prefix
    sk_prefix suffix encap_msg decap_msg =>
  0 <= i < 32 =>
  decap_msg.[96 + i] = suffix.[i].
proof.
  move=> [Hsuffix [_ ->]] Hi.
  move: Hsuffix => [_ Hproj].
  rewrite /decap_hash_f_msg_payload Hproj.
  exact (keygen_hash_f_msg_payload_suffix_byte
    decap_msg_prefix suffix i Hi).
qed.

lemma encap_hash_f_suffix_agreement
    (hash_f_frontier : W8.t Array1152.t -> W8.t Array32.t -> bool)
    (pk : W8.t Array1152.t)
    (encap_msg_prefix decap_msg_prefix : W8.t Array96.t)
    (sk_prefix : W8.t Array2304.t)
    (suffix : W8.t Array32.t)
    (encap_msg decap_msg : W8.t Array128.t) :
  encap_hash_f_agreement_value_flow
    hash_f_frontier pk
    encap_msg_prefix decap_msg_prefix
    sk_prefix suffix encap_msg decap_msg =>
  encap_hash_f_msg_suffix encap_msg =
  decap_hash_f_msg_suffix decap_msg.
proof.
  move=> Hflow.
  rewrite (encap_hash_f_encap_suffix_exact
    hash_f_frontier pk
    encap_msg_prefix decap_msg_prefix
    sk_prefix suffix encap_msg decap_msg Hflow).
  apply eq_sym.
  exact (encap_hash_f_decap_suffix_exact
    hash_f_frontier pk
    encap_msg_prefix decap_msg_prefix
    sk_prefix suffix encap_msg decap_msg Hflow).
qed.

lemma encap_hash_f_agreement_outcome
    (hash_f_frontier : W8.t Array1152.t -> W8.t Array32.t -> bool)
    (pk : W8.t Array1152.t)
    (encap_msg_prefix decap_msg_prefix : W8.t Array96.t)
    (sk_prefix : W8.t Array2304.t)
    (suffix : W8.t Array32.t)
    (encap_msg decap_msg : W8.t Array128.t) :
  encap_hash_f_agreement_value_flow
    hash_f_frontier pk
    encap_msg_prefix decap_msg_prefix
    sk_prefix suffix encap_msg decap_msg =>
  hash_f_frontier pk suffix /\
  encap_hash_f_msg_suffix encap_msg = suffix /\
  keygen_hash_f_secret_suffix sk_prefix suffix = suffix /\
  decap_hash_f_msg_suffix decap_msg = suffix /\
  (forall i, 0 <= i < 32 => encap_msg.[96 + i] = suffix.[i]) /\
  (forall i, 0 <= i < 32 => decap_msg.[96 + i] = suffix.[i]) /\
  encap_hash_f_msg_suffix encap_msg =
    decap_hash_f_msg_suffix decap_msg.
proof.
  move=> Hflow.
  have Henc :=
    encap_hash_f_encap_suffix_exact
      hash_f_frontier pk
      encap_msg_prefix decap_msg_prefix
      sk_prefix suffix encap_msg decap_msg Hflow.
  have Hkey :=
    encap_hash_f_keygen_suffix_exact
      hash_f_frontier pk
      encap_msg_prefix decap_msg_prefix
      sk_prefix suffix encap_msg decap_msg Hflow.
  have Hdec :=
    encap_hash_f_decap_suffix_exact
      hash_f_frontier pk
      encap_msg_prefix decap_msg_prefix
      sk_prefix suffix encap_msg decap_msg Hflow.
  have Hagree :=
    encap_hash_f_suffix_agreement
      hash_f_frontier pk
      encap_msg_prefix decap_msg_prefix
      sk_prefix suffix encap_msg decap_msg Hflow.
  have Henc_bytes :
      forall i, 0 <= i < 32 => encap_msg.[96 + i] = suffix.[i].
  + move=> i Hi.
    exact (encap_hash_f_encap_suffix_byte
      hash_f_frontier pk
      encap_msg_prefix decap_msg_prefix
      sk_prefix suffix encap_msg decap_msg i Hflow Hi).
  have Hdec_bytes :
      forall i, 0 <= i < 32 => decap_msg.[96 + i] = suffix.[i].
  + move=> i Hi.
    exact (encap_hash_f_decap_suffix_byte
      hash_f_frontier pk
      encap_msg_prefix decap_msg_prefix
      sk_prefix suffix encap_msg decap_msg i Hflow Hi).
  move: Hflow => [[Hhash _] _].
  split; first exact Hhash.
  split; first exact Henc.
  split; first exact Hkey.
  split; first exact Hdec.
  split; first exact Henc_bytes.
  split; first exact Hdec_bytes.
  exact Hagree.
qed.
