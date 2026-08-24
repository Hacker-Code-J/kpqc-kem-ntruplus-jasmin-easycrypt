require import AllCore.
from Jasmin require import JWord.

require import Array32 Array96 Array128 Array224 Array1152 Array2304.

(* Lightweight split-layout provenance.  [Array2304 * Array32] represents the
   keygen prefix and hash suffix without introducing an unavailable Array2336;
   exact flat C offsets remain anchored by source/runtime checks.  The hash_f
   and hash_h computations stay behind typed frontiers to avoid loading their
   Keccak and terminal proof trees together. *)
op keygen_secret_layout_byte
    (sk_prefix : W8.t Array2304.t)
    (suffix : W8.t Array32.t)
    (idx : int) : W8.t =
  if 0 <= idx < 2304 then
    sk_prefix.[idx]
  else if 2304 <= idx < 2336 then
    suffix.[idx - 2304]
  else
    W8.zero.

op keygen_hash_f_secret_suffix
    (sk_prefix : W8.t Array2304.t)
    (suffix : W8.t Array32.t) : W8.t Array32.t =
  Array32.init (fun i => keygen_secret_layout_byte sk_prefix suffix (2304 + i)).

op keygen_hash_f_msg_payload
    (msg : W8.t Array96.t)
    (suffix : W8.t Array32.t) : W8.t Array128.t =
  Array128.init (fun i => if i < 96 then msg.[i] else suffix.[i - 96]).

op keygen_hash_f_msg_suffix
    (msg_payload : W8.t Array128.t) : W8.t Array32.t =
  Array32.init (fun i => msg_payload.[96 + i]).

op keygen_hash_f_suffix_value_flow
    (hash_f_frontier : W8.t Array1152.t -> W8.t Array32.t -> bool)
    (pk : W8.t Array1152.t)
    (sk_prefix : W8.t Array2304.t)
    (suffix : W8.t Array32.t) : bool =
  hash_f_frontier pk suffix /\
  keygen_hash_f_secret_suffix sk_prefix suffix = suffix.

op keygen_hash_f_correlated_suffix_value_flow
    (hash_f_frontier : W8.t Array1152.t -> W8.t Array32.t -> bool)
    (pk : W8.t Array1152.t)
    (msg : W8.t Array96.t)
    (sk_prefix : W8.t Array2304.t)
    (suffix : W8.t Array32.t)
    (msg_payload : W8.t Array128.t) : bool =
  keygen_hash_f_suffix_value_flow
    hash_f_frontier pk sk_prefix suffix /\
  msg_payload = keygen_hash_f_msg_payload msg suffix.

op keygen_hash_f_correlated_hash_closure
    (hash_f_frontier : W8.t Array1152.t -> W8.t Array32.t -> bool)
    (hash_h_frontier :
      bool ->
      W8.t Array1152.t ->
      W8.t Array96.t ->
      W8.t Array32.t ->
      W8.t Array224.t -> bool)
    (pk : W8.t Array1152.t)
    (decode_failed : bool)
    (buf1 : W8.t Array1152.t)
    (msg : W8.t Array96.t)
    (suffix : W8.t Array32.t)
    (buf3_prefix : W8.t Array224.t) : bool =
  hash_f_frontier pk suffix /\
  hash_h_frontier decode_failed buf1 msg suffix buf3_prefix.

lemma keygen_hash_f_secret_suffix_byte
    (sk_prefix : W8.t Array2304.t)
    (suffix : W8.t Array32.t)
    (i : int) :
  0 <= i < 32 =>
  (keygen_hash_f_secret_suffix sk_prefix suffix).[i] = suffix.[i].
proof.
  move=> Hi.
  rewrite /keygen_hash_f_secret_suffix Array32.initiE 1:/#.
  rewrite /keygen_secret_layout_byte.
  by smt().
qed.

lemma keygen_hash_f_secret_suffix_exact
    (sk_prefix : W8.t Array2304.t)
    (suffix : W8.t Array32.t) :
  keygen_hash_f_secret_suffix sk_prefix suffix = suffix.
proof.
  apply Array32.tP => i Hi.
  exact (keygen_hash_f_secret_suffix_byte sk_prefix suffix i Hi).
qed.

lemma keygen_hash_f_msg_payload_prefix_byte
    (msg : W8.t Array96.t)
    (suffix : W8.t Array32.t)
    (i : int) :
  0 <= i < 96 =>
  (keygen_hash_f_msg_payload msg suffix).[i] = msg.[i].
proof.
  move=> Hi.
  rewrite /keygen_hash_f_msg_payload Array128.initiE 1:/#.
  by smt().
qed.

lemma keygen_hash_f_msg_payload_suffix_byte
    (msg : W8.t Array96.t)
    (suffix : W8.t Array32.t)
    (i : int) :
  0 <= i < 32 =>
  (keygen_hash_f_msg_payload msg suffix).[96 + i] = suffix.[i].
proof.
  move=> Hi.
  rewrite /keygen_hash_f_msg_payload Array128.initiE 1:/#.
  by smt().
qed.

lemma keygen_hash_f_msg_suffix_exact
    (msg : W8.t Array96.t)
    (suffix : W8.t Array32.t) :
  keygen_hash_f_msg_suffix (keygen_hash_f_msg_payload msg suffix) = suffix.
proof.
  apply Array32.tP => i Hi.
  rewrite /keygen_hash_f_msg_suffix Array32.initiE 1:/#.
  exact (keygen_hash_f_msg_payload_suffix_byte msg suffix i Hi).
qed.

lemma keygen_hash_f_suffix_value_flow_intro
    (hash_f_frontier : W8.t Array1152.t -> W8.t Array32.t -> bool)
    (pk : W8.t Array1152.t)
    (sk_prefix : W8.t Array2304.t)
    (suffix : W8.t Array32.t) :
  hash_f_frontier pk suffix =>
  keygen_hash_f_suffix_value_flow
    hash_f_frontier pk sk_prefix suffix.
proof.
  move=> Hhash.
  rewrite /keygen_hash_f_suffix_value_flow.
  split; first exact Hhash.
  exact (keygen_hash_f_secret_suffix_exact sk_prefix suffix).
qed.

lemma keygen_hash_f_correlated_suffix_value_flow_intro
    (hash_f_frontier : W8.t Array1152.t -> W8.t Array32.t -> bool)
    (pk : W8.t Array1152.t)
    (msg : W8.t Array96.t)
    (sk_prefix : W8.t Array2304.t)
    (suffix : W8.t Array32.t) :
  hash_f_frontier pk suffix =>
  keygen_hash_f_correlated_suffix_value_flow
    hash_f_frontier pk msg sk_prefix suffix
    (keygen_hash_f_msg_payload msg suffix).
proof.
  move=> Hhash.
  rewrite /keygen_hash_f_correlated_suffix_value_flow.
  split.
  + exact (keygen_hash_f_suffix_value_flow_intro
      hash_f_frontier pk sk_prefix suffix Hhash).
  + done.
qed.

lemma keygen_hash_f_correlated_hash_closure_intro
    (hash_f_frontier : W8.t Array1152.t -> W8.t Array32.t -> bool)
    (hash_h_frontier :
      bool ->
      W8.t Array1152.t ->
      W8.t Array96.t ->
      W8.t Array32.t ->
      W8.t Array224.t -> bool)
    (pk : W8.t Array1152.t)
    (msg : W8.t Array96.t)
    (sk_prefix : W8.t Array2304.t)
    (suffix : W8.t Array32.t)
    (msg_payload : W8.t Array128.t)
    (decode_failed : bool)
    (buf1 : W8.t Array1152.t)
    (buf3_prefix : W8.t Array224.t) :
  keygen_hash_f_correlated_suffix_value_flow
    hash_f_frontier pk msg sk_prefix suffix msg_payload =>
  hash_h_frontier decode_failed buf1 msg suffix buf3_prefix =>
  keygen_hash_f_correlated_hash_closure
    hash_f_frontier hash_h_frontier
    pk decode_failed buf1 msg suffix buf3_prefix.
proof.
  move=> [[Hhash _] Hhash_h].
  by rewrite /keygen_hash_f_correlated_hash_closure.
qed.

lemma keygen_hash_f_correlated_suffix_outcome
    (hash_f_frontier : W8.t Array1152.t -> W8.t Array32.t -> bool)
    (pk : W8.t Array1152.t)
    (msg : W8.t Array96.t)
    (sk_prefix : W8.t Array2304.t)
    (suffix : W8.t Array32.t)
    (msg_payload : W8.t Array128.t) :
  keygen_hash_f_correlated_suffix_value_flow
    hash_f_frontier pk msg sk_prefix suffix msg_payload =>
  hash_f_frontier pk suffix /\
  keygen_hash_f_secret_suffix sk_prefix suffix = suffix /\
  keygen_hash_f_msg_suffix msg_payload = suffix /\
  (forall i, 0 <= i < 32 => msg_payload.[96 + i] = suffix.[i]).
proof.
  move=> [[Hhash Hsuffix] Hpayload].
  split; first exact Hhash.
  split; first exact Hsuffix.
  split.
  + rewrite Hpayload.
    exact (keygen_hash_f_msg_suffix_exact msg suffix).
  + move=> i Hi.
    rewrite Hpayload.
    exact (keygen_hash_f_msg_payload_suffix_byte msg suffix i Hi).
qed.

lemma keygen_hash_f_correlated_hash_closure_outcome
    (hash_f_frontier : W8.t Array1152.t -> W8.t Array32.t -> bool)
    (hash_h_frontier :
      bool ->
      W8.t Array1152.t ->
      W8.t Array96.t ->
      W8.t Array32.t ->
      W8.t Array224.t -> bool)
    (pk : W8.t Array1152.t)
    (decode_failed : bool)
    (buf1 : W8.t Array1152.t)
    (msg : W8.t Array96.t)
    (suffix : W8.t Array32.t)
    (buf3_prefix : W8.t Array224.t) :
  keygen_hash_f_correlated_hash_closure
    hash_f_frontier hash_h_frontier
    pk decode_failed buf1 msg suffix buf3_prefix =>
  hash_f_frontier pk suffix /\
  hash_h_frontier decode_failed buf1 msg suffix buf3_prefix.
proof. by rewrite /keygen_hash_f_correlated_hash_closure. qed.
