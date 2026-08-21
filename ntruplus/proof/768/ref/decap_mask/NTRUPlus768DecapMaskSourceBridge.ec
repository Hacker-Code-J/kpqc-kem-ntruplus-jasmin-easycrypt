require import AllCore.
from Jasmin require import JWord.

require import Array32 Array224.

(* Lightweight 224-to-32 projection boundary.  [hash_frontier] is a closure
   over the established hash_h value flow, so this file does not reload the
   full Keccak/decode dependency tree. *)
op decap_mask_ss_source
    (buf3_prefix : W8.t Array224.t) : W8.t Array32.t =
  Array32.init (fun i => buf3_prefix.[i]).

op decap_mask_source_value_flow
    (hash_frontier : W8.t Array224.t -> bool)
    (buf3_prefix : W8.t Array224.t)
    (ss_source : W8.t Array32.t) : bool =
  hash_frontier buf3_prefix /\
  ss_source = decap_mask_ss_source buf3_prefix.

op projected_ss_source_frontier
    (hash_frontier : W8.t Array224.t -> bool)
    (ss_source : W8.t Array32.t) : bool =
  exists buf3_prefix,
    decap_mask_source_value_flow hash_frontier buf3_prefix ss_source.

lemma decap_mask_ss_source_byte
    (buf3_prefix : W8.t Array224.t)
    (i : int) :
  0 <= i < 32 =>
  (decap_mask_ss_source buf3_prefix).[i] = buf3_prefix.[i].
proof.
  move=> Hi.
  by rewrite /decap_mask_ss_source Array32.initiE.
qed.

lemma decap_mask_source_value_flow_intro
    (hash_frontier : W8.t Array224.t -> bool)
    (buf3_prefix : W8.t Array224.t) :
  hash_frontier buf3_prefix =>
  decap_mask_source_value_flow
    hash_frontier buf3_prefix (decap_mask_ss_source buf3_prefix).
proof. by rewrite /decap_mask_source_value_flow. qed.

lemma decap_mask_source_value_flow_exact
    (hash_frontier : W8.t Array224.t -> bool)
    (buf3_prefix : W8.t Array224.t)
    (ss_source : W8.t Array32.t) :
  decap_mask_source_value_flow hash_frontier buf3_prefix ss_source =>
  ss_source = decap_mask_ss_source buf3_prefix.
proof. by move=> [_ ->]. qed.

lemma decap_mask_source_value_flow_byte
    (hash_frontier : W8.t Array224.t -> bool)
    (buf3_prefix : W8.t Array224.t)
    (ss_source : W8.t Array32.t)
    (i : int) :
  decap_mask_source_value_flow hash_frontier buf3_prefix ss_source =>
  0 <= i < 32 =>
  ss_source.[i] = buf3_prefix.[i].
proof.
  move=> [_ ->] Hi.
  exact (decap_mask_ss_source_byte buf3_prefix i Hi).
qed.

lemma projected_ss_source_frontier_intro
    (hash_frontier : W8.t Array224.t -> bool)
    (buf3_prefix : W8.t Array224.t) :
  hash_frontier buf3_prefix =>
  projected_ss_source_frontier
    hash_frontier (decap_mask_ss_source buf3_prefix).
proof.
  move=> Hhash.
  rewrite /projected_ss_source_frontier.
  exists buf3_prefix.
  exact (decap_mask_source_value_flow_intro
    hash_frontier buf3_prefix Hhash).
qed.
