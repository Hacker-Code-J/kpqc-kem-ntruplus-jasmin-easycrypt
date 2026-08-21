require import AllCore Distr.
from Jasmin require import JWord.

require import Array32 Array224.
require import NTRUPlus768DecapFailProof.
require import NTRUPlus768DecapMaskProof.
require import NTRUPlus768DecapMaskSourceBridge.

(* Memory-bounded value composition for the final shared-secret loop.
   [ss_source_frontier] closes over the established hash_h projection, and
   [fail_frontier] closes over the established decode/compare failure flow.
   Keeping both producer trees behind typed predicates avoids loading their
   full dependencies together.  This proves the 32-byte result, not C memory,
   pointer, integer-representation, binary, or full-KEM equivalence. *)
op decap_mask_value_flow
    (ss_source_frontier : W8.t Array32.t -> bool)
    (fail_frontier : bool -> W8.t -> bool)
    (buf3_prefix : W8.t Array32.t)
    (failed : bool)
    (failv : W8.t)
    (ss : W8.t Array32.t) : bool =
  ss_source_frontier buf3_prefix /\
  fail_frontier failed failv /\
  failv = fail_byte failed /\
  ss = decap_mask_ss_spec failv buf3_prefix.

lemma decap_mask_value_flow_intro
    (ss_source_frontier : W8.t Array32.t -> bool)
    (fail_frontier : bool -> W8.t -> bool)
    (buf3_prefix : W8.t Array32.t)
    (failed : bool) :
  ss_source_frontier buf3_prefix =>
  fail_frontier failed (fail_byte failed) =>
  decap_mask_value_flow
    ss_source_frontier fail_frontier
    buf3_prefix failed (fail_byte failed)
    (decap_mask_ss_spec (fail_byte failed) buf3_prefix).
proof. by rewrite /decap_mask_value_flow. qed.

lemma decap_mask_value_flow_from_hash_frontier
    (hash_frontier : W8.t Array224.t -> bool)
    (fail_frontier : bool -> W8.t -> bool)
    (buf3_prefix : W8.t Array224.t)
    (failed : bool) :
  hash_frontier buf3_prefix =>
  fail_frontier failed (fail_byte failed) =>
  decap_mask_value_flow
    (projected_ss_source_frontier hash_frontier)
    fail_frontier
    (decap_mask_ss_source buf3_prefix)
    failed
    (fail_byte failed)
    (decap_mask_ss_spec
      (fail_byte failed) (decap_mask_ss_source buf3_prefix)).
proof.
  move=> Hhash Hfail.
  apply (decap_mask_value_flow_intro
    (projected_ss_source_frontier hash_frontier)
    fail_frontier
    (decap_mask_ss_source buf3_prefix)
    failed).
  + exact (projected_ss_source_frontier_intro
      hash_frontier buf3_prefix Hhash).
  + exact Hfail.
qed.

lemma decap_mask_value_flow_fail_range
    (ss_source_frontier : W8.t Array32.t -> bool)
    (fail_frontier : bool -> W8.t -> bool)
    (buf3_prefix : W8.t Array32.t)
    (failed : bool)
    (failv : W8.t)
    (ss : W8.t Array32.t) :
  decap_mask_value_flow
    ss_source_frontier fail_frontier buf3_prefix failed failv ss =>
  failv = W8.of_int 0 \/ failv = W8.of_int 1.
proof.
  move=> [_ [_ [-> _]]].
  case failed; smt(fail_byte_false fail_byte_true).
qed.

lemma decap_mask_value_flow_fail_zero_iff
    (ss_source_frontier : W8.t Array32.t -> bool)
    (fail_frontier : bool -> W8.t -> bool)
    (buf3_prefix : W8.t Array32.t)
    (failed : bool)
    (failv : W8.t)
    (ss : W8.t Array32.t) :
  decap_mask_value_flow
    ss_source_frontier fail_frontier buf3_prefix failed failv ss =>
  (failv = W8.of_int 0 <=> ! failed).
proof.
  move=> [_ [_ [-> _]]].
  case failed; smt(fail_byte_false fail_byte_true).
qed.

lemma decap_mask_value_flow_fail_one_iff
    (ss_source_frontier : W8.t Array32.t -> bool)
    (fail_frontier : bool -> W8.t -> bool)
    (buf3_prefix : W8.t Array32.t)
    (failed : bool)
    (failv : W8.t)
    (ss : W8.t Array32.t) :
  decap_mask_value_flow
    ss_source_frontier fail_frontier buf3_prefix failed failv ss =>
  (failv = W8.of_int 1 <=> failed).
proof.
  move=> [_ [_ [-> _]]].
  case failed; smt(fail_byte_false fail_byte_true).
qed.

lemma decap_mask_value_flow_selection
    (ss_source_frontier : W8.t Array32.t -> bool)
    (fail_frontier : bool -> W8.t -> bool)
    (buf3_prefix : W8.t Array32.t)
    (failed : bool)
    (failv : W8.t)
    (ss : W8.t Array32.t) :
  decap_mask_value_flow
    ss_source_frontier fail_frontier buf3_prefix failed failv ss =>
  ss = if failed then decap_mask_zero_ss else buf3_prefix.
proof.
  move=> [_ [_ [-> ->]]].
  exact (decap_mask_ss_select failed buf3_prefix).
qed.

lemma decap_mask_value_flow_copy
    (ss_source_frontier : W8.t Array32.t -> bool)
    (fail_frontier : bool -> W8.t -> bool)
    (buf3_prefix : W8.t Array32.t)
    (failed : bool)
    (failv : W8.t)
    (ss : W8.t Array32.t) :
  decap_mask_value_flow
    ss_source_frontier fail_frontier buf3_prefix failed failv ss =>
  ! failed => ss = buf3_prefix.
proof.
  move=> Hflow Hsuccess.
  have Hselect := decap_mask_value_flow_selection
    ss_source_frontier fail_frontier buf3_prefix failed failv ss Hflow.
  by move: Hselect; case failed.
qed.

lemma decap_mask_value_flow_zero
    (ss_source_frontier : W8.t Array32.t -> bool)
    (fail_frontier : bool -> W8.t -> bool)
    (buf3_prefix : W8.t Array32.t)
    (failed : bool)
    (failv : W8.t)
    (ss : W8.t Array32.t) :
  decap_mask_value_flow
    ss_source_frontier fail_frontier buf3_prefix failed failv ss =>
  failed => ss = decap_mask_zero_ss.
proof.
  move=> Hflow Hfailed.
  have Hselect := decap_mask_value_flow_selection
    ss_source_frontier fail_frontier buf3_prefix failed failv ss Hflow.
  by move: Hselect; case failed.
qed.

lemma decap_mask_value_flow_byte_selection
    (ss_source_frontier : W8.t Array32.t -> bool)
    (fail_frontier : bool -> W8.t -> bool)
    (buf3_prefix : W8.t Array32.t)
    (failed : bool)
    (failv : W8.t)
    (ss : W8.t Array32.t)
    (i : int) :
  decap_mask_value_flow
    ss_source_frontier fail_frontier buf3_prefix failed failv ss =>
  0 <= i < 32 =>
  ss.[i] = if failed then W8.zero else buf3_prefix.[i].
proof.
  move=> Hflow Hi.
  rewrite (decap_mask_value_flow_selection
    ss_source_frontier fail_frontier buf3_prefix failed failv ss Hflow).
  case failed => /=.
  + by rewrite /decap_mask_zero_ss Array32.initiE.
  + done.
qed.

lemma decap_mask_procedure_functional
    (ss_source_frontier : W8.t Array32.t -> bool)
    (fail_frontier : bool -> W8.t -> bool)
    (buf3_prefix : W8.t Array32.t)
    (failed : bool)
    (failv : W8.t)
    (ss : W8.t Array32.t) :
  decap_mask_value_flow
    ss_source_frontier fail_frontier buf3_prefix failed failv ss =>
  hoare [DecapMask.mask_ss :
    arg = (buf3_prefix, failv) ==> res = ss].
proof.
  move=> [_ [_ [_ ->]]].
  exact (decap_mask_functional buf3_prefix failv).
qed.

lemma decap_mask_procedure_correct
    (ss_source_frontier : W8.t Array32.t -> bool)
    (fail_frontier : bool -> W8.t -> bool)
    (buf3_prefix : W8.t Array32.t)
    (failed : bool)
    (failv : W8.t)
    (ss : W8.t Array32.t) :
  decap_mask_value_flow
    ss_source_frontier fail_frontier buf3_prefix failed failv ss =>
  phoare [DecapMask.mask_ss :
    arg = (buf3_prefix, failv) ==> res = ss] = 1%r.
proof.
  move=> [_ [_ [_ ->]]].
  exact (decap_mask_correct buf3_prefix failv).
qed.
