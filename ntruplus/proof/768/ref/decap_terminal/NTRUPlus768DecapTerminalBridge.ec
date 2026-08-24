require import AllCore Distr.
from Jasmin require import JWord.

require import Array32 Array96 Array224 Array1152.
require import NTRUPlus768DecapFailBridge.
require import NTRUPlus768DecapMaskProof.
require import NTRUPlus768DecapMaskSourceBridge.
require import NTRUPlus768DecapMaskBridge.
require import NTRUPlus768DecapTerminalProof.

(* Thin terminal composition over typed predecessor closures.  The correlated
   layer exposes the decode flag, serialized comparison input, message, and
   arbitrary suffix to one hash closure without importing the full
   hash_h/Keccak tree.  The returned value remains W8: no C int conversion,
   memory/pointer/binary, concrete full-procedure, or KEM theorem is claimed. *)
op decap_terminal_failed
    (decode_failed compare_failed : bool) : bool =
  decode_failed \/ compare_failed.

op decap_terminal_fail_frontier
    (decode_frontier : bool -> W8.t -> bool)
    (compare_frontier :
      W8.t Array1152.t -> W8.t Array1152.t -> bool -> W64.t -> bool)
    (decode_failed compare_failed : bool)
    (decode_fail_byte : W8.t)
    (buf1 buf2 : W8.t Array1152.t)
    (compare_result : W64.t)
    (failed : bool)
    (failv : W8.t) : bool =
  decap_fail_value_flow
    decode_frontier compare_frontier
    decode_failed compare_failed
    decode_fail_byte buf1 buf2 compare_result failv /\
  failed = decap_terminal_failed decode_failed compare_failed.

op decap_terminal_value_flow
    (hash_frontier : W8.t Array224.t -> bool)
    (decode_frontier : bool -> W8.t -> bool)
    (compare_frontier :
      W8.t Array1152.t -> W8.t Array1152.t -> bool -> W64.t -> bool)
    (decode_failed compare_failed : bool)
    (decode_fail_byte : W8.t)
    (buf1 buf2 : W8.t Array1152.t)
    (compare_result : W64.t)
    (buf3_prefix : W8.t Array224.t)
    (ss_source ss : W8.t Array32.t)
    (failv ret_fail : W8.t) : bool =
  decap_fail_value_flow
    decode_frontier compare_frontier
    decode_failed compare_failed
    decode_fail_byte buf1 buf2 compare_result failv /\
  decap_mask_source_value_flow
    hash_frontier buf3_prefix ss_source /\
  decap_mask_value_flow
    (projected_ss_source_frontier hash_frontier)
    (decap_terminal_fail_frontier
      decode_frontier compare_frontier
      decode_failed compare_failed
      decode_fail_byte buf1 buf2 compare_result)
    ss_source
    (decap_terminal_failed decode_failed compare_failed)
    failv
    ss /\
  ret_fail = failv.

op decap_terminal_correlated_hash_frontier
    (hash_frontier :
      bool ->
      W8.t Array1152.t ->
      W8.t Array96.t ->
      W8.t Array32.t ->
      W8.t Array224.t -> bool)
    (decode_failed : bool)
    (buf1 : W8.t Array1152.t)
    (msg : W8.t Array96.t)
    (suffix : W8.t Array32.t)
    (buf3_prefix : W8.t Array224.t) : bool =
  hash_frontier decode_failed buf1 msg suffix buf3_prefix.

op decap_terminal_correlated_value_flow
    (hash_frontier :
      bool ->
      W8.t Array1152.t ->
      W8.t Array96.t ->
      W8.t Array32.t ->
      W8.t Array224.t -> bool)
    (decode_frontier : bool -> W8.t -> bool)
    (compare_frontier :
      W8.t Array1152.t -> W8.t Array1152.t -> bool -> W64.t -> bool)
    (decode_failed compare_failed : bool)
    (decode_fail_byte : W8.t)
    (buf1 buf2 : W8.t Array1152.t)
    (msg : W8.t Array96.t)
    (suffix : W8.t Array32.t)
    (compare_result : W64.t)
    (buf3_prefix : W8.t Array224.t)
    (ss_source ss : W8.t Array32.t)
    (failv ret_fail : W8.t) : bool =
  decap_terminal_value_flow
    (decap_terminal_correlated_hash_frontier
      hash_frontier decode_failed buf1 msg suffix)
    decode_frontier compare_frontier
    decode_failed compare_failed
    decode_fail_byte buf1 buf2 compare_result
    buf3_prefix ss_source ss failv ret_fail.

lemma decap_terminal_fail_frontier_intro
    (decode_frontier : bool -> W8.t -> bool)
    (compare_frontier :
      W8.t Array1152.t -> W8.t Array1152.t -> bool -> W64.t -> bool)
    (decode_failed compare_failed : bool)
    (decode_fail_byte : W8.t)
    (buf1 buf2 : W8.t Array1152.t)
    (compare_result : W64.t)
    (failv : W8.t) :
  decap_fail_value_flow
    decode_frontier compare_frontier
    decode_failed compare_failed
    decode_fail_byte buf1 buf2 compare_result failv =>
  decap_terminal_fail_frontier
    decode_frontier compare_frontier
    decode_failed compare_failed
    decode_fail_byte buf1 buf2 compare_result
    (decap_terminal_failed decode_failed compare_failed)
    failv.
proof.
  by rewrite /decap_terminal_fail_frontier.
qed.

lemma decap_terminal_value_flow_intro
    (hash_frontier : W8.t Array224.t -> bool)
    (decode_frontier : bool -> W8.t -> bool)
    (compare_frontier :
      W8.t Array1152.t -> W8.t Array1152.t -> bool -> W64.t -> bool)
    (decode_failed compare_failed : bool)
    (decode_fail_byte : W8.t)
    (buf1 buf2 : W8.t Array1152.t)
    (compare_result : W64.t)
    (buf3_prefix : W8.t Array224.t)
    (ss_source : W8.t Array32.t)
    (failv : W8.t) :
  decap_fail_value_flow
    decode_frontier compare_frontier
    decode_failed compare_failed
    decode_fail_byte buf1 buf2 compare_result failv =>
  decap_mask_source_value_flow
    hash_frontier buf3_prefix ss_source =>
  decap_terminal_value_flow
    hash_frontier decode_frontier compare_frontier
    decode_failed compare_failed
    decode_fail_byte buf1 buf2 compare_result
    buf3_prefix ss_source
    (decap_mask_ss_spec failv ss_source)
    failv failv.
proof.
  move=> Hfail [Hhash Hsrc].
  rewrite /decap_terminal_value_flow.
  split; first exact Hfail.
  split; first by split.
  split.
  + rewrite /decap_mask_value_flow.
    split.
    * rewrite Hsrc.
      exact (projected_ss_source_frontier_intro
        hash_frontier buf3_prefix Hhash).
    split.
    * exact (decap_terminal_fail_frontier_intro
        decode_frontier compare_frontier
        decode_failed compare_failed
        decode_fail_byte buf1 buf2 compare_result
        failv Hfail).
    split.
    * exact (decap_fail_value_flow_combined_fail
        decode_frontier compare_frontier
        decode_failed compare_failed
        decode_fail_byte buf1 buf2 compare_result
        failv Hfail).
    * done.
  + done.
qed.

lemma decap_terminal_correlated_value_flow_intro
    (hash_frontier :
      bool ->
      W8.t Array1152.t ->
      W8.t Array96.t ->
      W8.t Array32.t ->
      W8.t Array224.t -> bool)
    (decode_frontier : bool -> W8.t -> bool)
    (compare_frontier :
      W8.t Array1152.t -> W8.t Array1152.t -> bool -> W64.t -> bool)
    (decode_failed compare_failed : bool)
    (decode_fail_byte : W8.t)
    (buf1 buf2 : W8.t Array1152.t)
    (msg : W8.t Array96.t)
    (suffix : W8.t Array32.t)
    (compare_result : W64.t)
    (buf3_prefix : W8.t Array224.t)
    (ss_source : W8.t Array32.t)
    (failv : W8.t) :
  decap_fail_value_flow
    decode_frontier compare_frontier
    decode_failed compare_failed
    decode_fail_byte buf1 buf2 compare_result failv =>
  decap_mask_source_value_flow
    (decap_terminal_correlated_hash_frontier
      hash_frontier decode_failed buf1 msg suffix)
    buf3_prefix ss_source =>
  decap_terminal_correlated_value_flow
    hash_frontier decode_frontier compare_frontier
    decode_failed compare_failed
    decode_fail_byte buf1 buf2
    msg suffix compare_result
    buf3_prefix ss_source
    (decap_mask_ss_spec failv ss_source)
    failv failv.
proof.
  move=> Hfail Hsource.
  exact (decap_terminal_value_flow_intro
    (decap_terminal_correlated_hash_frontier
      hash_frontier decode_failed buf1 msg suffix)
    decode_frontier compare_frontier
    decode_failed compare_failed
    decode_fail_byte buf1 buf2 compare_result
    buf3_prefix ss_source failv
    Hfail Hsource).
qed.

lemma decap_terminal_value_flow_source_exact
    (hash_frontier : W8.t Array224.t -> bool)
    (decode_frontier : bool -> W8.t -> bool)
    (compare_frontier :
      W8.t Array1152.t -> W8.t Array1152.t -> bool -> W64.t -> bool)
    (decode_failed compare_failed : bool)
    (decode_fail_byte : W8.t)
    (buf1 buf2 : W8.t Array1152.t)
    (compare_result : W64.t)
    (buf3_prefix : W8.t Array224.t)
    (ss_source ss : W8.t Array32.t)
    (failv ret_fail : W8.t) :
  decap_terminal_value_flow
    hash_frontier decode_frontier compare_frontier
    decode_failed compare_failed
    decode_fail_byte buf1 buf2 compare_result
    buf3_prefix ss_source ss failv ret_fail =>
  ss_source = decap_mask_ss_source buf3_prefix.
proof.
  move=> [_ [Hsource _]].
  exact (decap_mask_source_value_flow_exact
    hash_frontier buf3_prefix ss_source Hsource).
qed.

lemma decap_terminal_value_flow_failed_iff
    (hash_frontier : W8.t Array224.t -> bool)
    (decode_frontier : bool -> W8.t -> bool)
    (compare_frontier :
      W8.t Array1152.t -> W8.t Array1152.t -> bool -> W64.t -> bool)
    (decode_failed compare_failed : bool)
    (decode_fail_byte : W8.t)
    (buf1 buf2 : W8.t Array1152.t)
    (compare_result : W64.t)
    (buf3_prefix : W8.t Array224.t)
    (ss_source ss : W8.t Array32.t)
    (failv ret_fail : W8.t) :
  decap_terminal_value_flow
    hash_frontier decode_frontier compare_frontier
    decode_failed compare_failed
    decode_fail_byte buf1 buf2 compare_result
    buf3_prefix ss_source ss failv ret_fail =>
  decap_terminal_failed decode_failed compare_failed <=>
  decode_failed \/ buf1 <> buf2.
proof.
  move=> [Hfail _].
  move: Hfail => [_ [_ [_ [_ [Hcmp _]]]]].
  by rewrite /decap_terminal_failed Hcmp.
qed.

lemma decap_terminal_value_flow_return_range
    (hash_frontier : W8.t Array224.t -> bool)
    (decode_frontier : bool -> W8.t -> bool)
    (compare_frontier :
      W8.t Array1152.t -> W8.t Array1152.t -> bool -> W64.t -> bool)
    (decode_failed compare_failed : bool)
    (decode_fail_byte : W8.t)
    (buf1 buf2 : W8.t Array1152.t)
    (compare_result : W64.t)
    (buf3_prefix : W8.t Array224.t)
    (ss_source ss : W8.t Array32.t)
    (failv ret_fail : W8.t) :
  decap_terminal_value_flow
    hash_frontier decode_frontier compare_frontier
    decode_failed compare_failed
    decode_fail_byte buf1 buf2 compare_result
    buf3_prefix ss_source ss failv ret_fail =>
  ret_fail = W8.of_int 0 \/ ret_fail = W8.of_int 1.
proof.
  move=> [Hfail [_ [_ ->]]].
  exact (decap_fail_value_flow_result_range
    decode_frontier compare_frontier
    decode_failed compare_failed
    decode_fail_byte buf1 buf2 compare_result failv Hfail).
qed.

lemma decap_terminal_value_flow_return_zero_iff
    (hash_frontier : W8.t Array224.t -> bool)
    (decode_frontier : bool -> W8.t -> bool)
    (compare_frontier :
      W8.t Array1152.t -> W8.t Array1152.t -> bool -> W64.t -> bool)
    (decode_failed compare_failed : bool)
    (decode_fail_byte : W8.t)
    (buf1 buf2 : W8.t Array1152.t)
    (compare_result : W64.t)
    (buf3_prefix : W8.t Array224.t)
    (ss_source ss : W8.t Array32.t)
    (failv ret_fail : W8.t) :
  decap_terminal_value_flow
    hash_frontier decode_frontier compare_frontier
    decode_failed compare_failed
    decode_fail_byte buf1 buf2 compare_result
    buf3_prefix ss_source ss failv ret_fail =>
  (ret_fail = W8.of_int 0 <=> ! decode_failed /\ buf1 = buf2).
proof.
  move=> [Hfail [_ [_ ->]]].
  exact (decap_fail_value_flow_zero_iff
    decode_frontier compare_frontier
    decode_failed compare_failed
    decode_fail_byte buf1 buf2 compare_result failv Hfail).
qed.

lemma decap_terminal_value_flow_return_one_iff
    (hash_frontier : W8.t Array224.t -> bool)
    (decode_frontier : bool -> W8.t -> bool)
    (compare_frontier :
      W8.t Array1152.t -> W8.t Array1152.t -> bool -> W64.t -> bool)
    (decode_failed compare_failed : bool)
    (decode_fail_byte : W8.t)
    (buf1 buf2 : W8.t Array1152.t)
    (compare_result : W64.t)
    (buf3_prefix : W8.t Array224.t)
    (ss_source ss : W8.t Array32.t)
    (failv ret_fail : W8.t) :
  decap_terminal_value_flow
    hash_frontier decode_frontier compare_frontier
    decode_failed compare_failed
    decode_fail_byte buf1 buf2 compare_result
    buf3_prefix ss_source ss failv ret_fail =>
  (ret_fail = W8.of_int 1 <=> decode_failed \/ buf1 <> buf2).
proof.
  move=> [Hfail [_ [_ ->]]].
  exact (decap_fail_value_flow_one_iff
    decode_frontier compare_frontier
    decode_failed compare_failed
    decode_fail_byte buf1 buf2 compare_result failv Hfail).
qed.

lemma decap_terminal_value_flow_selection
    (hash_frontier : W8.t Array224.t -> bool)
    (decode_frontier : bool -> W8.t -> bool)
    (compare_frontier :
      W8.t Array1152.t -> W8.t Array1152.t -> bool -> W64.t -> bool)
    (decode_failed compare_failed : bool)
    (decode_fail_byte : W8.t)
    (buf1 buf2 : W8.t Array1152.t)
    (compare_result : W64.t)
    (buf3_prefix : W8.t Array224.t)
    (ss_source ss : W8.t Array32.t)
    (failv ret_fail : W8.t) :
  decap_terminal_value_flow
    hash_frontier decode_frontier compare_frontier
    decode_failed compare_failed
    decode_fail_byte buf1 buf2 compare_result
    buf3_prefix ss_source ss failv ret_fail =>
  ss = if decap_terminal_failed decode_failed compare_failed
       then decap_mask_zero_ss
       else ss_source.
proof.
  move=> [_ [_ [Hmask _]]].
  exact (decap_mask_value_flow_selection
    (projected_ss_source_frontier hash_frontier)
    (decap_terminal_fail_frontier
      decode_frontier compare_frontier
      decode_failed compare_failed
      decode_fail_byte buf1 buf2 compare_result)
    ss_source
    (decap_terminal_failed decode_failed compare_failed)
    failv ss Hmask).
qed.

lemma decap_terminal_value_flow_selection_from_prefix
    (hash_frontier : W8.t Array224.t -> bool)
    (decode_frontier : bool -> W8.t -> bool)
    (compare_frontier :
      W8.t Array1152.t -> W8.t Array1152.t -> bool -> W64.t -> bool)
    (decode_failed compare_failed : bool)
    (decode_fail_byte : W8.t)
    (buf1 buf2 : W8.t Array1152.t)
    (compare_result : W64.t)
    (buf3_prefix : W8.t Array224.t)
    (ss_source ss : W8.t Array32.t)
    (failv ret_fail : W8.t) :
  decap_terminal_value_flow
    hash_frontier decode_frontier compare_frontier
    decode_failed compare_failed
    decode_fail_byte buf1 buf2 compare_result
    buf3_prefix ss_source ss failv ret_fail =>
  ss = if decap_terminal_failed decode_failed compare_failed
       then decap_mask_zero_ss
       else decap_mask_ss_source buf3_prefix.
proof.
  move=> Hflow.
  rewrite (decap_terminal_value_flow_selection
    hash_frontier decode_frontier compare_frontier
    decode_failed compare_failed
    decode_fail_byte buf1 buf2 compare_result
    buf3_prefix ss_source ss failv ret_fail Hflow).
  case (decap_terminal_failed decode_failed compare_failed); first done.
  by rewrite (decap_terminal_value_flow_source_exact
    hash_frontier decode_frontier compare_frontier
    decode_failed compare_failed
    decode_fail_byte buf1 buf2 compare_result
    buf3_prefix ss_source ss failv ret_fail Hflow).
qed.

lemma decap_terminal_correlated_outcome
    (hash_frontier :
      bool ->
      W8.t Array1152.t ->
      W8.t Array96.t ->
      W8.t Array32.t ->
      W8.t Array224.t -> bool)
    (decode_frontier : bool -> W8.t -> bool)
    (compare_frontier :
      W8.t Array1152.t -> W8.t Array1152.t -> bool -> W64.t -> bool)
    (decode_failed compare_failed : bool)
    (decode_fail_byte : W8.t)
    (buf1 buf2 : W8.t Array1152.t)
    (msg : W8.t Array96.t)
    (suffix : W8.t Array32.t)
    (compare_result : W64.t)
    (buf3_prefix : W8.t Array224.t)
    (ss_source ss : W8.t Array32.t)
    (failv ret_fail : W8.t) :
  decap_terminal_correlated_value_flow
    hash_frontier decode_frontier compare_frontier
    decode_failed compare_failed
    decode_fail_byte buf1 buf2
    msg suffix compare_result
    buf3_prefix ss_source ss failv ret_fail =>
  (ret_fail = W8.of_int 0 <=> ! decode_failed /\ buf1 = buf2) /\
  (ret_fail = W8.of_int 1 <=> decode_failed \/ buf1 <> buf2) /\
  ss_source = decap_mask_ss_source buf3_prefix /\
  ss =
    if decode_failed \/ buf1 <> buf2
    then decap_mask_zero_ss
    else decap_mask_ss_source buf3_prefix.
proof.
  move=> Hflow.
  have Hzero :=
    decap_terminal_value_flow_return_zero_iff
      (decap_terminal_correlated_hash_frontier
        hash_frontier decode_failed buf1 msg suffix)
      decode_frontier compare_frontier
      decode_failed compare_failed
      decode_fail_byte buf1 buf2 compare_result
      buf3_prefix ss_source ss failv ret_fail Hflow.
  have Hone :=
    decap_terminal_value_flow_return_one_iff
      (decap_terminal_correlated_hash_frontier
        hash_frontier decode_failed buf1 msg suffix)
      decode_frontier compare_frontier
      decode_failed compare_failed
      decode_fail_byte buf1 buf2 compare_result
      buf3_prefix ss_source ss failv ret_fail Hflow.
  have Hsrc :=
    decap_terminal_value_flow_source_exact
      (decap_terminal_correlated_hash_frontier
        hash_frontier decode_failed buf1 msg suffix)
      decode_frontier compare_frontier
      decode_failed compare_failed
      decode_fail_byte buf1 buf2 compare_result
      buf3_prefix ss_source ss failv ret_fail Hflow.
  have Hfailed :=
    decap_terminal_value_flow_failed_iff
      (decap_terminal_correlated_hash_frontier
        hash_frontier decode_failed buf1 msg suffix)
      decode_frontier compare_frontier
      decode_failed compare_failed
      decode_fail_byte buf1 buf2 compare_result
      buf3_prefix ss_source ss failv ret_fail Hflow.
  have Hsel :=
    decap_terminal_value_flow_selection_from_prefix
      (decap_terminal_correlated_hash_frontier
        hash_frontier decode_failed buf1 msg suffix)
      decode_frontier compare_frontier
      decode_failed compare_failed
      decode_fail_byte buf1 buf2 compare_result
      buf3_prefix ss_source ss failv ret_fail Hflow.
  by smt().
qed.

lemma decap_terminal_value_flow_byte_selection
    (hash_frontier : W8.t Array224.t -> bool)
    (decode_frontier : bool -> W8.t -> bool)
    (compare_frontier :
      W8.t Array1152.t -> W8.t Array1152.t -> bool -> W64.t -> bool)
    (decode_failed compare_failed : bool)
    (decode_fail_byte : W8.t)
    (buf1 buf2 : W8.t Array1152.t)
    (compare_result : W64.t)
    (buf3_prefix : W8.t Array224.t)
    (ss_source ss : W8.t Array32.t)
    (failv ret_fail : W8.t)
    (i : int) :
  decap_terminal_value_flow
    hash_frontier decode_frontier compare_frontier
    decode_failed compare_failed
    decode_fail_byte buf1 buf2 compare_result
    buf3_prefix ss_source ss failv ret_fail =>
  0 <= i < 32 =>
  ss.[i] =
    if decap_terminal_failed decode_failed compare_failed
    then W8.zero
    else ss_source.[i].
proof.
  move=> [_ [_ [Hmask _]]] Hi.
  exact (decap_mask_value_flow_byte_selection
    (projected_ss_source_frontier hash_frontier)
    (decap_terminal_fail_frontier
      decode_frontier compare_frontier
      decode_failed compare_failed
      decode_fail_byte buf1 buf2 compare_result)
    ss_source
    (decap_terminal_failed decode_failed compare_failed)
    failv ss i Hmask Hi).
qed.

lemma decap_terminal_value_flow_success_pair
    (hash_frontier : W8.t Array224.t -> bool)
    (decode_frontier : bool -> W8.t -> bool)
    (compare_frontier :
      W8.t Array1152.t -> W8.t Array1152.t -> bool -> W64.t -> bool)
    (decode_failed compare_failed : bool)
    (decode_fail_byte : W8.t)
    (buf1 buf2 : W8.t Array1152.t)
    (compare_result : W64.t)
    (buf3_prefix : W8.t Array224.t)
    (ss_source ss : W8.t Array32.t)
    (failv ret_fail : W8.t) :
  decap_terminal_value_flow
    hash_frontier decode_frontier compare_frontier
    decode_failed compare_failed
    decode_fail_byte buf1 buf2 compare_result
    buf3_prefix ss_source ss failv ret_fail =>
  ! decode_failed /\ buf1 = buf2 =>
  ss = ss_source /\ ret_fail = W8.of_int 0.
proof.
  move=> Hflow Hsuccess.
  have Hzero :=
    decap_terminal_value_flow_return_zero_iff
      hash_frontier decode_frontier compare_frontier
      decode_failed compare_failed
      decode_fail_byte buf1 buf2 compare_result
      buf3_prefix ss_source ss failv ret_fail Hflow.
  have Hret0 : ret_fail = W8.of_int 0 by smt().
  split; last exact Hret0.
  have Hselect :=
    decap_terminal_value_flow_selection
      hash_frontier decode_frontier compare_frontier
      decode_failed compare_failed
      decode_fail_byte buf1 buf2 compare_result
      buf3_prefix ss_source ss failv ret_fail Hflow.
  have Hfailed :
      decap_terminal_failed decode_failed compare_failed = false.
  + have Hiff :=
      decap_terminal_value_flow_failed_iff
        hash_frontier decode_frontier compare_frontier
        decode_failed compare_failed
        decode_fail_byte buf1 buf2 compare_result
        buf3_prefix ss_source ss failv ret_fail Hflow.
    smt().
  by rewrite Hselect Hfailed.
qed.

lemma decap_terminal_value_flow_failure_pair
    (hash_frontier : W8.t Array224.t -> bool)
    (decode_frontier : bool -> W8.t -> bool)
    (compare_frontier :
      W8.t Array1152.t -> W8.t Array1152.t -> bool -> W64.t -> bool)
    (decode_failed compare_failed : bool)
    (decode_fail_byte : W8.t)
    (buf1 buf2 : W8.t Array1152.t)
    (compare_result : W64.t)
    (buf3_prefix : W8.t Array224.t)
    (ss_source ss : W8.t Array32.t)
    (failv ret_fail : W8.t) :
  decap_terminal_value_flow
    hash_frontier decode_frontier compare_frontier
    decode_failed compare_failed
    decode_fail_byte buf1 buf2 compare_result
    buf3_prefix ss_source ss failv ret_fail =>
  decode_failed \/ buf1 <> buf2 =>
  ss = decap_mask_zero_ss /\ ret_fail = W8.of_int 1.
proof.
  move=> Hflow Hfailure.
  have Hone :=
    decap_terminal_value_flow_return_one_iff
      hash_frontier decode_frontier compare_frontier
      decode_failed compare_failed
      decode_fail_byte buf1 buf2 compare_result
      buf3_prefix ss_source ss failv ret_fail Hflow.
  have Hret1 : ret_fail = W8.of_int 1 by smt().
  split; last exact Hret1.
  have Hselect :=
    decap_terminal_value_flow_selection
      hash_frontier decode_frontier compare_frontier
      decode_failed compare_failed
      decode_fail_byte buf1 buf2 compare_result
      buf3_prefix ss_source ss failv ret_fail Hflow.
  have Hfailed :
      decap_terminal_failed decode_failed compare_failed = true.
  + have Hiff :=
      decap_terminal_value_flow_failed_iff
        hash_frontier decode_frontier compare_frontier
        decode_failed compare_failed
        decode_fail_byte buf1 buf2 compare_result
        buf3_prefix ss_source ss failv ret_fail Hflow.
    smt().
  by rewrite Hselect Hfailed.
qed.

lemma finish_functional_from_value_flow
    (hash_frontier : W8.t Array224.t -> bool)
    (decode_frontier : bool -> W8.t -> bool)
    (compare_frontier :
      W8.t Array1152.t -> W8.t Array1152.t -> bool -> W64.t -> bool)
    (decode_failed compare_failed : bool)
    (decode_fail_byte : W8.t)
    (buf1 buf2 : W8.t Array1152.t)
    (compare_result : W64.t)
    (buf3_prefix : W8.t Array224.t)
    (ss_source ss : W8.t Array32.t)
    (failv ret_fail : W8.t) :
  decap_terminal_value_flow
    hash_frontier decode_frontier compare_frontier
    decode_failed compare_failed
    decode_fail_byte buf1 buf2 compare_result
    buf3_prefix ss_source ss failv ret_fail =>
  hoare [DecapTerminal.finish :
    arg = (ss_source, failv) ==>
      res.`1 = ss /\ res.`2 = ret_fail].
proof.
  move=> [_ [_ [Hmask ->]]].
  move: Hmask => [_ [_ [_ ->]]].
  exact (finish_functional ss_source failv).
qed.

lemma finish_correct_from_value_flow
    (hash_frontier : W8.t Array224.t -> bool)
    (decode_frontier : bool -> W8.t -> bool)
    (compare_frontier :
      W8.t Array1152.t -> W8.t Array1152.t -> bool -> W64.t -> bool)
    (decode_failed compare_failed : bool)
    (decode_fail_byte : W8.t)
    (buf1 buf2 : W8.t Array1152.t)
    (compare_result : W64.t)
    (buf3_prefix : W8.t Array224.t)
    (ss_source ss : W8.t Array32.t)
    (failv ret_fail : W8.t) :
  decap_terminal_value_flow
    hash_frontier decode_frontier compare_frontier
    decode_failed compare_failed
    decode_fail_byte buf1 buf2 compare_result
    buf3_prefix ss_source ss failv ret_fail =>
  phoare [DecapTerminal.finish :
    arg = (ss_source, failv) ==>
      res.`1 = ss /\ res.`2 = ret_fail] = 1%r.
proof.
  move=> [_ [_ [Hmask ->]]].
  move: Hmask => [_ [_ [_ ->]]].
  exact (finish_correct ss_source failv).
qed.
