require import AllCore IntDiv List Distr.
from Jasmin require import JWord JModel_x86.
require import Array2336 Array2304 Array1152 Array32 Array96 Array192 Array224 Array768.
require import NTRUPlus768DecapMessageSpec NTRUPlus768DecapMessageAlgebra.
require import NTRUPlus768DecapGuardSpec NTRUPlus768EncapGuardSpec.
require import NTRUPlus768DecapHashGBridge NTRUPlus768DecapHashHBridge.
require import NTRUPlus768PolyToBytesProof NTRUPlus768PolyCBD1Algebra.
require import NTRUPlus768PolySOTPDecodeAlgebra NTRUPlus768NTTProof NTRUPlus768NTTAlgebra.
require import NTRUPlus768NTTStage1Algebra NTRUPlus768BasemulAlgebra.

(* Exact API layout. The suffix is an input value; no provenance as HashF(pk)
   is required for functional refinement on arbitrary 2336-byte secret keys. *)
op complete_sk_poly (sk : W8.t Array2336.t) : W8.t Array2304.t =
  Array2304.init (fun i => sk.[i]).
op complete_sk_suffix (sk : W8.t Array2336.t) : W8.t Array32.t =
  Array32.init (fun i => sk.[2304+i]).
op complete_sk_join (p : W8.t Array2304.t) (s : W8.t Array32.t) : W8.t Array2336.t =
  Array2336.init (fun i => if i<2304 then p.[i] else s.[i-2304]).

lemma complete_sk_poly_byte sk i : 0<=i<2304 => (complete_sk_poly sk).[i]=sk.[i].
proof. move=> hi; by rewrite /complete_sk_poly Array2304.initiE. qed.
lemma complete_sk_suffix_byte sk i : 0<=i<32 => (complete_sk_suffix sk).[i]=sk.[2304+i].
proof. move=> hi; by rewrite /complete_sk_suffix Array32.initiE. qed.
lemma complete_sk_layout sk : complete_sk_join (complete_sk_poly sk) (complete_sk_suffix sk) = sk.
proof.
  apply Array2336.tP => i hi; rewrite /complete_sk_join Array2336.initiE //.
  case (i<2304) => hc.
  + by rewrite hc complete_sk_poly_byte 1:/#.
  rewrite hc complete_sk_suffix_byte 1:/#; smt().
qed.

op complete_hash_tail (h : W8.t Array224.t) : W8.t Array192.t =
  Array192.init (fun i => h.[32+i]).
op complete_regenerated (h : W8.t Array224.t) : W8.t Array1152.t =
  poly_tobytes_spec (ntt_spec (poly_cbd1_spec (complete_hash_tail h))).
op complete_selected (h : W8.t Array224.t) (failed : bool) : W8.t Array32.t =
  if failed then encap_zero_ss else Array32.init (fun i => h.[i]).
op complete_tail_reject (bs : W8.t Array1152.t) (msg : W8.t Array96.t)
    (df : bool) (suffix : W8.t Array32.t) : bool =
  df \/ bs <> complete_regenerated (hash_h_spec msg suffix).
op complete_tail_spec (bs : W8.t Array1152.t) (msg : W8.t Array96.t)
    (df : bool) (suffix : W8.t Array32.t) : W8.t Array32.t * W32.t =
  (complete_selected (hash_h_spec msg suffix) (complete_tail_reject bs msg df suffix),
   W32.of_int (b2i (complete_tail_reject bs msg df suffix))).

op complete_entry_accepts ct sk =
  decap_guard_accepts ct (decap_fbytes (complete_sk_poly sk)) (decap_hbytes (complete_sk_poly sk)).
op complete_message_result ct sk =
  decap_message_spec (message_r2 ct (complete_sk_poly sk)) (message_candidate ct (complete_sk_poly sk)).
op complete_sotp_failed ct sk =
  poly_sotp_decode_fail_spec (message_candidate ct (complete_sk_poly sk))
    (hash_g_spec (poly_tobytes_spec (message_r2 ct (complete_sk_poly sk)))).
op complete_spec ct sk : W8.t Array32.t * W32.t =
  if complete_entry_accepts ct sk then
    complete_tail_spec (complete_message_result ct sk).`1 (complete_message_result ct sk).`2
      (complete_sotp_failed ct sk) (complete_sk_suffix sk)
  else (encap_zero_ss,W32.one).
op complete_accepts ct sk =
  complete_entry_accepts ct sk /\
  !complete_tail_reject (complete_message_result ct sk).`1 (complete_message_result ct sk).`2
    (complete_sotp_failed ct sk) (complete_sk_suffix sk).

lemma complete_message_status ct sk :
  (complete_message_result ct sk).`3 = W32.of_int (b2i (complete_sotp_failed ct sk)).
proof. by rewrite /complete_message_result /decap_message_spec /complete_sotp_failed. qed.

lemma complete_regeneration_qrange h :
  poly_tobytes_input_qrange (ntt_spec (poly_cbd1_spec (complete_hash_tail h))).
proof.
  move=> j hj; rewrite ntt_specE.
  exact (forward_ntt_centered_coeff_range _ j (poly_cbd1_spec_input_qrange _) hj).
qed.

lemma complete_reject_result ct sk : !complete_accepts ct sk => complete_spec ct sk=(encap_zero_ss,W32.one).
proof.
  rewrite /complete_accepts /complete_spec.
  case (complete_entry_accepts ct sk) => he /=; last done.
  rewrite /complete_tail_spec /complete_selected; smt().
qed.

lemma complete_accept_result ct sk : complete_accepts ct sk =>
  complete_spec ct sk =
  (Array32.init (fun i => (hash_h_spec (complete_message_result ct sk).`2 (complete_sk_suffix sk)).[i]),W32.zero).
proof.
  rewrite /complete_accepts; move=> [he ht].
  by rewrite /complete_spec he /complete_tail_spec /complete_selected ht /=.
qed.

lemma complete_flag_boolean ct sk :
  (complete_spec ct sk).`2=W32.zero \/ (complete_spec ct sk).`2=W32.one.
proof.
  case (complete_accepts ct sk) => ha.
  + by rewrite (complete_accept_result ct sk ha).
  by rewrite (complete_reject_result ct sk ha).
qed.

lemma complete_failure_zero ct sk : (complete_spec ct sk).`2=W32.one =>
  (complete_spec ct sk).`1=encap_zero_ss.
proof.
  case (complete_accepts ct sk) => ha.
  + rewrite (complete_accept_result ct sk ha); smt(W32.to_uint0 W32.to_uint1).
  by rewrite (complete_reject_result ct sk ha).
qed.

lemma complete_status_zero ct sk :
  ((complete_spec ct sk).`2=W32.zero) = complete_accepts ct sk.
proof.
  case (complete_accepts ct sk) => ha.
  + by rewrite (complete_accept_result ct sk ha).
  rewrite (complete_reject_result ct sk ha); smt(W32.to_uint0 W32.to_uint1).
qed.
