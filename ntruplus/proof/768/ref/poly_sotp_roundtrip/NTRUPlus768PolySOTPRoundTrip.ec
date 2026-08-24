require import AllCore BitEncoding IntDiv List Ring StdOrder.
from Jasmin require import JWord JModel_x86 JUtils.

require import Array96 Array192.
require import NTRUPlus768PolySOTPDecodeAlgebra.
require import NTRUPlus768PolySOTPEncodeAlgebra.

import BS2Int Ring.IntID IntOrder.

(* Encode/decode inverse at the array-value seam only.  No C/Jasmin procedure,
   NTT/ciphertext relation, r recovery, or hash_g/hash_h claim is made here. *)

lemma xor_b2i_cancel_mod2 (x y : bool) :
  (b2i (Bool.(^^) x y) + b2i x) %% 2 = b2i y.
proof. by case: x; case: y. qed.

lemma poly_sotp_encode_decoded_bit
    (msg : W8.t Array96.t)
    (pad : W8.t Array192.t)
    (i j : int) :
  0 <= i < 96 =>
  0 <= j < 8 =>
  NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_decoded_bit_int
    (NTRUPlus768PolySOTPEncodeAlgebra.poly_sotp_encode_spec msg pad)
    pad i j =
  NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_bit msg.[i] j.
proof.
  move=> Hi Hj.
  rewrite /NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_decoded_bit_int.
  rewrite NTRUPlus768PolySOTPEncodeAlgebra.poly_sotp_encode_sum_int_xor 1:Hi 1:Hj.
  rewrite /NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_head_bit.
  rewrite NTRUPlus768PolySOTPEncodeAlgebra.poly_sotp_bit_b2i 1:Hj.
  rewrite NTRUPlus768PolySOTPEncodeAlgebra.poly_sotp_bit_b2i 1:Hj.
  exact (xor_b2i_cancel_mod2 pad.[i].[j] msg.[i].[j]).
qed.

lemma poly_sotp_encode_raw_byte_int
    (msg : W8.t Array96.t)
    (pad : W8.t Array192.t)
    (i : int) :
  0 <= i < 96 =>
  NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_raw_byte_int
    (NTRUPlus768PolySOTPEncodeAlgebra.poly_sotp_encode_spec msg pad)
    pad i =
  W8.to_uint msg.[i].
proof.
  move=> Hi.
  rewrite /NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_raw_byte_int.
  rewrite (poly_sotp_encode_decoded_bit msg pad i 0) 1:Hi 1:/#.
  rewrite (poly_sotp_encode_decoded_bit msg pad i 1) 1:Hi 1:/#.
  rewrite (poly_sotp_encode_decoded_bit msg pad i 2) 1:Hi 1:/#.
  rewrite (poly_sotp_encode_decoded_bit msg pad i 3) 1:Hi 1:/#.
  rewrite (poly_sotp_encode_decoded_bit msg pad i 4) 1:Hi 1:/#.
  rewrite (poly_sotp_encode_decoded_bit msg pad i 5) 1:Hi 1:/#.
  rewrite (poly_sotp_encode_decoded_bit msg pad i 6) 1:Hi 1:/#.
  rewrite (poly_sotp_encode_decoded_bit msg pad i 7) 1:Hi 1:/#.
  rewrite !NTRUPlus768PolySOTPEncodeAlgebra.poly_sotp_bit_b2i 1..8:/#.
  rewrite W8.to_uintE.
  have -> :
      W8.w2bits msg.[i] =
      msg.[i].[0] :: msg.[i].[1] :: msg.[i].[2] :: msg.[i].[3] ::
      msg.[i].[4] :: msg.[i].[5] :: msg.[i].[6] :: msg.[i].[7] ::
      []
    by rewrite /w2bits /bits /mkseq -iotaredE /=.
  rewrite !JUtils.bs2int_cons bs2int_nil /=.
  ring.
qed.

lemma poly_sotp_encode_raw_byte
    (msg : W8.t Array96.t)
    (pad : W8.t Array192.t)
    (i : int) :
  0 <= i < 96 =>
  (NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_raw_msg_spec
    (NTRUPlus768PolySOTPEncodeAlgebra.poly_sotp_encode_spec msg pad)
    pad).[i] = msg.[i].
proof.
  move=> Hi.
  rewrite /NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_raw_msg_spec Array96.initiE 1:Hi.
  apply W8.to_uint_eq.
  rewrite W8.of_uintK.
  rewrite poly_sotp_encode_raw_byte_int 1:Hi.
  by rewrite modz_small 1:(W8.to_uint_cmp msg.[i]).
qed.

lemma poly_sotp_encode_raw_msg
    (msg : W8.t Array96.t)
    (pad : W8.t Array192.t) :
  NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_raw_msg_spec
    (NTRUPlus768PolySOTPEncodeAlgebra.poly_sotp_encode_spec msg pad)
    pad = msg.
proof.
  apply Array96.tP => i Hi.
  exact (poly_sotp_encode_raw_byte msg pad i Hi).
qed.

lemma poly_sotp_encode_decode_msg
    (msg : W8.t Array96.t)
    (pad : W8.t Array192.t) :
  NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_decode_msg_spec
    (NTRUPlus768PolySOTPEncodeAlgebra.poly_sotp_encode_spec msg pad)
    pad = msg.
proof.
  rewrite NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_decode_success_raw.
  + exact (NTRUPlus768PolySOTPEncodeAlgebra.poly_sotp_encode_fail_spec msg pad).
  + exact (poly_sotp_encode_raw_msg msg pad).
qed.

lemma poly_sotp_encode_decode_spec
    (msg : W8.t Array96.t)
    (pad : W8.t Array192.t) :
  NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_decode_spec
    (NTRUPlus768PolySOTPEncodeAlgebra.poly_sotp_encode_spec msg pad)
    pad = (msg, false).
proof.
  rewrite /NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_decode_spec.
  rewrite poly_sotp_encode_decode_msg.
  rewrite NTRUPlus768PolySOTPEncodeAlgebra.poly_sotp_encode_fail_spec_false.
  done.
qed.

lemma poly_sotp_encode_decode_roundtrip
    (msg : W8.t Array96.t)
    (pad : W8.t Array192.t) :
  NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_decode_spec
    (NTRUPlus768PolySOTPEncodeAlgebra.poly_sotp_encode_spec msg pad)
    pad = (msg, false).
proof. exact (poly_sotp_encode_decode_spec msg pad). qed.
