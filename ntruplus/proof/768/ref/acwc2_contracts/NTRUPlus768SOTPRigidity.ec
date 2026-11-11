require import AllCore IntDiv Ring StdOrder List BitEncoding.
from Jasmin require import JWord JModel_x86 JUtils.
require import Array96 Array192 Array768.
require import NTRUPlus768BasemulAlgebra NTRUPlus768Crepmod3Algebra.
require import NTRUPlus768PolySOTPDecodeAlgebra NTRUPlus768PolySOTPEncodeAlgebra.
require import NTRUPlus768PolySOTPRoundTrip NTRUPlus768PolyCBD1Algebra.
import Ring.IntID IntOrder.

lemma sotp_raw_message_byte a pad i : 0<=i<96 =>
 (poly_sotp_raw_msg_spec a pad).[i] =
 W8.bits2w (mkseq (fun j=>poly_sotp_decoded_bit_int a pad i j=1) 8).
proof.
 move=>hi.
 have h0:=poly_sotp_decoded_bit_bound a pad i 0 hi.
 have h1:=poly_sotp_decoded_bit_bound a pad i 1 hi.
 have h2:=poly_sotp_decoded_bit_bound a pad i 2 hi.
 have h3:=poly_sotp_decoded_bit_bound a pad i 3 hi.
 have h4:=poly_sotp_decoded_bit_bound a pad i 4 hi.
 have h5:=poly_sotp_decoded_bit_bound a pad i 5 hi.
 have h6:=poly_sotp_decoded_bit_bound a pad i 6 hi.
 have h7:=poly_sotp_decoded_bit_bound a pad i 7 hi.
 rewrite /poly_sotp_raw_msg_spec Array96.initiE 1:hi.
 apply W8.to_uint_eq.
 rewrite W8.of_uintK /= (modz_small _ 256 (poly_sotp_raw_byte_int_range a pad i hi)).
 rewrite W8.to_uintE W8.bits2wK; first by rewrite size_mkseq.
 rewrite /mkseq -iotaredE /=.
 rewrite !JUtils.bs2int_cons BS2Int.bs2int_nil /poly_sotp_raw_byte_int /b2i /=.
 smt().
qed.

lemma sotp_raw_message_bit a pad i j :
 0<=i<96 => 0<=j<8 =>
 poly_sotp_bit (poly_sotp_raw_msg_spec a pad).[i] j =
 poly_sotp_decoded_bit_int a pad i j.
proof.
 move=>hi hj.
 rewrite (sotp_raw_message_byte a pad i hi) poly_sotp_bit_b2i 1:hj
   W8.get_bits2w 1:hj nth_mkseq 1:hj /=.
 have hb:=poly_sotp_decoded_bit_bound a pad i j hi.
 rewrite /b2i; smt().
qed.

lemma sotp_xor_decode_cancel (b:W8.t) j v :
 0<=j<8 => (v=0 \/ v=1) =>
 b2i (Bool.(^^) b.[j] ((v+poly_sotp_bit b j) %% 2 = 1)) = v.
proof.
 move=>hj hv; rewrite poly_sotp_bit_b2i 1:hj.
 case hv=>->; case b.[j]; done.
qed.

lemma sotp_decode_encode_coefficient a pad i j :
 !poly_sotp_decode_fail_spec a pad => 0<=i<96 => 0<=j<8 =>
 coeff (poly_sotp_encode_spec (poly_sotp_decode_msg_spec a pad) pad).[8*i+j] =
 coeff a.[8*i+j].
proof.
 move=>hs hi hj.
 have hv:=poly_sotp_decode_success_valid a pad.
 have hvij:poly_sotp_sum_valid a pad i j by smt().
 have hb:=sotp_raw_message_bit a pad i j hi hj.
 have hd: (poly_sotp_raw_msg_spec a pad).[i].[j] =
   (poly_sotp_decoded_bit_int a pad i j=1).
 + rewrite poly_sotp_bit_b2i 1:hj in hb; smt().
 rewrite (poly_sotp_decode_success_raw a pad hs)
   poly_sotp_encode_spec_coeff 1:hi 1:hj poly_sotp_bit_b2i 1:hj W8.xorwE hd.
 rewrite /poly_sotp_decoded_bit_int /poly_sotp_head_bit.
 rewrite (sotp_xor_decode_cancel pad.[i] j (poly_sotp_sum_int a pad i j) hj hvij).
 by rewrite /poly_sotp_sum_int /poly_sotp_tail_bit; ring.
qed.

(* Reverse recovery is a statement about successful decoding, not the
   zeroed output used by a failure. The pure success predicate also
   implies that the coefficient array lies in the trit domain. *)
lemma sotp_decode_encode_rigidity a pad :
 !poly_sotp_decode_fail_spec a pad =>
 poly_sotp_encode_spec (poly_sotp_decode_msg_spec a pad) pad = a.
proof.
 move=>hs; apply Array768.tP=>k hk.
 have hi:0<=k %/8<96 by smt().
 have hj:0<=k %%8<8 by smt().
 have hidx:8*(k %/8)+k %%8=k by smt(divz_eq).
 have hc:=sotp_decode_encode_coefficient a pad (k %/8) (k %%8) hs hi hj.
 rewrite hidx in hc.
 rewrite (NTRUPlus768Crepmod3Algebra.word_from_coeff (poly_sotp_encode_spec (poly_sotp_decode_msg_spec a pad) pad).[k])
   (NTRUPlus768Crepmod3Algebra.word_from_coeff a.[k]) hc.
 done.
qed.

lemma sotp_decode_success_trits a pad :
 !poly_sotp_decode_fail_spec a pad => poly_sotp_trit_input a.
proof.
 move=>hs; rewrite -(sotp_decode_encode_rigidity a pad hs) /poly_sotp_encode_spec.
 exact(poly_cbd1_spec_sotp_trit_input _).
qed.
