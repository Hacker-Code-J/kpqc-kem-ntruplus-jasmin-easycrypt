require import AllCore IntDiv List Ring StdOrder.
from Jasmin require import JWord JModel_x86.
require import Array96 Array192 Array768.
require import NTRUPlus768PolySOTPDecodeAlgebra.
require NTRUPlus768PolyToBytesProof.

import IntOrder.

lemma sotp_mask_lowbit (x : W16.t) :
  x `&` W16.one = W16.of_int (W16.to_uint x %% 2).
proof. by rewrite (W16.and_mod 1) 1:// /=. qed.

lemma sotp_xor_lowbit (x y : W16.t) :
  (x `^` y) `&` W16.one =
    W16.of_int ((W16.to_uint x + W16.to_uint y) %% 2).
proof.
  rewrite W16.andwDl !sotp_mask_lowbit.
  have hx : W16.to_uint x %% 2 = 0 \/ W16.to_uint x %% 2 = 1 by smt(modz_cmp).
  have hy : W16.to_uint y %% 2 = 0 \/ W16.to_uint y %% 2 = 1 by smt(modz_cmp).
  rewrite -modzDm.
  case hx => ->; case hy => ->; done.
qed.

lemma sotp_shift_bit (b : W8.t) (j : int) : 0 <= j < 8 =>
  W8.to_uint (b `>>>` j) %% 2 = poly_sotp_bit b j.
proof. move=> hj; by rewrite W8.to_uint_shr 1:/# /poly_sotp_bit. qed.

lemma sotp_sum_word (w : W16.t) (b : W8.t) :
  (zeroextu16 b `&` W16.one) + w =
    W16.of_int (NTRUPlus768BasemulAlgebra.coeff w + W8.to_uint b %% 2).
proof.
  rewrite sotp_mask_lowbit W2u8.to_uint_zeroextu16.
  rewrite {1}(NTRUPlus768PolyToBytesProof.poly_tobytes_word_from_coeff w).
  by rewrite -W16.of_intD; congr; ring.
qed.

lemma sotp_lowbit_int (w : W16.t) (b1 b2 : W8.t) :
  (((zeroextu16 b2 `&` W16.one) + w) `^` zeroextu16 b1) `&` W16.one =
  W16.of_int ((NTRUPlus768BasemulAlgebra.coeff w + W8.to_uint b2 %% 2 + W8.to_uint b1 %% 2) %% 2).
proof.
  rewrite sotp_sum_word sotp_xor_lowbit W16.of_uintK W2u8.to_uint_zeroextu16 /=.
  congr.
  rewrite -modzDm (modz_dvd _ 65536 2) 1://.
  by rewrite modzDml.
qed.

lemma sotp_pack_disjoint (x b : W16.t) j :
  0 <= j < 8 => W16.to_uint x < 2^j =>
  x `&` (b `<<<` j) = W16.zero.
proof.
  move=> hj hx; apply W16.wordP => k hk.
  rewrite W16.andwE W16.shlwE W16.zerowE.
  case (k < j) => hkj; first smt(W16.get_out).
  have hp : 2^j <= 2^k.
  + apply (IntOrder.ler_weexpn2l 2 _ j k); smt().
  have hx0 := W16.to_uint_cmp x.
  rewrite W16.get_to_uint hk /=.
  have hd : W16.to_uint x %/ 2^k = 0.
  + apply divz_small; smt(gt0_pow2).
  by rewrite hd /=.
qed.

lemma sotp_pack_uint (x : W16.t) b j :
  0 <= j < 8 => W16.to_uint x < 2^j => 0 <= b < 2 =>
  x `^` (W16.of_int b `<<<` j) = W16.of_int (W16.to_uint x + 2^j*b).
proof.
  move=> hj hx hb.
  have hd := sotp_pack_disjoint x (W16.of_int b) j hj hx.
  have he : x `^` (W16.of_int b `<<<` j) = x `|` (W16.of_int b `<<<` j).
  + by rewrite W16.orw_xorw hd W16.xorw0.
  rewrite he (W16.orw_disjoint _ _ hd).
  apply W16.to_uint_eq.
  rewrite (W16.to_uintD_disjoint _ _ hd) W16.to_uint_shl 1:/# !W16.of_uintK /=.
  have hp : 2^j <= 128.
  + apply (IntOrder.ler_weexpn2l 2 _ j 7); smt().
  have hp0 := gt0_pow2 j.
  have hu := W16.to_uint_cmp x.
  rewrite !modz_small; smt().
qed.

op sotp_packed (a : W16.t Array768.t) (buf : W8.t Array192.t) (i n : int) : int =
  foldl (fun x j => x + 2^j * poly_sotp_decoded_bit_int a buf i j) 0 (iota_ 0 n).

lemma sotp_packed0 a buf i : sotp_packed a buf i 0 = 0.
proof. by rewrite /sotp_packed iota0. qed.

lemma sotp_packedS a buf i n : 0 <= n =>
  sotp_packed a buf i (n+1) = sotp_packed a buf i n + 2^n * poly_sotp_decoded_bit_int a buf i n.
proof. by move=> hn; rewrite /sotp_packed iotaSr 1:hn foldl_rcons /=. qed.

lemma sotp_packed_bound a buf i n : 0 <= i < 96 => 0 <= n =>
  0 <= sotp_packed a buf i n < 2^n.
proof.
  move=> hi; elim/intind : n => [|n hn ih].
  + by rewrite sotp_packed0 /=.
  rewrite sotp_packedS 1:hn exprS 1:hn.
  have hb := poly_sotp_decoded_bit_bound a buf i n hi.
  have hp := gt0_pow2 n.
  have he : poly_sotp_decoded_bit_int a buf i n = 0 \/ poly_sotp_decoded_bit_int a buf i n = 1 by smt().
  case he => ->; smt().
qed.

lemma sotp_packed8 a buf i : sotp_packed a buf i 8 = poly_sotp_raw_byte_int a buf i.
proof.
  rewrite /sotp_packed /poly_sotp_raw_byte_int.
  rewrite (iotaS 0 7) 1:// /= (iotaS 1 6) 1:// /=
    (iotaS 2 5) 1:// /= (iotaS 3 4) 1:// /= (iotaS 4 3) 1:// /=
    (iotaS 5 2) 1:// /= (iotaS 6 1) 1:// /= (iotaS 7 0) 1:// /= iota0 /=.
  done. done.
qed.

op sotp_valid_until (a : W16.t Array768.t) (buf : W8.t Array192.t) (n : int) : bool =
  forall k, 0 <= k < n => poly_sotp_sum_valid a buf (k %/ 8) (k %% 8).

lemma sotp_valid_until0 a buf : sotp_valid_until a buf 0.
proof. rewrite /sotp_valid_until; smt(). qed.

lemma sotp_valid_untilS a buf i j : 0 <= i < 96 => 0 <= j < 8 =>
  sotp_valid_until a buf (8*i+j+1) =
  (sotp_valid_until a buf (8*i+j) /\ poly_sotp_sum_valid a buf i j).
proof.
  move=> hi hj.
  have he : (8*i+j) %/ 8 = i /\ (8*i+j) %% 8 = j by smt().
  rewrite /sotp_valid_until; smt().
qed.

lemma sotp_valid_until_full a buf :
  sotp_valid_until a buf 768 = !poly_sotp_decode_fail_spec a buf.
proof.
  rewrite eqboolP (poly_sotp_decode_success_valid a buf) /sotp_valid_until.
  split.
  + move=> hv i j hi hj.
    have he : (8*i+j) %/ 8 = i /\ (8*i+j) %% 8 = j by smt().
    have hh := hv (8*i+j) _; smt().
  move=> hv k hk.
  have hi : 0 <= k %/ 8 < 96 by smt().
  have hj : 0 <= k %% 8 < 8 by smt(modz_cmp).
  exact (hv _ _ hi hj).
qed.

lemma sotp_sum_word_valid a buf i j :
  poly_sotp_trit_input a => 0 <= i < 96 => 0 <= j < 8 =>
  (W32.to_uint (zeroextu32 (W16.of_int (poly_sotp_sum_int a buf i j))) <= 1) =
    poly_sotp_sum_valid a buf i j.
proof.
  move=> ht hi hj.
  have hs := poly_sotp_trit_sum_range a buf i j ht hi hj.
  rewrite W2u16.to_uint_zeroextu32 W16.of_uintK /poly_sotp_sum_valid /=.
  have he : poly_sotp_sum_int a buf i j = -1 \/ poly_sotp_sum_int a buf i j = 0 \/
    poly_sotp_sum_int a buf i j = 1 \/ poly_sotp_sum_int a buf i j = 2 by smt().
  case he => [-> | [-> | [-> | ->]]]; done.
qed.

lemma sotp_raw_mask a buf k : 0 <= k < 96 =>
  (poly_sotp_raw_msg_spec a buf).[k] `&`
    (if poly_sotp_decode_fail_spec a buf then W8.zero else W8.onew) =
  (poly_sotp_decode_msg_spec a buf).[k].
proof.
  move=> hk; rewrite /poly_sotp_decode_msg_spec.
  case (poly_sotp_decode_fail_spec a buf) => hf.
  + by rewrite W8.andw0 /poly_sotp_zero_msg_spec Array96.initiE 1:hk.
  by rewrite W8.andw1.
qed.
