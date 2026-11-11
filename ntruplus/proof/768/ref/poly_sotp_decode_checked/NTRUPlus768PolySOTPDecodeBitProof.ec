require import AllCore IntDiv List Distr Ring StdOrder.
from Jasmin require import JWord JModel_x86.
require import Array96 Array192 Array768 NTRUPlus768PolySOTPDecodeChecked.
require import NTRUPlus768PolySOTPDecodeAlgebra NTRUPlus768PolySOTPDecodeWords NTRUPlus768PolySOTPDecodeFlag.

op sotp_partial (a : W16.t Array768.t) (buf : W8.t Array192.t) (i j : int)
    (t1 t2 : W8.t) (t3 : W16.t) (r : W32.t) : bool =
  t1 = buf.[i] `>>>` j /\ t2 = buf.[96+i] `>>>` j /\
  t3 = W16.of_int (sotp_packed a buf i j) /\
  W32.to_uint r < 65536 /\
  (W32.to_uint r <= 1 <=> sotp_valid_until a buf (8*i+j)).

lemma sotp_decode_bit_partial a buf0 i j :
  hoare [NTRUPlus768PolySOTPDecodeChecked.M.__decode_bit :
    poly_sotp_trit_input a /\ 0 <= i < 96 /\ 0 <= j < 8 /\
    coeff = a.[8*i+j] /\ sHIFT=j /\ sotp_partial a buf0 i j t1 t2 t3 r ==>
    sotp_partial a buf0 i (j+1) res.`1 res.`2 res.`3 res.`4].
proof.
  proc; auto => /> &hr ht hi0 hi96 hj0 hj8 hr hv.
  have hi : 0 <= i < 96 by smt().
  have hj : 0 <= j < 8 by smt().
  rewrite /W8.(`>>`) /W16.(`<<`) /=.
  have hjmod : j %% 256 = j by rewrite modz_small; smt().
  rewrite hjmod !W8.shrw_add 1,2,3,4:/# /=.
  rewrite sotp_lowbit_int !sotp_shift_bit 1,2:hj.
  rewrite -/poly_sotp_head_bit -/poly_sotp_tail_bit -/poly_sotp_sum_int -/poly_sotp_decoded_bit_int.
  have hpbound := sotp_packed_bound a buf0 i j hi _; first smt().
  have hjpow : 2^j <= 128 by apply (StdOrder.IntOrder.ler_weexpn2l 2 _ j 7); smt().
  have hpuint : W16.to_uint (W16.of_int (sotp_packed a buf0 i j)) = sotp_packed a buf0 i j.
  + rewrite W16.of_uintK modz_small; smt().
  have hbit := poly_sotp_decoded_bit_bound a buf0 i j hi.
  rewrite sotp_pack_uint 1:hj 1:/# 1:hbit hpuint -sotp_packedS 1:/#.
  rewrite sotp_sum_word !sotp_shift_bit 1:hj -/poly_sotp_tail_bit -/poly_sotp_sum_int.
  have hrange : W32.to_uint (zeroextu32 (W16.of_int (poly_sotp_sum_int a buf0 i j))) < 65536.
  + rewrite W2u16.to_uint_zeroextu32.
    have /= hh := W16.to_uint_cmp (W16.of_int (poly_sotp_sum_int a buf0 i j)); smt().
  have hsum : NTRUPlus768BasemulAlgebra.coeff a.[8*i+j] + poly_sotp_bit buf0.[96+i] j = poly_sotp_sum_int a buf0 i j by done.
  rewrite hsum.
  have hgood := sotp_sum_word_valid a buf0 i j ht hi hj.
  have hnext := sotp_valid_untilS a buf0 i j hi hj.
  have hrange2 := sotp_or_range _ _ hr hrange.
  have hvalid := sotp_or_valid r{hr} (zeroextu32 (W16.of_int (poly_sotp_sum_int a buf0 i j))).
  rewrite (_ : 8*i+(j+1)=8*i+j+1) 1:/# hnext.
  rewrite hrange2 /=.
  rewrite hvalid hgood hv.
  done.
qed.

lemma sotp_decode_bit_lossless : islossless NTRUPlus768PolySOTPDecodeChecked.M.__decode_bit.
proof. by proc; auto. qed.
