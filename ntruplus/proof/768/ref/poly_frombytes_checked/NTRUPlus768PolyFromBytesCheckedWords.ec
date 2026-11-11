require import AllCore IntDiv List Ring StdOrder.
from Jasmin require import JWord JModel_x86.
require import Array768 Array1152 NTRUPlus768CanonicalDecoder.
require NTRUPlus768PolyToBytesProof.

op checked_even_word (b0 b1 : W8.t) : W16.t =
  (zeroextu16 b0 `|` (zeroextu16 b1 `<<` W8.of_int 8)) `&` W16.of_int 4095.

op checked_odd_word (b1 b2 : W8.t) : W16.t =
  ((zeroextu16 b1 `>>` W8.of_int 4) `|`
    (zeroextu16 b2 `<<` W8.of_int 4)) `&` W16.of_int 4095.

lemma checked_even_wordE b0 b1 :
  checked_even_word b0 b1 = W16.of_int (W8.to_uint b0 + 256 * (W8.to_uint b1 %% 16)).
proof.
  have /= hb0 := W8.to_uint_cmp b0.
  have /= hb1 := W8.to_uint_cmp b1.
  rewrite /checked_even_word W16.orw_disjoint.
  + apply W16.wordP => k hk.
    rewrite W16.andwE /W16.(`<<`) W16.shlwE
      !W2u8.zeroextu16_bit W16.zerowE /=.
    smt().
  apply W16.to_uint_eq.
  rewrite (W16.to_uint_and_mod 12) 1:// /= W16.to_uintD_small.
  + rewrite /W16.(`<<`) W16.to_uint_shl 1://
      !W2u8.to_uint_zeroextu16 /=; smt().
  rewrite /W16.(`<<`) W16.to_uint_shl 1://
    !W2u8.to_uint_zeroextu16 W16.of_uintK /=.
  smt().
qed.

lemma checked_odd_wordE b1 b2 :
  checked_odd_word b1 b2 = W16.of_int (W8.to_uint b1 %/ 16 + 16 * W8.to_uint b2).
proof.
  have /= hb1 := W8.to_uint_cmp b1.
  have /= hb2 := W8.to_uint_cmp b2.
  rewrite /checked_odd_word W16.orw_disjoint.
  + apply W16.wordP => k hk.
    rewrite W16.andwE /W16.(`<<`) /W16.(`>>`) W16.shlwE W16.shrwE
      !W2u8.zeroextu16_bit W16.zerowE /=.
    smt().
  apply W16.to_uint_eq.
  rewrite (W16.to_uint_and_mod 12) 1:// /= W16.to_uintD_small.
  + rewrite /W16.(`<<`) /W16.(`>>`) W16.to_uint_shl 1:// W16.to_uint_shr 1://
      !W2u8.to_uint_zeroextu16 /=; smt().
  rewrite /W16.(`<<`) /W16.(`>>`) W16.to_uint_shl 1:// W16.to_uint_shr 1://
    !W2u8.to_uint_zeroextu16 W16.of_uintK /=.
  smt().
qed.

lemma checked_zeroext32_of_int t : 0 <= t < 4096 =>
  zeroextu32 (W16.of_int t) = W32.of_int t.
proof.
  move=> ht; apply W32.to_uint_eq.
  rewrite W2u16.to_uint_zeroextu32 !W16.of_uintK W32.of_uintK /=.
  rewrite !modz_small; smt().
qed.

op checked_prefix (ap : W8.t Array1152.t) (rp : W16.t Array768.t) (n : int) : bool =
  forall j, 0 <= j < n =>
    rp.[2*j] = W16.of_int (decoded_even ap j) /\
    rp.[2*j+1] = W16.of_int (decoded_odd ap j).

lemma checked_prefix_extend ap rp i :
  0 <= i < 384 => checked_prefix ap rp i =>
  checked_prefix ap
    (rp.[2*i <- W16.of_int (decoded_even ap i)]
       .[2*i+1 <- W16.of_int (decoded_odd ap i)]) (i+1).
proof.
  move=> hi hp j hj.
  case (j=i) => [-> | hneq].
  + smt(Array768.get_setE).
  have hjold : 0 <= j < i by smt().
  have [he ho] := hp j hjold.
  smt(Array768.get_setE).
qed.

lemma checked_prefix_full ap rp :
  checked_prefix ap rp 384 => rp = decoded_poly ap.
proof.
  move=> hp; apply Array768.tP => j hj.
  have hi : 0 <= j %/ 2 < 384 by smt().
  have [he ho] := hp (j %/ 2) hi.
  rewrite /NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec Array768.initiE 1:hj.
  case (j %% 2 = 0) => hm.
  + have hjE : j = 2*(j %/ 2) by smt().
    by rewrite hjE he decoded_even_index.
  have hjE : j = 2*(j %/ 2)+1 by smt(modz_cmp).
  by rewrite hjE ho decoded_odd_index.
qed.
