require import AllCore Distr.
from Jasmin require import JWord.
require import Array96 Array192 Array768.
require import NTRUPlus768ROMDistributions.
require import NTRUPlus768PolySOTPEncodeAlgebra NTRUPlus768PolyCBD1Algebra.

(* The message is arbitrary and fixed. Only the 192-byte pad is uniform.
   This is a fresh random-oracle output law, not a SHAKE seed-expansion law. *)
lemma sotp_xor_byte_involution (byte mask : W8.t) :
  (byte +^ mask) +^ mask = byte.
proof. by rewrite -W8.xorwA W8.xorwK W8.xorw0. qed.

lemma sotp_xor_byte_bijection (mask : W8.t) :
  bijective (fun byte => byte +^ mask).
proof.
  exists (fun byte => byte +^ mask); split=> byte;
  exact (sotp_xor_byte_involution byte mask).
qed.

lemma sotp_xor_head_involution
    (coins : W8.t Array96.t) (pad : W8.t Array192.t) :
  poly_sotp_encode_input coins (poly_sotp_encode_input coins pad) = pad.
proof.
  apply Array192.tP => k hk.
  case (k < 96) => h.
  + have hh : 0 <= k < 96 by smt().
    rewrite !poly_sotp_encode_input_head_byte 1,2:hh.
    exact (sotp_xor_byte_involution pad.[k] coins.[k]).
  have ht : 0 <= k - 96 < 96 by smt().
  have hi : k = 96 + (k - 96) by ring.
  by rewrite hi !poly_sotp_encode_input_tail_byte 1,2:ht.
qed.

lemma sotp_xor_head_bijection (coins : W8.t Array96.t) :
  bijective (poly_sotp_encode_input coins).
proof.
  exists (poly_sotp_encode_input coins); split=> pad;
  exact (sotp_xor_head_involution coins pad).
qed.

lemma sotp_xor_head_uniform (coins : W8.t Array96.t) :
  dmap uniform192 (poly_sotp_encode_input coins) = uniform192.
proof.
  apply eq_distr => pad.
  rewrite (dmap1E_can _ _ (poly_sotp_encode_input coins)).
  + exact (sotp_xor_head_involution coins).
  + move=> buf _; exact (sotp_xor_head_involution coins buf).
  by rewrite !uniform192_point.
qed.

op cbd1_uniform = dmap uniform192 poly_cbd1_spec.

lemma cbd1_uniform_ll : is_lossless cbd1_uniform.
proof. by apply/dmap_ll/uniform192_ll. qed.

lemma sotp_encode_uniform_law (coins : W8.t Array96.t) :
  dmap uniform192 (poly_sotp_encode_spec coins) = cbd1_uniform.
proof.
  rewrite /poly_sotp_encode_spec /cbd1_uniform.
  by rewrite -dmap_comp sotp_xor_head_uniform.
qed.

lemma sotp_encode_uniform_event
    (coins : W8.t Array96.t) (event : W16.t Array768.t -> bool) :
  mu uniform192 (fun pad => event (poly_sotp_encode_spec coins pad)) =
  mu cbd1_uniform event.
proof.
  by rewrite -(sotp_encode_uniform_law coins)
    (dmapE uniform192 (poly_sotp_encode_spec coins) event) /(\o) /=.
qed.

lemma rom_sotp_mask_law_eof (coins : W8.t Array96.t) :
  dmap uniform192 (poly_sotp_encode_spec coins) =
  dmap uniform192 poly_cbd1_spec.
proof. exact (sotp_encode_uniform_law coins). qed.
