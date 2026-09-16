require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord.

require import Array4 Array768.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768NTTSchedule.
require import NTRUPlus768BaseInvAlgebra.
require import NTRUPlus768PolyBaseInvBridge.
require import NTRUPlus768PolyBasemulProof.
require import NTRUPlus768PolyBasemulAlgebra.
require import NTRUPlus768KeygenHBridge.
require import NTRUPlus768KeygenPublicKeyBridge.
require import NTRUPlus768EncapPolyBasemulAddAlgebra.
require import NTRUPlus768PolySubAlgebra.

import Ring.IntID IntOrder.

(* Cancellation in each terminal quartic uses only the successful keypair
   relation and coefficient congruences.  No global representative for h or
   hinv, or literal equality of their noncanonical word arrays, is needed. *)

lemma nested0_rotate (a b c : W16.t Array4.t) (z : int) :
  nested0 a b c z = nested0 c a b z.
proof. rewrite /nested0 /coeff0 /coeff1 /coeff2 /coeff3; ring. qed.

lemma nested1_rotate (a b c : W16.t Array4.t) (z : int) :
  nested1 a b c z = nested1 c a b z.
proof. rewrite /nested1 /coeff0 /coeff1 /coeff2 /coeff3; ring. qed.

lemma nested2_rotate (a b c : W16.t Array4.t) (z : int) :
  nested2 a b c z = nested2 c a b z.
proof. rewrite /nested2 /coeff0 /coeff1 /coeff2 /coeff3; ring. qed.

lemma nested3_rotate (a b c : W16.t Array4.t) (z : int) :
  nested3 a b c z = nested3 c a b z.
proof. rewrite /nested3 /coeff0 /coeff1 /coeff2 /coeff3; ring. qed.

lemma block_product_qring_comm (a b r : W16.t Array4.t) (z : int) :
  block_product_qring a b r z => block_product_qring b a r z.
proof.
  by rewrite /block_product_qring
    (coeff0_comm b a z) (coeff1_comm b a z)
    (coeff2_comm b a z) (coeff3_comm b a z).
qed.

lemma block_product_reassociate
    (a b c ab bc output : W16.t Array4.t) (z : int) :
  block_product_qring a b ab z =>
  block_product_qring b c bc z =>
  block_product_qring ab c output z =>
  block_product_qring a bc output z.
proof.
  move=> [A0 [A1 [A2 A3]]] [B0 [B1 [B2 B3]]]
    [O0 [O1 [O2 O3]]].
  have A0' : coeff ab.[0] %% q = coeff0 a b z %% q by smt().
  have A1' : coeff ab.[1] %% q = coeff1 a b z %% q by smt().
  have A2' : coeff ab.[2] %% q = coeff2 a b z %% q by smt().
  have A3' : coeff ab.[3] %% q = coeff3 a b z %% q by smt().
  have B0' : coeff bc.[0] %% q = coeff0 b c z %% q by smt().
  have B1' : coeff bc.[1] %% q = coeff1 b c z %% q by smt().
  have B2' : coeff bc.[2] %% q = coeff2 b c z %% q by smt().
  have B3' : coeff bc.[3] %% q = coeff3 b c z %% q by smt().
  rewrite /block_product_qring.
  split.
  + have HL : coeff0 c ab z %% q = nested0 c a b z %% q.
    + exact (coeff0_mod_congr_right c ab z
        (coeff0 a b z) (coeff1 a b z) (coeff2 a b z) (coeff3 a b z)
        A0' A1' A2' A3').
    have HR : coeff0 a bc z %% q = nested0 a b c z %% q.
    + exact (coeff0_mod_congr_right a bc z
        (coeff0 b c z) (coeff1 b c z) (coeff2 b c z) (coeff3 b c z)
        B0' B1' B2' B3').
    rewrite HR (nested0_rotate a b c z) -HL -(coeff0_comm ab c z).
    exact O0.
  split.
  + have HL : coeff1 c ab z %% q = nested1 c a b z %% q.
    + exact (coeff1_mod_congr_right c ab z
        (coeff0 a b z) (coeff1 a b z) (coeff2 a b z) (coeff3 a b z)
        A0' A1' A2' A3').
    have HR : coeff1 a bc z %% q = nested1 a b c z %% q.
    + exact (coeff1_mod_congr_right a bc z
        (coeff0 b c z) (coeff1 b c z) (coeff2 b c z) (coeff3 b c z)
        B0' B1' B2' B3').
    rewrite HR (nested1_rotate a b c z) -HL -(coeff1_comm ab c z).
    exact O1.
  split.
  + have HL : coeff2 c ab z %% q = nested2 c a b z %% q.
    + exact (coeff2_mod_congr_right c ab z
        (coeff0 a b z) (coeff1 a b z) (coeff2 a b z) (coeff3 a b z)
        A0' A1' A2' A3').
    have HR : coeff2 a bc z %% q = nested2 a b c z %% q.
    + exact (coeff2_mod_congr_right a bc z
        (coeff0 b c z) (coeff1 b c z) (coeff2 b c z) (coeff3 b c z)
        B0' B1' B2' B3').
    rewrite HR (nested2_rotate a b c z) -HL -(coeff2_comm ab c z).
    exact O2.
  have HL : coeff3 c ab z %% q = nested3 c a b z %% q.
  + exact (coeff3_mod_congr_right c ab z
      (coeff0 a b z) (coeff1 a b z) (coeff2 a b z) (coeff3 a b z)
      A0' A1' A2' A3').
  have HR : coeff3 a bc z %% q = nested3 a b c z %% q.
  + exact (coeff3_mod_congr_right a bc z
      (coeff0 b c z) (coeff1 b c z) (coeff2 b c z) (coeff3 b c z)
      B0' B1' B2' B3').
  rewrite HR (nested3_rotate a b c z) -HL -(coeff3_comm ab c z).
  exact O3.
qed.

lemma poly_basemul_qring_block_product
    (a b r : W16.t Array768.t) (k : int) :
  poly_basemul_qring a b r 192 => 0 <= k < 192 =>
  block_product_qring (block4 a k) (block4 b k) (block4 r k)
    (terminal_value k).
proof.
  move=> H Hk.
  have [_ [H0 [H1 [H2 H3]]]] := H k Hk.
  rewrite /block_product_qring; smt().
qed.

lemma poly_basemul_qring_comm (a b r : W16.t Array768.t) :
  poly_basemul_qring a b r 192 => poly_basemul_qring b a r 192.
proof.
  move=> H k Hk.
  have := H k Hk.
  by rewrite /= (coeff0_comm (block4 b k) (block4 a k) (terminal_value k))
    (coeff1_comm (block4 b k) (block4 a k) (terminal_value k))
    (coeff2_comm (block4 b k) (block4 a k) (terminal_value k))
    (coeff3_comm (block4 b k) (block4 a k) (terminal_value k)).
qed.

lemma poly_basemul_qring_reassociate
    (a b c ab bc output : W16.t Array768.t) :
  poly_basemul_qring a b ab 192 =>
  poly_basemul_qring b c bc 192 =>
  poly_basemul_qring ab c output 192 =>
  poly_basemul_qring a bc output 192.
proof.
  move=> Hab Hbc Hout k Hk.
  have [Hrange _] := Hout k Hk.
  have H := block_product_reassociate
    (block4 a k) (block4 b k) (block4 c k)
    (block4 ab k) (block4 bc k) (block4 output k) (terminal_value k)
    (poly_basemul_qring_block_product a b ab k Hab Hk)
    (poly_basemul_qring_block_product b c bc k Hbc Hk)
    (poly_basemul_qring_block_product ab c output k Hout Hk).
  move: H => [H0 [H1 [H2 H3]]].
  split; first exact Hrange.
  smt().
qed.

lemma keygen_h_hinv_inverse
    (f finv g ginv h hinv : W16.t Array768.t) :
  keygen_keypair_ntt_relation f finv g ginv h hinv =>
  poly_basemul_qring h hinv ntt_block_identity 192.
proof.
  move=> Hkey.
  have Hfinv : poly_baseinv_success f finv.
  + move: Hkey; rewrite /keygen_keypair_ntt_relation; smt().
  have Hh : poly_basemul_qring g finv h 192.
  + move: Hkey; rewrite /keygen_keypair_ntt_relation; smt().
  have Hhinvg : poly_basemul_qring hinv g f 192.
  + move: Hkey; rewrite /keygen_keypair_ntt_relation; smt().
  have Hunit := poly_baseinv_success_product_identity f finv Hfinv.
  have H := poly_basemul_qring_reassociate
    hinv g finv f h ntt_block_identity Hhinvg Hh Hunit.
  exact (poly_basemul_qring_comm hinv h ntt_block_identity H).
qed.

lemma decoded_h_hinv_inverse
    (f finv g ginv h hinv decoded_h decoded_hinv : W16.t Array768.t) :
  keygen_keypair_ntt_relation f finv g ginv h hinv =>
  poly_coeff_eq_mod_q decoded_h h =>
  poly_coeff_eq_mod_q decoded_hinv hinv =>
  poly_basemul_qring decoded_h decoded_hinv ntt_block_identity 192.
proof.
  move=> Hkey Hh Hhinv.
  have Hunit := keygen_h_hinv_inverse f finv g ginv h hinv Hkey.
  have Hleft := poly_basemul_qring_left_mod_q_congr
    h decoded_h hinv ntt_block_identity Hh Hunit.
  have Hswap := poly_basemul_qring_comm
    decoded_h hinv ntt_block_identity Hleft.
  have Hright := poly_basemul_qring_left_mod_q_congr
    hinv decoded_hinv decoded_h ntt_block_identity Hhinv Hswap.
  exact (poly_basemul_qring_comm
    decoded_hinv decoded_h ntt_block_identity Hright).
qed.

lemma mod_q_subtract_encoded_addend (decoded encoded product addend : int) :
  decoded %% q = encoded %% q =>
  encoded %% q = (product + addend) %% q =>
  (decoded - addend) %% q = product %% q.
proof.
  move=> Hdecode Hencode.
  rewrite -modzBm Hdecode Hencode modzBm.
  by rewrite (_ : product + addend - addend = product) 1:/#.
qed.

lemma poly_sub_algebra_block_coeff
    (a b output : W16.t Array768.t) (k i : int) :
  poly_sub_algebra a b output => 0 <= k < 192 => 0 <= i < 4 =>
  coeff (block4 output k).[i] =
    coeff (block4 a k).[i] - coeff (block4 b k).[i].
proof.
  move=> Hsub Hk Hi.
  have Hidx := block4_flat_index_range k i Hk Hi.
  have [Hcoeff _] := Hsub (4 * k + i) Hidx.
  by rewrite /block4 !Array4.initiE 1:/# 1:/# 1:/#.
qed.

lemma decoded_subtraction_block_product
    (h r m c decoded_c sub : W16.t Array768.t) (k : int) :
  poly_basemul_add_qring h r m c 192 =>
  poly_coeff_eq_mod_q decoded_c c =>
  poly_sub_algebra decoded_c m sub => 0 <= k < 192 =>
  block_product_qring (block4 h k) (block4 r k) (block4 sub k)
    (terminal_value k).
proof.
  move=> Henc Hdecode Hsub Hk.
  have [_ [E0 [E1 [E2 E3]]]] := Henc k Hk.
  have D0 := poly_coeff_eq_mod_q_block4 c decoded_c k 0 Hdecode Hk
    block4_offset0_range.
  have D1 := poly_coeff_eq_mod_q_block4 c decoded_c k 1 Hdecode Hk
    block4_offset1_range.
  have D2 := poly_coeff_eq_mod_q_block4 c decoded_c k 2 Hdecode Hk
    block4_offset2_range.
  have D3 := poly_coeff_eq_mod_q_block4 c decoded_c k 3 Hdecode Hk
    block4_offset3_range.
  have S0 := poly_sub_algebra_block_coeff decoded_c m sub k 0 Hsub Hk
    block4_offset0_range.
  have S1 := poly_sub_algebra_block_coeff decoded_c m sub k 1 Hsub Hk
    block4_offset1_range.
  have S2 := poly_sub_algebra_block_coeff decoded_c m sub k 2 Hsub Hk
    block4_offset2_range.
  have S3 := poly_sub_algebra_block_coeff decoded_c m sub k 3 Hsub Hk
    block4_offset3_range.
  rewrite /block_product_qring S0 S1 S2 S3.
  split.
  + apply/eq_sym.
    exact (mod_q_subtract_encoded_addend
      (coeff (block4 decoded_c k).[0]) (coeff (block4 c k).[0])
      (coeff0 (block4 h k) (block4 r k) (terminal_value k))
      (coeff (block4 m k).[0]) D0 E0).
  split.
  + apply/eq_sym.
    exact (mod_q_subtract_encoded_addend
      (coeff (block4 decoded_c k).[1]) (coeff (block4 c k).[1])
      (coeff1 (block4 h k) (block4 r k) (terminal_value k))
      (coeff (block4 m k).[1]) D1 E1).
  split.
  + apply/eq_sym.
    exact (mod_q_subtract_encoded_addend
      (coeff (block4 decoded_c k).[2]) (coeff (block4 c k).[2])
      (coeff2 (block4 h k) (block4 r k) (terminal_value k))
      (coeff (block4 m k).[2]) D2 E2).
  apply/eq_sym.
  exact (mod_q_subtract_encoded_addend
    (coeff (block4 decoded_c k).[3]) (coeff (block4 c k).[3])
    (coeff3 (block4 h k) (block4 r k) (terminal_value k))
    (coeff (block4 m k).[3]) D3 E3).
qed.

lemma ntt_identity_block (k : int) :
  0 <= k < 192 => block4 ntt_block_identity k = qring_unit4.
proof.
  move=> Hk.
  apply Array4.ext_eq => i Hi.
  have H0 := ntt_block_identity_coeff0 k Hk.
  have H1 := ntt_block_identity_coeff1 k Hk.
  have H2 := ntt_block_identity_coeff2 k Hk.
  have H3 := ntt_block_identity_coeff3 k Hk.
  have U0 := qring_unit4_coeff0.
  have U1 := qring_unit4_coeff1.
  have U2 := qring_unit4_coeff2.
  have U3 := qring_unit4_coeff3.
  have Heq : coeff (block4 ntt_block_identity k).[i] = coeff qring_unit4.[i].
  + have : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 by smt().
    smt().
  rewrite (NTRUPlus768PolySubAlgebra.word_from_coeff
      (block4 ntt_block_identity k).[i])
    (NTRUPlus768PolySubAlgebra.word_from_coeff qring_unit4.[i]) Heq.
  done.
qed.

lemma block_product_unit_coeff
    (a output : W16.t Array4.t) (z i : int) :
  block_product_qring a qring_unit4 output z => 0 <= i < 4 =>
  coeff output.[i] %% q = coeff a.[i] %% q.
proof.
  rewrite /block_product_qring coeff0_qring_unit4 coeff1_qring_unit4
    coeff2_qring_unit4 coeff3_qring_unit4.
  move=> [H0 [H1 [H2 H3]]] Hi.
  have : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 by smt().
  smt().
qed.

lemma inverse_r2_block_coeff
    (h hinv r m c decoded_c sub r2 : W16.t Array768.t) (k i : int) :
  poly_basemul_qring h hinv ntt_block_identity 192 =>
  poly_basemul_add_qring h r m c 192 =>
  poly_coeff_eq_mod_q decoded_c c =>
  poly_sub_algebra decoded_c m sub =>
  poly_basemul_qring sub hinv r2 192 =>
  0 <= k < 192 => 0 <= i < 4 =>
  coeff (block4 r2 k).[i] %% q = coeff (block4 r k).[i] %% q.
proof.
  move=> Hinv Henc Hdecode Hsub Hr2 Hk Hi.
  have Hhr := decoded_subtraction_block_product
    h r m c decoded_c sub k Henc Hdecode Hsub Hk.
  have Hrh := block_product_qring_comm
    (block4 h k) (block4 r k) (block4 sub k) (terminal_value k) Hhr.
  have Hunit := block_product_reassociate
    (block4 r k) (block4 h k) (block4 hinv k)
    (block4 sub k) (block4 ntt_block_identity k) (block4 r2 k)
    (terminal_value k) Hrh
    (poly_basemul_qring_block_product h hinv ntt_block_identity k Hinv Hk)
    (poly_basemul_qring_block_product sub hinv r2 k Hr2 Hk).
  rewrite (ntt_identity_block k Hk) in Hunit.
  exact (block_product_unit_coeff
    (block4 r k) (block4 r2 k) (terminal_value k) i Hunit Hi).
qed.

lemma inverse_r2_mod_q
    (h hinv r m c decoded_c sub r2 : W16.t Array768.t) :
  poly_basemul_qring h hinv ntt_block_identity 192 =>
  poly_basemul_add_qring h r m c 192 =>
  poly_coeff_eq_mod_q decoded_c c =>
  poly_sub_algebra decoded_c m sub =>
  poly_basemul_qring sub hinv r2 192 =>
  poly_coeff_eq_mod_q r2 r.
proof.
  move=> Hinv Henc Hdecode Hsub Hr2 j Hj.
  have Hdiv : 0 <= j %/ 4 < 192 by smt().
  have Hmod : 0 <= j %% 4 < 4 by smt().
  have Hidx : 4 * (j %/ 4) + j %% 4 = j by smt(IntDiv.divz_eq).
  have H := inverse_r2_block_coeff h hinv r m c decoded_c sub r2
    (j %/ 4) (j %% 4) Hinv Henc Hdecode Hsub Hr2 Hdiv Hmod.
  move: H; rewrite /block4 !Array4.initiE 1:/# 1:/#.
  smt().
qed.

lemma valid_key_r2_mod_q
    (f finv g ginv h hinv decoded_h decoded_hinv
     r_ntt m_ntt c_enc decoded_c sub r2 : W16.t Array768.t) :
  keygen_keypair_ntt_relation f finv g ginv h hinv =>
  poly_coeff_eq_mod_q decoded_h h =>
  poly_coeff_eq_mod_q decoded_hinv hinv =>
  poly_basemul_add_qring decoded_h r_ntt m_ntt c_enc 192 =>
  poly_coeff_eq_mod_q decoded_c c_enc =>
  poly_sub_algebra decoded_c m_ntt sub =>
  poly_basemul_qring sub decoded_hinv r2 192 =>
  poly_coeff_eq_mod_q r2 r_ntt.
proof.
  move=> Hkey Hh Hhinv Henc Hdecode Hsub Hr2.
  have Hinv := decoded_h_hinv_inverse
    f finv g ginv h hinv decoded_h decoded_hinv Hkey Hh Hhinv.
  exact (inverse_r2_mod_q decoded_h decoded_hinv r_ntt m_ntt
    c_enc decoded_c sub r2 Hinv Henc Hdecode Hsub Hr2).
qed.
