require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord.

require import Array768 Array1152.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768PolyBasemulAlgebra.
require import NTRUPlus768PolyFromBytesAlgebra.
require import NTRUPlus768PolyToBytesAlgebra.
require import NTRUPlus768KeygenHBridge.
require import NTRUPlus768KeygenPublicKeyBridge.
require import NTRUPlus768EncapPolyBasemulAddAlgebra.

import Ring.IntID IntOrder.

(* Array-value serialization of the ciphertext and the 1152-byte secret-key
   hinv block.  This is a block contract, not a whole-secret-key memory model.
   Exact bytes follow from congruence and the serializer's input range;
   intermediate signed words need not be equal. *)

op r2_serialized_decode (p : W16.t Array768.t) : W16.t Array768.t =
  NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec
    (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec p).

op r2_serialization_relation
    (c_enc hinv decoded_c decoded_hinv : W16.t Array768.t)
    (ct sk_hinv : W8.t Array1152.t) : bool =
  ct = NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c_enc /\
  sk_hinv = NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec hinv /\
  decoded_c = NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec ct /\
  decoded_hinv = NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec sk_hinv.

lemma r2_serialized_decode_roundtrip (p : W16.t Array768.t) :
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange p =>
  r2_serialized_decode p =
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_canonical_spec p.
proof.
  move=> Hp.
  exact (keygen_decoded_public_key_roundtrip p Hp).
qed.

lemma r2_serialized_decode_coeff_range
    (p : W16.t Array768.t) (j : int) :
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange p =>
  0 <= j < 768 =>
  0 <= coeff (r2_serialized_decode p).[j] < q.
proof.
  move=> Hp Hj.
  exact (keygen_decoded_public_key_coeff_range p j Hp Hj).
qed.

lemma r2_serialized_decode_canonical_range (p : W16.t Array768.t) :
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange p =>
  in_canonical_range768 (r2_serialized_decode p).
proof.
  move=> Hp.
  exact (keygen_decoded_public_key_canonical_range p Hp).
qed.

lemma r2_serialized_decode_mod_q (p : W16.t Array768.t) :
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange p =>
  poly_coeff_eq_mod_q (r2_serialized_decode p) p.
proof.
  move=> Hp.
  exact (keygen_decoded_public_key_mod_q p Hp).
qed.

lemma r2_serialized_decode_decoder_range (p : W16.t Array768.t) :
  NTRUPlus768PolyFromBytesAlgebra.coeff_lt_4096
    (r2_serialized_decode p).
proof.
  exact (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec_coeff_lt_4096
    (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec p)).
qed.

lemma r2_serialized_decode_tobytes_input_qrange (p : W16.t Array768.t) :
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange p =>
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange
    (r2_serialized_decode p).
proof.
  move=> Hp j Hj.
  have Hrange := r2_serialized_decode_coeff_range p j Hp Hj.
  have Hq : 0 < q by rewrite /q.
  smt().
qed.

lemma canonical_coeff_mod_q_unique (a b : W16.t) :
  -q <= coeff a < q =>
  -q <= coeff b < q =>
  coeff a %% q = coeff b %% q =>
  NTRUPlus768PolyToBytesAlgebra.canonical_coeff a =
  NTRUPlus768PolyToBytesAlgebra.canonical_coeff b.
proof.
  move=> Ha Hb Heq.
  have Har := NTRUPlus768PolyToBytesAlgebra.canonical_coeff_range a Ha.
  have Hbr := NTRUPlus768PolyToBytesAlgebra.canonical_coeff_range b Hb.
  have Ham := NTRUPlus768PolyToBytesAlgebra.canonical_coeff_mod_q a Ha.
  have Hbm := NTRUPlus768PolyToBytesAlgebra.canonical_coeff_mod_q b Hb.
  rewrite (modz_small _ q Har) in Ham.
  rewrite (modz_small _ q Hbr) in Hbm.
  smt().
qed.

lemma poly_tobytes_canonical_mod_q_unique (a b : W16.t Array768.t) :
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange a =>
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange b =>
  poly_coeff_eq_mod_q a b =>
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_canonical_spec a =
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_canonical_spec b.
proof.
  move=> Ha Hb Heq.
  apply Array768.ext_eq => j Hj.
  rewrite /NTRUPlus768PolyToBytesAlgebra.poly_tobytes_canonical_spec
    !Array768.initiE 1:Hj 1:Hj.
  have Hcanon := canonical_coeff_mod_q_unique a.[j] b.[j]
    (Ha j Hj) (Hb j Hj) (Heq j Hj).
  smt().
qed.

lemma poly_tobytes_mod_q_congr (a b : W16.t Array768.t) :
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange a =>
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange b =>
  poly_coeff_eq_mod_q a b =>
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec a =
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec b.
proof.
  move=> Ha Hb Heq.
  have Hcanon : forall j, 0 <= j < 768 =>
    NTRUPlus768PolyToBytesAlgebra.canonical_coeff a.[j] =
    NTRUPlus768PolyToBytesAlgebra.canonical_coeff b.[j].
  + move=> j Hj.
    exact (canonical_coeff_mod_q_unique a.[j] b.[j]
      (Ha j Hj) (Hb j Hj) (Heq j Hj)).
  apply Array1152.ext_eq => j Hj.
  have Hpair : 0 <= j %/ 3 < 384 by smt(IntDiv.edivzP).
  have H0 : 0 <= 2 * (j %/ 3) < 768 by smt().
  have H1 : 0 <= 2 * (j %/ 3) + 1 < 768 by smt().
  rewrite /NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec
    !Array1152.initiE 1:Hj 1:Hj
    /NTRUPlus768PolyToBytesAlgebra.poly_tobytes_byte_at
    /NTRUPlus768PolyToBytesAlgebra.poly_tobytes_byte0_int
    /NTRUPlus768PolyToBytesAlgebra.poly_tobytes_byte1_int
    /NTRUPlus768PolyToBytesAlgebra.poly_tobytes_byte2_int.
  have E0 := Hcanon (2 * (j %/ 3)) H0.
  have E1 := Hcanon (2 * (j %/ 3) + 1) H1.
  smt().
qed.

lemma keygen_hinv_qrange (f finv g ginv h hinv : W16.t Array768.t) :
  keygen_keypair_ntt_relation f finv g ginv h hinv =>
  in_qrange768 hinv.
proof.
  move=> Hkey.
  have Hhinv : poly_basemul_qring f ginv hinv 192.
  + move: Hkey; rewrite /keygen_keypair_ntt_relation; smt().
  move=> k Hk.
  have [Hrange _] := Hhinv k Hk.
  exact Hrange.
qed.

lemma keygen_hinv_tobytes_input_qrange
    (f finv g ginv h hinv : W16.t Array768.t) :
  keygen_keypair_ntt_relation f finv g ginv h hinv =>
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange hinv.
proof.
  move=> Hkey.
  exact (in_qrange768_poly_tobytes_input_qrange hinv
    (keygen_hinv_qrange f finv g ginv h hinv Hkey)).
qed.

lemma encap_cipher_qrange (h r m c : W16.t Array768.t) :
  poly_basemul_add_qring h r m c 192 =>
  in_qrange768 c.
proof.
  move=> Henc k Hk.
  have Hblock := Henc k Hk.
  by move: Hblock => [Hrange _].
qed.

lemma encap_cipher_tobytes_input_qrange (h r m c : W16.t Array768.t) :
  poly_basemul_add_qring h r m c 192 =>
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange c.
proof.
  move=> Henc.
  exact (in_qrange768_poly_tobytes_input_qrange c
    (encap_cipher_qrange h r m c Henc)).
qed.

lemma decoded_cipher_product_transfer
    (c_enc decoded_f product : W16.t Array768.t) :
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange c_enc =>
  poly_basemul_qring (r2_serialized_decode c_enc) decoded_f product 192 =>
  poly_basemul_qring c_enc decoded_f product 192.
proof.
  move=> Hrange Hproduct.
  have Hdecode := r2_serialized_decode_mod_q c_enc Hrange.
  have Heq : poly_coeff_eq_mod_q c_enc (r2_serialized_decode c_enc).
  + move=> j Hj.
    have := Hdecode j Hj.
    smt().
  exact (poly_basemul_qring_left_mod_q_congr
    (r2_serialized_decode c_enc) c_enc decoded_f product Heq Hproduct).
qed.

lemma r2_serialization_relation_intro (c_enc hinv : W16.t Array768.t) :
  r2_serialization_relation c_enc hinv
    (r2_serialized_decode c_enc) (r2_serialized_decode hinv)
    (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c_enc)
    (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec hinv).
proof. done. qed.

lemma r2_serialization_relation_decode
    (c_enc hinv decoded_c decoded_hinv : W16.t Array768.t)
    (ct sk_hinv : W8.t Array1152.t) :
  r2_serialization_relation c_enc hinv decoded_c decoded_hinv ct sk_hinv =>
  decoded_c = r2_serialized_decode c_enc /\
  decoded_hinv = r2_serialized_decode hinv.
proof.
  rewrite /r2_serialization_relation /r2_serialized_decode.
  smt().
qed.

lemma r2_serialization_relation_mod_q
    (c_enc hinv decoded_c decoded_hinv : W16.t Array768.t)
    (ct sk_hinv : W8.t Array1152.t) :
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange c_enc =>
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange hinv =>
  r2_serialization_relation c_enc hinv decoded_c decoded_hinv ct sk_hinv =>
  poly_coeff_eq_mod_q decoded_c c_enc /\
  poly_coeff_eq_mod_q decoded_hinv hinv.
proof.
  move=> Hc Hh Hser.
  have [Ec Eh] := r2_serialization_relation_decode
    c_enc hinv decoded_c decoded_hinv ct sk_hinv Hser.
  rewrite Ec Eh.
  split.
  + exact (r2_serialized_decode_mod_q c_enc Hc).
  exact (r2_serialized_decode_mod_q hinv Hh).
qed.
