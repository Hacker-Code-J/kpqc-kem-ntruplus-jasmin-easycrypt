require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array4 Array192 Array768 Array1152.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768BaseInvAlgebra.
require import NTRUPlus768NTTSchedule.
require import NTRUPlus768PolyBasemulProof.
require import NTRUPlus768PolyBasemulAlgebra.
require import NTRUPlus768PolyBasemulInvNTTAlgebra.
require NTRUPlus768PolyFromBytesAlgebra.
require import NTRUPlus768PolyToBytes.
require import NTRUPlus768PolyToBytesProof.
require import NTRUPlus768PolyToBytesAlgebra.
require import NTRUPlus768KeygenSamplerBridge.
require import NTRUPlus768KeygenHBridge.

import Ring.IntID IntOrder.

(* Scope: proof-facing composition from the verified keygen h relation through
   the exact Jasmin poly_tobytes procedure and the mathematical decoder.  It
   proves public-key bytes, canonical roundtrip, coefficientwise mod-q
   preservation, and decoded_h * f = g in the terminal quotient rings.  It
   does not claim production-C semantics or C/Jasmin equivalence, random retry
   termination or probability, a high-level NTT/InvNTT homomorphism, secret-key
   serialization, hash provenance, aggregate CT/SCT, or full-KEM correctness. *)

op keygen_public_key_bytes
    (h : W16.t Array768.t) : W8.t Array1152.t =
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec h.

op keygen_decoded_public_key
    (pk : W8.t Array1152.t) : W16.t Array768.t =
  NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec pk.

op poly_coeff_eq_mod_q
    (a b : W16.t Array768.t) : bool =
  forall j, 0 <= j < 768 => coeff a.[j] %% q = coeff b.[j] %% q.

op keygen_public_key_serialization_relation
    (f finv g ginv h hinv decoded_h : W16.t Array768.t)
    (pk : W8.t Array1152.t) : bool =
  keygen_keypair_ntt_relation f finv g ginv h hinv /\
  pk = keygen_public_key_bytes h /\
  decoded_h = keygen_decoded_public_key pk /\
  decoded_h = NTRUPlus768PolyToBytesAlgebra.poly_tobytes_canonical_spec h /\
  in_canonical_range768 decoded_h /\
  poly_coeff_eq_mod_q decoded_h h /\
  poly_basemul_qring decoded_h f g 192.

lemma poly_frombytes_specsE (a : W8.t Array1152.t) :
  NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec a =
  NTRUPlus768PolyToBytesAlgebra.poly_frombytes_spec a.
proof.
  rewrite /NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec
    /NTRUPlus768PolyToBytesAlgebra.poly_frombytes_spec
    /NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_int
    /NTRUPlus768PolyToBytesAlgebra.poly_frombytes_int
    /NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_even_int
    /NTRUPlus768PolyToBytesAlgebra.poly_frombytes_even_int
    /NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_odd_int
    /NTRUPlus768PolyToBytesAlgebra.poly_frombytes_odd_int.
  done.
qed.

lemma keygen_public_key_bytes_procedure_specE
    (h : W16.t Array768.t) :
  NTRUPlus768PolyToBytesProof.poly_tobytes_spec h =
  keygen_public_key_bytes h.
proof.
  rewrite /keygen_public_key_bytes poly_tobytes_procedure_specE.
  done.
qed.

lemma poly_basemul_qring_output_in_qrange768
    (ap bp rp : W16.t Array768.t) :
  poly_basemul_qring ap bp rp 192 => in_qrange768 rp.
proof.
  move=> Hqring k Hk.
  have Hblock := Hqring k Hk.
  by move: Hblock => [Hrange _].
qed.

lemma in_qrange768_coeff
    (p : W16.t Array768.t) (j : int) :
  in_qrange768 p =>
  0 <= j < 768 =>
  -q <= coeff p.[j] < q.
proof.
  move=> Hp Hj.
  have Hshape :=
    NTRUPlus768PolyBasemulInvNTTAlgebra.in_qrange768_implies_invntt_input_shape
      p Hp.
  exact (Hshape j Hj).
qed.

lemma in_qrange768_poly_tobytes_input_qrange
    (p : W16.t Array768.t) :
  in_qrange768 p =>
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange p.
proof.
  move=> Hp j Hj.
  exact (in_qrange768_coeff p j Hp Hj).
qed.

lemma keygen_public_h_qrange
    (f finv g ginv h hinv : W16.t Array768.t) :
  keygen_keypair_ntt_relation f finv g ginv h hinv =>
  in_qrange768 h.
proof.
  move=> Hrelation.
  rewrite /keygen_keypair_ntt_relation in Hrelation.
  move: Hrelation => [_ [_ [Hh _]]].
  exact (poly_basemul_qring_output_in_qrange768 g finv h Hh).
qed.

lemma keygen_public_h_tobytes_input_qrange
    (f finv g ginv h hinv : W16.t Array768.t) :
  keygen_keypair_ntt_relation f finv g ginv h hinv =>
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange h.
proof.
  move=> Hrelation.
  exact (in_qrange768_poly_tobytes_input_qrange h
    (keygen_public_h_qrange f finv g ginv h hinv Hrelation)).
qed.

lemma keygen_decoded_public_key_roundtrip
    (h : W16.t Array768.t) :
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange h =>
  keygen_decoded_public_key (keygen_public_key_bytes h) =
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_canonical_spec h.
proof.
  move=> Hh.
  rewrite /keygen_decoded_public_key /keygen_public_key_bytes
    poly_frombytes_specsE.
  exact
    (NTRUPlus768PolyToBytesAlgebra.poly_frombytes_poly_tobytes_roundtrip h Hh).
qed.

lemma keygen_decoded_public_key_coeff_range
    (h : W16.t Array768.t) (j : int) :
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange h =>
  0 <= j < 768 =>
  0 <= coeff
    (keygen_decoded_public_key (keygen_public_key_bytes h)).[j] < q.
proof.
  move=> Hh Hj.
  rewrite /keygen_decoded_public_key /keygen_public_key_bytes
    poly_frombytes_specsE.
  exact
    (NTRUPlus768PolyToBytesAlgebra.poly_frombytes_poly_tobytes_roundtrip_coeff_range
      h j Hh Hj).
qed.

lemma keygen_decoded_public_key_canonical_range
    (h : W16.t Array768.t) :
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange h =>
  in_canonical_range768
    (keygen_decoded_public_key (keygen_public_key_bytes h)).
proof.
  move=> Hh k Hk.
  rewrite /in_canonical_range4 /in_canonical_range /block4.
  split.
  + rewrite Array4.initiE 1:/#.
    apply (keygen_decoded_public_key_coeff_range h (4 * k) Hh).
    smt().
  split.
  + rewrite Array4.initiE 1:/#.
    apply (keygen_decoded_public_key_coeff_range h (4 * k + 1) Hh).
    smt().
  split.
  + rewrite Array4.initiE 1:/#.
    apply (keygen_decoded_public_key_coeff_range h (4 * k + 2) Hh).
    smt().
  rewrite Array4.initiE 1:/#.
  apply (keygen_decoded_public_key_coeff_range h (4 * k + 3) Hh).
  smt().
qed.

lemma keygen_decoded_public_key_mod_q
    (h : W16.t Array768.t) :
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange h =>
  poly_coeff_eq_mod_q
    (keygen_decoded_public_key (keygen_public_key_bytes h)) h.
proof.
  move=> Hh j Hj.
  rewrite /keygen_decoded_public_key /keygen_public_key_bytes
    poly_frombytes_specsE.
  exact
    (NTRUPlus768PolyToBytesAlgebra.poly_frombytes_poly_tobytes_roundtrip_coeff_mod_q
      h j Hh Hj).
qed.

lemma coeff0_left_mod_q_congr
    (a a' b : W16.t Array4.t) (z : int) :
  coeff a'.[0] %% q = coeff a.[0] %% q =>
  coeff a'.[1] %% q = coeff a.[1] %% q =>
  coeff a'.[2] %% q = coeff a.[2] %% q =>
  coeff a'.[3] %% q = coeff a.[3] %% q =>
  coeff0 a' b z %% q = coeff0 a b z %% q.
proof.
  move=> H0 H1 H2 H3.
  have Hright : coeff0 b a' z %% q = coeff0 b a z %% q.
  + exact (coeff0_mod_congr_right b a' z
      (coeff a.[0]) (coeff a.[1]) (coeff a.[2]) (coeff a.[3])
      H0 H1 H2 H3).
  rewrite (NTRUPlus768KeygenHBridge.coeff0_comm a' b z)
    (NTRUPlus768KeygenHBridge.coeff0_comm a b z).
  exact Hright.
qed.

lemma coeff1_left_mod_q_congr
    (a a' b : W16.t Array4.t) (z : int) :
  coeff a'.[0] %% q = coeff a.[0] %% q =>
  coeff a'.[1] %% q = coeff a.[1] %% q =>
  coeff a'.[2] %% q = coeff a.[2] %% q =>
  coeff a'.[3] %% q = coeff a.[3] %% q =>
  coeff1 a' b z %% q = coeff1 a b z %% q.
proof.
  move=> H0 H1 H2 H3.
  have Hright : coeff1 b a' z %% q = coeff1 b a z %% q.
  + exact (coeff1_mod_congr_right b a' z
      (coeff a.[0]) (coeff a.[1]) (coeff a.[2]) (coeff a.[3])
      H0 H1 H2 H3).
  rewrite (NTRUPlus768KeygenHBridge.coeff1_comm a' b z)
    (NTRUPlus768KeygenHBridge.coeff1_comm a b z).
  exact Hright.
qed.

lemma coeff2_left_mod_q_congr
    (a a' b : W16.t Array4.t) (z : int) :
  coeff a'.[0] %% q = coeff a.[0] %% q =>
  coeff a'.[1] %% q = coeff a.[1] %% q =>
  coeff a'.[2] %% q = coeff a.[2] %% q =>
  coeff a'.[3] %% q = coeff a.[3] %% q =>
  coeff2 a' b z %% q = coeff2 a b z %% q.
proof.
  move=> H0 H1 H2 H3.
  have Hright : coeff2 b a' z %% q = coeff2 b a z %% q.
  + exact (coeff2_mod_congr_right b a' z
      (coeff a.[0]) (coeff a.[1]) (coeff a.[2]) (coeff a.[3])
      H0 H1 H2 H3).
  rewrite (NTRUPlus768KeygenHBridge.coeff2_comm a' b z)
    (NTRUPlus768KeygenHBridge.coeff2_comm a b z).
  exact Hright.
qed.

lemma coeff3_left_mod_q_congr
    (a a' b : W16.t Array4.t) (z : int) :
  coeff a'.[0] %% q = coeff a.[0] %% q =>
  coeff a'.[1] %% q = coeff a.[1] %% q =>
  coeff a'.[2] %% q = coeff a.[2] %% q =>
  coeff a'.[3] %% q = coeff a.[3] %% q =>
  coeff3 a' b z %% q = coeff3 a b z %% q.
proof.
  move=> H0 H1 H2 H3.
  have Hright : coeff3 b a' z %% q = coeff3 b a z %% q.
  + exact (coeff3_mod_congr_right b a' z
      (coeff a.[0]) (coeff a.[1]) (coeff a.[2]) (coeff a.[3])
      H0 H1 H2 H3).
  rewrite (NTRUPlus768KeygenHBridge.coeff3_comm a' b z)
    (NTRUPlus768KeygenHBridge.coeff3_comm a b z).
  exact Hright.
qed.

lemma block4_flat_index_range (k i : int) :
  0 <= k < 192 =>
  0 <= i < 4 =>
  0 <= 4 * k + i < 768.
proof.
  smt().
qed.

lemma block4_offset0_range : 0 <= 0 < 4.
proof. smt(). qed.

lemma block4_offset1_range : 0 <= 1 < 4.
proof. smt(). qed.

lemma block4_offset2_range : 0 <= 2 < 4.
proof. smt(). qed.

lemma block4_offset3_range : 0 <= 3 < 4.
proof. smt(). qed.

lemma poly_coeff_eq_mod_q_block4
    (a a' : W16.t Array768.t) (k i : int) :
  poly_coeff_eq_mod_q a' a =>
  0 <= k < 192 =>
  0 <= i < 4 =>
  coeff (block4 a' k).[i] %% q = coeff (block4 a k).[i] %% q.
proof.
  move=> Heq Hk Hi.
  have Hidx : 0 <= 4 * k + i < 768.
  + exact (block4_flat_index_range k i Hk Hi).
  rewrite /block4 !Array4.initiE 1:/# 1:/#.
  exact (Heq (4 * k + i) Hidx).
qed.

lemma poly_basemul_qring_left_mod_q_congr
    (a a' b r : W16.t Array768.t) :
  poly_coeff_eq_mod_q a' a =>
  poly_basemul_qring a b r 192 =>
  poly_basemul_qring a' b r 192.
proof.
  move=> Heq Hproduct k Hk.
  have Hblock := Hproduct k Hk.
  move: Hblock => /= [Hrange [H0 [H1 [H2 H3]]]].
  have C0 :
      coeff0 (block4 a' k) (block4 b k) (terminal_value k) %% q =
      coeff0 (block4 a k) (block4 b k) (terminal_value k) %% q.
  + apply (coeff0_left_mod_q_congr
      (block4 a k) (block4 a' k) (block4 b k) (terminal_value k)).
    - exact (poly_coeff_eq_mod_q_block4 a a' k 0 Heq Hk
        block4_offset0_range).
    - exact (poly_coeff_eq_mod_q_block4 a a' k 1 Heq Hk
        block4_offset1_range).
    - exact (poly_coeff_eq_mod_q_block4 a a' k 2 Heq Hk
        block4_offset2_range).
    exact (poly_coeff_eq_mod_q_block4 a a' k 3 Heq Hk
      block4_offset3_range).
  have C1 :
      coeff1 (block4 a' k) (block4 b k) (terminal_value k) %% q =
      coeff1 (block4 a k) (block4 b k) (terminal_value k) %% q.
  + apply (coeff1_left_mod_q_congr
      (block4 a k) (block4 a' k) (block4 b k) (terminal_value k)).
    - exact (poly_coeff_eq_mod_q_block4 a a' k 0 Heq Hk
        block4_offset0_range).
    - exact (poly_coeff_eq_mod_q_block4 a a' k 1 Heq Hk
        block4_offset1_range).
    - exact (poly_coeff_eq_mod_q_block4 a a' k 2 Heq Hk
        block4_offset2_range).
    exact (poly_coeff_eq_mod_q_block4 a a' k 3 Heq Hk
      block4_offset3_range).
  have C2 :
      coeff2 (block4 a' k) (block4 b k) (terminal_value k) %% q =
      coeff2 (block4 a k) (block4 b k) (terminal_value k) %% q.
  + apply (coeff2_left_mod_q_congr
      (block4 a k) (block4 a' k) (block4 b k) (terminal_value k)).
    - exact (poly_coeff_eq_mod_q_block4 a a' k 0 Heq Hk
        block4_offset0_range).
    - exact (poly_coeff_eq_mod_q_block4 a a' k 1 Heq Hk
        block4_offset1_range).
    - exact (poly_coeff_eq_mod_q_block4 a a' k 2 Heq Hk
        block4_offset2_range).
    exact (poly_coeff_eq_mod_q_block4 a a' k 3 Heq Hk
      block4_offset3_range).
  have C3 :
      coeff3 (block4 a' k) (block4 b k) (terminal_value k) %% q =
      coeff3 (block4 a k) (block4 b k) (terminal_value k) %% q.
  + apply (coeff3_left_mod_q_congr
      (block4 a k) (block4 a' k) (block4 b k) (terminal_value k)).
    - exact (poly_coeff_eq_mod_q_block4 a a' k 0 Heq Hk
        block4_offset0_range).
    - exact (poly_coeff_eq_mod_q_block4 a a' k 1 Heq Hk
        block4_offset1_range).
    - exact (poly_coeff_eq_mod_q_block4 a a' k 2 Heq Hk
        block4_offset2_range).
    exact (poly_coeff_eq_mod_q_block4 a a' k 3 Heq Hk
      block4_offset3_range).
  split; first exact Hrange.
  split.
  + rewrite C0.
    exact H0.
  split.
  + rewrite C1.
    exact H1.
  split.
  + rewrite C2.
    exact H2.
  rewrite C3.
  exact H3.
qed.

lemma keygen_decoded_h_f_equals_g
    (f finv g ginv h hinv : W16.t Array768.t) :
  keygen_keypair_ntt_relation f finv g ginv h hinv =>
  poly_basemul_qring
    (keygen_decoded_public_key (keygen_public_key_bytes h)) f g 192.
proof.
  move=> Hrelation.
  have Hrange := keygen_public_h_tobytes_input_qrange
    f finv g ginv h hinv Hrelation.
  have Heq := keygen_decoded_public_key_mod_q h Hrange.
  rewrite /keygen_keypair_ntt_relation in Hrelation.
  move: Hrelation => [_ [_ [_ [_ [Hhf _]]]]].
  exact (poly_basemul_qring_left_mod_q_congr h
    (keygen_decoded_public_key (keygen_public_key_bytes h)) f g Heq Hhf).
qed.

lemma keygen_public_key_serialization_relation_intro
    (f finv g ginv h hinv : W16.t Array768.t) :
  keygen_keypair_ntt_relation f finv g ginv h hinv =>
  keygen_public_key_serialization_relation
    f finv g ginv h hinv
    (keygen_decoded_public_key (keygen_public_key_bytes h))
    (keygen_public_key_bytes h).
proof.
  move=> Hrelation.
  have Hrange := keygen_public_h_tobytes_input_qrange
    f finv g ginv h hinv Hrelation.
  rewrite /keygen_public_key_serialization_relation.
  split; first exact Hrelation.
  split; first done.
  split; first done.
  split.
  + exact (keygen_decoded_public_key_roundtrip h Hrange).
  split.
  + exact (keygen_decoded_public_key_canonical_range h Hrange).
  split.
  + exact (keygen_decoded_public_key_mod_q h Hrange).
  exact (keygen_decoded_h_f_equals_g f finv g ginv h hinv Hrelation).
qed.

lemma keygen_public_key_procedure_result_implies_relation
    (f finv g ginv h hinv : W16.t Array768.t)
    (pk : W8.t Array1152.t) :
  keygen_keypair_ntt_relation f finv g ginv h hinv =>
  pk = NTRUPlus768PolyToBytesProof.poly_tobytes_spec h =>
  keygen_public_key_serialization_relation
    f finv g ginv h hinv (keygen_decoded_public_key pk) pk.
proof.
  move=> Hrelation Hpk.
  have Hpk_bytes : pk = keygen_public_key_bytes h.
  + rewrite Hpk.
    exact (keygen_public_key_bytes_procedure_specE h).
  have Hrange := keygen_public_h_tobytes_input_qrange
    f finv g ginv h hinv Hrelation.
  rewrite /keygen_public_key_serialization_relation.
  split; first exact Hrelation.
  split; first exact Hpk_bytes.
  split; first done.
  split.
  + rewrite Hpk_bytes.
    exact (keygen_decoded_public_key_roundtrip h Hrange).
  split.
  + rewrite Hpk_bytes.
    exact (keygen_decoded_public_key_canonical_range h Hrange).
  split.
  + rewrite Hpk_bytes.
    exact (keygen_decoded_public_key_mod_q h Hrange).
  rewrite Hpk_bytes.
  exact (keygen_decoded_h_f_equals_g f finv g ginv h hinv Hrelation).
qed.

lemma keygen_public_key_jasmin_tobytes_functional
    (f finv g ginv h hinv : W16.t Array768.t)
    (pk0 : W8.t Array1152.t) :
  keygen_keypair_ntt_relation f finv g ginv h hinv =>
  hoare [NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes :
    rp = pk0 /\ ap = h ==>
    res = NTRUPlus768PolyToBytesProof.poly_tobytes_spec h].
proof.
  move=> Hrelation.
  have Hrange := keygen_public_h_tobytes_input_qrange
    f finv g ginv h hinv Hrelation.
  have Hprocedure_range :
      NTRUPlus768PolyToBytesProof.poly_tobytes_input_qrange h.
  + rewrite poly_tobytes_procedure_input_qrangeE.
    exact Hrange.
  exact (NTRUPlus768PolyToBytesProof.poly_tobytes_functional
    pk0 h Hprocedure_range).
qed.

lemma keygen_public_key_jasmin_tobytes_correct
    (f finv g ginv h hinv : W16.t Array768.t)
    (pk0 : W8.t Array1152.t) :
  keygen_keypair_ntt_relation f finv g ginv h hinv =>
  phoare [NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes :
    rp = pk0 /\ ap = h ==>
    res = NTRUPlus768PolyToBytesProof.poly_tobytes_spec h] = 1%r.
proof.
  move=> Hrelation.
  have Hrange := keygen_public_h_tobytes_input_qrange
    f finv g ginv h hinv Hrelation.
  have Hprocedure_range :
      NTRUPlus768PolyToBytesProof.poly_tobytes_input_qrange h.
  + rewrite poly_tobytes_procedure_input_qrangeE.
    exact Hrange.
  exact (NTRUPlus768PolyToBytesProof.poly_tobytes_correct
    pk0 h Hprocedure_range).
qed.

lemma keygen_sampled_public_key_jasmin_tobytes_functional
    (fbuf gbuf : W8.t Array192.t)
    (finv ginv h hinv : W16.t Array768.t)
    (pk0 : W8.t Array1152.t) :
  keygen_keypair_ntt_relation
    (keygen_f_ntt_spec fbuf) finv
    (keygen_g_ntt_spec gbuf) ginv h hinv =>
  hoare [NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes :
    rp = pk0 /\ ap = h ==>
    res = NTRUPlus768PolyToBytesProof.poly_tobytes_spec h].
proof.
  move=> Hrelation.
  exact (keygen_public_key_jasmin_tobytes_functional
    (keygen_f_ntt_spec fbuf) finv
    (keygen_g_ntt_spec gbuf) ginv h hinv pk0 Hrelation).
qed.

lemma keygen_sampled_public_key_jasmin_tobytes_correct
    (fbuf gbuf : W8.t Array192.t)
    (finv ginv h hinv : W16.t Array768.t)
    (pk0 : W8.t Array1152.t) :
  keygen_keypair_ntt_relation
    (keygen_f_ntt_spec fbuf) finv
    (keygen_g_ntt_spec gbuf) ginv h hinv =>
  phoare [NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes :
    rp = pk0 /\ ap = h ==>
    res = NTRUPlus768PolyToBytesProof.poly_tobytes_spec h] = 1%r.
proof.
  move=> Hrelation.
  exact (keygen_public_key_jasmin_tobytes_correct
    (keygen_f_ntt_spec fbuf) finv
    (keygen_g_ntt_spec gbuf) ginv h hinv pk0 Hrelation).
qed.

lemma keygen_public_key_serialization_relation_outcome
    (f finv g ginv h hinv decoded_h : W16.t Array768.t)
    (pk : W8.t Array1152.t) :
  keygen_public_key_serialization_relation
    f finv g ginv h hinv decoded_h pk =>
  pk = keygen_public_key_bytes h /\
  decoded_h = keygen_decoded_public_key pk /\
  in_canonical_range768 decoded_h /\
  poly_coeff_eq_mod_q decoded_h h /\
  poly_basemul_qring decoded_h f g 192.
proof.
  by rewrite /keygen_public_key_serialization_relation => />.
qed.
