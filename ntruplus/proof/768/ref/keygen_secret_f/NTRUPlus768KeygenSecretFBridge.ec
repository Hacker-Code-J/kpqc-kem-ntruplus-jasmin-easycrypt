require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array4 Array192 Array768 Array1152.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768NTTSchedule.
require import NTRUPlus768BaseInvAlgebra.
require import NTRUPlus768PolyBasemulAlgebra.
require import NTRUPlus768PolyBasemulProof.
require import NTRUPlus768PolyBasemulInvNTTAlgebra.
require import NTRUPlus768PolyFromBytesAlgebra.
require import NTRUPlus768PolyToBytes NTRUPlus768PolyToBytesProof.
require import NTRUPlus768PolyToBytesAlgebra.
require import NTRUPlus768EncapPolyBasemulAddAlgebra.
require import NTRUPlus768KeygenSamplerAlgebra.
require import NTRUPlus768KeygenSamplerBridge.
require import NTRUPlus768KeygenInverseBridge.
require import NTRUPlus768KeygenHBridge.
require import NTRUPlus768KeygenPublicKeyBridge.
require import NTRUPlus768EvaluationSemantics.
require import NTRUPlus768TerminalRepresentation.
require import NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768ForwardNTTSemantics.
require import NTRUPlus768ValidKeyDecapM1Semantics.

import Ring.IntID IntOrder.

(* Scope: the first 1152 secret-key bytes only.  This theory ties the exact
   `poly_tobytes(sk, f)` / `poly_frombytes(&f, sk)` seam to the existing NTT
   keypair relation and terminal representation of sampled secret `f`.  It
   deliberately avoids hinv/hash suffix provenance, no-wrap claims, crepmod3
   exact recovery, formal production-C semantics, or C/Jasmin equivalence. *)

op keygen_secret_f_bytes
    (f : W16.t Array768.t) : W8.t Array1152.t =
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec f.

op keygen_decoded_secret_f
    (sk : W8.t Array1152.t) : W16.t Array768.t =
  NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec sk.

op keygen_secret_f_serialization_relation
    (f finv g ginv h hinv decoded_h decoded_f : W16.t Array768.t)
    (pk sk_f : W8.t Array1152.t) (F : poly) : bool =
  NTRUPlus768KeygenPublicKeyBridge.keygen_public_key_serialization_relation
    f finv g ginv h hinv decoded_h pk /\
  sk_f = keygen_secret_f_bytes f /\
  decoded_f = keygen_decoded_secret_f sk_f /\
  decoded_f = NTRUPlus768PolyToBytesAlgebra.poly_tobytes_canonical_spec f /\
  in_canonical_range768 decoded_f /\
  NTRUPlus768KeygenPublicKeyBridge.poly_coeff_eq_mod_q decoded_f f /\
  terminal_represents f F /\
  terminal_represents decoded_f F /\
  poly_basemul_qring decoded_h decoded_f g 192.

lemma keygen_secret_f_bytes_procedure_specE
    (f : W16.t Array768.t) :
  NTRUPlus768PolyToBytesProof.poly_tobytes_spec f =
  keygen_secret_f_bytes f.
proof.
  rewrite /keygen_secret_f_bytes
    NTRUPlus768PolyToBytesAlgebra.poly_tobytes_procedure_specE.
  done.
qed.

lemma keygen_secret_f_bytes_as_public_key_bytes
    (f : W16.t Array768.t) :
  keygen_secret_f_bytes f =
  NTRUPlus768KeygenPublicKeyBridge.keygen_public_key_bytes f.
proof. done. qed.

lemma keygen_decoded_secret_f_as_public_key_decoder
    (sk : W8.t Array1152.t) :
  keygen_decoded_secret_f sk =
  NTRUPlus768KeygenPublicKeyBridge.keygen_decoded_public_key sk.
proof. done. qed.

lemma keygen_secret_f_tobytes_input_qrange
    (f : W16.t Array768.t) :
  in_qrange768 f =>
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange f.
proof.
  move=> Hf.
  exact
    (NTRUPlus768KeygenPublicKeyBridge.in_qrange768_poly_tobytes_input_qrange
      f Hf).
qed.

lemma keygen_decoded_secret_f_roundtrip
    (f : W16.t Array768.t) :
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange f =>
  keygen_decoded_secret_f (keygen_secret_f_bytes f) =
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_canonical_spec f.
proof.
  move=> Hf.
  rewrite keygen_decoded_secret_f_as_public_key_decoder
          keygen_secret_f_bytes_as_public_key_bytes.
  exact
    (NTRUPlus768KeygenPublicKeyBridge.keygen_decoded_public_key_roundtrip
      f Hf).
qed.

lemma keygen_decoded_secret_f_coeff_range
    (f : W16.t Array768.t) (j : int) :
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange f =>
  0 <= j < 768 =>
  0 <= coeff (keygen_decoded_secret_f (keygen_secret_f_bytes f)).[j] < q.
proof.
  move=> Hf Hj.
  rewrite keygen_decoded_secret_f_as_public_key_decoder
          keygen_secret_f_bytes_as_public_key_bytes.
  exact
    (NTRUPlus768KeygenPublicKeyBridge.keygen_decoded_public_key_coeff_range
      f j Hf Hj).
qed.

lemma keygen_decoded_secret_f_canonical_range
    (f : W16.t Array768.t) :
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange f =>
  in_canonical_range768
    (keygen_decoded_secret_f (keygen_secret_f_bytes f)).
proof.
  move=> Hf.
  rewrite keygen_decoded_secret_f_as_public_key_decoder
          keygen_secret_f_bytes_as_public_key_bytes.
  exact
    (NTRUPlus768KeygenPublicKeyBridge.keygen_decoded_public_key_canonical_range
      f Hf).
qed.

lemma keygen_decoded_secret_f_mod_q
    (f : W16.t Array768.t) :
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange f =>
  NTRUPlus768KeygenPublicKeyBridge.poly_coeff_eq_mod_q
    (keygen_decoded_secret_f (keygen_secret_f_bytes f)) f.
proof.
  move=> Hf.
  rewrite keygen_decoded_secret_f_as_public_key_decoder
          keygen_secret_f_bytes_as_public_key_bytes.
  exact
    (NTRUPlus768KeygenPublicKeyBridge.keygen_decoded_public_key_mod_q
      f Hf).
qed.

lemma poly_coeff_eq_mod_q_block_poly
    (a a' : W16.t Array768.t) (k : int) :
  NTRUPlus768KeygenPublicKeyBridge.poly_coeff_eq_mod_q a' a =>
  0 <= k < 192 =>
  block_poly (block4 a' k) = block_poly (block4 a k).
proof.
  move=> Heq Hk.
  apply block_poly_eq_of_lifts.
  + rewrite /lift_word.
    apply lift_int_eq.
    exact
      (NTRUPlus768KeygenPublicKeyBridge.poly_coeff_eq_mod_q_block4
        a a' k 0 Heq Hk
        NTRUPlus768KeygenPublicKeyBridge.block4_offset0_range).
  + rewrite /lift_word.
    apply lift_int_eq.
    exact
      (NTRUPlus768KeygenPublicKeyBridge.poly_coeff_eq_mod_q_block4
        a a' k 1 Heq Hk
        NTRUPlus768KeygenPublicKeyBridge.block4_offset1_range).
  + rewrite /lift_word.
    apply lift_int_eq.
    exact
      (NTRUPlus768KeygenPublicKeyBridge.poly_coeff_eq_mod_q_block4
        a a' k 2 Heq Hk
        NTRUPlus768KeygenPublicKeyBridge.block4_offset2_range).
  rewrite /lift_word.
  apply lift_int_eq.
  exact
    (NTRUPlus768KeygenPublicKeyBridge.poly_coeff_eq_mod_q_block4
      a a' k 3 Heq Hk
      NTRUPlus768KeygenPublicKeyBridge.block4_offset3_range).
qed.

lemma terminal_represents_mod_q_replacement
    (a a' : W16.t Array768.t) (p : poly) :
  NTRUPlus768KeygenPublicKeyBridge.poly_coeff_eq_mod_q a' a =>
  terminal_represents a p =>
  terminal_represents a' p.
proof.
  move=> Heq Hrep k Hk.
  rewrite (poly_coeff_eq_mod_q_block_poly a a' k Heq Hk).
  exact (Hrep k Hk).
qed.

lemma poly_basemul_qring_right_mod_q_congr
    (a b b' r : W16.t Array768.t) :
  NTRUPlus768KeygenPublicKeyBridge.poly_coeff_eq_mod_q b' b =>
  poly_basemul_qring a b r 192 =>
  poly_basemul_qring a b' r 192.
proof.
  move=> Heq Hproduct k Hk.
  have Hblock := Hproduct k Hk.
  move: Hblock => /= [Hrange [H0 [H1 [H2 H3]]]].
  have C0 :
      coeff0 (block4 a k) (block4 b' k) (terminal_value k) %% q =
      coeff0 (block4 a k) (block4 b k) (terminal_value k) %% q.
  + have :=
        coeff0_mod_congr_right
          (block4 a k) (block4 b' k) (terminal_value k)
          (coeff (block4 b k).[0])
          (coeff (block4 b k).[1])
          (coeff (block4 b k).[2])
          (coeff (block4 b k).[3])
          (NTRUPlus768KeygenPublicKeyBridge.poly_coeff_eq_mod_q_block4
            b b' k 0 Heq Hk
            NTRUPlus768KeygenPublicKeyBridge.block4_offset0_range)
          (NTRUPlus768KeygenPublicKeyBridge.poly_coeff_eq_mod_q_block4
            b b' k 1 Heq Hk
            NTRUPlus768KeygenPublicKeyBridge.block4_offset1_range)
          (NTRUPlus768KeygenPublicKeyBridge.poly_coeff_eq_mod_q_block4
            b b' k 2 Heq Hk
            NTRUPlus768KeygenPublicKeyBridge.block4_offset2_range)
          (NTRUPlus768KeygenPublicKeyBridge.poly_coeff_eq_mod_q_block4
            b b' k 3 Heq Hk
            NTRUPlus768KeygenPublicKeyBridge.block4_offset3_range).
    by rewrite /coeff0.
  have C1 :
      coeff1 (block4 a k) (block4 b' k) (terminal_value k) %% q =
      coeff1 (block4 a k) (block4 b k) (terminal_value k) %% q.
  + have :=
        coeff1_mod_congr_right
          (block4 a k) (block4 b' k) (terminal_value k)
          (coeff (block4 b k).[0])
          (coeff (block4 b k).[1])
          (coeff (block4 b k).[2])
          (coeff (block4 b k).[3])
          (NTRUPlus768KeygenPublicKeyBridge.poly_coeff_eq_mod_q_block4
            b b' k 0 Heq Hk
            NTRUPlus768KeygenPublicKeyBridge.block4_offset0_range)
          (NTRUPlus768KeygenPublicKeyBridge.poly_coeff_eq_mod_q_block4
            b b' k 1 Heq Hk
            NTRUPlus768KeygenPublicKeyBridge.block4_offset1_range)
          (NTRUPlus768KeygenPublicKeyBridge.poly_coeff_eq_mod_q_block4
            b b' k 2 Heq Hk
            NTRUPlus768KeygenPublicKeyBridge.block4_offset2_range)
          (NTRUPlus768KeygenPublicKeyBridge.poly_coeff_eq_mod_q_block4
            b b' k 3 Heq Hk
            NTRUPlus768KeygenPublicKeyBridge.block4_offset3_range).
    by rewrite /coeff1.
  have C2 :
      coeff2 (block4 a k) (block4 b' k) (terminal_value k) %% q =
      coeff2 (block4 a k) (block4 b k) (terminal_value k) %% q.
  + have :=
        coeff2_mod_congr_right
          (block4 a k) (block4 b' k) (terminal_value k)
          (coeff (block4 b k).[0])
          (coeff (block4 b k).[1])
          (coeff (block4 b k).[2])
          (coeff (block4 b k).[3])
          (NTRUPlus768KeygenPublicKeyBridge.poly_coeff_eq_mod_q_block4
            b b' k 0 Heq Hk
            NTRUPlus768KeygenPublicKeyBridge.block4_offset0_range)
          (NTRUPlus768KeygenPublicKeyBridge.poly_coeff_eq_mod_q_block4
            b b' k 1 Heq Hk
            NTRUPlus768KeygenPublicKeyBridge.block4_offset1_range)
          (NTRUPlus768KeygenPublicKeyBridge.poly_coeff_eq_mod_q_block4
            b b' k 2 Heq Hk
            NTRUPlus768KeygenPublicKeyBridge.block4_offset2_range)
          (NTRUPlus768KeygenPublicKeyBridge.poly_coeff_eq_mod_q_block4
            b b' k 3 Heq Hk
            NTRUPlus768KeygenPublicKeyBridge.block4_offset3_range).
    by rewrite /coeff2.
  have C3 :
      coeff3 (block4 a k) (block4 b' k) (terminal_value k) %% q =
      coeff3 (block4 a k) (block4 b k) (terminal_value k) %% q.
  + have :=
        coeff3_mod_congr_right
          (block4 a k) (block4 b' k) (terminal_value k)
          (coeff (block4 b k).[0])
          (coeff (block4 b k).[1])
          (coeff (block4 b k).[2])
          (coeff (block4 b k).[3])
          (NTRUPlus768KeygenPublicKeyBridge.poly_coeff_eq_mod_q_block4
            b b' k 0 Heq Hk
            NTRUPlus768KeygenPublicKeyBridge.block4_offset0_range)
          (NTRUPlus768KeygenPublicKeyBridge.poly_coeff_eq_mod_q_block4
            b b' k 1 Heq Hk
            NTRUPlus768KeygenPublicKeyBridge.block4_offset1_range)
          (NTRUPlus768KeygenPublicKeyBridge.poly_coeff_eq_mod_q_block4
            b b' k 2 Heq Hk
            NTRUPlus768KeygenPublicKeyBridge.block4_offset2_range)
          (NTRUPlus768KeygenPublicKeyBridge.poly_coeff_eq_mod_q_block4
            b b' k 3 Heq Hk
            NTRUPlus768KeygenPublicKeyBridge.block4_offset3_range).
    by rewrite /coeff3.
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

lemma keygen_secret_f_qrange
    (f finv g ginv h hinv : W16.t Array768.t) :
  keygen_keypair_ntt_relation f finv g ginv h hinv =>
  in_qrange768 f.
proof.
  move=> Hrelation.
  rewrite /keygen_keypair_ntt_relation in Hrelation.
  move: Hrelation => [_ [_ [_ [_ [_ Hhinv_gf]]]]].
  exact
    (NTRUPlus768KeygenPublicKeyBridge.poly_basemul_qring_output_in_qrange768
      hinv g f Hhinv_gf).
qed.

lemma keygen_decoded_h_decoded_f_equals_g
    (f finv g ginv h hinv : W16.t Array768.t) :
  keygen_keypair_ntt_relation f finv g ginv h hinv =>
  poly_basemul_qring
    (NTRUPlus768KeygenPublicKeyBridge.keygen_decoded_public_key
      (NTRUPlus768KeygenPublicKeyBridge.keygen_public_key_bytes h))
    (keygen_decoded_secret_f (keygen_secret_f_bytes f))
    g 192.
proof.
  move=> Hrelation.
  have Hf_range :=
    keygen_secret_f_qrange f finv g ginv h hinv Hrelation.
  have Hf_tobytes :=
    keygen_secret_f_tobytes_input_qrange f Hf_range.
  have Hdecoded_h_f :=
    NTRUPlus768KeygenPublicKeyBridge.keygen_decoded_h_f_equals_g
      f finv g ginv h hinv Hrelation.
  have Hdecoded_f_mod_q := keygen_decoded_secret_f_mod_q f Hf_tobytes.
  exact
    (poly_basemul_qring_right_mod_q_congr
      (NTRUPlus768KeygenPublicKeyBridge.keygen_decoded_public_key
        (NTRUPlus768KeygenPublicKeyBridge.keygen_public_key_bytes h))
      f
      (keygen_decoded_secret_f (keygen_secret_f_bytes f))
      g
      Hdecoded_f_mod_q
      Hdecoded_h_f).
qed.

lemma keygen_sampled_secret_f_tobytes_input_qrange
    (fbuf : W8.t Array192.t) :
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange
    (NTRUPlus768KeygenSamplerBridge.keygen_f_ntt_spec fbuf).
proof.
  apply keygen_secret_f_tobytes_input_qrange.
  exact (NTRUPlus768KeygenInverseBridge.keygen_f_ntt_qrange fbuf).
qed.

lemma keygen_secret_f_jasmin_tobytes_functional
    (f finv g ginv h hinv : W16.t Array768.t)
    (sk0 : W8.t Array1152.t) :
  keygen_keypair_ntt_relation f finv g ginv h hinv =>
  hoare [NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes :
    rp = sk0 /\ ap = f ==>
    res = NTRUPlus768PolyToBytesProof.poly_tobytes_spec f].
proof.
  move=> Hrelation.
  have Hrange :=
    keygen_secret_f_tobytes_input_qrange f
      (keygen_secret_f_qrange f finv g ginv h hinv Hrelation).
  have Hprocedure_range :
      NTRUPlus768PolyToBytesProof.poly_tobytes_input_qrange f.
  + rewrite
      NTRUPlus768PolyToBytesAlgebra.poly_tobytes_procedure_input_qrangeE.
    exact Hrange.
  exact
    (NTRUPlus768PolyToBytesProof.poly_tobytes_functional
      sk0 f Hprocedure_range).
qed.

lemma keygen_secret_f_jasmin_tobytes_correct
    (f finv g ginv h hinv : W16.t Array768.t)
    (sk0 : W8.t Array1152.t) :
  keygen_keypair_ntt_relation f finv g ginv h hinv =>
  phoare [NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes :
    rp = sk0 /\ ap = f ==>
    res = NTRUPlus768PolyToBytesProof.poly_tobytes_spec f] = 1%r.
proof.
  move=> Hrelation.
  have Hrange :=
    keygen_secret_f_tobytes_input_qrange f
      (keygen_secret_f_qrange f finv g ginv h hinv Hrelation).
  have Hprocedure_range :
      NTRUPlus768PolyToBytesProof.poly_tobytes_input_qrange f.
  + rewrite
      NTRUPlus768PolyToBytesAlgebra.poly_tobytes_procedure_input_qrangeE.
    exact Hrange.
  exact
    (NTRUPlus768PolyToBytesProof.poly_tobytes_correct
      sk0 f Hprocedure_range).
qed.

lemma keygen_sampled_secret_f_terminal_represents
    (fbuf : W8.t Array192.t) :
  terminal_represents
    (NTRUPlus768KeygenSamplerBridge.keygen_f_ntt_spec fbuf)
    (input_poly (keygen_f_pre_ntt_spec fbuf)).
proof.
  rewrite /NTRUPlus768KeygenSamplerBridge.keygen_f_ntt_spec.
  exact
    (NTRUPlus768ForwardNTTSemantics.forward_ntt_spec_terminal_represents
      (keygen_f_pre_ntt_spec fbuf)
      (keygen_f_pre_ntt_input_qrange fbuf)).
qed.

lemma keygen_sampled_decoded_secret_f_terminal_represents
    (fbuf : W8.t Array192.t) :
  terminal_represents
    (keygen_decoded_secret_f
      (keygen_secret_f_bytes
        (NTRUPlus768KeygenSamplerBridge.keygen_f_ntt_spec fbuf)))
    (input_poly (keygen_f_pre_ntt_spec fbuf)).
proof.
  have Hrep :
      terminal_represents
        (NTRUPlus768KeygenSamplerBridge.keygen_f_ntt_spec fbuf)
        (input_poly (keygen_f_pre_ntt_spec fbuf)).
  + exact (keygen_sampled_secret_f_terminal_represents fbuf).
  have Hdecoded_mod_q :
      NTRUPlus768KeygenPublicKeyBridge.poly_coeff_eq_mod_q
        (keygen_decoded_secret_f
          (keygen_secret_f_bytes
            (NTRUPlus768KeygenSamplerBridge.keygen_f_ntt_spec fbuf)))
        (NTRUPlus768KeygenSamplerBridge.keygen_f_ntt_spec fbuf).
  + exact
      (keygen_decoded_secret_f_mod_q
        (NTRUPlus768KeygenSamplerBridge.keygen_f_ntt_spec fbuf)
        (keygen_sampled_secret_f_tobytes_input_qrange fbuf)).
  exact
    (terminal_represents_mod_q_replacement
      (NTRUPlus768KeygenSamplerBridge.keygen_f_ntt_spec fbuf)
      (keygen_decoded_secret_f
        (keygen_secret_f_bytes
          (NTRUPlus768KeygenSamplerBridge.keygen_f_ntt_spec fbuf)))
      (input_poly (keygen_f_pre_ntt_spec fbuf))
      Hdecoded_mod_q
      Hrep).
qed.

lemma keygen_secret_f_serialization_relation_intro
    (f finv g ginv h hinv : W16.t Array768.t) (F : poly) :
  keygen_keypair_ntt_relation f finv g ginv h hinv =>
  terminal_represents f F =>
  keygen_secret_f_serialization_relation
    f finv g ginv h hinv
    (NTRUPlus768KeygenPublicKeyBridge.keygen_decoded_public_key
      (NTRUPlus768KeygenPublicKeyBridge.keygen_public_key_bytes h))
    (keygen_decoded_secret_f (keygen_secret_f_bytes f))
    (NTRUPlus768KeygenPublicKeyBridge.keygen_public_key_bytes h)
    (keygen_secret_f_bytes f) F.
proof.
  move=> Hrelation Hf_rep.
  have Hpublic :=
    NTRUPlus768KeygenPublicKeyBridge.keygen_public_key_serialization_relation_intro
      f finv g ginv h hinv Hrelation.
  have Htobytes :=
    keygen_secret_f_tobytes_input_qrange f
      (keygen_secret_f_qrange f finv g ginv h hinv Hrelation).
  have Hroundtrip := keygen_decoded_secret_f_roundtrip f Htobytes.
  have Hcanonical := keygen_decoded_secret_f_canonical_range f Htobytes.
  have Hmod := keygen_decoded_secret_f_mod_q f Htobytes.
  have Hdecoded_rep :=
    terminal_represents_mod_q_replacement f
      (keygen_decoded_secret_f (keygen_secret_f_bytes f)) F
      Hmod Hf_rep.
  have Hproduct :=
    keygen_decoded_h_decoded_f_equals_g f finv g ginv h hinv Hrelation.
  rewrite /keygen_secret_f_serialization_relation.
  split; first exact Hpublic.
  split; first done.
  split; first done.
  split; first exact Hroundtrip.
  split; first exact Hcanonical.
  split; first exact Hmod.
  split; first exact Hf_rep.
  split; first exact Hdecoded_rep.
  exact Hproduct.
qed.

lemma keygen_sampled_secret_f_serialization_relation_intro
    (fbuf gbuf : W8.t Array192.t)
    (finv ginv h hinv : W16.t Array768.t) :
  keygen_keypair_ntt_relation
    (NTRUPlus768KeygenSamplerBridge.keygen_f_ntt_spec fbuf) finv
    (NTRUPlus768KeygenSamplerBridge.keygen_g_ntt_spec gbuf) ginv h hinv =>
  keygen_secret_f_serialization_relation
    (NTRUPlus768KeygenSamplerBridge.keygen_f_ntt_spec fbuf) finv
    (NTRUPlus768KeygenSamplerBridge.keygen_g_ntt_spec gbuf) ginv h hinv
    (NTRUPlus768KeygenPublicKeyBridge.keygen_decoded_public_key
      (NTRUPlus768KeygenPublicKeyBridge.keygen_public_key_bytes h))
    (keygen_decoded_secret_f
      (keygen_secret_f_bytes
        (NTRUPlus768KeygenSamplerBridge.keygen_f_ntt_spec fbuf)))
    (NTRUPlus768KeygenPublicKeyBridge.keygen_public_key_bytes h)
    (keygen_secret_f_bytes
      (NTRUPlus768KeygenSamplerBridge.keygen_f_ntt_spec fbuf))
    (input_poly (keygen_f_pre_ntt_spec fbuf)).
proof.
  move=> Hrelation.
  exact
    (keygen_secret_f_serialization_relation_intro
      (NTRUPlus768KeygenSamplerBridge.keygen_f_ntt_spec fbuf) finv
      (NTRUPlus768KeygenSamplerBridge.keygen_g_ntt_spec gbuf) ginv h hinv
      (input_poly (keygen_f_pre_ntt_spec fbuf)) Hrelation
      (keygen_sampled_secret_f_terminal_represents fbuf)).
qed.

lemma keygen_secret_f_serialization_relation_outcome
    (f finv g ginv h hinv decoded_h decoded_f : W16.t Array768.t)
    (pk sk_f : W8.t Array1152.t) (F : poly) :
  keygen_secret_f_serialization_relation
    f finv g ginv h hinv decoded_h decoded_f pk sk_f F =>
  sk_f = keygen_secret_f_bytes f /\
  decoded_f = keygen_decoded_secret_f sk_f /\
  decoded_f = NTRUPlus768PolyToBytesAlgebra.poly_tobytes_canonical_spec f /\
  in_canonical_range768 decoded_f /\
  NTRUPlus768KeygenPublicKeyBridge.poly_coeff_eq_mod_q decoded_f f /\
  terminal_represents decoded_f F /\
  poly_basemul_qring decoded_h decoded_f g 192.
proof.
  by rewrite /keygen_secret_f_serialization_relation => />.
qed.

lemma keygen_secret_f_valid_key_m1_spec_semantics
    (f finv g ginv h hinv decoded_h decoded_f r m c product_ntt :
      W16.t Array768.t)
    (pk sk_f : W8.t Array1152.t) (F G R M : poly) :
  keygen_secret_f_serialization_relation
    f finv g ginv h hinv decoded_h decoded_f pk sk_f F =>
  terminal_represents g G =>
  terminal_represents r R =>
  terminal_represents m M =>
  poly_basemul_add_qring decoded_h r m c 192 =>
  poly_basemul_qring c decoded_f product_ntt 192 =>
  valid_key_decap_m1_semantics G R M F
    (NTRUPlus768InvNTTAlgebra.inverse_invntt_spec product_ntt).
proof.
  move=> Hserialization Hg Hr Hm Hcrm Hcf.
  have Houtcome :=
    keygen_secret_f_serialization_relation_outcome
      f finv g ginv h hinv decoded_h decoded_f pk sk_f F Hserialization.
  move: Houtcome => [_ [_ [_ [_ [_ [Hdecoded_rep Hkey]]]]]].
  exact
    (valid_key_decap_m1_local_spec_semantics
      decoded_h decoded_f g r m c product_ntt F G R M
      Hdecoded_rep Hg Hr Hm Hkey Hcrm Hcf).
qed.
