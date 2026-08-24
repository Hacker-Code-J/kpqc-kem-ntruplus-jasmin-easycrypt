require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord.

require import Array192 Array768.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768Crepmod3Algebra.
require import NTRUPlus768PolyCBD1Algebra.
require import NTRUPlus768NTTStage1Algebra.

import Ring.IntID IntOrder.

(* Coefficient-domain key-generation shaping only.  This theory deliberately
   stops before the forward NTT and poly_baseinv. *)

op keygen_delta0 (k : int) : int = if k = 0 then 1 else 0.

op poly_triple_spec (p : W16.t Array768.t) : W16.t Array768.t =
  Array768.init (fun k => W16.of_int (3 * coeff p.[k])).

op keygen_f_pre_ntt_spec (buf : W8.t Array192.t) : W16.t Array768.t =
  Array768.init (fun k =>
    W16.of_int
      (3 * NTRUPlus768PolyCBD1Algebra.poly_cbd1_coeff_int buf k +
       keygen_delta0 k)).

op keygen_g_pre_ntt_spec (buf : W8.t Array192.t) : W16.t Array768.t =
  poly_triple_spec (NTRUPlus768PolyCBD1Algebra.poly_cbd1_spec buf).

op keygen_f_mod3_shape (p : W16.t Array768.t) : bool =
  forall k, 0 <= k < 768 => coeff p.[k] %% 3 = keygen_delta0 k.

op keygen_g_mod3_shape (p : W16.t Array768.t) : bool =
  forall k, 0 <= k < 768 => coeff p.[k] %% 3 = 0.

op keygen_f_small_shape (p : W16.t Array768.t) : bool =
  -2 <= coeff p.[0] <= 4 /\
  forall k, 1 <= k < 768 => -3 <= coeff p.[k] <= 3.

op keygen_g_small_shape (p : W16.t Array768.t) : bool =
  forall k, 0 <= k < 768 => -3 <= coeff p.[k] <= 3.

lemma keygen_delta0_range (k : int) :
  0 <= keygen_delta0 k <= 1.
proof. by rewrite /keygen_delta0; smt(). qed.

lemma poly_triple_spec_coeff
    (p : W16.t Array768.t) (k : int) :
  0 <= k < 768 =>
  W16.min_sint <= 3 * coeff p.[k] <= W16.max_sint =>
  coeff (poly_triple_spec p).[k] = 3 * coeff p.[k].
proof.
  move=> Hk Hbound.
  rewrite /poly_triple_spec Array768.initiE 1:/#.
  exact
    (NTRUPlus768Crepmod3Algebra.coeff_of_word_small
      (3 * coeff p.[k]) Hbound).
qed.

lemma poly_triple_sampled_coeff
    (buf : W8.t Array192.t) (k : int) :
  0 <= k < 768 =>
  coeff
    (poly_triple_spec
      (NTRUPlus768PolyCBD1Algebra.poly_cbd1_spec buf)).[k] =
  3 * NTRUPlus768PolyCBD1Algebra.poly_cbd1_coeff_int buf k.
proof.
  move=> Hk.
  have Hsample :=
    NTRUPlus768PolyCBD1Algebra.poly_cbd1_coeff_int_range buf k Hk.
  have Hcoeff :=
    NTRUPlus768PolyCBD1Algebra.poly_cbd1_spec_coeff buf k Hk.
  have Hbound :
      W16.min_sint <=
        3 * coeff (NTRUPlus768PolyCBD1Algebra.poly_cbd1_spec buf).[k] <=
      W16.max_sint by rewrite Hcoeff; smt().
  have Htriple := poly_triple_spec_coeff
    (NTRUPlus768PolyCBD1Algebra.poly_cbd1_spec buf) k Hk Hbound.
  by rewrite Htriple Hcoeff.
qed.

lemma keygen_f_pre_ntt_coeff
    (buf : W8.t Array192.t) (k : int) :
  0 <= k < 768 =>
  coeff (keygen_f_pre_ntt_spec buf).[k] =
    3 * NTRUPlus768PolyCBD1Algebra.poly_cbd1_coeff_int buf k +
    keygen_delta0 k.
proof.
  move=> Hk.
  rewrite /keygen_f_pre_ntt_spec Array768.initiE 1:/#.
  have Hsample :=
    NTRUPlus768PolyCBD1Algebra.poly_cbd1_coeff_int_range buf k Hk.
  have Hdelta := keygen_delta0_range k.
  apply NTRUPlus768Crepmod3Algebra.coeff_of_word_small.
  smt().
qed.

lemma keygen_g_pre_ntt_coeff
    (buf : W8.t Array192.t) (k : int) :
  0 <= k < 768 =>
  coeff (keygen_g_pre_ntt_spec buf).[k] =
    3 * NTRUPlus768PolyCBD1Algebra.poly_cbd1_coeff_int buf k.
proof.
  move=> Hk.
  rewrite /keygen_g_pre_ntt_spec.
  exact (poly_triple_sampled_coeff buf k Hk).
qed.

lemma keygen_f_pre_ntt_constant_coeff
    (buf : W8.t Array192.t) :
  coeff (keygen_f_pre_ntt_spec buf).[0] =
    3 * NTRUPlus768PolyCBD1Algebra.poly_cbd1_coeff_int buf 0 + 1.
proof.
  rewrite keygen_f_pre_ntt_coeff 1:/# /keygen_delta0.
  done.
qed.

lemma keygen_f_pre_ntt_nonconstant_coeff
    (buf : W8.t Array192.t) (k : int) :
  1 <= k < 768 =>
  coeff (keygen_f_pre_ntt_spec buf).[k] =
    3 * NTRUPlus768PolyCBD1Algebra.poly_cbd1_coeff_int buf k.
proof.
  move=> Hk.
  rewrite keygen_f_pre_ntt_coeff 1:/# /keygen_delta0.
  by smt().
qed.

lemma keygen_f_pre_ntt_matches_triple_plus_one
    (buf : W8.t Array192.t) (k : int) :
  0 <= k < 768 =>
  coeff (keygen_f_pre_ntt_spec buf).[k] =
    coeff
      (poly_triple_spec
        (NTRUPlus768PolyCBD1Algebra.poly_cbd1_spec buf)).[k] +
    keygen_delta0 k.
proof.
  move=> Hk.
  rewrite keygen_f_pre_ntt_coeff 1:Hk poly_triple_sampled_coeff 1:Hk.
  done.
qed.

lemma keygen_f_pre_ntt_mod3
    (buf : W8.t Array192.t) :
  keygen_f_mod3_shape (keygen_f_pre_ntt_spec buf).
proof.
  move=> k Hk.
  rewrite keygen_f_pre_ntt_coeff 1:Hk /keygen_delta0.
  case (k = 0) => Hzero; smt().
qed.

lemma keygen_g_pre_ntt_mod3
    (buf : W8.t Array192.t) :
  keygen_g_mod3_shape (keygen_g_pre_ntt_spec buf).
proof.
  move=> k Hk.
  rewrite keygen_g_pre_ntt_coeff 1:Hk.
  smt().
qed.

lemma keygen_f_pre_ntt_small
    (buf : W8.t Array192.t) :
  keygen_f_small_shape (keygen_f_pre_ntt_spec buf).
proof.
  rewrite /keygen_f_small_shape.
  split.
  + rewrite keygen_f_pre_ntt_constant_coeff.
    have Hsample :=
      NTRUPlus768PolyCBD1Algebra.poly_cbd1_coeff_int_range buf 0 _.
    - smt().
    smt().
  move=> k Hk.
  rewrite keygen_f_pre_ntt_nonconstant_coeff 1:Hk.
  have Hsample :=
    NTRUPlus768PolyCBD1Algebra.poly_cbd1_coeff_int_range buf k _.
  + smt().
  smt().
qed.

lemma keygen_g_pre_ntt_small
    (buf : W8.t Array192.t) :
  keygen_g_small_shape (keygen_g_pre_ntt_spec buf).
proof.
  move=> k Hk.
  rewrite keygen_g_pre_ntt_coeff 1:Hk.
  have Hsample :=
    NTRUPlus768PolyCBD1Algebra.poly_cbd1_coeff_int_range buf k Hk.
  smt().
qed.

lemma keygen_f_pre_ntt_input_qrange
    (buf : W8.t Array192.t) :
  NTRUPlus768NTTStage1Algebra.input_qrange
    (keygen_f_pre_ntt_spec buf).
proof.
  move=> k Hk.
  rewrite /in_qrange keygen_f_pre_ntt_coeff 1:Hk /q.
  have Hsample :=
    NTRUPlus768PolyCBD1Algebra.poly_cbd1_coeff_int_range buf k Hk.
  have Hdelta := keygen_delta0_range k.
  smt().
qed.

lemma keygen_g_pre_ntt_input_qrange
    (buf : W8.t Array192.t) :
  NTRUPlus768NTTStage1Algebra.input_qrange
    (keygen_g_pre_ntt_spec buf).
proof.
  move=> k Hk.
  rewrite /in_qrange keygen_g_pre_ntt_coeff 1:Hk /q.
  have Hsample :=
    NTRUPlus768PolyCBD1Algebra.poly_cbd1_coeff_int_range buf k Hk.
  smt().
qed.
