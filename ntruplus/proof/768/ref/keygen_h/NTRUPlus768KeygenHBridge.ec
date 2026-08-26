require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord.

require import Array4 Array192 Array768.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768NTTSchedule.
require import NTRUPlus768BaseInvAlgebra.
require import NTRUPlus768PolyBaseInvBridge.
require import NTRUPlus768PolyBasemulProof.
require import NTRUPlus768PolyBasemulAlgebra.
require import NTRUPlus768KeygenSamplerBridge.
require import NTRUPlus768KeygenInverseBridge.

import Ring.IntID IntOrder.

(* Scope: terminal four-coefficient quotient-ring algebra and the verified
   Jasmin poly_basemul procedure only.  The proof composes the already-proved
   successful finv/ginv contracts with the two keypair products.  It does not
   claim production-C semantics or C/Jasmin equivalence, random-retry
   termination or probability, a high-level NTT/InvNTT ring homomorphism,
   public/secret-key serialization, hash provenance, aggregate CT/SCT, or
   full-KEM correctness. *)

op qring_unit4 : W16.t Array4.t =
  Array4.init (fun i => W16.of_int (if i = 0 then 1 else 0)).

op nested0
    (a b c : W16.t Array4.t) (z : int) : int =
  coeff a.[0] * coeff0 b c z +
  z * (coeff a.[1] * coeff3 b c z +
       coeff a.[2] * coeff2 b c z +
       coeff a.[3] * coeff1 b c z).

op nested1
    (a b c : W16.t Array4.t) (z : int) : int =
  coeff a.[0] * coeff1 b c z +
  coeff a.[1] * coeff0 b c z +
  z * (coeff a.[2] * coeff3 b c z +
       coeff a.[3] * coeff2 b c z).

op nested2
    (a b c : W16.t Array4.t) (z : int) : int =
  coeff a.[0] * coeff2 b c z +
  coeff a.[1] * coeff1 b c z +
  coeff a.[2] * coeff0 b c z +
  z * (coeff a.[3] * coeff3 b c z).

op nested3
    (a b c : W16.t Array4.t) (z : int) : int =
  coeff a.[0] * coeff3 b c z +
  coeff a.[1] * coeff2 b c z +
  coeff a.[2] * coeff1 b c z +
  coeff a.[3] * coeff0 b c z.

op block_product_qring
    (a b r : W16.t Array4.t) (z : int) : bool =
  coeff0 a b z %% q = coeff r.[0] %% q /\
  coeff1 a b z %% q = coeff r.[1] %% q /\
  coeff2 a b z %% q = coeff r.[2] %% q /\
  coeff3 a b z %% q = coeff r.[3] %% q.

op keygen_keypair_ntt_relation
    (f finv g ginv h hinv : W16.t Array768.t) : bool =
  poly_baseinv_success f finv /\
  poly_baseinv_success g ginv /\
  poly_basemul_qring g finv h 192 /\
  poly_basemul_qring f ginv hinv 192 /\
  poly_basemul_qring h f g 192 /\
  poly_basemul_qring hinv g f 192.

lemma qring_unit4_coeff0 : coeff qring_unit4.[0] = 1.
proof.
  rewrite /qring_unit4 Array4.initiE 1:/# /= /coeff.
  by rewrite W16.to_sintK_small 1:/#.
qed.

lemma qring_unit4_coeff1 : coeff qring_unit4.[1] = 0.
proof.
  rewrite /qring_unit4 Array4.initiE 1:/# /= /coeff.
  by rewrite W16.to_sintK_small 1:/#.
qed.

lemma qring_unit4_coeff2 : coeff qring_unit4.[2] = 0.
proof.
  rewrite /qring_unit4 Array4.initiE 1:/# /= /coeff.
  by rewrite W16.to_sintK_small 1:/#.
qed.

lemma qring_unit4_coeff3 : coeff qring_unit4.[3] = 0.
proof.
  rewrite /qring_unit4 Array4.initiE 1:/# /= /coeff.
  by rewrite W16.to_sintK_small 1:/#.
qed.

lemma coeff0_qring_unit4 (a : W16.t Array4.t) (z : int) :
  coeff0 a qring_unit4 z = coeff a.[0].
proof.
  rewrite /coeff0 qring_unit4_coeff0 qring_unit4_coeff1.
  rewrite qring_unit4_coeff2 qring_unit4_coeff3.
  ring.
qed.

lemma coeff1_qring_unit4 (a : W16.t Array4.t) (z : int) :
  coeff1 a qring_unit4 z = coeff a.[1].
proof.
  rewrite /coeff1 qring_unit4_coeff0 qring_unit4_coeff1.
  rewrite qring_unit4_coeff2 qring_unit4_coeff3.
  ring.
qed.

lemma coeff2_qring_unit4 (a : W16.t Array4.t) (z : int) :
  coeff2 a qring_unit4 z = coeff a.[2].
proof.
  rewrite /coeff2 qring_unit4_coeff0 qring_unit4_coeff1.
  rewrite qring_unit4_coeff2 qring_unit4_coeff3.
  ring.
qed.

lemma coeff3_qring_unit4 (a : W16.t Array4.t) (z : int) :
  coeff3 a qring_unit4 z = coeff a.[3].
proof.
  rewrite /coeff3 qring_unit4_coeff0 qring_unit4_coeff1.
  rewrite qring_unit4_coeff2 qring_unit4_coeff3.
  ring.
qed.

lemma coeff0_comm (a b : W16.t Array4.t) (z : int) :
  coeff0 a b z = coeff0 b a z.
proof. rewrite /coeff0; ring. qed.

lemma coeff1_comm (a b : W16.t Array4.t) (z : int) :
  coeff1 a b z = coeff1 b a z.
proof. rewrite /coeff1; ring. qed.

lemma coeff2_comm (a b : W16.t Array4.t) (z : int) :
  coeff2 a b z = coeff2 b a z.
proof. rewrite /coeff2; ring. qed.

lemma coeff3_comm (a b : W16.t Array4.t) (z : int) :
  coeff3 a b z = coeff3 b a z.
proof. rewrite /coeff3; ring. qed.

lemma nested0_swap_first_two
    (a b c : W16.t Array4.t) (z : int) :
  nested0 a b c z = nested0 b a c z.
proof.
  rewrite /nested0 /coeff0 /coeff1 /coeff2 /coeff3.
  ring.
qed.

lemma nested1_swap_first_two
    (a b c : W16.t Array4.t) (z : int) :
  nested1 a b c z = nested1 b a c z.
proof.
  rewrite /nested1 /coeff0 /coeff1 /coeff2 /coeff3.
  ring.
qed.

lemma nested2_swap_first_two
    (a b c : W16.t Array4.t) (z : int) :
  nested2 a b c z = nested2 b a c z.
proof.
  rewrite /nested2 /coeff0 /coeff1 /coeff2 /coeff3.
  ring.
qed.

lemma nested3_swap_first_two
    (a b c : W16.t Array4.t) (z : int) :
  nested3 a b c z = nested3 b a c z.
proof.
  rewrite /nested3 /coeff0 /coeff1 /coeff2 /coeff3.
  ring.
qed.

lemma nested0_inverse_cancel
    (numerator denominator inverse : W16.t Array4.t) (z : int) :
  block_inverse_qring denominator inverse z =>
  nested0 numerator denominator inverse z %% q = coeff numerator.[0] %% q.
proof.
  move=> [_ [H0 [H1 [H2 H3]]]].
  have Hunit :
      coeff0 numerator qring_unit4 z %% q =
      nested0 numerator denominator inverse z %% q.
  + apply (coeff0_mod_congr_right numerator qring_unit4 z
      (coeff0 denominator inverse z)
      (coeff1 denominator inverse z)
      (coeff2 denominator inverse z)
      (coeff3 denominator inverse z)).
    - rewrite qring_unit4_coeff0; smt().
    - rewrite qring_unit4_coeff1; smt().
    - rewrite qring_unit4_coeff2; smt().
    rewrite qring_unit4_coeff3; smt().
  move: Hunit; rewrite coeff0_qring_unit4; smt().
qed.

lemma nested1_inverse_cancel
    (numerator denominator inverse : W16.t Array4.t) (z : int) :
  block_inverse_qring denominator inverse z =>
  nested1 numerator denominator inverse z %% q = coeff numerator.[1] %% q.
proof.
  move=> [_ [H0 [H1 [H2 H3]]]].
  have Hunit :
      coeff1 numerator qring_unit4 z %% q =
      nested1 numerator denominator inverse z %% q.
  + apply (coeff1_mod_congr_right numerator qring_unit4 z
      (coeff0 denominator inverse z)
      (coeff1 denominator inverse z)
      (coeff2 denominator inverse z)
      (coeff3 denominator inverse z)).
    - rewrite qring_unit4_coeff0; smt().
    - rewrite qring_unit4_coeff1; smt().
    - rewrite qring_unit4_coeff2; smt().
    rewrite qring_unit4_coeff3; smt().
  move: Hunit; rewrite coeff1_qring_unit4; smt().
qed.

lemma nested2_inverse_cancel
    (numerator denominator inverse : W16.t Array4.t) (z : int) :
  block_inverse_qring denominator inverse z =>
  nested2 numerator denominator inverse z %% q = coeff numerator.[2] %% q.
proof.
  move=> [_ [H0 [H1 [H2 H3]]]].
  have Hunit :
      coeff2 numerator qring_unit4 z %% q =
      nested2 numerator denominator inverse z %% q.
  + apply (coeff2_mod_congr_right numerator qring_unit4 z
      (coeff0 denominator inverse z)
      (coeff1 denominator inverse z)
      (coeff2 denominator inverse z)
      (coeff3 denominator inverse z)).
    - rewrite qring_unit4_coeff0; smt().
    - rewrite qring_unit4_coeff1; smt().
    - rewrite qring_unit4_coeff2; smt().
    rewrite qring_unit4_coeff3; smt().
  move: Hunit; rewrite coeff2_qring_unit4; smt().
qed.

lemma nested3_inverse_cancel
    (numerator denominator inverse : W16.t Array4.t) (z : int) :
  block_inverse_qring denominator inverse z =>
  nested3 numerator denominator inverse z %% q = coeff numerator.[3] %% q.
proof.
  move=> [_ [H0 [H1 [H2 H3]]]].
  have Hunit :
      coeff3 numerator qring_unit4 z %% q =
      nested3 numerator denominator inverse z %% q.
  + apply (coeff3_mod_congr_right numerator qring_unit4 z
      (coeff0 denominator inverse z)
      (coeff1 denominator inverse z)
      (coeff2 denominator inverse z)
      (coeff3 denominator inverse z)).
    - rewrite qring_unit4_coeff0; smt().
    - rewrite qring_unit4_coeff1; smt().
    - rewrite qring_unit4_coeff2; smt().
    rewrite qring_unit4_coeff3; smt().
  move: Hunit; rewrite coeff3_qring_unit4; smt().
qed.

lemma block_inverse_product_cancel
    (denominator numerator inverse quotient : W16.t Array4.t) (z : int) :
  block_inverse_qring denominator inverse z =>
  block_product_qring numerator inverse quotient z =>
  block_product_qring quotient denominator numerator z.
proof.
  move=> Hinverse Hproduct.
  rewrite /block_product_qring in Hproduct.
  move: Hproduct => [H0 [H1 [H2 H3]]].
  have H0' : coeff quotient.[0] %% q = coeff0 numerator inverse z %% q
    by smt().
  have H1' : coeff quotient.[1] %% q = coeff1 numerator inverse z %% q
    by smt().
  have H2' : coeff quotient.[2] %% q = coeff2 numerator inverse z %% q
    by smt().
  have H3' : coeff quotient.[3] %% q = coeff3 numerator inverse z %% q
    by smt().
  rewrite /block_product_qring.
  split.
  + rewrite coeff0_comm.
    have Hlift : coeff0 denominator quotient z %% q =
        nested0 denominator numerator inverse z %% q.
    + exact (coeff0_mod_congr_right denominator quotient z
        (coeff0 numerator inverse z)
        (coeff1 numerator inverse z)
        (coeff2 numerator inverse z)
        (coeff3 numerator inverse z) H0' H1' H2' H3').
    rewrite Hlift (nested0_swap_first_two denominator numerator inverse z).
    exact (nested0_inverse_cancel numerator denominator inverse z Hinverse).
  split.
  + rewrite coeff1_comm.
    have Hlift : coeff1 denominator quotient z %% q =
        nested1 denominator numerator inverse z %% q.
    + exact (coeff1_mod_congr_right denominator quotient z
        (coeff0 numerator inverse z)
        (coeff1 numerator inverse z)
        (coeff2 numerator inverse z)
        (coeff3 numerator inverse z) H0' H1' H2' H3').
    rewrite Hlift (nested1_swap_first_two denominator numerator inverse z).
    exact (nested1_inverse_cancel numerator denominator inverse z Hinverse).
  split.
  + rewrite coeff2_comm.
    have Hlift : coeff2 denominator quotient z %% q =
        nested2 denominator numerator inverse z %% q.
    + exact (coeff2_mod_congr_right denominator quotient z
        (coeff0 numerator inverse z)
        (coeff1 numerator inverse z)
        (coeff2 numerator inverse z)
        (coeff3 numerator inverse z) H0' H1' H2' H3').
    rewrite Hlift (nested2_swap_first_two denominator numerator inverse z).
    exact (nested2_inverse_cancel numerator denominator inverse z Hinverse).
  rewrite coeff3_comm.
  have Hlift : coeff3 denominator quotient z %% q =
      nested3 denominator numerator inverse z %% q.
  + exact (coeff3_mod_congr_right denominator quotient z
      (coeff0 numerator inverse z)
      (coeff1 numerator inverse z)
      (coeff2 numerator inverse z)
      (coeff3 numerator inverse z) H0' H1' H2' H3').
  rewrite Hlift (nested3_swap_first_two denominator numerator inverse z).
  exact (nested3_inverse_cancel numerator denominator inverse z Hinverse).
qed.

lemma poly_inverse_product_cancel
    (denominator numerator inverse quotient : W16.t Array768.t) :
  in_qrange768 numerator =>
  poly_baseinv_success denominator inverse =>
  poly_basemul_qring numerator inverse quotient 192 =>
  poly_basemul_qring quotient denominator numerator 192.
proof.
  move=> Hnumerator Hinverse Hproduct k Hk.
  have Hproduct_k := Hproduct k Hk.
  move: Hproduct_k => /= [_ [H0 [H1 [H2 H3]]]].
  split; first exact (Hnumerator k Hk).
  have Hblock : block_product_qring
      (block4 numerator k) (block4 inverse k) (block4 quotient k)
      (terminal_value k).
  + rewrite /block_product_qring.
    split; first smt().
    split; first smt().
    split; first smt().
    smt().
  have Hcancel := block_inverse_product_cancel
    (block4 denominator k) (block4 numerator k)
    (block4 inverse k) (block4 quotient k) (terminal_value k)
    (Hinverse k Hk) Hblock.
  rewrite /block_product_qring in Hcancel.
  move: Hcancel => [HC0 [HC1 [HC2 HC3]]].
  split; first smt().
  split; first smt().
  split; first smt().
  smt().
qed.

lemma keygen_h_f_equals_g
    (fbuf gbuf : W8.t Array192.t)
    (finv h : W16.t Array768.t) :
  poly_baseinv_success (keygen_f_ntt_spec fbuf) finv =>
  poly_basemul_qring (keygen_g_ntt_spec gbuf) finv h 192 =>
  poly_basemul_qring h
    (keygen_f_ntt_spec fbuf) (keygen_g_ntt_spec gbuf) 192.
proof.
  move=> Hinverse Hproduct.
  exact (poly_inverse_product_cancel
    (keygen_f_ntt_spec fbuf) (keygen_g_ntt_spec gbuf) finv h
    (keygen_g_ntt_qrange gbuf) Hinverse Hproduct).
qed.

lemma keygen_hinv_g_equals_f
    (fbuf gbuf : W8.t Array192.t)
    (ginv hinv : W16.t Array768.t) :
  poly_baseinv_success (keygen_g_ntt_spec gbuf) ginv =>
  poly_basemul_qring (keygen_f_ntt_spec fbuf) ginv hinv 192 =>
  poly_basemul_qring hinv
    (keygen_g_ntt_spec gbuf) (keygen_f_ntt_spec fbuf) 192.
proof.
  move=> Hinverse Hproduct.
  exact (poly_inverse_product_cancel
    (keygen_g_ntt_spec gbuf) (keygen_f_ntt_spec fbuf) ginv hinv
    (keygen_f_ntt_qrange fbuf) Hinverse Hproduct).
qed.

lemma keygen_h_poly_basemul_ready
    (fbuf gbuf : W8.t Array192.t)
    (finv : W16.t Array768.t) :
  poly_baseinv_success (keygen_f_ntt_spec fbuf) finv =>
  in_qrange768 (keygen_g_ntt_spec gbuf) /\ in_qrange768 finv.
proof.
  move=> Hinverse.
  split; first exact (keygen_g_ntt_qrange gbuf).
  exact (poly_baseinv_success_output_qrange
    (keygen_f_ntt_spec fbuf) finv Hinverse).
qed.

lemma keygen_hinv_poly_basemul_ready
    (fbuf gbuf : W8.t Array192.t)
    (ginv : W16.t Array768.t) :
  poly_baseinv_success (keygen_g_ntt_spec gbuf) ginv =>
  in_qrange768 (keygen_f_ntt_spec fbuf) /\ in_qrange768 ginv.
proof.
  move=> Hinverse.
  split; first exact (keygen_f_ntt_qrange fbuf).
  exact (poly_baseinv_success_output_qrange
    (keygen_g_ntt_spec gbuf) ginv Hinverse).
qed.

lemma keygen_keypair_ntt_relation_intro
    (fbuf gbuf : W8.t Array192.t)
    (finv ginv h hinv : W16.t Array768.t) :
  poly_baseinv_success (keygen_f_ntt_spec fbuf) finv =>
  poly_baseinv_success (keygen_g_ntt_spec gbuf) ginv =>
  poly_basemul_qring (keygen_g_ntt_spec gbuf) finv h 192 =>
  poly_basemul_qring (keygen_f_ntt_spec fbuf) ginv hinv 192 =>
  keygen_keypair_ntt_relation
    (keygen_f_ntt_spec fbuf) finv
    (keygen_g_ntt_spec gbuf) ginv h hinv.
proof.
  move=> Hfinv Hginv Hh Hhinv.
  rewrite /keygen_keypair_ntt_relation.
  split; first exact Hfinv.
  split; first exact Hginv.
  split; first exact Hh.
  split; first exact Hhinv.
  split; first exact (keygen_h_f_equals_g fbuf gbuf finv h Hfinv Hh).
  exact (keygen_hinv_g_equals_f fbuf gbuf ginv hinv Hginv Hhinv).
qed.

lemma keypair_ntt_relation_intro
    (f finv g ginv h hinv : W16.t Array768.t) :
  in_qrange768 f =>
  in_qrange768 g =>
  poly_baseinv_success f finv =>
  poly_baseinv_success g ginv =>
  poly_basemul_qring g finv h 192 =>
  poly_basemul_qring f ginv hinv 192 =>
  keygen_keypair_ntt_relation f finv g ginv h hinv.
proof.
  move=> Hf Hg Hfinv Hginv Hh Hhinv.
  rewrite /keygen_keypair_ntt_relation.
  split; first exact Hfinv.
  split; first exact Hginv.
  split; first exact Hh.
  split; first exact Hhinv.
  split.
  + exact (poly_inverse_product_cancel f g finv h Hg Hfinv Hh).
  exact (poly_inverse_product_cancel g f ginv hinv Hf Hginv Hhinv).
qed.

(* Proof-only composition of the two exact verified Jasmin poly_basemul calls.
   The successful inverses are supplied by the preceding verified keygen
   inverse contract; this wrapper is not a production-C retry model. *)
module KeygenHComposition = {
  proc derive_products
      (f : W16.t Array768.t,
       finv : W16.t Array768.t,
       g : W16.t Array768.t,
       ginv : W16.t Array768.t,
       h0 : W16.t Array768.t,
       hinv0 : W16.t Array768.t) :
      W16.t Array768.t * W16.t Array768.t = {
    var h : W16.t Array768.t;
    var hinv : W16.t Array768.t;

    h <@
      NTRUPlus768PolyBasemul.M.jade_ntruplus_ntruplus768_amd64_ref_poly_basemul(
        h0, g, finv);
    hinv <@
      NTRUPlus768PolyBasemul.M.jade_ntruplus_ntruplus768_amd64_ref_poly_basemul(
        hinv0, f, ginv);
    return (h, hinv);
  }
}.

op keypair_products_word_post
    (f finv g ginv h hinv : W16.t Array768.t) : bool =
  is_poly_basemul g finv h 192 /\
  is_poly_basemul f ginv hinv 192.

lemma keypair_products_jasmin_calls_word_correct
    (f finv g ginv h0 hinv0 : W16.t Array768.t) :
  hoare [KeygenHComposition.derive_products :
    arg = (f, finv, g, ginv, h0, hinv0) ==>
    keypair_products_word_post f finv g ginv res.`1 res.`2].
proof.
  proc.
  call (poly_basemul_functional hinv0 f ginv).
  call (poly_basemul_functional h0 g finv).
  by auto => />.
qed.

lemma keypair_products_word_post_implies_relation
    (f finv g ginv h hinv : W16.t Array768.t) :
  in_qrange768 f =>
  in_qrange768 g =>
  poly_baseinv_success f finv =>
  poly_baseinv_success g ginv =>
  keypair_products_word_post f finv g ginv h hinv =>
  keygen_keypair_ntt_relation f finv g ginv h hinv.
proof.
  move=> Hf Hg Hfinv Hginv Hword.
  rewrite /keypair_products_word_post in Hword.
  move: Hword => [Hh Hhinv].
  have Hfinv_range := poly_baseinv_success_output_qrange f finv Hfinv.
  have Hginv_range := poly_baseinv_success_output_qrange g ginv Hginv.
  have Hh_qring := poly_basemul_word_to_qring
    g finv h Hg Hfinv_range Hh.
  have Hhinv_qring := poly_basemul_word_to_qring
    f ginv hinv Hf Hginv_range Hhinv.
  exact (keypair_ntt_relation_intro
    f finv g ginv h hinv
    Hf Hg Hfinv Hginv Hh_qring Hhinv_qring).
qed.

lemma keypair_products_jasmin_calls_correct
    (f finv g ginv h0 hinv0 : W16.t Array768.t) :
  in_qrange768 f =>
  in_qrange768 g =>
  poly_baseinv_success f finv =>
  poly_baseinv_success g ginv =>
  hoare [KeygenHComposition.derive_products :
    arg = (f, finv, g, ginv, h0, hinv0) ==>
    keygen_keypair_ntt_relation f finv g ginv res.`1 res.`2].
proof.
  move=> Hf Hg Hfinv Hginv.
  conseq (keypair_products_jasmin_calls_word_correct
    f finv g ginv h0 hinv0).
  move=> &hr _ result Hword.
  exact (keypair_products_word_post_implies_relation
    f finv g ginv result.`1 result.`2
    Hf Hg Hfinv Hginv Hword).
qed.

lemma keygen_sampled_keypair_jasmin_calls_correct
    (fbuf gbuf : W8.t Array192.t)
    (finv ginv h0 hinv0 : W16.t Array768.t) :
  poly_baseinv_success (keygen_f_ntt_spec fbuf) finv =>
  poly_baseinv_success (keygen_g_ntt_spec gbuf) ginv =>
  hoare [KeygenHComposition.derive_products :
    arg = (keygen_f_ntt_spec fbuf, finv,
           keygen_g_ntt_spec gbuf, ginv, h0, hinv0) ==>
    keygen_keypair_ntt_relation
      (keygen_f_ntt_spec fbuf) finv
      (keygen_g_ntt_spec gbuf) ginv res.`1 res.`2].
proof.
  move=> Hfinv Hginv.
  exact (keypair_products_jasmin_calls_correct
    (keygen_f_ntt_spec fbuf) finv
    (keygen_g_ntt_spec gbuf) ginv h0 hinv0
    (keygen_f_ntt_qrange fbuf) (keygen_g_ntt_qrange gbuf)
    Hfinv Hginv).
qed.
