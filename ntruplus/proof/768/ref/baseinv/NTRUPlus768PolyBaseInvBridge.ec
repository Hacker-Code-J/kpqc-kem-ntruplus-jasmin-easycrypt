require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord.

require import Array4 Array768.
require import NTRUPlus768NTTSchedule.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768PolyBasemulProof.
require import NTRUPlus768PolyBasemulAlgebra.
require import NTRUPlus768BaseInvAlgebra.

(* Logical success contract over all terminal blocks.  No correspondence with
   the C poly_baseinv return code is claimed in this theory. *)

op ntt_block_identity : W16.t Array768.t =
  Array768.init (fun j => W16.of_int (if j %% 4 = 0 then 1 else 0)).

op poly_baseinv_success
    (a inv : W16.t Array768.t) : bool =
  forall k, 0 <= k < 192 =>
    block_inverse_qring
      (block4 a k) (block4 inv k) (terminal_value k).

op poly_baseinv_witness_contract
    (a inv : W16.t Array768.t) (dinv : int -> int) : bool =
  forall k, 0 <= k < 192 =>
    determinant_inverse_witness
      (block4 a k) (terminal_value k) (dinv k) /\
    inverse_coeff_relation
      (block4 a k) (block4 inv k) (terminal_value k) (dinv k).

lemma ntt_block_identity_coeff0 (k : int) :
  0 <= k < 192 => coeff (block4 ntt_block_identity k).[0] = 1.
proof.
  move=> Hk.
  rewrite /block4 Array4.initiE 1:/#.
  rewrite /ntt_block_identity.
  rewrite /=.
  rewrite Array768.initiE 1:/#.
  rewrite /= /coeff.
  have -> : 4 * k = k * 4 by ring.
  rewrite modzMl /= W16.to_sintK_small 1:/#.
  done.
qed.

lemma ntt_block_identity_coeff1 (k : int) :
  0 <= k < 192 => coeff (block4 ntt_block_identity k).[1] = 0.
proof.
  move=> Hk.
  rewrite /block4 Array4.initiE 1:/#.
  rewrite /ntt_block_identity.
  rewrite /=.
  rewrite Array768.initiE 1:/#.
  rewrite /= /coeff.
  have -> : 4 * k + 1 = k * 4 + 1 by ring.
  rewrite modzMDl /= W16.to_sintK_small 1:/#.
  done.
qed.

lemma ntt_block_identity_coeff2 (k : int) :
  0 <= k < 192 => coeff (block4 ntt_block_identity k).[2] = 0.
proof.
  move=> Hk.
  rewrite /block4 Array4.initiE 1:/#.
  rewrite /ntt_block_identity.
  rewrite /=.
  rewrite Array768.initiE 1:/#.
  rewrite /= /coeff.
  have -> : 4 * k + 2 = k * 4 + 2 by ring.
  rewrite modzMDl /= W16.to_sintK_small 1:/#.
  done.
qed.

lemma ntt_block_identity_coeff3 (k : int) :
  0 <= k < 192 => coeff (block4 ntt_block_identity k).[3] = 0.
proof.
  move=> Hk.
  rewrite /block4 Array4.initiE 1:/#.
  rewrite /ntt_block_identity.
  rewrite /=.
  rewrite Array768.initiE 1:/#.
  rewrite /= /coeff.
  have -> : 4 * k + 3 = k * 4 + 3 by ring.
  rewrite modzMDl /= W16.to_sintK_small 1:/#.
  done.
qed.

lemma ntt_block_identity_qrange (k : int) :
  0 <= k < 192 => in_qrange4 (block4 ntt_block_identity k).
proof.
  move=> Hk.
  rewrite /in_qrange4 /in_qrange.
  rewrite ntt_block_identity_coeff0 1:Hk.
  rewrite ntt_block_identity_coeff1 1:Hk.
  rewrite ntt_block_identity_coeff2 1:Hk.
  rewrite ntt_block_identity_coeff3 1:Hk /q /=.
  done.
qed.

lemma poly_baseinv_witness_contract_implies_success
    (a inv : W16.t Array768.t) (dinv : int -> int) :
  poly_baseinv_witness_contract a inv dinv =>
  poly_baseinv_success a inv.
proof.
  move=> Hcontract k Hk.
  have Hkcontract := Hcontract k Hk.
  move: Hkcontract => [Hdet Hrel].
  exact (inverse_coeff_relation_implies_block_inverse
    (block4 a k) (block4 inv k) (terminal_value k) (dinv k)
    Hdet Hrel).
qed.

lemma poly_baseinv_success_output_qrange
    (a inv : W16.t Array768.t) :
  poly_baseinv_success a inv => in_qrange768 inv.
proof.
  move=> Hsuccess k Hk.
  have Hblock := Hsuccess k Hk.
  by move: Hblock; rewrite /block_inverse_qring => [[Hrange _]].
qed.

lemma poly_baseinv_success_product_identity
    (a inv : W16.t Array768.t) :
  poly_baseinv_success a inv =>
  poly_basemul_qring a inv ntt_block_identity 192.
proof.
  move=> Hsuccess k Hk.
  have Hblock := Hsuccess k Hk.
  move: Hblock => [Hrange [H0 [H1 [H2 H3]]]].
  rewrite /=.
  split; first exact (ntt_block_identity_qrange k Hk).
  split.
  + rewrite ntt_block_identity_coeff0 1:Hk.
    smt().
  split.
  + rewrite ntt_block_identity_coeff1 1:Hk.
    smt().
  split.
  + rewrite ntt_block_identity_coeff2 1:Hk.
    smt().
  rewrite ntt_block_identity_coeff3 1:Hk.
  smt().
qed.
