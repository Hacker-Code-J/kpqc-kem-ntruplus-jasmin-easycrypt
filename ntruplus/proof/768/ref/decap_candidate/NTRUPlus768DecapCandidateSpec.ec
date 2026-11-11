require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.
require import Array4 Array768.
require import NTRUPlus768PolyBasemulProof.
require import NTRUPlus768InvNTTProof.
require import NTRUPlus768Crepmod3Proof.

(* An exact word-level specification, valid for all input words. The
   mathematical interpretation requires the range lemmas in Algebra. *)
op candidate_product_spec (cp fp : W16.t Array768.t) : W16.t Array768.t =
  Array768.init (fun j => (basemul_block_spec cp fp (j %/ 4)).[j %% 4]).

op decap_candidate_spec (cp fp : W16.t Array768.t) : W16.t Array768.t =
  poly_crepmod3_spec (invntt_spec (candidate_product_spec cp fp)).

lemma candidate_product_block cp fp k : 0 <= k < 192 =>
  block4 (candidate_product_spec cp fp) k = basemul_block_spec cp fp k.
proof.
  move=> hk; apply Array4.tP => j hj.
  rewrite /block4 Array4.initiE 1:hj /=.
  rewrite /candidate_product_spec.
  rewrite Array768.initiE 1:/# /=.
  have hd : (4 * k + j) %/ 4 = k by smt(divz_eqP).
  have hm : (4 * k + j) %% 4 = j by smt(edivzP).
  by rewrite hd hm.
qed.

lemma candidate_product_word cp fp :
  is_poly_basemul cp fp (candidate_product_spec cp fp) 192.
proof. move=> k hk; exact (candidate_product_block cp fp k hk). qed.

lemma candidate_product_unique cp fp rp :
  is_poly_basemul cp fp rp 192 => rp = candidate_product_spec cp fp.
proof.
  move=> hp; apply Array768.tP => j hj.
  have hk : 0 <= j %/ 4 < 192 by smt().
  have hm : 0 <= j %% 4 < 4 by smt().
  have hb := hp (j %/ 4) hk.
  have hn : (block4 rp (j %/ 4)).[j %% 4] =
      (basemul_block_spec cp fp (j %/ 4)).[j %% 4] by rewrite hb.
  rewrite /block4 Array4.initiE 1:hm /= in hn.
  have he : 4 * (j %/ 4) + j %% 4 = j by smt(edivzP).
  by rewrite /candidate_product_spec Array768.initiE 1:hj /= -hn he.
qed.
