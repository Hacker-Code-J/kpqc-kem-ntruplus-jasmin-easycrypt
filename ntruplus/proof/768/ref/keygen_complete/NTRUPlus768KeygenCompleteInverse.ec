require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.
require import Array4 Array768.
require import NTRUPlus768PolyBaseInv NTRUPlus768PolyBaseInvProof.
require import NTRUPlus768PolyBasemulProof NTRUPlus768PolyBaseInvBridge NTRUPlus768PolyBasemulAlgebra.

op keygen_inverse_value (p : W16.t Array768.t) : W16.t Array768.t =
  if poly_blocks_succeed p 192 then
    Array768.init (fun j => (poly_block_output p (j %/ 4)).[j %% 4])
  else poly_zero.
op keygen_inverse_status (p : W16.t Array768.t) : W64.t =
  if poly_blocks_succeed p 192 then W64.zero else W64.one.

lemma keygen_inverse_unique p r s :
  poly_baseinv_exact_post p r s =>
  r = keygen_inverse_value p /\ s = keygen_inverse_status p.
proof.
  move=> hp.
  have hs := poly_baseinv_exact_status_zero_iff p r s hp.
  move: hp => [[hz [ha hw]] | [ho [hf hr]]].
  + rewrite /keygen_inverse_value /keygen_inverse_status ha /= hz.
    split; last done.
    apply Array768.tP => j hj.
    rewrite Array768.initiE //.
    have hjm : 0 <= j %% 4 < 4 by smt(IntDiv.modz_ge0 IntDiv.ltz_pmod).
    have hjb : 0 <= j %/ 4 < 192 by smt(IntDiv.edivzP).
    have hb : block4 r (j %/ 4) = poly_block_output p (j %/ 4).
    + exact (hw (j %/ 4) hjb).
    have he : (block4 r (j %/ 4)).[j %% 4] = (poly_block_output p (j %/ 4)).[j %% 4] by rewrite hb.
    move: he; rewrite /block4 Array4.initiE 1:hjm.
    smt(IntDiv.edivzP).
  have hn : !poly_blocks_succeed p 192 by smt(poly_baseinv_w64_zero_neq_one).
  by rewrite /keygen_inverse_value /keygen_inverse_status hn /= hr ho.
qed.

lemma keygen_inverse_functional rp0 ap0 :
  hoare [NTRUPlus768PolyBaseInv.M.__poly_baseinv_core : rp=rp0 /\ ap=ap0 ==>
    res=(keygen_inverse_value ap0,keygen_inverse_status ap0)].
proof.
  conseq (poly_baseinv_functional rp0 ap0) => />.
  move=> &hr result hp; have [hr hs] := keygen_inverse_unique _ _ _ hp.
  smt().
qed.

lemma keygen_inverse_success p r s :
  in_qrange768 p => poly_baseinv_exact_post p r s => s=W64.zero => poly_baseinv_success p r.
proof. move=> hq hp hs; exact (poly_baseinv_exact_success_semantic p r s hq hp hs). qed.

lemma keygen_inverse_apply_lossless : islossless NTRUPlus768PolyBaseInv.M.__poly_baseinv_apply.
proof. proc; islossless. qed.
lemma keygen_inverse_pair_lossless : islossless NTRUPlus768PolyBaseInv.M.__poly_baseinv_pair.
proof. proc; islossless. qed.
lemma keygen_inverse_zero_lossless : islossless NTRUPlus768PolyBaseInv.M.__poly_baseinv_zero.
proof.
  proc; while (0 <= W64.to_uint j <= 768) (768 - W64.to_uint j).
  + auto => /> &hr hlo hhi hg; rewrite W64.ultE /= in hg.
    rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  auto => /> j hlo hhi hd; rewrite W64.ultE /=; smt().
qed.
lemma keygen_inverse_lossless : islossless NTRUPlus768PolyBaseInv.M.__poly_baseinv_core.
proof.
 proc.
 seq 6 : true 1%r 1%r 0%r 0%r (true) => //.
 + while (0 <= W64.to_uint i <= 96) (96 - W64.to_uint i).
   - move=> *; wp; call keygen_inverse_pair_lossless; wp.
     auto => /> &hr hlo hhi hg; rewrite W64.ultE /= in hg.
     move=> result; split=> hs; first smt().
     rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
   auto => /> i hlo hhi hd; rewrite W64.ultE /=; smt().
 if.
 + call keygen_inverse_zero_lossless; auto.
 auto.
qed.
