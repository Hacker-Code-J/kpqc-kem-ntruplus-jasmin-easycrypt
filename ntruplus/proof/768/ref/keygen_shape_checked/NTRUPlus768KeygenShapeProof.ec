require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.
require import Array192 Array768 NTRUPlus768KeygenShapeF NTRUPlus768KeygenShapeG.
require import NTRUPlus768PolyCBD1Algebra NTRUPlus768KeygenSamplerAlgebra.

(* Total word specifications; no trit or coefficient-range premise. *)
op keygen_shape_g_spec (p : W16.t Array768.t) : W16.t Array768.t =
  Array768.init (fun j => (p.[j] + p.[j]) + p.[j]).
op keygen_shape_f_spec (p : W16.t Array768.t) : W16.t Array768.t =
  let t = keygen_shape_g_spec p in t.[0 <- t.[0] + W16.one].

lemma keygen_shape_g_functional p0 :
  hoare [NTRUPlus768KeygenShapeG.M.jade_ntruplus_ntruplus768_amd64_ref_keygen_shape_g :
    arg = p0 ==> res = keygen_shape_g_spec p0].
proof.
  proc.
  while (0 <= W64.to_uint i <= 768 /\
    forall j, 0 <= j < 768 =>
      rp.[j] = if j < W64.to_uint i then (p0.[j] + p0.[j]) + p0.[j] else p0.[j]); last first.
  + auto => />; split; first smt().
    move=> i1 rp1 hd hlo hhi hall.
    rewrite W64.ultE /= in hd.
    have hi : W64.to_uint i1 = 768 by smt().
    apply Array768.tP => j hj.
    rewrite /keygen_shape_g_spec Array768.initiE //.
    have hh := hall j hj.
    by move: hh; rewrite hi; smt().
  auto => /> &hr hlo hhi hall hloop.
  rewrite W64.ultE /= in hloop.
  have hn : W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  rewrite hn.
  split; first smt().
  move=> j hjlo hjhi.
  rewrite Array768.get_setE 1:/# /=.
  have hcur := hall (W64.to_uint i{hr}) _; first smt().
  have hj := hall j _; first smt().
  have hc : rp{hr}.[W64.to_uint i{hr}] = p0.[W64.to_uint i{hr}].
  + move: hcur.
    have hnlt : !(W64.to_uint i{hr} < W64.to_uint i{hr}) by smt().
    by rewrite hnlt.
  case (j = W64.to_uint i{hr}) => heq.
  + rewrite heq hc /=.
    have -> : W64.to_uint i{hr} < W64.to_uint i{hr} + 1 by smt().
    done.
  rewrite hj.
  have -> : (j < W64.to_uint i{hr} + 1) = (j < W64.to_uint i{hr}) by smt().
  done.
qed.

lemma keygen_shape_g_lossless : islossless
  NTRUPlus768KeygenShapeG.M.jade_ntruplus_ntruplus768_amd64_ref_keygen_shape_g.
proof.
  proc.
  while (0 <= W64.to_uint i <= 768) (768 - W64.to_uint i).
  + auto => /> &hr hlo hhi hloop.
    rewrite W64.ultE /= in hloop.
    rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  auto => /> i hlo hhi hd; rewrite W64.ultE /=; smt().
qed.

lemma keygen_shape_g_correct p0 :
  phoare [NTRUPlus768KeygenShapeG.M.jade_ntruplus_ntruplus768_amd64_ref_keygen_shape_g :
    arg = p0 ==> res = keygen_shape_g_spec p0] = 1%r.
proof. by conseq keygen_shape_g_lossless (keygen_shape_g_functional p0). qed.

lemma keygen_shape_f_functional p0 :
  hoare [NTRUPlus768KeygenShapeF.M.jade_ntruplus_ntruplus768_amd64_ref_keygen_shape_f :
    arg = p0 ==> res = keygen_shape_f_spec p0].
proof.
  proc.
  seq 3 : (rp = keygen_shape_g_spec p0); last by auto => />; rewrite /keygen_shape_f_spec.
  while (0 <= W64.to_uint i <= 768 /\
    forall j, 0 <= j < 768 =>
      rp.[j] = if j < W64.to_uint i then (p0.[j] + p0.[j]) + p0.[j] else p0.[j]); last first.
  + auto => />; split; first smt().
    move=> i1 rp1 hd hlo hhi hall.
    rewrite W64.ultE /= in hd.
    have hi : W64.to_uint i1 = 768 by smt().
    apply Array768.tP => j hj.
    rewrite /keygen_shape_g_spec Array768.initiE //.
    have hh := hall j hj.
    by move: hh; rewrite hi; smt().
  auto => /> &hr hlo hhi hall hloop.
  rewrite W64.ultE /= in hloop.
  have hn : W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  rewrite hn.
  split; first smt().
  move=> j hjlo hjhi.
  rewrite Array768.get_setE 1:/# /=.
  have hcur := hall (W64.to_uint i{hr}) _; first smt().
  have hj := hall j _; first smt().
  have hc : rp{hr}.[W64.to_uint i{hr}] = p0.[W64.to_uint i{hr}].
  + move: hcur.
    have hnlt : !(W64.to_uint i{hr} < W64.to_uint i{hr}) by smt().
    by rewrite hnlt.
  case (j = W64.to_uint i{hr}) => heq.
  + rewrite heq hc /=.
    have -> : W64.to_uint i{hr} < W64.to_uint i{hr} + 1 by smt().
    done.
  rewrite hj.
  have -> : (j < W64.to_uint i{hr} + 1) = (j < W64.to_uint i{hr}) by smt().
  done.
qed.

lemma keygen_shape_f_lossless : islossless
  NTRUPlus768KeygenShapeF.M.jade_ntruplus_ntruplus768_amd64_ref_keygen_shape_f.
proof.
  proc.
  wp.
  while (0 <= W64.to_uint i <= 768) (768 - W64.to_uint i).
  + auto => /> &hr hlo hhi hloop.
    rewrite W64.ultE /= in hloop.
    rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  auto => /> i hlo hhi hd; rewrite W64.ultE /=; smt().
qed.

lemma keygen_shape_f_correct p0 :
  phoare [NTRUPlus768KeygenShapeF.M.jade_ntruplus_ntruplus768_amd64_ref_keygen_shape_f :
    arg = p0 ==> res = keygen_shape_f_spec p0] = 1%r.
proof. by conseq keygen_shape_f_lossless (keygen_shape_f_functional p0). qed.

lemma keygen_shape_g_sampled_spec buf :
  keygen_shape_g_spec (poly_cbd1_spec buf) = keygen_g_pre_ntt_spec buf.
proof.
  apply Array768.tP => j hj.
  rewrite /keygen_shape_g_spec /keygen_g_pre_ntt_spec /poly_triple_spec !Array768.initiE //.
  rewrite /= poly_cbd1_spec_coeff 1:hj !poly_cbd1_spec_word //.
  rewrite (_ : 3 * poly_cbd1_coeff_int buf j =
    (poly_cbd1_coeff_int buf j + poly_cbd1_coeff_int buf j) + poly_cbd1_coeff_int buf j) 1:/#.
  by rewrite !W16.of_intD.
qed.

lemma keygen_shape_f_sampled_spec buf :
  keygen_shape_f_spec (poly_cbd1_spec buf) = keygen_f_pre_ntt_spec buf.
proof.
  apply Array768.tP => j hj.
  rewrite /keygen_shape_f_spec /= Array768.get_setE 1:/# /=.
  rewrite /keygen_shape_g_spec /keygen_f_pre_ntt_spec !Array768.initiE //=.
  simplify.
  case (j = 0) => heq.
  + rewrite heq !poly_cbd1_spec_word 1:/# /keygen_delta0 /=.
    rewrite (_ : 3 * poly_cbd1_coeff_int buf 0 + 1 =
      ((poly_cbd1_coeff_int buf 0 + poly_cbd1_coeff_int buf 0) + poly_cbd1_coeff_int buf 0) + 1) 1:/#.
    by rewrite !W16.of_intD.
  rewrite poly_cbd1_spec_word 1:hj /keygen_delta0 heq /=.
  rewrite (_ : 3 * poly_cbd1_coeff_int buf j =
    (poly_cbd1_coeff_int buf j + poly_cbd1_coeff_int buf j) + poly_cbd1_coeff_int buf j) 1:/#.
  by rewrite !W16.of_intD.
qed.

lemma keygen_shape_g_sampled_correct buf :
  phoare [NTRUPlus768KeygenShapeG.M.jade_ntruplus_ntruplus768_amd64_ref_keygen_shape_g :
    arg = poly_cbd1_spec buf ==> res = keygen_g_pre_ntt_spec buf] = 1%r.
proof.
  rewrite -(keygen_shape_g_sampled_spec buf).
  exact (keygen_shape_g_correct (poly_cbd1_spec buf)).
qed.

lemma keygen_shape_f_sampled_correct buf :
  phoare [NTRUPlus768KeygenShapeF.M.jade_ntruplus_ntruplus768_amd64_ref_keygen_shape_f :
    arg = poly_cbd1_spec buf ==> res = keygen_f_pre_ntt_spec buf] = 1%r.
proof.
  rewrite -(keygen_shape_f_sampled_spec buf).
  exact (keygen_shape_f_correct (poly_cbd1_spec buf)).
qed.

