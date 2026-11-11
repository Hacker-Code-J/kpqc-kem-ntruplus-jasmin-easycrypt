require import AllCore List Distr DProd RealSeries StdOrder.
from Jasmin require import JWord.
require import Array96 Array192 Array768 Array1152.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768PKEModel NTRUPlus768PKEKeyDistribution.
require import NTRUPlus768PolySOTPEncodeAlgebra NTRUPlus768SOTPContracts NTRUPlus768ROMDistributions.
require import NTRUPlus768ACWC2Domains NTRUPlus768ACWC2Oracle NTRUPlus768ACWC2Mean.
require import NTRUPlus768SpreadBase.
import RealOrder.

op [opaque] spread_pad_cipher_mass (w:keygen_witness) (msg:W8.t Array96.t)
 (r:pke_poly) (ct:W8.t Array1152.t) =
 mu uniform192(fun pad=>pke_enc_spec w.`kg_pk (poly_sotp_encode_spec msg pad) r=Some ct).
op [opaque] spread_cipher_mass (w:keygen_witness) (msg:W8.t Array96.t)
 (g:acwc2_g_function) (ct:W8.t Array1152.t) =
 mu pke_psi1(fun r=>pke_enc_spec w.`kg_pk (poly_sotp_encode_spec msg(g r)) r=Some ct).

lemma spread_mu_swap ['a 'b] (da:'a distr) (db:'b distr) (f:'a->'b->bool) :
 E da(fun a=>mu db(fun b=>f a b))=E db(fun b=>mu da(fun a=>f a b)).
proof.
 rewrite -(acwc2_mu_product_mean da db (fun (ab:'a*'b)=>f ab.`1 ab.`2)).
 by rewrite(dprodC da db) dmapE /(\o) acwc2_mu_product_mean.
qed.
lemma spread_pad_cipher_hiding w msg r ct :
 spread_pad_cipher_mass w msg r ct=
 mu pke_psi1(fun code=>pke_enc_spec w.`kg_pk code r=Some ct).
proof.
 by rewrite /spread_pad_cipher_mass -(sotp_encode_psi1 msg)
 (dmapE uniform192 (poly_sotp_encode_spec msg) (fun code=>pke_enc_spec w.`kg_pk code r=Some ct)) /(\o).
qed.
lemma spread_g_cipher_marginal w msg r ct : pke_domain r=>
 mu acwc2_eager_g_law(fun g=>pke_enc_spec w.`kg_pk(poly_sotp_encode_spec msg(g r))r=Some ct)=
 spread_pad_cipher_mass w msg r ct.
proof.
 move=>hr; by rewrite /spread_pad_cipher_mass -(acwc2_g_marginal r hr)
 (dmapE acwc2_eager_g_law (fun g=>g r)
  (fun pad=>pke_enc_spec w.`kg_pk(poly_sotp_encode_spec msg pad)r=Some ct)) /(\o).
qed.

(* Average over independently sampled G first, then fresh randomness. The
   theorem does not take a maximum inside the G expectation. *)
lemma spread_cipher_mass_average w msg ct :
 E acwc2_eager_g_law(fun g=>spread_cipher_mass w msg g ct)=
 E pke_psi1(fun code=>mu pke_psi1(fun r=>pke_enc_spec w.`kg_pk code r=Some ct)).
proof.
 rewrite /spread_cipher_mass spread_mu_swap /=.
 have he:E pke_psi1(fun r=>mu acwc2_eager_g_law
   (fun g=>pke_enc_spec w.`kg_pk(poly_sotp_encode_spec msg(g r))r=Some ct))=
   E pke_psi1(fun r=>mu pke_psi1(fun code=>pke_enc_spec w.`kg_pk code r=Some ct)).
 + apply eq_exp=>r hr /=.
   have hd:pke_domain r by move:hr; rewrite acwc2_psi1_support.
   by rewrite(spread_g_cipher_marginal w msg r ct hd) spread_pad_cipher_hiding.
 by rewrite he spread_mu_swap.
qed.
lemma spread_cipher_mass_pads_average w msg ct :
 E acwc2_gpads_law(fun pads=>spread_cipher_mass w msg(acwc2_gfun pads)ct)=
 E pke_psi1(fun code=>mu pke_psi1(fun r=>pke_enc_spec w.`kg_pk code r=Some ct)).
proof.
 rewrite -(spread_cipher_mass_average w msg ct) /acwc2_eager_g_law.
 rewrite(exp_dmap _ _ _ (hasE_finite _ _ (acwc2_dmap_finite _ _ acwc2_gpads_finite))) /(\o).
 done.
qed.

lemma spread_base_average_bound w ct : pke_key_relation w=>
 E pke_psi1(fun code=>mu pke_psi1(fun r=>pke_enc_spec w.`kg_pk code r=Some ct))<=1%r/(2%r^768).
proof.
 move=>hk.
 have h:=in_ler_exp pke_psi1
  (fun code=>mu pke_psi1(fun r=>pke_enc_spec w.`kg_pk code r=Some ct))
  (fun _=>1%r/(2%r^768)) (hasE_finite _ _ acwc2_psi1_finite) (hasEC _ _) _.
 + move=>code hc; apply(spread_base_bound w code ct hk).
   by move:hc; rewrite acwc2_psi1_support.
 by move:h; rewrite expC pke_psi1_lossless.
qed.
lemma spread_cipher_average_bound w msg ct : pke_key_relation w=>
 E acwc2_eager_g_law(fun g=>spread_cipher_mass w msg g ct)<=1%r/(2%r^768).
proof. move=>hk; rewrite spread_cipher_mass_average; exact(spread_base_average_bound w ct hk). qed.
lemma spread_cipher_pads_average_bound w msg ct : pke_key_relation w=>
 E acwc2_gpads_law(fun pads=>spread_cipher_mass w msg(acwc2_gfun pads)ct)<=1%r/(2%r^768).
proof. move=>hk; rewrite spread_cipher_mass_pads_average; exact(spread_base_average_bound w ct hk). qed.
lemma spread_independent_pad_bound w msg ct : pke_key_relation w=>
 mu (pke_psi1 `*` uniform192)
  (fun (rp:pke_poly*W8.t Array192.t)=>pke_enc_spec w.`kg_pk(poly_sotp_encode_spec msg rp.`2)rp.`1=Some ct)
 <=1%r/(2%r^768).
proof.
 move=>hk; rewrite acwc2_mu_product_mean /=.
 have he:E pke_psi1(fun r=>mu uniform192(fun pad=>pke_enc_spec w.`kg_pk(poly_sotp_encode_spec msg pad)r=Some ct))=
 E pke_psi1(fun r=>mu pke_psi1(fun code=>pke_enc_spec w.`kg_pk code r=Some ct)).
 + apply eq_exp=>r hr /=.
   have hh:=spread_pad_cipher_hiding w msg r ct.
   by move:hh; rewrite /spread_pad_cipher_mass.
 rewrite he spread_mu_swap; exact(spread_base_average_bound w ct hk).
qed.
