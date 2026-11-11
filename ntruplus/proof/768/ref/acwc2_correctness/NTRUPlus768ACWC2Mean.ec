require import AllCore List Distr DList DProd Finite RealSeries StdBigop StdOrder.
from Jasmin require import JWord.
require import Array96 Array192 Array768.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768PKEModel NTRUPlus768PKEKeyDistribution.
require import NTRUPlus768ROMDistributions NTRUPlus768PolySOTPEncodeAlgebra NTRUPlus768SOTPContracts.
require import NTRUPlus768ACWC2Domains NTRUPlus768ACWC2Oracle NTRUPlus768ACWC2BaseModel.
import RealOrder RField Bigreal.

(* The envelope at coordinate r reads only G(r). It is underlying PKE
   failure, not the transformed decoder, which may read a second entry. *)
op [opaque] acwc2_fixed_mean (w:keygen_witness) (msg:W8.t Array96.t) =
 BRA.big predT (fun r=>acwc2_r_weight r*mu uniform192(acwc2_pad_bad w msg r)) acwc2_r_enum.
op [opaque] acwc2_weighted_bad (w:keygen_witness) (msg:W8.t Array96.t) (g:acwc2_g_function) =
 BRA.big predT (fun r=>acwc2_r_weight r*b2r(acwc2_pad_bad w msg r (g r))) acwc2_r_enum.
op [opaque] acwc2_centered_value (w:keygen_witness) (msg:W8.t Array96.t)
 (r:pke_poly) (pad:W8.t Array192.t) =
 acwc2_r_weight r*(b2r(acwc2_pad_bad w msg r pad)-mu uniform192(acwc2_pad_bad w msg r)).
op [opaque] acwc2_centered_distr w msg r = dmap uniform192(acwc2_centered_value w msg r).

lemma acwc2_pad_mean w msg r :
 mu uniform192(acwc2_pad_bad w msg r)=mu pke_psi1 (fun code=>acwc2_base_failure w code r).
proof.
 rewrite -(sotp_encode_psi1 msg)
   (dmapE uniform192 (poly_sotp_encode_spec msg) (fun code=>acwc2_base_failure w code r)).
 apply mu_eq=>pad; by rewrite /(\o) acwc2_pad_badE.
qed.
lemma acwc2_mu_product_mean ['a 'b] (da:'a distr) (db:'b distr) (p:'a*'b->bool) :
 mu (da `*` db) p=E da (fun a=>mu db (fun b=>p(a,b))).
proof.
 rewrite dprod_dlet dletE /E; apply eq_sum=>a /=.
 rewrite dmapE /(\o); ring.
qed.
lemma acwc2_fixed_mean_base w msg : acwc2_fixed_mean w msg=acwc2_base_mean w.
proof.
 rewrite /acwc2_fixed_mean acwc2_base_meanE acwc2_mu_product_mean.
 rewrite(fin_expE pke_psi1 (fun r=>mu pke_psi1(fun code=>acwc2_base_failure w code r)) acwc2_psi1_finite).
 rewrite /acwc2_r_enum /acwc2_r_weight.
 apply BRA.eq_bigr=>r hr /=; rewrite acwc2_pad_mean; ring.
qed.
lemma acwc2_fixed_mean_message_independent w msg1 msg2 :
 acwc2_fixed_mean w msg1=acwc2_fixed_mean w msg2.
proof. by rewrite !acwc2_fixed_mean_base. qed.
lemma acwc2_fixed_mean_range w msg : 0%r<=acwc2_fixed_mean w msg<=1%r.
proof. rewrite acwc2_fixed_mean_base; exact(acwc2_base_mean_range w). qed.
lemma acwc2_weighted_bad_probability w msg g :
 acwc2_weighted_bad w msg g=
 mu pke_psi1(fun r=>acwc2_pad_bad w msg r(g r)).
proof.
 rewrite /acwc2_weighted_bad acwc2_r_weight_law
   (BRA.big_mkcond (fun r=>acwc2_pad_bad w msg r(g r)) acwc2_r_weight acwc2_r_enum).
 apply BRA.eq_bigr=>r hr /=; case(acwc2_pad_bad w msg r(g r)); smt().
qed.
lemma acwc2_weighted_bad_range w msg g : 0%r<=acwc2_weighted_bad w msg g<=1%r.
proof. rewrite acwc2_weighted_bad_probability; exact(mu_bounded _ _). qed.

lemma acwc2_indicator_mean ['a] (d:'a distr) (p:'a->bool) :
 E d (fun x=>b2r(p x))=mu d p.
proof.
 have he:(fun x=>b2r(p x))=(fun x=>if p x then 1%r else 0%r).
 + apply fun_ext=>x; by case(p x).
 by rewrite he expC_cond mul1r.
qed.
lemma acwc2_centered_finite w msg r : is_finite(support(acwc2_centered_distr w msg r)).
proof. rewrite /acwc2_centered_distr; apply acwc2_dmap_finite; exact acwc2_uniform192_finite. qed.
lemma acwc2_centered_lossless w msg r : is_lossless(acwc2_centered_distr w msg r).
proof. rewrite /acwc2_centered_distr; apply/dmap_ll; exact uniform192_ll. qed.
lemma acwc2_centered_mean_zero w msg r : E(acwc2_centered_distr w msg r)idfun=0%r.
proof.
 have hi:=hasE_finite (acwc2_centered_distr w msg r) idfun (acwc2_centered_finite w msg r).
 rewrite /acwc2_centered_distr in hi.
 rewrite /acwc2_centered_distr (exp_dmap _ _ _ hi) /(\o) /idfun /acwc2_centered_value expZ.
 have hf:=hasE_finite uniform192 (fun pad=>b2r(acwc2_pad_bad w msg r pad)) acwc2_uniform192_finite.
 have hc:=hasEC uniform192 (mu uniform192(acwc2_pad_bad w msg r)).
 have he:(fun x=>acwc2_pad_bad w msg r x)=acwc2_pad_bad w msg r by apply fun_ext=>x; done.
 rewrite(expB _ _ _ hf hc) acwc2_indicator_mean expC uniform192_ll he; ring.
qed.
lemma acwc2_centered_bool_bound weight prob bit :
 0%r<=weight => 0%r<=prob<=1%r => `|weight*(b2r bit-prob)|<=weight.
proof. move=>hw hp; rewrite ler_norml; case bit; simplify; smt(). qed.
lemma acwc2_centered_support_bound w msg r x :
 x \in acwc2_centered_distr w msg r => `|x|<=acwc2_r_weight r.
proof.
 move=>hx; rewrite /acwc2_centered_distr supp_dmap in hx.
 case hx=>pad hp.
 have he:x=acwc2_centered_value w msg r pad by smt().
 rewrite he /acwc2_centered_value.
 exact(acwc2_centered_bool_bound _ _ _ (acwc2_r_weight_nonnegative r) (mu_bounded _ _)).
qed.
lemma acwc2_centered_joint_law w msg :
 dmap acwc2_eager_g_law (acwc2_g_observe(acwc2_centered_value w msg))=
 djoin(map (acwc2_centered_distr w msg) acwc2_r_enum).
proof. rewrite /acwc2_centered_distr; exact(acwc2_g_independent_observations(acwc2_centered_value w msg)). qed.
lemma acwc2_centered_sum w msg g :
 BRA.big predT idfun (acwc2_g_observe(acwc2_centered_value w msg)g)=
 acwc2_weighted_bad w msg g-acwc2_fixed_mean w msg.
proof.
 rewrite /acwc2_g_observe BRA.big_mapT /(\o) /idfun /acwc2_centered_value.
 rewrite /acwc2_weighted_bad /acwc2_fixed_mean BRA.sumrB.
 apply BRA.eq_bigr=>r hr /=; ring.
qed.
lemma acwc2_centered_sum_law w msg :
 dmap acwc2_eager_g_law (fun g=>acwc2_weighted_bad w msg g-acwc2_base_mean w)=
 dmap (djoin(map (acwc2_centered_distr w msg) acwc2_r_enum)) (BRA.big predT idfun).
proof.
 rewrite -(acwc2_fixed_mean_base w msg).
 have he:(fun g=>acwc2_weighted_bad w msg g-acwc2_fixed_mean w msg)=
   (BRA.big predT idfun) \o (acwc2_g_observe(acwc2_centered_value w msg)).
 + apply fun_ext=>g; rewrite /(\o); apply/eq_sym; exact(acwc2_centered_sum w msg g).
 by rewrite he -dmap_comp acwc2_centered_joint_law.
qed.

require import NTRUPlus768ACWC2Moment.
(* Discharge the generic moment theorem's actual distribution premises.
   The key is fixed here; no per-key numerical correctness bound is used. *)
lemma acwc2_actual_centered_bounded w msg r :
 acwc2_centered_bounded (acwc2_centered_distr w msg r) (acwc2_r_weight r).
proof.
 rewrite /acwc2_centered_bounded; split; first exact(acwc2_centered_finite w msg r).
 split; first exact(acwc2_centered_lossless w msg r).
 split; first exact(acwc2_centered_mean_zero w msg r).
 split; first exact(acwc2_centered_support_bound w msg r).
 exact(acwc2_r_weight_nonnegative r).
qed.

lemma acwc2_centered_list_finite w msg :
 is_finite(support(djoin(map (acwc2_centered_distr w msg) acwc2_r_enum))).
proof.
 apply acwc2_finite_djoin; rewrite allP=>d hd.
 move:hd; move/mapP=>[r [hr ->]].
 exact(acwc2_centered_finite w msg r).
qed.
lemma acwc2_eager_eighth_bound w msg :
 E acwc2_eager_g_law (fun g=>(acwc2_weighted_bad w msg g-acwc2_base_mean w)^8) <=
 105%r*(BRA.big predT (fun r=>(acwc2_r_weight r)^2) acwc2_r_enum)^4.
proof.
 have hb:=acwc2_independent_eighth acwc2_r_enum acwc2_r_weight (acwc2_centered_distr w msg) _.
 + move=>r hr; exact(acwc2_actual_centered_bounded w msg r).
 have hl:hasE (dmap acwc2_eager_g_law
   (fun g=>acwc2_weighted_bad w msg g-acwc2_base_mean w)) (fun x=>x^8).
 + apply hasE_finite; apply acwc2_dmap_finite; exact acwc2_eager_g_finite.
 have hr:hasE (dmap (djoin(map (acwc2_centered_distr w msg) acwc2_r_enum))
   (BRA.big predT idfun)) (fun x=>x^8).
 + apply hasE_finite; apply acwc2_dmap_finite; exact(acwc2_centered_list_finite w msg).
 have he:=congr1 (fun (d:real distr)=>E d (fun x=>x^8)) _ _ (acwc2_centered_sum_law w msg).
 rewrite /= (exp_dmap _ _ _ hl) (exp_dmap _ _ _ hr) /(\o) in he.
 by rewrite he; exact hb.
qed.
