require import AllCore Distr DList List Ring.
require import NTRUPlus768OWUniform NTRUPlus768CyclotomicFactorization NTRUPlus768EvaluationSemantics.
require import NTRUPlus768AcceptanceAlgebra NTRUPlus768PKEKeyDistribution.

op ow_coeff_scale(c:CycloFq.cyclocoeff)(x:CycloFq.cyclocoeff)=CycloFq.( * ) c x.
op ow_polyscale(c:CycloFq.cyclocoeff)(p:NTRUPoly.poly)=NTRUPoly.polyZ c p.

lemma ow_coeff_scale_cancel c x : c<>CycloFq.zero=>
 ow_coeff_scale(CycloFq.inv c)(ow_coeff_scale c x)=x.
proof.
 move=>hc;by rewrite /ow_coeff_scale CycloFq.CycloFqField.mulrA
  (CycloFq.CycloFqField.mulVf c hc) CycloFq.CycloFqField.mul1r.
qed.
lemma ow_coeff_scale_cancel_right c x : c<>CycloFq.zero=>
 ow_coeff_scale c (ow_coeff_scale(CycloFq.inv c)x)=x.
proof.
 move=>hc;by rewrite /ow_coeff_scale CycloFq.CycloFqField.mulrA
  (CycloFq.CycloFqField.mulfV c hc) CycloFq.CycloFqField.mul1r.
qed.
lemma ow_coeff_uniform_scale c : c<>CycloFq.zero=>
 dmap CycloFq.DZmodP.dunifin (ow_coeff_scale c)=CycloFq.DZmodP.dunifin.
proof.
 move=>hc;apply(dmap_bij _ _ (ow_coeff_scale c) (ow_coeff_scale(CycloFq.inv c))).
 + move=>x hx;exact(CycloFq.DZmodP.supp_dunifin _).
 + move=>x hx;by rewrite !CycloFq.DZmodP.dunifin1E.
 + move=>x hx;exact(ow_coeff_scale_cancel c x hc).
 move=>x hx;exact(ow_coeff_scale_cancel_right c x hc).
qed.
lemma ow_polyL_scaled c xs :
 NTRUPoly.polyL(map(ow_coeff_scale c)xs)=ow_polyscale c (NTRUPoly.polyL xs).
proof.
 apply/NTRUPoly.poly_eqP=>i hi.
 rewrite /ow_polyscale NTRUPoly.polyZE !NTRUPoly.polyLE.
 case(0<=i<size xs)=>hx.
 + by rewrite(nth_map CycloFq.zero) // /ow_coeff_scale.
 have hm:!(0<=i<size(map(ow_coeff_scale c)xs)) by rewrite size_map;exact hx.
 rewrite(nth_out CycloFq.zero _ _ hm)(nth_out CycloFq.zero _ _ hx).
 by rewrite CycloFq.CycloFqField.mulr0.
qed.
lemma ow_uniform_scale c : c<>CycloFq.zero=>
 dmap ow_uniform_rq (ow_polyscale c)=ow_uniform_rq.
proof.
 move=>hc;rewrite /ow_uniform_rq dmap_comp.
 have he:(ow_polyscale c \o NTRUPoly.polyL)=NTRUPoly.polyL \o map(ow_coeff_scale c).
 + apply fun_ext=>xs;apply/eq_sym;exact(ow_polyL_scaled c xs).
 by rewrite he -dmap_comp -dlist_dmap (ow_coeff_uniform_scale c hc).
qed.
lemma ow_scale3E p : ow_scale3 p=ow_polyscale(lift_int 3)p.
proof. by rewrite /ow_scale3 /ow_polyscale NTRUPoly.scalepE. qed.
lemma ow_unscale3E p : ow_unscale3 p=ow_polyscale(CycloFq.inv(lift_int 3))p.
proof. by rewrite /ow_unscale3 /ow_polyscale NTRUPoly.scalepE. qed.
lemma ow_uniform_scale3 : dmap ow_uniform_rq ow_scale3=ow_uniform_rq.
proof.
 have he:ow_scale3=ow_polyscale(lift_int 3) by apply fun_ext=>p;exact(ow_scale3E p).
 rewrite he;exact(ow_uniform_scale (lift_int 3) lift_three_nonzero).
qed.
lemma ow_polyscale_domain c p : ow_rq_domain p=>ow_rq_domain(ow_polyscale c p).
proof. rewrite /ow_rq_domain /ow_polyscale;have h:=NTRUPoly.degZ_le c p;smt(). qed.
lemma ow_scale3_domain p : ow_rq_domain p=>ow_rq_domain(ow_scale3 p).
proof. rewrite ow_scale3E;exact(ow_polyscale_domain (lift_int 3) p). qed.
lemma ow_unscale3_domain p : ow_rq_domain p=>ow_rq_domain(ow_unscale3 p).
proof. rewrite ow_unscale3E;exact(ow_polyscale_domain (CycloFq.inv(lift_int 3)) p). qed.
lemma ow_scale3_cancel p : ow_unscale3(ow_scale3 p)=p.
proof.
 apply/NTRUPoly.poly_eqP=>i hi;rewrite ow_unscale3E ow_scale3E /ow_polyscale !NTRUPoly.polyZE.
 exact(ow_coeff_scale_cancel (lift_int 3) (NTRUPoly."_.[_]" p i) lift_three_nonzero).
qed.
lemma ow_scale3_cancel_right p : ow_scale3(ow_unscale3 p)=p.
proof.
 apply/NTRUPoly.poly_eqP=>i hi;rewrite ow_unscale3E ow_scale3E /ow_polyscale !NTRUPoly.polyZE.
 exact(ow_coeff_scale_cancel_right (lift_int 3) (NTRUPoly."_.[_]" p i) lift_three_nonzero).
qed.
lemma ow_scale3_unit p : pke_rq_unit(ow_scale3 p)<=>pke_rq_unit p.
proof. rewrite /ow_scale3;exact(pke_rq_unit_three p). qed.

(* This sampler equality can be called before an arbitrary later adaptive
   context; it does not discard or constrain that context's global state. *)
module OWUniformSampler = {
 proc sample():NTRUPoly.poly = {var p;p<$ow_uniform_rq;return p;}
 proc scale3():NTRUPoly.poly = {
  var p,a:NTRUPoly.poly;p<$ow_uniform_rq;a<-ow_scale3 p;return a;
 }
}.
lemma ow_uniform_sampler_scale3 :
 equiv[OWUniformSampler.scale3 ~ OWUniformSampler.sample:true ==> ={res}].
proof. proc;rndsem*{1} 0;rnd;auto=> />;by rewrite ow_uniform_scale3. qed.
