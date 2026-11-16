require import AllCore List Distr DProd FMap FSet RealSeries StdOrder.
from Jasmin require import JWord.
require import Array96 Array192 Array768 Array1152.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768PKEModel NTRUPlus768PKEKeyDistribution.
require import NTRUPlus768PolySOTPEncodeAlgebra NTRUPlus768ROMDistributions NTRUPlus768ROMOracles.
require import NTRUPlus768RRecCodec NTRUPlus768ACWC2Domains NTRUPlus768ACWC2Oracle NTRUPlus768SpreadTransfer NTRUPlus768SpreadCBD.
import RealOrder.

(* The cache is fixed before the fresh, independent randomness draw. *)
module SpreadEncodedValue = {
 proc run(pk:W8.t Array1152.t,msg:W8.t Array96.t) : W8.t Array1152.t option = {
  var r:pke_poly; var pad:W8.t Array192.t;
  r <$ pke_psi1;
  pad <@ ROG.get(rr_G_input r);
  return pke_enc_spec pk (poly_sotp_encode_spec msg pad) r;
 }
}.

lemma spread_g_input_point_bound bs :
 mu pke_psi1(fun r=>rr_G_input r=bs)<=1%r/(2%r^768).
proof.
 case(exists r,pke_domain r /\ rr_G_input r=bs)=>he.
 + move:he=>[r [hr hb]].
   have hm:mu pke_psi1(fun s=>rr_G_input s=bs)=mu1 pke_psi1 r.
   - apply mu_eq_support=>s hs; rewrite /pred1.
     have hd:pke_domain s by move:hs; rewrite acwc2_psi1_support.
     apply eq_iff; split=>h.
     + apply(rr_G_input_injective s r hd hr); smt().
     by rewrite /= h hb.
   rewrite hm; exact(spread_cbd_point_bound r).
 have hm:mu pke_psi1(fun r=>rr_G_input r=bs)=0%r.
 + rewrite -(mu0 pke_psi1); apply mu_eq_support=>r hr /=.
   have hd:pke_domain r by move:hr; rewrite acwc2_psi1_support.
   smt().
 rewrite hm; exact(ltrW _ _ spread_cbd_bound_positive).
qed.
lemma spread_g_cache_hit_bound (gm:(W8.t Array1152.t,W8.t Array192.t)fmap) :
 mu pke_psi1(fun r=>rr_G_input r \in gm)<=(fsize gm)%r/(2%r^768).
proof.
 have he:mu pke_psi1(fun r=>rr_G_input r \in gm)=
  mu pke_psi1(fun r=>has(fun x=>rr_G_input r=x)(elems(fdom gm))).
 + apply mu_eq=>r; rewrite hasP -mem_fdom FSet.memE; smt().
 rewrite he /fsize FSet.cardE.
 apply mu_has_leM=>x hx; exact(spread_g_input_point_bound x).
qed.

module SpreadEncodedReference = {
 proc run(pk:W8.t Array1152.t,msg:W8.t Array96.t,
   gm:(W8.t Array1152.t,W8.t Array192.t)fmap) : W8.t Array1152.t option = {
  var r:pke_poly; var pad:W8.t Array192.t;
  r <$ pke_psi1;
  pad <$ uniform192;
  return pke_enc_spec pk (poly_sotp_encode_spec msg
   (if rr_G_input r \in gm then oget gm.[rr_G_input r] else pad)) r;
 }
}.
lemma spread_encoded_reference :
 equiv[SpreadEncodedValue.run ~ SpreadEncodedReference.run:
 ={pk,msg} /\ ROG.m{1}=gm{2} ==> ={res}].
proof.
 proc; inline{1} ROG.get.
 seq 1 1:(={r,pk,msg} /\ ROG.m{1}=gm{2}); first by rnd; auto.
 case(rr_G_input r{1} \in gm{2}).
 + rcondf{1} 2; first by auto.
   rnd{2}; auto=> />; rewrite uniform192_ll; smt().
 rcondt{1} 2; first by auto.
 wp; rnd; auto=> />.
 move=> &2 hmiss pad hpad; by rewrite get_set_sameE.
qed.
lemma spread_encoded_reference_law &m pk0 msg0 gm0 ct0 :
 Pr[SpreadEncodedReference.run(pk0,msg0,gm0) @ &m:res=Some ct0]=
 mu(pke_psi1 `*` uniform192)
  (fun (rp:pke_poly*W8.t Array192.t)=>pke_enc_spec pk0
   (poly_sotp_encode_spec msg0(if rr_G_input rp.`1 \in gm0 then oget gm0.[rr_G_input rp.`1] else rp.`2))rp.`1=Some ct0).
proof.
 byphoare(_:pk=pk0 /\ msg=msg0 /\ gm=gm0 ==>res=Some ct0)=> //.
 proc; rndsem 0.
 rnd(fun (rp:pke_poly*W8.t Array192.t)=>pke_enc_spec pk0
   (poly_sotp_encode_spec msg0(if rr_G_input rp.`1 \in gm0 then oget gm0.[rr_G_input rp.`1] else rp.`2))rp.`1=Some ct0).
 skip=> />.
 by rewrite -dprod_dlet.
qed.

lemma spread_encoded_value_lossless : islossless SpreadEncodedValue.run.
proof. proc; call rog_get_ll; rnd; auto=> />; exact pke_psi1_lossless. qed.

lemma spread_encoded_reference_bound w msg ct gm &m : pke_key_relation w=>
 Pr[SpreadEncodedReference.run(w.`kg_pk,msg,gm) @ &m:res=Some ct]<=
 (fsize gm+1)%r/(2%r^768).
proof.
 move=>hk; rewrite spread_encoded_reference_law.
 pose hit := (fun r:pke_poly=>rr_G_input r \in gm).
 pose fresh := (fun (rp:pke_poly*W8.t Array192.t)=>
  pke_enc_spec w.`kg_pk(poly_sotp_encode_spec msg rp.`2)rp.`1=Some ct).
 have hs:mu(pke_psi1 `*` uniform192)
  (fun (rp:pke_poly*W8.t Array192.t)=>pke_enc_spec w.`kg_pk
    (poly_sotp_encode_spec msg(if rr_G_input rp.`1 \in gm then oget gm.[rr_G_input rp.`1] else rp.`2))rp.`1=Some ct)
  <=mu(pke_psi1 `*` uniform192)(fun (rp:pke_poly*W8.t Array192.t)=>hit rp.`1 \/ fresh rp).
 + clear hk; apply mu_le=>rp hr /=; rewrite /hit /fresh; case(rr_G_input rp.`1 \in gm); smt().
 have hu:mu(pke_psi1 `*` uniform192)(fun (rp:pke_poly*W8.t Array192.t)=>hit rp.`1 \/ fresh rp)<=
  mu pke_psi1 hit+mu(pke_psi1 `*` uniform192)fresh.
 + clear hk hs; rewrite mu_or (dprodEl pke_psi1 uniform192 hit) uniform192_ll.
   have h:=ge0_mu(pke_psi1 `*` uniform192)(predI (fun (rp:pke_poly*W8.t Array192.t)=>hit rp.`1) fresh); smt().
 have hh:=spread_g_cache_hit_bound gm.
 have hf:=spread_independent_pad_bound w msg ct hk.
 apply(ler_trans _ _ _ hs); apply(ler_trans _ _ _ hu).
 rewrite /hit /fresh.
 have he:(fsize gm)%r/(2%r^768)+1%r/(2%r^768)=(fsize gm+1)%r/(2%r^768).
 + by rewrite fromintD /=; ring.
 rewrite -he; apply ler_add; [exact hh|exact hf].
qed.

lemma spread_encoded_cache_probability w msg ct gm &m : pke_key_relation w=>ROG.m{m}=gm=>
 Pr[SpreadEncodedValue.run(w.`kg_pk,msg) @ &m:res=Some ct]<=(fsize gm+1)%r/(2%r^768).
proof.
 move=>hk hm.
 have he:Pr[SpreadEncodedValue.run(w.`kg_pk,msg) @ &m:res=Some ct]=
  Pr[SpreadEncodedReference.run(w.`kg_pk,msg,gm) @ &m:res=Some ct].
 + by byequiv spread_encoded_reference=> //.
 rewrite he; exact(spread_encoded_reference_bound w msg ct gm &m hk).
qed.
lemma spread_encoded_cache_bound w msg0 ct0 gm0 : pke_key_relation w=>
 phoare[SpreadEncodedValue.run:
 pk=w.`kg_pk /\ msg=msg0 /\ ROG.m=gm0 ==>res=Some ct0] <=((fsize gm0+1)%r/(2%r^768)).
proof.
 move=>hk; bypr=> &m [hp [hm hg]]; rewrite hp hm.
 exact(spread_encoded_cache_probability w msg0 ct0 gm0 &m hk hg).
qed.

(* This is an exact prepared-table observation law, not a fixed-G bound. *)
lemma spread_encoded_prepared_probability w msg g gm ct &m :
 acwc2_cache_matches g gm=>ROG.m{m}=gm=>
 Pr[SpreadEncodedValue.run(w.`kg_pk,msg) @ &m:res=Some ct]=spread_cipher_mass w msg g ct.
proof.
 move=>hg hm.
 have he:Pr[SpreadEncodedValue.run(w.`kg_pk,msg) @ &m:res=Some ct]=
  Pr[SpreadEncodedReference.run(w.`kg_pk,msg,gm) @ &m:res=Some ct].
 + by byequiv spread_encoded_reference=> //.
 rewrite he spread_encoded_reference_law /spread_cipher_mass.
 have hp:mu(pke_psi1 `*` uniform192)
  (fun (rp:pke_poly*W8.t Array192.t)=>pke_enc_spec w.`kg_pk
   (poly_sotp_encode_spec msg(if rr_G_input rp.`1 \in gm then oget gm.[rr_G_input rp.`1] else rp.`2))rp.`1=Some ct)=
  mu(pke_psi1 `*` uniform192)
   (fun (rp:pke_poly*W8.t Array192.t)=>pke_enc_spec w.`kg_pk(poly_sotp_encode_spec msg(g rp.`1))rp.`1=Some ct).
 + apply mu_eq_support=>rp hr /=.
   have hr0:rp.`1 \in pke_psi1 by move:hr; rewrite supp_dprod; smt().
   have hd:pke_domain rp.`1 by move:hr0; rewrite acwc2_psi1_support.
   have hv:=hg rp.`1 hd.
   have hx:rr_G_input rp.`1 \in gm by rewrite domE hv.
   by rewrite hx hv /=.
 rewrite hp (dprodEl pke_psi1 uniform192
  (fun r=>pke_enc_spec w.`kg_pk(poly_sotp_encode_spec msg(g r))r=Some ct)) uniform192_ll; ring.
qed.
