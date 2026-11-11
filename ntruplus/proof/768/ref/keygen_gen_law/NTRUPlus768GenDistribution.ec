require import AllCore Distr DProd.
from Jasmin require import JWord.
require import Array192 Array768 Array1152 Array2336 Array14466.
require import NTRUPlus768GenModel NTRUPlus768GenAcceptance.
require import NTRUPlus768PKEKeyDistribution NTRUPlus768PKEModel.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteProof.
require import NTRUPlus768KeygenSamplerAlgebra.
require import NTRUPlus768ROMDistributions NTRUPlus768ROMOracles.
require import NTRUPlus768FreshRetryLaw NTRUPlus768FreshKeyPairLaw.
require import NTRUPlus768AcceptanceProbability.
require import NTRUPlus768CCASetupState NTRUPlus768CCASetupProgrammed.
require import NTRUPlus768CyclotomicFactorization NTRUPlus768ForwardNTTStage1Semantics.

(* Figure 18 samples two independent whole polynomials. The f draw is
   shaped before its unit test; the g draw is unscaled at this interface. *)
op [opaque] gen_f0_accept (p:NTRUPoly.poly) = pke_rq_unit(gen_shape_f p).
op [opaque] gen_f0_law = dcond pke_field_psi1 gen_f0_accept.
op [opaque] gen_g_law = dcond pke_field_psi1 pke_rq_unit.
op [opaque] gen_f_law = dmap gen_f0_law gen_shape_f.
op [opaque] gen_fg_law = gen_f_law `*` gen_g_law.
op [opaque] gen_key_law = dmap gen_fg_law gen_key_from_fg.
op [opaque] gen_buffer_fg (bs:W8.t Array192.t*W8.t Array192.t) =
 (input_poly(keygen_f_pre_ntt_spec bs.`1),pke_cbd_field bs.`2).

lemma gen_field_psi_lossless : is_lossless pke_field_psi1.
proof. rewrite /pke_field_psi1; apply/dmap_ll; exact pke_psi1_lossless. qed.

lemma gen_f_predicate_factor :
 keygen_f_accept=gen_f0_accept \o pke_cbd_field.
proof.
 apply fun_ext=>b; rewrite /(\o) /gen_f0_accept -gen_shape_fE.
 exact(gen_f_accept_unit b).
qed.
lemma gen_g_predicate_factor :
 keygen_g_accept=pke_rq_unit \o pke_cbd_field.
proof. apply fun_ext=>b; exact(gen_g_accept_unit b). qed.

lemma gen_f_conditioned_field :
 dmap (dcond uniform192 keygen_f_accept) pke_cbd_field=gen_f0_law.
proof.
 by rewrite /gen_f0_law -pke_field_psi1_uniform
  (dcond_dmap uniform192 pke_cbd_field gen_f0_accept) -gen_f_predicate_factor.
qed.
lemma gen_g_conditioned_field :
 dmap (dcond uniform192 keygen_g_accept) pke_cbd_field=gen_g_law.
proof.
 by rewrite /gen_g_law -pke_field_psi1_uniform
  (dcond_dmap uniform192 pke_cbd_field pke_rq_unit) -gen_g_predicate_factor.
qed.
lemma gen_f_shaped_field :
 dmap (dcond uniform192 keygen_f_accept) (fun b=>input_poly(keygen_f_pre_ntt_spec b))=gen_f_law.
proof.
 have he:(fun b=>input_poly(keygen_f_pre_ntt_spec b))=gen_shape_f \o pke_cbd_field.
 + apply fun_ext=>b; by rewrite /(\o) pke_f_field_shape gen_shape_fE.
 by rewrite he -dmap_comp gen_f_conditioned_field /gen_f_law.
qed.
lemma gen_buffer_pair_law : dmap fresh_accepted_pair_law gen_buffer_fg=gen_fg_law.
proof.
 rewrite /fresh_accepted_pair_law /gen_fg_law.
 have h:=dmap_dprod (dcond uniform192 keygen_f_accept) (dcond uniform192 keygen_g_accept)
  (fun b=>input_poly(keygen_f_pre_ntt_spec b)) pke_cbd_field.
 rewrite gen_f_shaped_field gen_g_conditioned_field in h.
 rewrite /gen_buffer_fg; apply/eq_sym; exact h.
qed.

lemma gen_f_accept_mass : mu pke_field_psi1 gen_f0_accept=fresh_f_accept_mass.
proof.
 rewrite -pke_field_psi1_uniform (dmapE uniform192 pke_cbd_field gen_f0_accept)
  -gen_f_predicate_factor /fresh_f_accept_mass.
 done.
qed.
lemma gen_g_accept_mass : mu pke_field_psi1 pke_rq_unit=fresh_g_accept_mass.
proof.
 rewrite -pke_field_psi1_uniform (dmapE uniform192 pke_cbd_field pke_rq_unit)
  -gen_g_predicate_factor /fresh_g_accept_mass.
 done.
qed.
lemma gen_f0_lossless : is_lossless gen_f0_law.
proof. rewrite /gen_f0_law; apply/dcond_ll; rewrite gen_f_accept_mass; exact fresh_f_accept_positive. qed.
lemma gen_g_lossless : is_lossless gen_g_law.
proof. rewrite /gen_g_law; apply/dcond_ll; rewrite gen_g_accept_mass; exact fresh_g_accept_positive. qed.
lemma gen_f_lossless : is_lossless gen_f_law.
proof. rewrite /gen_f_law; apply/dmap_ll; exact gen_f0_lossless. qed.
lemma gen_fg_lossless : is_lossless gen_fg_law.
proof. rewrite /gen_fg_law dprod_ll; split; [exact gen_f_lossless|exact gen_g_lossless]. qed.
lemma gen_key_lossless : is_lossless gen_key_law.
proof. rewrite /gen_key_law; apply/dmap_ll; exact gen_fg_lossless. qed.

lemma gen_f0_support f0 : f0 \in gen_f0_law =>
 f0 \in pke_field_psi1 /\ pke_rq_unit(gen_shape_f f0).
proof. by rewrite /gen_f0_law dcond_supp /gen_f0_accept. qed.
lemma gen_f_support_unit f : f \in gen_f_law => pke_rq_unit f.
proof.
 move=>hs; rewrite /gen_f_law supp_dmap in hs.
 case hs=>f0 [hf he].
 have [_ hu]:=gen_f0_support f0 hf; smt().
qed.
lemma gen_g_support g : g \in gen_g_law => g \in pke_field_psi1 /\ pke_rq_unit g.
proof. by rewrite /gen_g_law dcond_supp. qed.
lemma gen_fg_support_unit fg : fg \in gen_fg_law =>
 pke_rq_unit fg.`1 /\ pke_rq_unit fg.`2.
proof.
 move=>hs; rewrite /gen_fg_law supp_dprod in hs.
 have [hf hg]:=hs.
 split; first exact(gen_f_support_unit fg.`1 hf).
 have [_ hu]:=gen_g_support fg.`2 hg; exact hu.
qed.

(* These are actual instrumented-call laws, before discarding the private
   accepted buffers. The final public-key law below uses serialized pk/sk. *)
lemma gen_fresh_fg_law &m workspace (event:NTRUPoly.poly*NTRUPoly.poly->bool) :
 Pr[KeygenInstrumented(UniformSeedRNG,FreshExpand,SHAKEFROM).run(workspace) @ &m:
 event(input_poly(keygen_f_pre_ntt_spec res.`1.`kg_fbuf),pke_cbd_field res.`1.`kg_gbuf)]=
 mu gen_fg_law event.
proof.
 rewrite -gen_buffer_pair_law dmapE.
 have h:=fresh_keygen_buffer_pair_probability &m workspace (event \o gen_buffer_fg).
 by move:h; rewrite /gen_buffer_fg /(\o).
qed.

require import NTRUPlus768GenKeyProjection NTRUPlus768ROMKeygen.

(* The independent mathematical public-key choice is defined throughout
   the supported conditioned law; its default is not silently assumed away. *)
lemma gen_fg_support_defined fg : fg \in gen_fg_law =>
 gen_public_defined fg.`1 fg.`2.
proof.
 move=>hg; rewrite -gen_buffer_pair_law supp_dmap in hg.
 case hg=>bs [hs he].
 rewrite /fresh_accepted_pair_law supp_dprod in hs.
 have [hf hg]:=hs.
 rewrite dcond_supp in hf; have [_ af]:=hf.
 rewrite dcond_supp in hg; have [_ ag]:=hg.
 rewrite he /gen_buffer_fg /=.
 exact(gen_accepted_buffers_defined bs.`1 bs.`2 af ag).
qed.
lemma gen_supported_key_relation fg : fg \in gen_fg_law =>
 gen_public_relation fg.`1 fg.`2 (gen_key_from_fg fg).`1.
proof.
 move=>hs; rewrite /gen_key_from_fg /=.
 exact(gen_public_key_relation fg.`1 fg.`2 (gen_fg_support_defined fg hs)).
qed.

lemma gen_fresh_core_value :
 hoare[KeygenInstrumented(UniformSeedRNG,FreshExpand,SHAKEFROM).run:true ==>
 gen_actual_core res.`1=gen_key_from_fg
   (input_poly(keygen_f_pre_ntt_spec res.`1.`kg_fbuf),pke_cbd_field res.`1.`kg_gbuf)].
proof.
 conseq(rom_keygen_instrumented UniformSeedRNG FreshExpand)=> />;
 smt(pke_key_from_rom gen_valid_key_projection).
qed.

lemma gen_fresh_core_law &m workspace (event:NTRUPoly.poly*NTRUPoly.poly->bool) :
 Pr[KeygenInstrumented(UniformSeedRNG,FreshExpand,SHAKEFROM).run(workspace) @ &m:
 event(gen_actual_core res.`1)]=mu gen_key_law event.
proof.
 rewrite /gen_key_law dmapE.
 rewrite -(gen_fresh_fg_law &m workspace (event \o gen_key_from_fg)).
 byequiv (_: ={workspace,glob ROF} ==> ={res} /\
   gen_actual_core res.`1{1}=gen_key_from_fg
    (input_poly(keygen_f_pre_ntt_spec res.`1.`kg_fbuf){1},pke_cbd_field res.`1.`kg_gbuf{1})).
 + conseq (_: ={workspace,glob ROF} ==> ={res,glob ROF}) gen_fresh_core_value _ => />.
   sim.
 + done.
 move=> &1 &2 [he hp]; by rewrite /(\o) -he -hp.
qed.
lemma gen_fresh_core_phoare (event:NTRUPoly.poly*NTRUPoly.poly->bool) :
 phoare[KeygenInstrumented(UniformSeedRNG,FreshExpand,SHAKEFROM).run:true ==>
 event(gen_actual_core res.`1)]=(mu gen_key_law event).
proof. bypr=> &m _; exact(gen_fresh_core_law &m workspace{m} event). qed.

(* The public endpoint observes the returned pk/sk byte arrays. Neither
   private sampler buffers nor E-table contents are inputs to this observation. *)
lemma gen_fresh_public_key_law &m (event:NTRUPoly.poly*NTRUPoly.poly->bool) :
 Pr[Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run() @ &m:
 event(gen_serialized_core res.`1 res.`2)]=mu gen_key_law event.
proof.
 byphoare (_:true ==>event(gen_serialized_core res.`1 res.`2))=> //.
 proc; call(gen_fresh_core_phoare event); auto=> />; by rewrite /gen_actual_core.
qed.
lemma gen_programmed_public_projection :
 equiv[Keygen(UniformSeedRNG,ProgrammedFreshExpand,SHAKEFROM).run ~
       Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run :
 ={glob ROF} ==> ={res,glob ROF}].
proof. proc; call programmed_keygen_projection; auto. qed.
lemma gen_programmed_public_key_law &m (event:NTRUPoly.poly*NTRUPoly.poly->bool) :
 Pr[Keygen(UniformSeedRNG,ProgrammedFreshExpand,SHAKEFROM).run() @ &m:
 event(gen_serialized_core res.`1 res.`2)]=mu gen_key_law event.
proof.
 rewrite -(gen_fresh_public_key_law &m event).
 by byequiv gen_programmed_public_projection.
qed.

