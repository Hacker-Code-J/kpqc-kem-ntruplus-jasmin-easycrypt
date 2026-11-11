require import AllCore Distr Ring.
from Jasmin require import JWord.
require import Array192 Array768.
require import NTRUPlus768GenModel NTRUPlus768GenDistribution NTRUPlus768GenKeyProjection.
require import NTRUPlus768PKEKeyDistribution NTRUPlus768PKEModel.
require import NTRUPlus768KeygenSamplerBridge NTRUPlus768KeygenCompleteSpec.
require import NTRUPlus768KeygenSamplerAlgebra NTRUPlus768KeygenGlobalUnit.
require import NTRUPlus768KeygenCompleteInverse NTRUPlus768KeygenInverseBridge.
require import NTRUPlus768RRecInverseAlgebra NTRUPlus768PolyBaseInvBridge.
require import NTRUPlus768RRecPublicInverse.
require import NTRUPlus768KeygenSecretFBridge NTRUPlus768PolyBasemulAlgebra.
require import NTRUPlus768DecapCandidateSpec NTRUPlus768PolyBasemulProof.
require import NTRUPlus768ROMDistributions NTRUPlus768FreshRetryLaw.
require import NTRUPlus768CyclotomicFactorization NTRUPlus768EvaluationSemantics NTRUPlus768TerminalRepresentation.
require import NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768CoefficientRecovery.
require import NTRUPlus768OWUniform NTRUPlus768OWUniformScale NTRUPlus768OWAlgebra.
abbrev ( * ) = NTRUPoly.PolyComRing.( * ).

(* Definition 2.6 is interpreted on its defined inverse: f is sampled
   from gen_f_law, while g is UNCONDITIONED pke_field_psi1. The operation
   below is the unique ordinary-degree<768 quotient on precisely that
   support. The reduction itself receives h; it does not evaluate choice. *)
op [opaque] ow_ntru_key (f g:NTRUPoly.poly) = ow_unscale3(gen_public_key f g).

lemma ow_gen_buffers_defined fb gb : keygen_f_accept fb=>
 gen_public_defined (input_poly(keygen_f_pre_ntt_spec fb)) (pke_cbd_field gb).
proof.
 move=>hf.
 have hs:keygen_inverse_status(keygen_f_ntt_spec fb)=W64.zero.
 + exact(iffRL _ _ (keygen_f_attempt_accept fb) hf).
 have hi:=rrec_raw_inverse_success _ (keygen_f_ntt_qrange fb) hs.
 have hir:=poly_baseinv_success_output_qrange _ _ hi.
 have hp:poly_basemul_qring (keygen_g_ntt_spec gb) (keygen_inverse_value(keygen_f_ntt_spec fb))
   (candidate_product_spec (keygen_g_ntt_spec gb) (keygen_inverse_value(keygen_f_ntt_spec fb))) 192.
 + exact(poly_basemul_word_to_qring _ _ _ (keygen_g_ntt_qrange gb) hir (candidate_product_word _ _)).
 apply(gen_public_defined_witness _ _
   (gen_inverse_poly(candidate_product_spec (keygen_g_ntt_spec gb) (keygen_inverse_value(keygen_f_ntt_spec fb))))).
 exact(gen_public_product_relation fb gb _ _ hi hp).
qed.

lemma ow_gen_public_defined f g : f \in gen_f_law=>g \in pke_field_psi1=>gen_public_defined f g.
proof.
 rewrite -gen_f_shaped_field -pke_field_psi1_uniform !supp_dmap.
 move=>[fb [hf he]] [gb [hg hge]].
 rewrite dcond_supp in hf;have [_ ha]:=hf.
 rewrite he hge;exact(ow_gen_buffers_defined fb gb ha).
qed.

lemma ow_gen_public_relation f g : f \in gen_f_law=>g \in pke_field_psi1=>
 gen_public_relation f g (gen_public_key f g).
proof. move=>hf hg;exact(gen_public_key_relation f g (ow_gen_public_defined f g hf hg)). qed.

lemma ow_ntru_scale3 f g : ow_scale3(ow_ntru_key f g)=gen_public_key f g.
proof. rewrite /ow_ntru_key;exact(ow_scale3_cancel_right _). qed.

lemma ow_ntru_degree f g : f \in gen_f_law=>g \in pke_field_psi1=>NTRUPoly.deg(ow_ntru_key f g)<=768.
proof.
 move=>hf hg;have hr:=ow_gen_public_relation f g hf hg.
 have hd:NTRUPoly.deg(gen_public_key f g)<=768 by move:hr;rewrite /gen_public_relation;smt().
 rewrite /ow_ntru_key;exact(ow_unscale3_domain _ hd).
qed.

lemma ow_ntru_relation f g : f \in gen_f_law=>g \in pke_field_psi1=>
 eqm_global((ow_ntru_key f g)*f)g.
proof.
 move=>hf hg;have hr:=ow_gen_public_relation f g hf hg.
 have he:eqm_global((gen_public_key f g)*f)(NTRUPoly.polyC(lift_int 3)*g)
 by move:hr;rewrite /gen_public_relation;smt().
 have hs:=eqm_global_mul (NTRUPoly.polyC(CycloFq.inv(lift_int 3)))
  (NTRUPoly.polyC(CycloFq.inv(lift_int 3))) _ _
  (eqm_global_refl _) he.
 have e1:NTRUPoly.polyC(CycloFq.inv(lift_int 3))*(gen_public_key f g*f)=ow_ntru_key f g*f
 by rewrite /ow_ntru_key /ow_unscale3;ring.
 have e2:NTRUPoly.polyC(CycloFq.inv(lift_int 3))*(NTRUPoly.polyC(lift_int 3)*g)=g.
 + change(ow_unscale3(ow_scale3 g)=g);exact(ow_scale3_cancel g).
 by move:hs;rewrite e1 e2.
qed.

lemma ow_ntru_unique f g h : f \in gen_f_law=>g \in pke_field_psi1=>
 NTRUPoly.deg h<=768=>eqm_global(h*f)g=>h=ow_ntru_key f g.
proof.
 move=>hf hg hd he;have hu:=gen_f_support_unit f hf.
 have hc:=eqm_global_trans _ _ _ he (eqm_global_sym _ _ (ow_ntru_relation f g hf hg)).
 have ep:f*h=h*f by ring.
 have eq:f*ow_ntru_key f g=ow_ntru_key f g*f by ring.
 apply(eqm_global_low_degree_unique _ _ hd (ow_ntru_degree f g hf hg)).
 apply(gen_rq_unit_cancel f _ _ hu);by rewrite ep eq.
qed.

lemma ow_gen_public_unit f g : f \in gen_f_law=>g \in pke_field_psi1=>
 (pke_rq_unit(gen_public_key f g)<=>pke_rq_unit g).
proof.
 move=>hf hg;have hu:=gen_f_support_unit f hf.
 have hr:=ow_gen_public_relation f g hf hg.
 have he:eqm_global(gen_public_key f g*f)(NTRUPoly.polyC(lift_int 3)*g)
 by move:hr;rewrite /gen_public_relation;smt().
 have hh:=ow_unit_congr _ _ he.
 by move:hh;rewrite ow_unit_mul hu pke_rq_unit_three /=.
qed.
