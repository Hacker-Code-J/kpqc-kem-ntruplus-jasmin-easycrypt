require import AllCore IntDiv List Finite Ring StdOrder.
from Jasmin require import JWord.
require import Array4 Array768.
require import NTRUPlus768BasemulAlgebra NTRUPlus768PolyBasemulProof NTRUPlus768PolyBasemulAlgebra.
require import NTRUPlus768PolyBaseInvBridge NTRUPlus768KeygenHBridge NTRUPlus768KeygenPublicKeyBridge.
require import NTRUPlus768KeygenSecretFBridge NTRUPlus768ValidKeyR2Algebra.
require import NTRUPlus768EvaluationSemantics NTRUPlus768TerminalRepresentation.
require import NTRUPlus768CyclotomicFactorization NTRUPlus768EncapCompleteAlgebra.
require import NTRUPlus768ForwardNTTStage1Semantics NTRUPlus768InverseNTTSemantics.
require import NTRUPlus768InvNTTAlgebra NTRUPlus768InvNTTRadix2_4Algebra.
require import NTRUPlus768PolyBasemulInvNTTAlgebra NTRUPlus768DecapCandidateSpec.
require import NTRUPlus768RRecCanonical NTRUPlus768RRecTerminal NTRUPlus768RRecTransform.
require import NTRUPlus768PKEKeyDistribution NTRUPlus768KeygenTerminalUnit.
import IntOrder Ring.IntID.
abbrev ( + ) = NTRUPoly.PolyComRing.( + ).
abbrev ( * ) = NTRUPoly.PolyComRing.( * ).
abbrev [ - ] = NTRUPoly.PolyComRing.([-]).
abbrev ( - ) (p q:poly) = p+(-q).

(* A represented terminal value determines one global quotient class.
   This follows from the proved inverse semantics, without a CRT axiom. *)
lemma gen_terminal_global_congr a p r :
 qrange_input_shape a => terminal_represents a p =>terminal_represents a r =>eqm_global p r.
proof.
 move=>ha hp hr.
 have h1:=inverse_invntt_spec_semantics p a hp ha.
 have h2:=inverse_invntt_spec_semantics r a hr ha.
 exact(eqm_global_trans _ _ _ h1 (eqm_global_sym _ _ h2)).
qed.

lemma gen_rq_unit_cancel p u v :
 pke_rq_unit p =>eqm_global(p*u)(p*v)=>eqm_global u v.
proof.
 move=>hu heq.
 rewrite /pke_rq_unit in hu.
 move:hu=>[r hu].
 rewrite /eqm_global in hu.
 rewrite /eqm_global in heq.
 move:hu heq=>[h hh] [k hk].
 rewrite /eqm_global.
 exists(r*k+h*(v-u)).
 have he:v-u=r*(p*v-p*u)+(poly1-p*r)*(v-u) by ring.
 rewrite {1}he hk hh; ring.
qed.

lemma gen_identity_represents_one : terminal_represents ntt_block_identity poly1.
proof.
 move=>k hk; rewrite (ntt_identity_block k hk).
 have he:block_poly qring_unit4=poly1.
 + rewrite /block_poly /block_poly_fq /lift_word
     qring_unit4_coeff0 qring_unit4_coeff1 qring_unit4_coeff2 qring_unit4_coeff3.
   change(poly1+poly0*X+poly0*(NTRUPoly.PolyComRing.exp X 2)+
     poly0*(NTRUPoly.PolyComRing.exp X 3)=poly1).
   ring.
 rewrite he; exact(eqm4_refl k poly1).
qed.

lemma gen_identity_qrange : in_qrange768 ntt_block_identity.
proof. move=>k hk; exact(ntt_block_identity_qrange k hk). qed.

lemma gen_product_output_congr a b r s :
 in_qrange768 s =>poly_coeff_eq_mod_q s r =>poly_basemul_qring a b r 192 =>
 poly_basemul_qring a b s 192.
proof.
 move=>hs he hr k hk.
 have [_ hp]:=hr k hk.
 have e0:=poly_coeff_eq_mod_q_block4 r s k 0 he hk block4_offset0_range.
 have e1:=poly_coeff_eq_mod_q_block4 r s k 1 he hk block4_offset1_range.
 have e2:=poly_coeff_eq_mod_q_block4 r s k 2 he hk block4_offset2_range.
 have e3:=poly_coeff_eq_mod_q_block4 r s k 3 he hk block4_offset3_range.
 split; first exact(hs k hk).
 by rewrite e0 e1 e2 e3.
qed.

lemma gen_terminal_unit_implies_rq a p :
 terminal_represents a p =>gen_terminal_unit a =>pke_rq_unit p.
proof.
 move=>hp hu.
 rewrite /gen_terminal_unit in hu.
 move:hu=>[b hab].
 have [r hr]:=rrec_terminal_represented b.
 have hprod:=poly_basemul_qring_represents_product a b ntt_block_identity p r hp hr hab.
 rewrite /pke_rq_unit; exists r.
 exact(gen_terminal_global_congr ntt_block_identity (p*r) poly1
   (in_qrange768_implies_invntt_input_shape _ gen_identity_qrange)
   hprod gen_identity_represents_one).
qed.

lemma gen_finite_endomap_surjective ['a] (S:'a->bool) (F:'a->'a) :
 is_finite S =>(forall x,S x=>S(F x)) =>
 (forall x y,S x=>S y=>F x=F y=>x=y) =>
 forall y,S y=>exists x,S x /\ F x=y.
proof.
 move=>[s [hu hs]] hF hi y hy.
 have hinj:forall x z,x \in s=>z \in s=>F x=F z=>x=z.
 + move=>x z hx hz he; apply(hi x z _ _ he); by rewrite -hs.
 have hmap:uniq(map F s) by rewrite (map_inj_in_uniq F s hinj).
 have hsub:mem(map F s)<=mem s.
 + move=>z; move/mapP=>[x [hx ->]]; rewrite hs; apply hF; by rewrite -hs.
 have hsize:size s<=size(map F s) by rewrite size_map.
 have hp:=uniq_le_perm_eq (map F s) s hmap hsub hsize.
 have hym:y \in map F s by rewrite (perm_eq_mem _ _ hp y) hs.
 move/mapP:hym=>[x [hx he]]; exists x; split.
 + by rewrite -hs.
 by rewrite he.
qed.

lemma gen_canonical_block_range b : rrec_canonical_domain b=>in_qrange768 b.
proof.
 move=>hb; exact(encap_pointwise_blocks b (rrec_canonical_domain_input_qrange b hb)).
qed.
lemma gen_candidate_product_qring a b : in_qrange768 a=>rrec_canonical_domain b=>
 poly_basemul_qring a b (candidate_product_spec a b) 192.
proof.
 move=>ha hb; exact(poly_basemul_word_to_qring a b _ ha
   (gen_canonical_block_range b hb) (candidate_product_word a b)).
qed.

op [opaque] gen_terminal_multiply (a b:W16.t Array768.t) =
 rrec_canonical(candidate_product_spec a b).
lemma gen_terminal_multiply_closed a b :
 rrec_canonical_domain(gen_terminal_multiply a b).
proof. rewrite /gen_terminal_multiply; exact(rrec_canonical_range _). qed.

lemma gen_terminal_multiply_represents a p b :
 in_qrange768 a=>terminal_represents a p=>rrec_canonical_domain b=>
 terminal_represents(gen_terminal_multiply a b)(p*input_poly(inverse_invntt_spec b)).
proof.
 move=>ha hp hb; rewrite /gen_terminal_multiply.
 apply(terminal_represents_mod_q_replacement (candidate_product_spec a b)).
 + exact(rrec_canonical_mod _).
 exact(poly_basemul_qring_represents_product a b _ p (input_poly(inverse_invntt_spec b))
   hp (rrec_terminal_inverse_represents b (rrec_canonical_domain_qrange b hb))
   (gen_candidate_product_qring a b ha hb)).
qed.

(* Multiplication by a global unit is injective on the finite canonical
   terminal arrays. This avoids constructing remainders of arbitrary
   polynomial inverse witnesses or assuming a CRT isomorphism. *)
lemma gen_terminal_multiply_injective a p :
 in_qrange768 a=>terminal_represents a p=>pke_rq_unit p=>
 forall b c,rrec_canonical_domain b=>rrec_canonical_domain c=>
 gen_terminal_multiply a b=gen_terminal_multiply a c=>b=c.
proof.
 move=>ha hp hu b c hb hc he.
 have hbp:=gen_terminal_multiply_represents a p b ha hp hb.
 have hcp:terminal_represents(gen_terminal_multiply a b)(p*input_poly(inverse_invntt_spec c)).
 + rewrite he; exact(gen_terminal_multiply_represents a p c ha hp hc).
 have hg:=gen_terminal_global_congr _ _ _
   (rrec_canonical_domain_qrange _ (gen_terminal_multiply_closed a b)) hbp hcp.
 have hcan:=gen_rq_unit_cancel p _ _ hu hg.
 have hbr:=rrec_terminal_inverse_represents b (rrec_canonical_domain_qrange b hb).
 have hcr:=rrec_terminal_inverse_represents c (rrec_canonical_domain_qrange c hc).
 have hbc:=terminal_represents_global_congr b _ _ hcan hbr.
 have hmod:=rrec_terminal_same_poly_mod_q b c _ hbc hcr.
 rewrite -(rrec_canonical_fixed b hb) -(rrec_canonical_fixed c hc).
 exact(rrec_canonical_congruent b c hmod).
qed.

lemma gen_rq_unit_implies_terminal a p :
 in_qrange768 a=>terminal_represents a p=>pke_rq_unit p=>gen_terminal_unit a.
proof.
 move=>ha hp hu.
 have hclosed:forall b,rrec_canonical_domain b=>rrec_canonical_domain(gen_terminal_multiply a b).
 + move=>b _; exact(gen_terminal_multiply_closed a b).
 have [b [hb he]]:=gen_finite_endomap_surjective rrec_canonical_domain (gen_terminal_multiply a)
   rrec_canonical_domain_finite hclosed (gen_terminal_multiply_injective a p ha hp hu)
   (rrec_canonical ntt_block_identity) (rrec_canonical_range ntt_block_identity).
 have heq:rrec_canonical(candidate_product_spec a b)=rrec_canonical ntt_block_identity.
 + by move:he; rewrite /gen_terminal_multiply.
 have hm:=iffLR _ _ (rrec_canonical_eq_iff (candidate_product_spec a b) ntt_block_identity) heq.
 have hrev:poly_coeff_eq_mod_q ntt_block_identity(candidate_product_spec a b).
 + move=>j hj; apply/eq_sym; exact(hm j hj).
 rewrite /gen_terminal_unit; exists b.
 exact(gen_product_output_congr a b _ _ gen_identity_qrange hrev (gen_candidate_product_qring a b ha hb)).
qed.

lemma gen_terminal_unit_iff_rq a p :
 in_qrange768 a=>terminal_represents a p=>(gen_terminal_unit a<=>pke_rq_unit p).
proof.
 move=>ha hp; split.
 + exact(gen_terminal_unit_implies_rq a p hp).
 exact(gen_rq_unit_implies_terminal a p ha hp).
qed.
