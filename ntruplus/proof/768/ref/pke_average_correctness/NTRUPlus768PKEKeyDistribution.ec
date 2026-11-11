require import AllCore List Distr DList DProd Ring.
from Jasmin require import JWord.
require import Array192 Array768 Array14466.
require import NTRUPlus768ROMDistributions NTRUPlus768ROMOracles.
require import NTRUPlus768PolyCBD1Algebra NTRUPlus768CBDDistribution.
require import NTRUPlus768KeygenSamplerAlgebra NTRUPlus768KeygenSamplerBridge.
require import NTRUPlus768KeygenShapeProof NTRUPlus768NTTAlgebra.
require import NTRUPlus768PolyBaseInvProof NTRUPlus768KeygenCompleteSpec.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768FreshRetryLaw.
require import NTRUPlus768FreshKeyPairLaw NTRUPlus768AcceptanceProbability.
require import NTRUPlus768CyclotomicFactorization NTRUPlus768EvaluationSemantics.
require import NTRUPlus768TerminalRepresentation NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768ValidKeyM1Recovery NTRUPlus768AcceptanceAlgebra.
require import NTRUPlus768NumericalDFRModel NTRUPlus768KEMProposalContext.
require import NTRUPlus768KEMIdealObservation.
require import NTRUPlus768CoefficientRecovery NTRUPlus768Crepmod3Algebra.
require import NTRUPlus768BasemulAlgebra.
import CycloFq.
abbrev ( + ) = NTRUPoly.PolyComRing.( + ).
abbrev ( * ) = NTRUPoly.PolyComRing.( * ).

(* psi_1 describes an UNCONDITIONED polynomial: 768 independent CBD1 trits.
   Accepted keys condition a whole polynomial with the actual NTT/baseinv
   predicate. No independence of accepted coefficients is asserted. *)
op pke_psi1 : W16.t Array768.t distr = dmap (dlist dcbd 768) cbd_word_array.
op pke_field_psi1 : NTRUPoly.poly distr = dmap pke_psi1 input_poly.
op pke_cbd_field (buf:W8.t Array192.t) = input_poly(poly_cbd1_spec buf).
op pke_f_accept_array (p:W16.t Array768.t) =
 poly_blocks_succeed (forward_ntt_spec(keygen_shape_f_spec p)) 192.
op pke_g_accept_array (p:W16.t Array768.t) =
 poly_blocks_succeed (forward_ntt_spec(keygen_shape_g_spec p)) 192.
op pke_accepted_cbd_pair =
 (dcond pke_psi1 pke_f_accept_array) `*` (dcond pke_psi1 pke_g_accept_array).
op pke_buffer_cbd_pair (bs:W8.t Array192.t*W8.t Array192.t) =
 (poly_cbd1_spec bs.`1,poly_cbd1_spec bs.`2).
op pke_four_cbd (bs:four_buffers) =
 (pke_buffer_cbd_pair bs.`1,pke_buffer_cbd_pair bs.`2).

lemma pke_cbd1_uniform : dmap uniform192 poly_cbd1_spec=pke_psi1.
proof. exact cbd_poly_uniform. qed.
lemma pke_psi1_lossless : is_lossless pke_psi1.
proof. apply/dmap_ll/dlist_ll; exact dcbd_ll. qed.
lemma pke_psi1_trits p : p \in pke_psi1 => poly_cbd1_trit_output p.
proof.
 rewrite -pke_cbd1_uniform supp_dmap.
 move=>[buf hb].
 have hp:=poly_cbd1_spec_trit_output buf.
 smt().
qed.
lemma pke_field_psi1_uniform : dmap uniform192 pke_cbd_field=pke_field_psi1.
proof.
 rewrite /pke_field_psi1 -pke_cbd1_uniform (dmap_comp poly_cbd1_spec input_poly uniform192) /pke_cbd_field /(\o).
 apply eq_dmap=>buf; done.
qed.
lemma pke_f_accept_factors buf :
 keygen_f_accept buf=pke_f_accept_array(poly_cbd1_spec buf).
proof.
 by rewrite /keygen_f_accept /pke_f_accept_array /keygen_f_ntt_spec
 keygen_shape_f_sampled_spec.
qed.
lemma pke_g_accept_factors buf :
 keygen_g_accept buf=pke_g_accept_array(poly_cbd1_spec buf).
proof.
 by rewrite /keygen_g_accept /pke_g_accept_array /keygen_g_ntt_spec
 keygen_shape_g_sampled_spec.
qed.

(* Conditioning commutes with this pushforward because the implemented
   acceptance event factors through the entire CBD array. *)
lemma pke_f_conditioned_cbd :
 dmap (dcond uniform192 keygen_f_accept) poly_cbd1_spec=
 dcond pke_psi1 pke_f_accept_array.
proof.
 rewrite -pke_cbd1_uniform (dcond_dmap uniform192 poly_cbd1_spec pke_f_accept_array).
 have he : keygen_f_accept=pke_f_accept_array \o poly_cbd1_spec.
 + apply fun_ext=>buf; exact(pke_f_accept_factors buf).
 by rewrite he.
qed.
lemma pke_g_conditioned_cbd :
 dmap (dcond uniform192 keygen_g_accept) poly_cbd1_spec=
 dcond pke_psi1 pke_g_accept_array.
proof.
 rewrite -pke_cbd1_uniform (dcond_dmap uniform192 poly_cbd1_spec pke_g_accept_array).
 have he : keygen_g_accept=pke_g_accept_array \o poly_cbd1_spec.
 + apply fun_ext=>buf; exact(pke_g_accept_factors buf).
 by rewrite he.
qed.
lemma pke_accepted_cbd_pair_law :
 dmap fresh_accepted_pair_law pke_buffer_cbd_pair=pke_accepted_cbd_pair.
proof.
 rewrite /fresh_accepted_pair_law /pke_accepted_cbd_pair.
 have h:=dmap_dprod (dcond uniform192 keygen_f_accept)
  (dcond uniform192 keygen_g_accept) poly_cbd1_spec poly_cbd1_spec.
 rewrite pke_f_conditioned_cbd pke_g_conditioned_cbd in h.
 apply/eq_sym; exact h.
qed.
lemma pke_accepted_cbd_pair_lossless : is_lossless pke_accepted_cbd_pair.
proof. rewrite -pke_accepted_cbd_pair_law; apply/dmap_ll; exact fresh_accepted_pair_normalized. qed.
lemma pke_independent_cbd_pair :
 dmap (uniform192 `*` uniform192) pke_buffer_cbd_pair=pke_psi1 `*` pke_psi1.
proof.
 have h:=dmap_dprod uniform192 uniform192 poly_cbd1_spec poly_cbd1_spec.
 rewrite pke_cbd1_uniform in h; apply/eq_sym; exact h.
qed.
lemma pke_independent_key_randomness_message :
 dmap accepted_four_law pke_four_cbd=
 pke_accepted_cbd_pair `*` (pke_psi1 `*` pke_psi1).
proof.
 rewrite /accepted_four_law -/fresh_accepted_pair_law.
 have h:=dmap_dprod fresh_accepted_pair_law (uniform192 `*` uniform192)
  pke_buffer_cbd_pair pke_buffer_cbd_pair.
 rewrite pke_accepted_cbd_pair_law pke_independent_cbd_pair in h.
 apply/eq_sym; exact h.
qed.

(* This invokes the exact actual f-then-g retries, Finish and clearing law. *)
lemma pke_actual_keygen_cbd_pair_law &m workspace
 (event:(W16.t Array768.t*W16.t Array768.t)->bool) :
 Pr[KeygenInstrumented(UniformSeedRNG,FreshExpand,SHAKEFROM).run(workspace) @ &m :
 event(poly_cbd1_spec res.`1.`kg_fbuf,poly_cbd1_spec res.`1.`kg_gbuf)]=
 mu pke_accepted_cbd_pair event.
proof.
 rewrite -pke_accepted_cbd_pair_law dmapE.
 exact(fresh_keygen_buffer_pair_probability &m workspace (event \o pke_buffer_cbd_pair)).
qed.
lemma pke_actual_four_cbd_law &m
 (event:((W16.t Array768.t*W16.t Array768.t)*(W16.t Array768.t*W16.t Array768.t))->bool) :
 Pr[KeygenThenUniform(FreshExpand).run() @ &m :
 event(pke_four_cbd(observation_four_buffers res))]=
 mu (pke_accepted_cbd_pair `*` (pke_psi1 `*` pke_psi1)) event.
proof.
 rewrite -pke_independent_key_randomness_message dmapE.
 rewrite -(accepted_four_sample_law &m (event \o pke_four_cbd)).
 by byequiv fresh_keygen_four_buffers=> //.
qed.

(* Genuine quotient-ring invertibility; scalar three is a unit modulo q.
   Identifying the exact implemented acceptance test with this predicate is
   a separate obligation. None of the distribution laws above assumes it. *)
op pke_rq_unit (p:NTRUPoly.poly) : bool =
 exists r, eqm_global (p*r) NTRUPoly.poly1.
lemma pke_rq_unit_scale (c:CycloFq.cyclocoeff) (p:NTRUPoly.poly) :
 c<>CycloFq.zero =>
 (pke_rq_unit(NTRUPoly.polyC c*p) <=> pke_rq_unit p).
proof.
 move=>hc; rewrite /pke_rq_unit; split.
 + move=>[r hr]; exists(NTRUPoly.polyC c*r).
   have -> : p*(NTRUPoly.polyC c*r)=(NTRUPoly.polyC c*p)*r by ring.
   exact hr.
 move=>[r hr]; exists(NTRUPoly.polyC(CycloFq.inv c)*r).
 have hh : NTRUPoly.polyC c*NTRUPoly.polyC(CycloFq.inv c)=NTRUPoly.poly1.
 + by rewrite /NTRUPoly.PolyComRing.( * ) -NTRUPoly.polyCM (CycloFqField.mulfV c hc).
 have -> : (NTRUPoly.polyC c*p)*(NTRUPoly.polyC(CycloFq.inv c)*r)=
   (NTRUPoly.polyC c*NTRUPoly.polyC(CycloFq.inv c))*(p*r) by ring.
 rewrite hh /NTRUPoly.PolyComRing.( * ) NTRUPoly.mul1p.
 exact hr.
qed.
lemma pke_rq_unit_three p :
 pke_rq_unit(NTRUPoly.polyC(lift_int 3)*p) <=> pke_rq_unit p.
proof. exact(pke_rq_unit_scale (lift_int 3) p lift_three_nonzero). qed.
lemma pke_f_field_shape buf :
 input_poly(keygen_f_pre_ntt_spec buf)=
 NTRUPoly.poly1+NTRUPoly.polyC(lift_int 3)*pke_cbd_field buf.
proof. exact(keygen_f_input_poly_shape buf). qed.
lemma pke_g_field_shape buf :
 input_poly(keygen_g_pre_ntt_spec buf)=NTRUPoly.polyC(lift_int 3)*pke_cbd_field buf.
proof. exact(keygen_g_input_poly_shape buf). qed.
lemma pke_g_unscaled_unit buf :
 pke_rq_unit(input_poly(keygen_g_pre_ntt_spec buf)) <=> pke_rq_unit(pke_cbd_field buf).
proof. by rewrite pke_g_field_shape pke_rq_unit_three. qed.
lemma pke_f_shaped_unit buf :
 pke_rq_unit(input_poly(keygen_f_pre_ntt_spec buf)) <=>
 pke_rq_unit(NTRUPoly.poly1+NTRUPoly.polyC(lift_int 3)*pke_cbd_field buf).
proof. by rewrite pke_f_field_shape. qed.

(* The polynomial pushforward is the ordinary coefficient polynomial of
   the 768 iid integer trits; the word encoding introduces no truncation. *)
op pke_list_poly (xs:int list) = int_poly(Array768.of_list 0 xs).
lemma pke_dcbd_trit x : x \in dcbd => -1<=x<=1.
proof. rewrite /support dcbd_point; smt(). qed.
lemma pke_cbd_list_poly xs : xs \in dlist dcbd 768 =>
 input_poly(cbd_word_array xs)=pke_list_poly xs.
proof.
 move=>hs.
 have hn:=supp_dlist_size dcbd 768 xs _ hs; first trivial.
 have ha : all (support dcbd) xs by move:hs; rewrite supp_dlist //=; smt().
 rewrite /pke_list_poly -int_poly_words.
 congr; apply Array768.tP=>i hi.
 rewrite Array768.mapiE // /cbd_word_array Array768.get_of_list //.
 rewrite (nth_map 0) 1:/# Array768.get_of_list //.
 have hx : nth 0 xs i \in dcbd.
 + move:ha; rewrite allP=>ha; apply ha; apply mem_nth; smt().
 have ht:=pke_dcbd_trit _ hx.
 apply coeff_of_word_small; smt().
qed.
lemma pke_field_psi1_iid :
 pke_field_psi1=dmap (dlist dcbd 768) pke_list_poly.
proof.
 rewrite /pke_field_psi1 /pke_psi1 (dmap_comp cbd_word_array input_poly (dlist dcbd 768)).
 apply eq_dmap_in=>xs hs; exact(pke_cbd_list_poly xs hs).
qed.

(* This pair is (f,g0); the implemented public-key numerator is 3*g0. *)
op pke_field_key_pair (p:W16.t Array768.t*W16.t Array768.t) =
 (NTRUPoly.poly1+NTRUPoly.polyC(lift_int 3)*input_poly p.`1,input_poly p.`2).
op pke_accepted_field_pair = dmap pke_accepted_cbd_pair pke_field_key_pair.
lemma pke_actual_keygen_field_pair_law &m workspace
 (event:(NTRUPoly.poly*NTRUPoly.poly)->bool) :
 Pr[KeygenInstrumented(UniformSeedRNG,FreshExpand,SHAKEFROM).run(workspace) @ &m :
 event(input_poly(keygen_f_pre_ntt_spec res.`1.`kg_fbuf),pke_cbd_field res.`1.`kg_gbuf)]=
 mu pke_accepted_field_pair event.
proof.
 rewrite /pke_accepted_field_pair dmapE.
 rewrite -(pke_actual_keygen_cbd_pair_law &m workspace (event \o pke_field_key_pair)).
 rewrite Pr[mu_eq]=> />.
 move=> &hr; by rewrite /(\o) /pke_field_key_pair /= pke_f_field_shape /pke_cbd_field.
qed.
