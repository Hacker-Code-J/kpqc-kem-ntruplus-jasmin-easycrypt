require import AllCore IntDiv List Finite Ring StdOrder.
from Jasmin require import JWord JUtils.
require import Array768.
require import NTRUPlus768BasemulAlgebra NTRUPlus768Crepmod3Algebra.
require import NTRUPlus768NTTStage1Algebra NTRUPlus768InvNTTRadix2_4Algebra.
require import NTRUPlus768KeygenPublicKeyBridge NTRUPlus768EvaluationSemantics.
require import NTRUPlus768TerminalRepresentation NTRUPlus768CoefficientRecovery.
require import NTRUPlus768ForwardNTTStage1Semantics NTRUPlus768CyclotomicFactorization.
require import NTRUPlus768ValidKeyM1Recovery.
import Ring.IntID IntOrder.

(* Canonical representatives are nonnegative residues in 0,...,3456.
   The finite-domain proof remains symbolic; no q^768 list is expanded. *)
op [opaque] rrec_canonical (a:W16.t Array768.t) : W16.t Array768.t =
 Array768.init(fun i=>W16.of_int(coeff a.[i] %% q)).
op rrec_canonical_domain (a:W16.t Array768.t) =
 forall i,0<=i<768=>0<=coeff a.[i]<q.

lemma rrec_canonical_residue_range x : 0<=x %% q<q.
proof. rewrite /q; smt(IntDiv.modz_ge0 IntDiv.ltz_pmod). qed.
lemma rrec_canonical_residue_word x : coeff(W16.of_int(x %% q))=x %% q.
proof.
 apply coeff_of_word_small.
 have hr:=rrec_canonical_residue_range x.
 move:hr; rewrite /q /=; smt().
qed.
lemma rrec_canonical_coeff a i : 0<=i<768 =>
 coeff(rrec_canonical a).[i]=coeff a.[i] %% q.
proof.
 move=>hi; rewrite /rrec_canonical Array768.initiE //.
 exact(rrec_canonical_residue_word _).
qed.
lemma rrec_canonical_range a : rrec_canonical_domain(rrec_canonical a).
proof.
 move=>i hi; rewrite rrec_canonical_coeff //; exact(rrec_canonical_residue_range _).
qed.
lemma rrec_canonical_fixed a : rrec_canonical_domain a => rrec_canonical a=a.
proof.
 move=>ha; apply Array768.tP=>i hi.
 rewrite /rrec_canonical Array768.initiE 1:hi /= (modz_small _ q (ha i hi)).
 by rewrite -(NTRUPlus768Crepmod3Algebra.word_from_coeff a.[i]).
qed.
lemma rrec_canonical_idempotent a : rrec_canonical(rrec_canonical a)=rrec_canonical a.
proof. exact(rrec_canonical_fixed _ (rrec_canonical_range a)). qed.
lemma rrec_canonical_mod a : poly_coeff_eq_mod_q (rrec_canonical a) a.
proof. move=>i hi; by rewrite rrec_canonical_coeff // modz_mod. qed.
lemma rrec_canonical_congruent a b : poly_coeff_eq_mod_q a b => rrec_canonical a=rrec_canonical b.
proof.
 move=>he; apply Array768.tP=>i hi.
 by rewrite /rrec_canonical !Array768.initiE 1,2:hi /= (he i hi).
qed.
lemma rrec_canonical_eq_iff a b :
 rrec_canonical a=rrec_canonical b <=> poly_coeff_eq_mod_q a b.
proof.
 split=>he; last exact(rrec_canonical_congruent a b he).
 move=>i hi; rewrite -(rrec_canonical_coeff a i hi) -(rrec_canonical_coeff b i hi) he.
 done.
qed.
lemma rrec_canonical_domain_qrange a : rrec_canonical_domain a => qrange_input_shape a.
proof.
 move=>ha i hi; have h:=ha i hi; move:h; rewrite /q; smt().
qed.
lemma rrec_canonical_domain_input_qrange a : rrec_canonical_domain a => input_qrange a.
proof.
 move=>ha; rewrite /input_qrange /in_qrange.
 exact(rrec_canonical_domain_qrange a ha).
qed.

lemma rrec_input_poly_mod_congr a b :
 poly_coeff_eq_mod_q a b => input_poly a=input_poly b.
proof.
 move=>he; rewrite -!integer_coefficients_poly /int_poly.
 apply NTRUPoly.BigPoly.PCA.eq_big_int=>i hi /=.
 rewrite !integer_coefficients_get 1,2:hi.
 have hl:lift_int(coeff a.[i])=lift_int(coeff b.[i]).
 + apply CycloFq.asint_inj; rewrite /lift_int !CycloFq.incyclocoeffK.
   exact(he i hi).
 by rewrite hl.
qed.
lemma rrec_canonical_input_poly a : input_poly(rrec_canonical a)=input_poly a.
proof. exact(rrec_input_poly_mod_congr _ _ (rrec_canonical_mod a)). qed.
lemma rrec_eqm_canonical a b :
 eqm_global (input_poly a) (input_poly b) => rrec_canonical a=rrec_canonical b.
proof.
 move=>he; apply rrec_canonical_congruent=>i hi.
 have hg:eqm_global (int_poly(integer_coefficients a)) (int_poly(integer_coefficients b))
   by rewrite !integer_coefficients_poly.
 have hc:=eqm_global_int_poly_coeff (integer_coefficients a) (integer_coefficients b) i hg hi.
 by move:hc; rewrite !integer_coefficients_get.
qed.
lemma rrec_canonical_domain_unique a b :
 rrec_canonical_domain a => rrec_canonical_domain b =>
 eqm_global (input_poly a) (input_poly b) => a=b.
proof.
 move=>ha hb he; rewrite -(rrec_canonical_fixed a ha) -(rrec_canonical_fixed b hb).
 exact(rrec_eqm_canonical a b he).
qed.

lemma rrec_word_type_finite : is_finite(predT<:W16.t>).
proof.
 apply/finiteP; exists W16.all_words=>w hw; exact(W16.all_wordsP w).
qed.
lemma rrec_all_word_arrays_finite : is_finite(predT<:W16.t Array768.t>).
proof.
 apply(is_finite_surj (Array768.of_list W16.zero)
   (fun xs:W16.t list=>size xs=768 /\ all predT xs) predT).
 + move=>a ha; exists(Array768.to_list a); split.
   - by rewrite /= Array768.size_to_list all_predT.
   by rewrite Array768.to_listK.
 have h:=finite_list 768 (predT<:W16.t>) rrec_word_type_finite.
 by move:h; rewrite /max /=.
qed.
lemma rrec_canonical_domain_finite : is_finite rrec_canonical_domain.
proof.
 apply(finite_leq (predT<:W16.t Array768.t>) rrec_canonical_domain); first by done.
 exact rrec_all_word_arrays_finite.
qed.
