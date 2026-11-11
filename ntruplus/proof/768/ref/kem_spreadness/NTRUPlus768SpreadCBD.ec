require import AllCore List Distr DList StdOrder StdBigop.
from Jasmin require import JWord.
require import Array192 Array768.
require import NTRUPlus768CBDDistribution NTRUPlus768ROMDistributions.
require import NTRUPlus768PKEModel NTRUPlus768PKEKeyDistribution NTRUPlus768ACWC2Domains.
require import NTRUPlus768BasemulAlgebra NTRUPlus768Crepmod3Algebra NTRUPlus768PolyCBD1Algebra.
require import NTRUPlus768RRecCodec NTRUPlus768RRecWordChecks.
require import NTRUPlus768CyclotomicFactorization NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768TerminalRepresentation NTRUPlus768CoefficientRecovery NTRUPlus768IntegerConvolution.
import RealOrder RField Bigreal.

(* This is the actual UNCONDITIONED CBD1 law. Neither accepted key
   coefficients nor ciphertexts are assumed to have independent entries. *)
op spread_cbd_zero : pke_poly = Array768.init(fun _=>W16.zero).

lemma spread_dcbd_point_bound x : mu1 dcbd x<=1%r/2%r.
proof. rewrite dcbd_point; smt(). qed.

lemma spread_cbd_half_power : (1%r/2%r)^768=1%r/(2%r^768).
proof. by rewrite exprMn 1:// exprVn 1:// expr1z. qed.

lemma spread_cbd_bound_positive : 0%r<1%r/(2%r^768).
proof. apply divr_gt0; first done. apply expr_gt0; done. qed.

lemma spread_cbd_point_bound r : mu1 pke_psi1 r<=1%r/(2%r^768).
proof.
 rewrite acwc2_psi1_point dlist1E // acwc2_coeff_list_size /=.
 have hb:BRM.big predT (mu1 dcbd) (acwc2_coeff_list r)<=
   BRM.big predT (fun (_:int)=>1%r/2%r) (acwc2_coeff_list r).
 + apply Bigreal.ler_prod=>x _; split.
   - exact(ge0_mu1 dcbd x).
   move=>_; exact(spread_dcbd_point_bound x).
 by move:hb; rewrite Bigreal.mulr_const acwc2_coeff_list_size spread_cbd_half_power.
qed.

lemma spread_cbd_zero_coeff i : 0<=i<768 =>coeff spread_cbd_zero.[i]=0.
proof.
 move=>hi; rewrite /spread_cbd_zero Array768.initiE //.
 change (coeff(W16.of_int 0)=0).
 apply coeff_of_word_small; done.
qed.

lemma spread_cbd_zero_domain : pke_domain spread_cbd_zero.
proof.
 rewrite /pke_domain /poly_cbd1_trit_output=>i hi.
 by rewrite spread_cbd_zero_coeff // /is_trit.
qed.

lemma spread_cbd_zero_coeff_list : acwc2_coeff_list spread_cbd_zero=nseq 768 0.
proof.
 apply(eq_from_nth 0).
 + by rewrite acwc2_coeff_list_size size_nseq.
 move=>i hi; rewrite acwc2_coeff_list_size in hi.
 by rewrite acwc2_coeff_list_nth // spread_cbd_zero_coeff // nth_nseq.
qed.

lemma spread_cbd_zero_point : mu1 pke_psi1 spread_cbd_zero=1%r/(2%r^768).
proof.
 rewrite acwc2_psi1_point spread_cbd_zero_coeff_list dlist1E // size_nseq /max /=.
 rewrite (BRM.eq_big_seq _ (fun (_:int)=>1%r/2%r)).
 + move=>x hx; have ->:x=0 by move:hx; rewrite mem_nseq; smt().
   by rewrite /= dcbd_point.
 by rewrite Bigreal.mulr_const size_nseq /max /= spread_cbd_half_power.
qed.

lemma spread_cbd_buffer_point r :
 mu uniform192(fun buf=>poly_cbd1_spec buf=r)=mu1 pke_psi1 r.
proof. by rewrite -pke_cbd1_uniform dmap1E /(\o) /pred1. qed.
lemma spread_cbd_buffer_point_bound r :
 mu uniform192(fun buf=>poly_cbd1_spec buf=r)<=1%r/(2%r^768).
proof. rewrite spread_cbd_buffer_point; exact(spread_cbd_point_bound r). qed.
lemma spread_cbd_buffer_zero_point :
 mu uniform192(fun buf=>poly_cbd1_spec buf=spread_cbd_zero)=1%r/(2%r^768).
proof. by rewrite spread_cbd_buffer_point spread_cbd_zero_point. qed.

(* Field-polynomial representation is injective on the actual trit support.
   This prevents pushforward from combining different array point masses. *)
lemma spread_cbd_input_poly_injective a b :
 pke_domain a=>pke_domain b=>input_poly a=input_poly b=>a=b.
proof.
 move=>ha hb he.
 have hna:=rrec_normalize_recovers_small a a ha (eqm_global_refl(input_poly a)).
 have hc:eqm_global(input_poly b)(input_poly a) by rewrite -he; exact(eqm_global_refl _).
 have hnb:=rrec_normalize_recovers_small a b hb hc.
 by rewrite -hna -hnb.
qed.

lemma spread_cbd_field_point_at r : pke_domain r =>
 mu1 pke_field_psi1(input_poly r)=mu1 pke_psi1 r.
proof.
 move=>hr; rewrite /pke_field_psi1 dmap1E.
 apply mu_eq_support=>s hs; rewrite /(\o) /pred1.
 have hsd:pke_domain s by move:hs; rewrite acwc2_psi1_support.
 apply eq_iff; split=>he.
 + exact(spread_cbd_input_poly_injective s r hsd hr he).
 by rewrite he.
qed.

lemma spread_cbd_field_point_bound p : mu1 pke_field_psi1 p<=1%r/(2%r^768).
proof.
 case(p \in pke_field_psi1)=>hp.
 + have hx:=hp; rewrite /pke_field_psi1 supp_dmap in hx.
   move:hx=>[r [hr he]]; rewrite he.
   have hd:pke_domain r by move:hr; rewrite acwc2_psi1_support.
   rewrite(spread_cbd_field_point_at r hd); exact(spread_cbd_point_bound r).
 have hz:mu1 pke_field_psi1 p=0%r by move:hp; rewrite supportPn.
 rewrite hz; exact(ltrW _ _ spread_cbd_bound_positive).
qed.

lemma spread_cbd_zero_field : input_poly spread_cbd_zero=NTRUPoly.poly0.
proof.
 rewrite -int_poly_words.
 have he:Array768.map coeff spread_cbd_zero=integer_zero.
 + apply Array768.tP=>i hi.
   by rewrite Array768.mapiE // spread_cbd_zero_coeff // integer_zero_get.
 by rewrite he int_poly_zero.
qed.

lemma spread_cbd_field_zero_point : mu1 pke_field_psi1 NTRUPoly.poly0=1%r/(2%r^768).
proof.
 rewrite -spread_cbd_zero_field (spread_cbd_field_point_at spread_cbd_zero spread_cbd_zero_domain).
 exact spread_cbd_zero_point.
qed.

lemma spread_cbd_field_buffer_point_bound p :
 mu uniform192(fun buf=>pke_cbd_field buf=p)<=1%r/(2%r^768).
proof.
 have h:=spread_cbd_field_point_bound p.
 by move:h; rewrite -pke_field_psi1_uniform dmap1E /(\o) /pred1.
qed.
