require import AllCore IntDiv List Distr Ring StdBigop StdOrder.
import RealOrder.
require import Array768.
require import NTRUPlus768INJCollision NTRUPlus768OWUniform.
require import NTRUPlus768SRMultiplication NTRUPlus768SRMultiplicationField.
require import NTRUPlus768IntegerConvolution NTRUPlus768CyclotomicFactorization.
require import NTRUPlus768CoefficientRecovery.

(* Enumerate canonical integer coefficient lists, not units. *)
op sr_residue_lists : int list list = alltuples 768 (range 0 3457).
op sr_list_poly (xs:int list) = int_poly(Array768.of_list 0 xs).
op sr_list_equation (m:sr_matrix) (w:inj_vector) (xs:int list) =
 forall k,0<=k<768=>
 (Bigint.BIA.bigi predT(fun j=>m k j*nth 0 xs j)0 768+w.[k])%%3457=0.
op sr_equation_lists (m:sr_matrix) (w:inj_vector) =
 filter (sr_list_equation m w) sr_residue_lists.
op sr_field_list (h:NTRUPoly.poly) =
 mkseq (fun i=>CycloFq.asint(NTRUPoly."_.[_]" h i)) 768.

lemma sr_residue_lists_size : size sr_residue_lists=3457^768.
proof. by rewrite /sr_residue_lists size_alltuples size_range /=. qed.
lemma sr_residue_lists_uniq : uniq sr_residue_lists.
proof. by rewrite /sr_residue_lists alltuples_uniq range_uniq. qed.
lemma sr_residue_list_size xs : xs \in sr_residue_lists=>size xs=768.
proof. rewrite /sr_residue_lists alltuplesP /=;smt(). qed.
lemma sr_field_list_size h : size(sr_field_list h)=768.
proof. by rewrite /sr_field_list size_mkseq. qed.
lemma sr_field_list_array h : Array768.of_list 0(sr_field_list h)=sr_field_vector h.
proof.
 apply Array768.tP=>i hi.
 by rewrite Array768.get_of_list 1:hi /sr_field_list nth_mkseq 1:hi sr_field_vector_get 1:hi.
qed.
lemma sr_field_list_in h : sr_field_list h \in sr_residue_lists.
proof.
 rewrite /sr_residue_lists alltuplesP /= sr_field_list_size /=.
 split;first smt().
 apply/(all_nthP _ _ 0)=>i;rewrite sr_field_list_size=>hi.
 rewrite /sr_field_list nth_mkseq 1:hi mem_range.
 have hr:=CycloFq.rg_asint(NTRUPoly."_.[_]" h i).
 by move:hr;rewrite /q.
qed.
lemma sr_list_equation_array m w xs :
 sr_list_equation m w xs <=>
 (forall k,0<=k<768=>((sr_matvec m (Array768.of_list 0 xs)).[k]+w.[k])%%3457=0).
proof.
 have he:forall k,0<=k<768=>
 (sr_matvec m (Array768.of_list 0 xs)).[k]=
 Bigint.BIA.bigi predT(fun j=>m k j*nth 0 xs j)0 768.
 + move=>k hk;rewrite sr_matvec_get 1:hk.
   apply Bigint.BIA.eq_big_int=>j hj /=.
   by rewrite Array768.get_of_list 1:hj.
 rewrite /sr_list_equation;split=>hc k hk.
 + by rewrite(he k hk);exact(hc k hk).
 by move:(hc k hk);rewrite(he k hk).
qed.
lemma sr_relation_list_cover h v w : ow_rq_domain h=>inj_relation h v w=>
 h \in map sr_list_poly (sr_equation_lists(sr_mul_matrix v)w).
proof.
 move=>hd hr;apply/mapP;exists(sr_field_list h);split.
 + rewrite /sr_equation_lists mem_filter sr_field_list_in /=.
   rewrite sr_list_equation_array sr_field_list_array.
   have he:=iffLR _ _ (sr_field_relation_matrix_iff h v w hd) hr.
   by move:he;rewrite /q.
 by rewrite /sr_list_poly sr_field_list_array sr_field_vector_poly.
qed.
lemma sr_uniform_fixed_pair_count v w :
 mu ow_uniform_rq (fun h=>inj_relation h v w)<=
 (size(sr_equation_lists(sr_mul_matrix v)w))%r*(1%r/3457%r)^768.
proof.
 have he:mu ow_uniform_rq (fun h=>inj_relation h v w)<=
 mu ow_uniform_rq (mem(map sr_list_poly(sr_equation_lists(sr_mul_matrix v)w))).
 + apply mu_le=>h hs hr;apply(sr_relation_list_cover h v w _ hr).
   by move:hs;rewrite ow_uniform_support.
 apply(ler_trans _ _ _ he).
 have hb:=mu_mem_le_mu1 ow_uniform_rq
   (map sr_list_poly(sr_equation_lists(sr_mul_matrix v)w)) ((1%r/3457%r)^768) _.
 + move=>h;rewrite ow_uniform_point;case(ow_rq_domain h)=>hh;first done.
   apply expr_ge0;smt().
 by move:hb;rewrite size_map.
qed.

lemma sr_residue_list_range xs : xs \in sr_residue_lists=>
 all(fun x=>0<=x<3457)xs.
proof.
 move=>hx.
 have [hs ha]:=iffLR _ _ (alltuplesP 768 xs (range 0 3457)) hx.
 have he:mem(range 0 3457)=(fun x=>0<=x<3457).
 + apply fun_ext=>x;by rewrite mem_range.
 by move:ha;rewrite he.
qed.

(* This lemma transports a cardinal bound; it does not postulate it. *)
lemma sr_uniform_fixed_pair_height v w :
 size(sr_equation_lists(sr_mul_matrix v)w)<=12288^384=>
 mu ow_uniform_rq(fun h=>inj_relation h v w)<=(12288^384)%r/(3457^768)%r.
proof.
 move=>hc;have h0:0%r<=(1%r/3457%r)^768 by apply expr_ge0;smt().
 have he:(1%r/3457%r)^768=1%r/(3457^768)%r.
 + by rewrite RField.exprMn 1:// RField.expr1z RField.exprVn 1:// RField.fromintXn.
 have hb:(size(sr_equation_lists(sr_mul_matrix v)w))%r*(1%r/3457%r)^768<=
 (12288^384)%r*(1%r/3457%r)^768.
 + apply ler_wpmul2r;first exact h0.
   by rewrite le_fromint.
 have hh:=ler_trans _ _ _ (sr_uniform_fixed_pair_count v w) hb.
 by move:hh;rewrite he /=.
qed.
