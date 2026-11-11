require import AllCore Distr DList List Ring Finite.
require import NTRUPlus768CyclotomicFactorization NTRUPlus768EvaluationSemantics.
require import NTRUPlus768CoefficientRecovery NTRUPlus768BasemulAlgebra NTRUPlus768TerminalRepresentation.

(* EasyCrypt's deg is coefficient-list length: deg<=768 means ordinary
   degree<768. The support includes zero and every nonunit; no condition
   on invertibility is applied to this uniform ring experiment. *)
op ow_rq_domain(p:NTRUPoly.poly) = NTRUPoly.deg p<=768.
op ow_coefficients(p:NTRUPoly.poly) : CycloFq.cyclocoeff list =
 mkseq (fun i=>NTRUPoly."_.[_]" p i) 768.
op ow_uniform_rq : NTRUPoly.poly distr =
 dmap (dlist CycloFq.DZmodP.dunifin 768) NTRUPoly.polyL.
op ow_scale3(p:NTRUPoly.poly) : NTRUPoly.poly =
 NTRUPoly.PolyComRing.( * ) (NTRUPoly.polyC(lift_int 3)) p.
op ow_unscale3(p:NTRUPoly.poly) : NTRUPoly.poly =
 NTRUPoly.PolyComRing.( * ) (NTRUPoly.polyC(CycloFq.inv(lift_int 3))) p.

lemma ow_coefficients_size p : size(ow_coefficients p)=768.
proof. by rewrite /ow_coefficients size_mkseq. qed.
lemma ow_coefficients_get p i : 0<=i<768=>
 nth CycloFq.zero (ow_coefficients p) i=NTRUPoly."_.[_]" p i.
proof. move=>hi;by rewrite /ow_coefficients nth_mkseq. qed.
lemma ow_coefficients_polyL xs : size xs=768=>ow_coefficients(NTRUPoly.polyL xs)=xs.
proof.
 move=>hs;apply(eq_from_nth CycloFq.zero);first by rewrite ow_coefficients_size hs.
 move=>i hi;rewrite ow_coefficients_size in hi.
 by rewrite(ow_coefficients_get _ i hi) NTRUPoly.polyLE.
qed.
lemma ow_polyL_coefficients p : NTRUPoly.deg p<=768=>NTRUPoly.polyL(ow_coefficients p)=p.
proof.
 move=>hp;have [xs [hs he]]:=NTRUPoly.surj_polyL p 768 hp.
 by rewrite he(ow_coefficients_polyL xs hs).
qed.
lemma ow_coefficients_unique p r : ow_rq_domain p=>ow_rq_domain r=>
 eqm_global p r=>p=r.
proof. rewrite /ow_rq_domain;exact(eqm_global_low_degree_unique p r). qed.
lemma ow_uniform_coeff_point x : mu1 CycloFq.DZmodP.dunifin x=1%r/3457%r.
proof. by rewrite CycloFq.DZmodP.dunifin1E CycloFq.DZmodP.cardE /q. qed.
lemma ow_uniform_list_support xs :
 xs \in dlist CycloFq.DZmodP.dunifin 768 <=> size xs=768.
proof.
 rewrite supp_dlist //;split;first by smt().
 move=>hs;split;first exact hs.
 apply allP=>x hx;exact(CycloFq.DZmodP.supp_dunifin x).
qed.
lemma ow_uniform_support p : p \in ow_uniform_rq <=> ow_rq_domain p.
proof.
 rewrite /ow_uniform_rq supp_dmap /ow_rq_domain;split.
 + move=>[xs [hx ->]];have hs:=iffLR _ _ (ow_uniform_list_support xs) hx.
   have hd:=NTRUPoly.degL_le xs;smt().
 move=>hp;exists(ow_coefficients p);split.
 + by rewrite ow_uniform_list_support ow_coefficients_size.
 by rewrite(ow_polyL_coefficients p hp).
qed.
lemma ow_uniform_lossless : is_lossless ow_uniform_rq.
proof. apply/dmap_ll/dlist_ll;exact CycloFq.DZmodP.dunifin_ll. qed.
lemma ow_uniform_zero_support : NTRUPoly.poly0 \in ow_uniform_rq.
proof. by rewrite ow_uniform_support /ow_rq_domain NTRUPoly.deg0. qed.

lemma ow_uniform_list_point(xs:CycloFq.cyclocoeff list) :
 mu1(dlist CycloFq.DZmodP.dunifin(size xs)) xs=(1%r/3457%r)^(size xs).
proof.
 elim xs=>[|x xs ih];first by rewrite dlist01E // RField.expr0.
 rewrite dlistS1E ow_uniform_coeff_point ih /=;smt(RField.exprS size_ge0).
qed.
lemma ow_uniform_point_in p : ow_rq_domain p=>mu1 ow_uniform_rq p=(1%r/3457%r)^768.
proof.
 move=>hp;rewrite /ow_uniform_rq (in_dmap1E_can _ _ ow_coefficients p).
 + exact(ow_polyL_coefficients p hp).
 + move=>xs hx he;have hs:=iffLR _ _ (ow_uniform_list_support xs) hx.
   by rewrite -he(ow_coefficients_polyL xs hs).
 rewrite -{1}(ow_coefficients_size p) ow_uniform_list_point ow_coefficients_size;done.
qed.
lemma ow_uniform_point p :
 mu1 ow_uniform_rq p=if ow_rq_domain p then (1%r/3457%r)^768 else 0%r.
proof.
 case(ow_rq_domain p)=>hp;first exact(ow_uniform_point_in p hp).
 apply supportPn;by rewrite ow_uniform_support.
qed.
lemma ow_uniform_is_uniform : is_uniform ow_uniform_rq.
proof.
 move=>p r hp hr;rewrite !ow_uniform_point.
 by rewrite -(ow_uniform_support p) hp -(ow_uniform_support r) hr.
qed.
lemma ow_rq_domain_finite : is_finite ow_rq_domain.
proof.
 have he:ow_rq_domain=support ow_uniform_rq.
 + apply fun_ext=>p;by rewrite ow_uniform_support.
 rewrite he;exact(uniform_finite ow_uniform_rq ow_uniform_is_uniform).
qed.
