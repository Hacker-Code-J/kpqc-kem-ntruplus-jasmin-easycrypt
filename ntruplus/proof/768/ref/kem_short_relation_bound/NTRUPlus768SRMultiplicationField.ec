require import AllCore IntDiv Ring.
require import Array768.
require import NTRUPlus768INJCollision NTRUPlus768SRMultiplication NTRUPlus768SRMultiplicationProof.
require import NTRUPlus768OWUniform.
require import NTRUPlus768IntegerConvolution NTRUPlus768CoefficientRecovery.
require import NTRUPlus768CyclotomicFactorization NTRUPlus768EvaluationSemantics.
require import NTRUPlus768TerminalRepresentation NTRUPlus768BasemulAlgebra.
abbrev ( + ) = NTRUPoly.PolyComRing.( + ).
abbrev ( * ) = NTRUPoly.PolyComRing.( * ).

(* Canonical field coefficients of the ordinary polynomial challenge.
   This interface neither conditions on units nor uses byte encodings. *)
op sr_field_vector(h:NTRUPoly.poly):inj_vector =
 Array768.init(fun i=>CycloFq.asint(NTRUPoly."_.[_]" h i)).

lemma sr_field_vector_get h i : 0<=i<768=>
 (sr_field_vector h).[i]=CycloFq.asint(NTRUPoly."_.[_]" h i).
proof. by move=>hi;rewrite /sr_field_vector Array768.initiE. qed.

lemma sr_field_vector_range h i : 0<=i<768=>0<=(sr_field_vector h).[i]<q.
proof. move=>hi;rewrite(sr_field_vector_get h i hi);exact(CycloFq.rg_asint _). qed.

lemma sr_field_vector_poly h : ow_rq_domain h=>int_poly(sr_field_vector h)=h.
proof.
 rewrite /ow_rq_domain=>hh;apply/NTRUPoly.poly_eqP=>i hi.
 case(i<768)=>hn.
 + rewrite int_poly_coeff 1:/# (sr_field_vector_get h i _) 1:/# /lift_int.
   exact(CycloFq.asintK _).
 rewrite int_poly_coeff_out 1:/# (NTRUPoly.gedeg_coeff h i _) 1:/#;done.
qed.

lemma sr_int_poly_zero_mod u :
 (forall i,0<=i<768=>u.[i]%%q=0)=>int_poly u=NTRUPoly.poly0.
proof.
 move=>hu;apply/NTRUPoly.poly_eqP=>i hi.
 rewrite NTRUPoly.poly0E;case(i<768)=>hn.
 + rewrite int_poly_coeff 1:/# /lift_int CycloFq.incyclocoeff_mod.
   rewrite(hu i _) 1:/#;done.
 rewrite int_poly_coeff_out 1:/#;done.
qed.

lemma sr_coefficients_relation a v w :
 (forall k,0<=k<768=>((sr_matvec(sr_mul_matrix v)a).[k]+w.[k])%%q=0)=>
 inj_relation(int_poly a)v w.
proof.
 move=>hc;have hz:int_poly(integer_add(sr_matvec(sr_mul_matrix v)a)w)=NTRUPoly.poly0.
 + apply sr_int_poly_zero_mod=>k hk;rewrite integer_add_get 1:hk;exact(hc k hk).
 have hm:=sr_mul_matrix_eqm a v.
 have ht:=eqm_global_add _ _ (int_poly w)(int_poly w) hm (eqm_global_refl _).
 rewrite -int_poly_add hz in ht;exact ht.
qed.

lemma sr_relation_matrix_iff a v w :
 inj_relation(int_poly a)v w <=>
 (forall k,0<=k<768=>((sr_matvec(sr_mul_matrix v)a).[k]+w.[k])%%q=0).
proof. split;[exact(sr_relation_coefficients a v w)|exact(sr_coefficients_relation a v w)]. qed.

lemma sr_field_relation_matrix_iff h v w : ow_rq_domain h=>
 (inj_relation h v w <=>
  (forall k,0<=k<768=>((sr_matvec(sr_mul_matrix v)(sr_field_vector h)).[k]+w.[k])%%q=0)).
proof.
 move=>hh;have he:=sr_relation_matrix_iff (sr_field_vector h)v w.
 by move:he;rewrite(sr_field_vector_poly h hh).
qed.
