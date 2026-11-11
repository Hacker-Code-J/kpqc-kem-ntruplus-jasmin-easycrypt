require import AllCore IntDiv List Ring StdBigop StdOrder.
require import Array768.
require import NTRUPlus768INJCollision NTRUPlus768SRMultiplication.
require import NTRUPlus768IntegerConvolution NTRUPlus768CoefficientRecovery.
require import NTRUPlus768CyclotomicFactorization NTRUPlus768EvaluationSemantics.
require import NTRUPlus768TerminalRepresentation NTRUPlus768BasemulAlgebra.
abbrev ( + ) = NTRUPoly.PolyComRing.( + ).
abbrev ( * ) = NTRUPoly.PolyComRing.( * ).

lemma sr_mul_matrix_eqm a v :
 eqm_global(int_poly a*int_poly v)(int_poly(sr_matvec(sr_mul_matrix v)a)).
proof. rewrite sr_mul_matrix_product;exact(integer_product_eqm_global a v). qed.

lemma sr_zero_poly : int_poly inj_zero=NTRUPoly.PolyComRing.zeror.
proof. rewrite /inj_zero -/integer_zero;exact int_poly_zero. qed.

lemma sr_relation_zero_left h w : inj_short w=>inj_relation h inj_zero w=>w=inj_zero.
proof.
 move=>hw;rewrite /inj_relation=>hr.
 have hz:=sr_zero_poly.
 have hm:=NTRUPoly.PolyComRing.mulr0 h.
 have ha:=NTRUPoly.PolyComRing.add0r(int_poly w).
 have he:eqm_global(int_poly w)(int_poly inj_zero).
 + smt().
 apply Array768.tP=>i hi.
 have hc:=eqm_global_int_poly_coeff w inj_zero i he hi.
 have hb:=hw i hi.
 move:hc;rewrite(inj_zero_get i hi) /q /= =>hc.
 have hd:=divz_eq w.[i] 3457;smt().
qed.

lemma sr_success_nonzero_left h v w : inj_short_win h(v,w)=>v<>inj_zero.
proof.
 rewrite /inj_short_win /inj_pair_nonzero /=.
 move=>[hv [hw [hn hr]]].
 case(v=inj_zero)=>he;last done.
 have hz:=sr_relation_zero_left h w hw _;first by rewrite -he.
 smt().
qed.

lemma sr_relation_coefficients a v w : inj_relation(int_poly a)v w=>
 forall k,0<=k<768=>((sr_matvec(sr_mul_matrix v)a).[k]+w.[k])%%q=0.
proof.
 rewrite /inj_relation=>hr k hk.
 have hm:=sr_mul_matrix_eqm a v.
 have ht:=eqm_global_add _ _ (int_poly w)(int_poly w) hm (eqm_global_refl _).
 have hh:=eqm_global_trans _ _ _ (eqm_global_sym _ _ ht) hr.
 rewrite -int_poly_add in hh.
 have he:eqm_global(int_poly(integer_add(sr_matvec(sr_mul_matrix v)a)w))(int_poly inj_zero).
 + by rewrite sr_zero_poly.
 have hc:=eqm_global_int_poly_coeff (integer_add(sr_matvec(sr_mul_matrix v)a)w) inj_zero k he hk.
 by move:hc;rewrite integer_add_get 1:hk (inj_zero_get k hk) /q /=.
qed.
