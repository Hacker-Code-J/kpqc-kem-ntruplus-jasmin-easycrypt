require import AllCore IntDiv Ring.
from Jasmin require import JWord.
require import Array192.
require import NTRUPlus768BasemulAlgebra NTRUPlus768NTTSchedule.
require import NTRUPlus768CyclotomicFactorization NTRUPlus768EvaluationSemantics.
require import NTRUPlus768ForwardNTTStage1Semantics NTRUPlus768KeygenSamplerAlgebra.
require import NTRUPlus768KeygenCompleteSpec.
require import NTRUPlus768AcceptanceRoots NTRUPlus768AcceptanceAlgebra.
import CycloFq.

lemma acceptance_root_field_square k : 0<=k<192 =>
 terminal_root_field k=lift_int(acceptance_root(2*k))*lift_int(acceptance_root(2*k)).
proof.
 move=> hk.
 have hs:=acceptance_root_square k false hk.
 rewrite /= in hs.
 rewrite /terminal_root_field /lift_int -CycloFq.incyclocoeffM.
 apply/CycloFq.eq_incyclocoeff.
 rewrite -Ring.IntID.expr2.
 change (terminal_value k %%3457=acceptance_root(2*k)^2 %%3457).
 rewrite hs /terminal_value /q modz_mod; done.
qed.
lemma acceptance_root_field_neg k : 0<=k<192 =>
 lift_int(acceptance_root(2*k+1))= -lift_int(acceptance_root(2*k)).
proof.
 move=> hk; rewrite (acceptance_root_neg k hk) /lift_int.
 change (CycloFq.incyclocoeff((-acceptance_root(2*k))%%q)= -CycloFq.incyclocoeff(acceptance_root(2*k))).
 by rewrite -CycloFq.incyclocoeff_mod CycloFq.incyclocoeffN.
qed.
lemma acceptance_root_field_nonsquare j : 0<=j<384 =>
 field_nonsquare(lift_int(acceptance_root j)).
proof. move=> hj; apply field_euler_nonsquare; exact(acceptance_root_euler j hj). qed.

lemma keygen_f_rejected_quadratic (buf:W8.t Array192.t) :
 !keygen_f_accept buf =>
 exists j,0<=j<384 /\
 quadratic_divides(lift_int(acceptance_root j))(input_poly(keygen_f_pre_ntt_spec buf)).
proof.
 apply(keygen_f_rejected_cover (fun (j:int)=>lift_int(acceptance_root j)) buf).
 + exact acceptance_root_field_square.
 + exact acceptance_root_field_neg.
 exact acceptance_root_field_nonsquare.
qed.
lemma keygen_g_rejected_quadratic (buf:W8.t Array192.t) :
 !keygen_g_accept buf =>
 exists j,0<=j<384 /\
 quadratic_divides(lift_int(acceptance_root j))(input_poly(keygen_g_pre_ntt_spec buf)).
proof.
 apply(keygen_g_rejected_cover (fun (j:int)=>lift_int(acceptance_root j)) buf).
 + exact acceptance_root_field_square.
 + exact acceptance_root_field_neg.
 exact acceptance_root_field_nonsquare.
qed.
