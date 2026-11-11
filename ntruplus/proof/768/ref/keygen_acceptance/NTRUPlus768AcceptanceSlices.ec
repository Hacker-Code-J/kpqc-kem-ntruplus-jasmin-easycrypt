require import AllCore IntDiv List Ring StdOrder.
from Jasmin require import JUtils.
require import NTRUPlus768AcceptanceRoots.
require import NTRUPlus768BasemulAlgebra NTRUPlus768CyclotomicFactorization NTRUPlus768EvaluationSemantics.
import IntOrder.

op slice_exponents (rho:int) : int list =
 [0;1;2;3;if rho \in [252;974;2483;3205] then 5 else 4].
op slice_bit (bits5 t:int) = (bits5 %/ (2^t)) %%2=1.
op slice_weighted_sum (rho bits5:int) : int =
 (b2i(slice_bit bits5 0) + b2i(slice_bit bits5 1)*rho +
  b2i(slice_bit bits5 2)*rho^2 + b2i(slice_bit bits5 3)*rho^3 +
  b2i(slice_bit bits5 4)*rho^(nth 0 (slice_exponents rho) 4)) %%3457.

lemma size_slice_exponents rho : size(slice_exponents rho)=5.
proof. by rewrite /slice_exponents /=. qed.
lemma uniq_slice_exponents rho : uniq(slice_exponents rho).
proof.
 by rewrite /slice_exponents; case (rho \in [252;974;2483;3205])=> /=.
qed.
lemma slice_exponent_range rho t : 0<=t<5 =>
 0<=nth 0 (slice_exponents rho) t<6.
proof.
 move=> ht; rewrite /slice_exponents.
 case (rho \in [252;974;2483;3205])=> /=; smt().
qed.
lemma slice_weighted_sum_range rho bits5 :
 0<=slice_weighted_sum rho bits5<3457.
proof. rewrite /slice_weighted_sum; smt(modz_cmp). qed.

(* Finite 384 x 32 certificate.  Collision freedom concerns the complete
   modular sum, without any assumptions on independence of its terms. *)
lemma acceptance_slice_certificate :
 all (fun rho=>uniq(map(slice_weighted_sum rho)(iota_ 0 32))) acceptance_roots.
proof.
 rewrite -iotaredE.
 by rewrite /acceptance_roots /slice_weighted_sum /slice_bit /slice_exponents /b2i /=.
qed.
lemma acceptance_slice_injective j u v :
 0<=j<384 => 0<=u<32 => 0<=v<32 =>
 slice_weighted_sum (acceptance_root j) u =
 slice_weighted_sum (acceptance_root j) v => u=v.
proof.
 move=> hj hu hv heq.
 have h:=acceptance_slice_certificate; rewrite allP in h.
 have hroot:acceptance_root j \in acceptance_roots.
 + rewrite /acceptance_root; apply mem_nth; by rewrite acceptance_roots_size.
 have huq:=h (acceptance_root j) hroot.
 apply (map_uniq_inj_in (slice_weighted_sum(acceptance_root j)) (iota_ 0 32) huq u v).
 + by rewrite mem_iota; smt().
 + by rewrite mem_iota; smt().
 + exact heq.
qed.
lemma slice_bits_reconstruction u : 0<=u<32 =>
 b2i(slice_bit u 0)+2*b2i(slice_bit u 1)+4*b2i(slice_bit u 2)+
 8*b2i(slice_bit u 3)+16*b2i(slice_bit u 4)=u.
proof.
 move=> hu.
 have h:all(fun v=>b2i(slice_bit v 0)+2*b2i(slice_bit v 1)+4*b2i(slice_bit v 2)+
  8*b2i(slice_bit v 3)+16*b2i(slice_bit v 4)=v)(iota_ 0 32).
 + by rewrite -iotaredE /slice_bit /b2i /=.
 rewrite allP in h; apply h; by rewrite mem_iota; smt().
qed.

lemma acceptance_slice_field_injective j u v :
 0<=j<384 => 0<=u<32 => 0<=v<32 =>
 lift_int(slice_weighted_sum(acceptance_root j) u)=
 lift_int(slice_weighted_sum(acceptance_root j) v) => u=v.
proof.
 move=> hj hu hv heq.
 apply (acceptance_slice_injective j u v hj hu hv).
 move/(congr1 CycloFq.asint):heq.
 by rewrite /lift_int !CycloFq.incyclocoeffK /q /slice_weighted_sum !modz_mod.
qed.
