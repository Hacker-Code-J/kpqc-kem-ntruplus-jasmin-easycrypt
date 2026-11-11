require import AllCore IntDiv List Ring StdOrder StdBigop.
from Jasmin require import JWord JUtils.
require import Array192.
require import NTRUPlus768AcceptanceAlgebra NTRUPlus768AcceptanceInput NTRUPlus768AcceptanceSlices.
require import NTRUPlus768CyclotomicFactorization NTRUPlus768EvaluationSemantics.
import NTRUPoly.BigPoly.
import CycloFq.
abbrev ( + ) = NTRUPoly.PolyComRing.( + ).
abbrev [ - ] = NTRUPoly.PolyComRing.([-]).
abbrev ( * ) = NTRUPoly.PolyComRing.( * ).
abbrev ( - ) (p q:poly) = p+(-q).

lemma head_big_cons ['a] (f:'a -> poly) x xs :
 PCA.big predT f (x::xs)=f x+PCA.big predT f xs.
proof. exact(PCA.big_consT f x xs). qed.

lemma head_polyC_mul (a b:CycloFq.cyclocoeff) :
 NTRUPoly.polyC(a*b)=NTRUPoly.polyC a*NTRUPoly.polyC b.
proof. exact(NTRUPoly.polyCM a b). qed.
lemma head_polyC_add (a b:CycloFq.cyclocoeff) :
 NTRUPoly.polyC(a+b)=NTRUPoly.polyC a+NTRUPoly.polyC b.
proof. exact(NTRUPoly.polyCD a b). qed.
lemma head_polyC_opp (a:CycloFq.cyclocoeff) :
 NTRUPoly.polyC(-a)= -NTRUPoly.polyC a.
proof. exact(NTRUPoly.polyCN a). qed.

op [opaque] acceptance_weight8 (r:CycloFq.cyclocoeff) (buf:W8.t Array192.t) p =
 lift_int(acceptance_head_bit buf p) +
 lift_int(acceptance_head_bit buf (2+p))*r +
 lift_int(acceptance_head_bit buf (4+p))*CycloFq.exp r 2 +
 lift_int(acceptance_head_bit buf (6+p))*CycloFq.exp r 3 +
 lift_int(acceptance_head_bit buf (8+p))*CycloFq.exp r 4 +
 lift_int(acceptance_head_bit buf (10+p))*CycloFq.exp r 5 +
 lift_int(acceptance_head_bit buf (12+p))*CycloFq.exp r 6 +
 lift_int(acceptance_head_bit buf (14+p))*CycloFq.exp r 7.

op [opaque] acceptance_selected_weight rho (buf:W8.t Array192.t) p =
 lift_int(acceptance_head_bit buf p) +
 lift_int(acceptance_head_bit buf (2+p))*lift_int rho +
 lift_int(acceptance_head_bit buf (4+p))*CycloFq.exp (lift_int rho) 2 +
 lift_int(acceptance_head_bit buf (6+p))*CycloFq.exp (lift_int rho) 3 +
 lift_int(acceptance_head_bit buf (2*nth 0 (slice_exponents rho) 4+p))*
   CycloFq.exp (lift_int rho) (nth 0 (slice_exponents rho) 4).

op acceptance_head_remainder r buf =
 NTRUPoly.polyC(lift_int 3*acceptance_weight8 r buf 0) +
 NTRUPoly.polyC(lift_int 3*acceptance_weight8 r buf 1)*NTRUPoly.X.

lemma quadratic_divides_big ['a] r (f:'a -> poly) xs :
 (forall x, x \in xs => quadratic_divides r (f x)) =>
 quadratic_divides r (PCA.big predT f xs).
proof.
 elim: xs=>[|x xs ih] hall.
 + rewrite PCA.big_nil; exact(quadratic_divides_zero r).
 rewrite PCA.big_consT; apply quadratic_divides_add.
 + apply hall; smt().
 apply ih=>y hy; apply hall; smt().
qed.

lemma quadratic_scaled_monomial r (a:CycloFq.cyclocoeff) k :
 0<=k => quadratic_divides r
 (NTRUPoly.polyC a*NTRUPoly.PolyComRing.exp NTRUPoly.X k-NTRUPoly.polyC(a*CycloFq.exp r (k %/ 2))*NTRUPoly.PolyComRing.exp NTRUPoly.X (k %% 2)).
proof.
 move=>hk.
 have he:k=2*(k %/ 2)+k %% 2 by smt(IntDiv.edivzP).
 have hj:0<=k %/ 2 by smt(IntDiv.divz_ge0).
 have hp:0<=k %% 2 by smt(IntDiv.modz_ge0).
 have h:=quadratic_monomial_reduction r (k %/ 2) (k %% 2) hj hp.
 have hs:=quadratic_divides_scale r a _ h.
 have hsame:
  NTRUPoly.polyC a*(NTRUPoly.PolyComRing.exp NTRUPoly.X (2*(k %/ 2)+k %% 2)-NTRUPoly.polyC(CycloFq.exp r (k %/ 2))*NTRUPoly.PolyComRing.exp NTRUPoly.X (k %% 2))=
  NTRUPoly.polyC a*NTRUPoly.PolyComRing.exp NTRUPoly.X k-NTRUPoly.polyC(a*CycloFq.exp r (k %/ 2))*NTRUPoly.PolyComRing.exp NTRUPoly.X (k %% 2).
 + rewrite -he head_polyC_mul; ring.
 rewrite -hsame; exact hs.
qed.

lemma acceptance_head_remainder_congr r buf :
 quadratic_divides r (acceptance_head_poly buf-acceptance_head_remainder r buf).
proof.
 have hd:=quadratic_divides_big r
  (fun k=>NTRUPoly.polyC(lift_int(3*acceptance_head_bit buf k))*NTRUPoly.PolyComRing.exp NTRUPoly.X k-
   NTRUPoly.polyC(lift_int(3*acceptance_head_bit buf k)*CycloFq.exp r (k %/ 2))*NTRUPoly.PolyComRing.exp NTRUPoly.X (k %% 2))
  (range 0 16) _.
 + move=>k hk; apply quadratic_scaled_monomial; move:hk; rewrite mem_range; smt().
 have he:
  PCA.big predT
   (fun k=>NTRUPoly.polyC(lift_int(3*acceptance_head_bit buf k))*NTRUPoly.PolyComRing.exp NTRUPoly.X k-
    NTRUPoly.polyC(lift_int(3*acceptance_head_bit buf k)*CycloFq.exp r (k %/ 2))*NTRUPoly.PolyComRing.exp NTRUPoly.X (k %% 2))
   (range 0 16)=acceptance_head_poly buf-acceptance_head_remainder r buf.
 + rewrite /acceptance_head_poly /acceptance_head_remainder /acceptance_weight8.
   rewrite /range -iotaredE //= !head_big_cons !PCA.big_nil /=.
   rewrite !CycloFqField.expr0 !CycloFqField.expr1 !CycloFqField.mulr1.
   rewrite /lift_int !CycloFq.incyclocoeffM.
   rewrite !(head_polyC_mul,head_polyC_add).
   ring.
 rewrite -he; exact hd.
qed.

lemma acceptance_head_divisors_weight8 is_f r b c :
 acceptance_same_tail b c =>
 quadratic_divides r (acceptance_input is_f b) =>
 quadratic_divides r (acceptance_input is_f c) =>
 acceptance_weight8 r b 0=acceptance_weight8 r c 0 /\
 acceptance_weight8 r b 1=acceptance_weight8 r c 1.
proof.
 move=>ht hb hc.
 have hd:=quadratic_divides_sub r _ _ hb hc.
 rewrite (acceptance_input_head_difference is_f b c ht) in hd.
 have hrb:=acceptance_head_remainder_congr r b.
 have hrc:=acceptance_head_remainder_congr r c.
 have hrbc:=quadratic_divides_sub r _ _ hrb hrc.
 have hrem:=quadratic_divides_sub r _ _ hd hrbc.
 have he:
  (acceptance_head_poly b-acceptance_head_poly c)-
   ((acceptance_head_poly b-acceptance_head_remainder r b)-
    (acceptance_head_poly c-acceptance_head_remainder r c))=
  NTRUPoly.polyC(lift_int 3*(acceptance_weight8 r b 0-acceptance_weight8 r c 0))+
  NTRUPoly.polyC(lift_int 3*(acceptance_weight8 r b 1-acceptance_weight8 r c 1))*NTRUPoly.X.
 + rewrite /acceptance_head_remainder !head_polyC_mul !head_polyC_add !head_polyC_opp; ring.
 move: hrem; rewrite he=>hrem.
 have [h0 h1]:=quadratic_divides_linear_zero r _ _ hrem.
 rewrite CycloFqField.mulf_eq0 lift_three_nonzero /= CycloFqField.subr_eq0 in h0.
 rewrite CycloFqField.mulf_eq0 lift_three_nonzero /= CycloFqField.subr_eq0 in h1.
 by split.
qed.

lemma acceptance_selected_difference rho b c p :
 0<=p<2 =>
 (forall k,8<=k<16 => k<>2*nth 0 (slice_exponents rho) 4 =>
  k<>2*nth 0 (slice_exponents rho) 4+1 => acceptance_head_bit b k=acceptance_head_bit c k) =>
 acceptance_weight8 (lift_int rho) b p-acceptance_weight8 (lift_int rho) c p=
 acceptance_selected_weight rho b p-acceptance_selected_weight rho c p.
proof.
 move=>hp hu.
 case(rho \in [252;974;2483;3205])=>hr.
 + have hlast:nth 0 (slice_exponents rho) 4=5 by rewrite /slice_exponents /= hr.
   have h8:=hu (8+p) _ _ _; first 3 smt().
   have h12:=hu (12+p) _ _ _; first 3 smt().
   have h14:=hu (14+p) _ _ _; first 3 smt().
   rewrite /acceptance_weight8 /acceptance_selected_weight /= hlast /= h8 h12 h14.
   ring.
 have hlast:nth 0 (slice_exponents rho) 4=4 by rewrite /slice_exponents /= hr.
 have h10:=hu (10+p) _ _ _; first 3 smt().
 have h12:=hu (12+p) _ _ _; first 3 smt().
 have h14:=hu (14+p) _ _ _; first 3 smt().
 rewrite /acceptance_weight8 /acceptance_selected_weight /= hlast /= h10 h12 h14.
 ring.
qed.

lemma acceptance_head_divisors_equal is_f rho b c :
 acceptance_same_tail b c =>
 (forall k,8<=k<16 => k<>2*nth 0 (slice_exponents rho) 4 =>
  k<>2*nth 0 (slice_exponents rho) 4+1 => acceptance_head_bit b k=acceptance_head_bit c k) =>
 quadratic_divides (lift_int rho) (acceptance_input is_f b) =>
 quadratic_divides (lift_int rho) (acceptance_input is_f c) =>
 forall p,0<=p<2 => acceptance_selected_weight rho b p=acceptance_selected_weight rho c p.
proof.
 move=>ht hu hb hc p hp.
 have [h0 h1]:=acceptance_head_divisors_weight8 is_f (lift_int rho) b c ht hb hc.
 have hpcases:p=0 \/ p=1 by smt().
 have hw:acceptance_weight8 (lift_int rho) b p=acceptance_weight8 (lift_int rho) c p.
 + case hpcases=>hv; rewrite hv; assumption.
 have hd:=acceptance_selected_difference rho b c p hp hu.
 clear ht hu hb hc.
 rewrite hw CycloFqField.subrr in hd.
 have hz:acceptance_selected_weight rho b p-acceptance_selected_weight rho c p=CycloFq.zero
  by apply/eq_sym; exact hd.
 have hi:=CycloFqField.subr_eq0 (acceptance_selected_weight rho b p) (acceptance_selected_weight rho c p).
 exact (iffLR _ _ hi hz).
qed.
