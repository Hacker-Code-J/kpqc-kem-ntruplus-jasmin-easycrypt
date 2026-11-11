require import AllCore IntDiv Ring StdOrder List.
from Jasmin require import JWord.
require import Array4 Array192 Array768.
require import NTRUPlus768BasemulAlgebra NTRUPlus768BaseInvAlgebra.
require import NTRUPlus768BaseInvProof NTRUPlus768PolyBaseInvProof.
require import NTRUPlus768PolyBasemulAlgebra NTRUPlus768PolyBasemulProof NTRUPlus768NTTSchedule.
require import NTRUPlus768CyclotomicFactorization NTRUPlus768EvaluationSemantics.
require import NTRUPlus768TerminalRepresentation NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768ForwardNTTSemantics NTRUPlus768KeygenCompleteSpec.
require import NTRUPlus768KeygenSamplerAlgebra NTRUPlus768KeygenSamplerBridge.
require import NTRUPlus768KeygenInverseBridge.
import CycloFq.

(* Exact baseinv failure is lifted through terminal_represents to a quadratic
   factor of the coefficient-domain input.  The small-remainder lemmas below
   support the later CBD head-bit perturbation argument. *)

op field_nonsquare (r:CycloFq.cyclocoeff) : bool =
 forall (x:CycloFq.cyclocoeff), x*x<>r.
op quadratic_modulus (r:CycloFq.cyclocoeff) : NTRUPoly.poly = NTRUPoly.PolyComRing.exp NTRUPoly.X 2-NTRUPoly.polyC r.
op quadratic_divides (r:CycloFq.cyclocoeff) (p:NTRUPoly.poly) : bool =
 exists h, p=h*quadratic_modulus r.

lemma quadratic_divides_zero r : quadratic_divides r NTRUPoly.PolyComRing.zeror.
proof. rewrite /quadratic_divides; exists NTRUPoly.PolyComRing.zeror; ring. qed.
lemma quadratic_divides_add r p q :
 quadratic_divides r p => quadratic_divides r q => quadratic_divides r (p+q).
proof.
 rewrite /quadratic_divides; move=> [h ->] [j ->].
 exists (h+j); ring.
qed.
lemma quadratic_divides_sub r p q :
 quadratic_divides r p => quadratic_divides r q => quadratic_divides r (p-q).
proof.
 rewrite /quadratic_divides; move=> [h ->] [j ->].
 exists (h-j); ring.
qed.
lemma quadratic_divides_mul r p q :
 quadratic_divides r p => quadratic_divides r (p*q).
proof. rewrite /quadratic_divides; move=> [h ->]; exists(h*q); ring. qed.

lemma quadratic_modulus_degree r : NTRUPoly.deg (quadratic_modulus r)=3.
proof.
 have he : quadratic_modulus r=NTRUPoly.PolyComRing.exp NTRUPoly.X 2+NTRUPoly.polyC(-r).
 + by rewrite /quadratic_modulus NTRUPoly.polyCN.
 rewrite he.
 by rewrite NTRUPoly.deg_polyXnDC.
qed.
lemma quadratic_modulus_leading r : NTRUPoly.lc (quadratic_modulus r)=CycloFq.one.
proof.
 have he : quadratic_modulus r=NTRUPoly.PolyComRing.exp NTRUPoly.X 2+NTRUPoly.polyC(-r).
 + by rewrite /quadratic_modulus NTRUPoly.polyCN.
 rewrite he.
 by rewrite NTRUPoly.lc_polyXnDC.
qed.
lemma quadratic_divides_small_zero r p :
 NTRUPoly.deg p<=2 => quadratic_divides r p => p=NTRUPoly.PolyComRing.zeror.
proof.
 move=> hd; rewrite /quadratic_divides; move=> [h hp].
 case(h=NTRUPoly.PolyComRing.zeror) => hh; first by rewrite hp hh; ring.
 have hl : (NTRUPoly.lc h)*(NTRUPoly.lc (quadratic_modulus r))<>CycloFq.zero.
 + by rewrite quadratic_modulus_leading CycloFqField.mulr1 NTRUPoly.lc_eq0.
 have hm := NTRUPoly.degM_proper h (quadratic_modulus r) hl.
 have hg := NTRUPoly.deg_ge1 h.
 rewrite quadratic_modulus_degree in hm.
 smt().
qed.
lemma quadratic_divides_linear_zero r (a b:CycloFq.cyclocoeff) :
 quadratic_divides r (NTRUPoly.polyC a+NTRUPoly.polyC b*NTRUPoly.X) => a=CycloFq.zero /\ b=CycloFq.zero.
proof.
 move=> hd.
 have hdeg : NTRUPoly.deg (NTRUPoly.polyC a+NTRUPoly.polyC b*NTRUPoly.X)<=2.
 + apply NTRUPoly.deg_leP; first done.
   move=> i hi; rewrite NTRUPoly.polyDE NTRUPoly.polyMXE !NTRUPoly.polyCE /=.
   have -> : i<>0 by smt().
   have -> : i-1<>0 by smt().
   by rewrite CycloFqField.add0r.
 have hz := quadratic_divides_small_zero r (NTRUPoly.polyC a+NTRUPoly.polyC b*NTRUPoly.X) hdeg hd.
 rewrite NTRUPoly.poly_eqP in hz.
 have h0:=hz 0 _; first done.
 have h1:=hz 1 _; first done.
 rewrite NTRUPoly.polyDE NTRUPoly.polyMXE !NTRUPoly.polyCE ?NTRUPoly.poly0E /= in h0.
 rewrite NTRUPoly.polyDE NTRUPoly.polyMXE !NTRUPoly.polyCE ?NTRUPoly.poly0E /= in h1.
 smt(CycloFqField.addr0 CycloFqField.add0r).
qed.

lemma nonsquare_norm_zero r (a b:CycloFq.cyclocoeff) :
 field_nonsquare r => a*a-r*(b*b)=CycloFq.zero => a=CycloFq.zero /\ b=CycloFq.zero.
proof.
 move=> hns hz.
 case(b=CycloFq.zero) => hb.
 + subst b; rewrite CycloFqField.mul0r CycloFqField.mulr0 CycloFqField.subr0 in hz.
   rewrite CycloFqField.mulf_eq0 in hz; smt().
 have hi : b*CycloFq.inv b=CycloFq.one by exact(CycloFqField.mulfV b hb).
 have hs : (a*CycloFq.inv b)*(a*CycloFq.inv b)=r.
 + rewrite CycloFqField.mulrACA.
   have haa : a*a=r*(b*b) by move:hz; rewrite CycloFqField.subr_eq0.
   rewrite haa -CycloFqField.mulrA CycloFqField.mulrACA hi CycloFqField.mul1r CycloFqField.mulr1.
   done.
 have hn := hns (a*CycloFq.inv b); smt().
qed.

lemma quadratic_divides_scale r c p :
 quadratic_divides r p => quadratic_divides r (NTRUPoly.polyC c*p).
proof.
 rewrite /quadratic_divides; move=> [h hp].
 exists(NTRUPoly.polyC c*h); rewrite hp; ring.
qed.
lemma quadratic_monomial_reduction r j p :
 0<=j => 0<=p =>
 quadratic_divides r (NTRUPoly.PolyComRing.exp NTRUPoly.X (2*j+p)-NTRUPoly.polyC(CycloFq.exp r j)*NTRUPoly.PolyComRing.exp NTRUPoly.X p).
proof.
 move=> hj hp.
 have h : quadratic_divides r (NTRUPoly.PolyComRing.exp NTRUPoly.X (2*j)-NTRUPoly.polyC(CycloFq.exp r j)).
 + rewrite /quadratic_divides.
   exists (NTRUPoly.BigPoly.PCA.bigi predT
     (fun i => NTRUPoly.PolyComRing.exp (NTRUPoly.PolyComRing.exp NTRUPoly.X 2) (j-1-i)*NTRUPoly.PolyComRing.exp (NTRUPoly.polyC r) i) 0 j).
   rewrite /quadratic_modulus -(NTRUPoly.polyCX r j hj).
   rewrite (NTRUPoly.PolyComRing.exprM NTRUPoly.X 2 j).
   have hf := NTRUPoly.BigPoly.subrXX (NTRUPoly.PolyComRing.exp NTRUPoly.X 2) (NTRUPoly.polyC r) j hj.
   smt(NTRUPoly.PolyComRing.mulrC).
 have hm:=quadratic_divides_mul r _ (NTRUPoly.PolyComRing.exp NTRUPoly.X p) h.
 have he : NTRUPoly.PolyComRing.exp NTRUPoly.X (2*j+p)-NTRUPoly.polyC(CycloFq.exp r j)*NTRUPoly.PolyComRing.exp NTRUPoly.X p =
   (NTRUPoly.PolyComRing.exp NTRUPoly.X (2*j)-NTRUPoly.polyC(CycloFq.exp r j))*NTRUPoly.PolyComRing.exp NTRUPoly.X p.
 + have hjj : 0<=2*j by smt().
   have hex : NTRUPoly.PolyComRing.exp NTRUPoly.X (2*j+p)=
     NTRUPoly.PolyComRing.exp NTRUPoly.X (2*j)*NTRUPoly.PolyComRing.exp NTRUPoly.X p
     by exact(NTRUPoly.PolyComRing.exprD_nneg NTRUPoly.X (2*j) p hjj hp).
   rewrite hex; ring.
 by rewrite he.
qed.
lemma lift_three_nonzero : lift_int 3<>CycloFq.zero.
proof.
 apply/negP=> h; move:(congr1 CycloFq.asint _ _ h).
 by rewrite /lift_int CycloFq.incyclocoeffK CycloFq.zeroE /q /=.
qed.

op block_even (a:W16.t Array4.t) (r:CycloFq.cyclocoeff) =
 lift_word a.[0]+r*lift_word a.[2].
op block_odd (a:W16.t Array4.t) (r:CycloFq.cyclocoeff) =
 lift_word a.[1]+r*lift_word a.[3].
op block_norm (a:W16.t Array4.t) (r:CycloFq.cyclocoeff) =
 block_even a r*block_even a r-r*(block_odd a r*block_odd a r).

lemma lifted_two : CycloFq.incyclocoeff 2=CycloFq.one+CycloFq.one.
proof.
 apply CycloFq.asint_inj.
 by rewrite CycloFq.incyclocoeffK CycloFq.addE CycloFq.oneE /q /=.
qed.
lemma determinant_quadratic_factor (a:W16.t Array4.t) z r :
 lift_int z=r*r =>
 lift_int(inverse_determinant a z)=block_norm a r*block_norm a (-r).
proof.
 move=> hz; rewrite /lift_int in hz.
 rewrite /inverse_determinant /inverse_u /inverse_v /block_norm /block_even /block_odd /lift_word /lift_int.
 rewrite !(CycloFq.incyclocoeffB, CycloFq.incyclocoeffD, CycloFq.incyclocoeffM).
 rewrite hz lifted_two; ring.
qed.

lemma block_linear_zero_divides a r :
 block_even a r=CycloFq.zero => block_odd a r=CycloFq.zero =>
 quadratic_divides r (block_poly a).
proof.
 move=> he ho.
 have he' := congr1 NTRUPoly.polyC _ _ he.
 have ho' := congr1 NTRUPoly.polyC _ _ ho.
 rewrite /block_even NTRUPoly.polyCD NTRUPoly.polyCM in he'.
 rewrite /block_odd NTRUPoly.polyCD NTRUPoly.polyCM in ho'.
 have ha : NTRUPoly.polyC(lift_word a.[0])= -(NTRUPoly.polyC r*NTRUPoly.polyC(lift_word a.[2])).
 + move:he'; rewrite NTRUPoly.PolyComRing.addr_eq0; done.
 have hb : NTRUPoly.polyC(lift_word a.[1])= -(NTRUPoly.polyC r*NTRUPoly.polyC(lift_word a.[3])).
 + move:ho'; rewrite NTRUPoly.PolyComRing.addr_eq0; done.
 rewrite /quadratic_divides.
 exists (NTRUPoly.polyC(lift_word a.[2])+NTRUPoly.polyC(lift_word a.[3])*NTRUPoly.X).
 rewrite /block_poly /block_poly_fq /quadratic_modulus ha hb.
 ring.
qed.

lemma determinant_zero_quadratic_divisor a z r :
 lift_int z=r*r => field_nonsquare r => field_nonsquare (-r) =>
 inverse_determinant a z %% q=0 =>
 quadratic_divides r (block_poly a) \/ quadratic_divides (-r) (block_poly a).
proof.
 move=> hz hn hp hd.
 have hzero : lift_int(inverse_determinant a z)=CycloFq.zero.
 + apply CycloFq.asint_inj.
   by rewrite /lift_int CycloFq.incyclocoeffK CycloFq.zeroE hd.
 rewrite (determinant_quadratic_factor a z r hz) CycloFqField.mulf_eq0 in hzero.
 case hzero => ht.
 + have [he ho] := nonsquare_norm_zero r (block_even a r) (block_odd a r) hn ht.
   left; exact(block_linear_zero_divides a r he ho).
 have [he ho] := nonsquare_norm_zero (-r) (block_even a (-r)) (block_odd a (-r)) hp ht.
 right; exact(block_linear_zero_divides a (-r) he ho).
qed.

lemma quartic_quadratic_factor k r :
 terminal_root_field k=r*r =>
 quartic_modulus k=quadratic_modulus r*quadratic_modulus (-r).
proof.
 move=> hr.
 have hc : NTRUPoly.polyC(r*r)=NTRUPoly.polyC r*NTRUPoly.polyC r by exact(NTRUPoly.polyCM r r).
 have hn : NTRUPoly.polyC(-r)= -NTRUPoly.polyC r by exact(NTRUPoly.polyCN r).
 rewrite /quartic_modulus /quadratic_modulus hr hc hn; ring.
qed.
lemma eqm4_quadratic_divisor k r p b :
 terminal_root_field k=r*r => eqm4 k p b =>
 quadratic_divides r b => quadratic_divides r p.
proof.
 move=> hr; rewrite /eqm4 /quadratic_divides; move=> [h hrep] [j hb].
 exists (j-h*quadratic_modulus (-r)).
 have hp : p=b-h*quartic_modulus k by rewrite -hrep; ring.
 rewrite hp hb (quartic_quadratic_factor k r hr); ring.
qed.

lemma failed_block_determinant (a:W16.t Array768.t) k :
 in_qrange768 a => 0<=k<192 => poly_block_status a k=W64.of_int 1 =>
 inverse_determinant (block4 a k) (terminal_value k) %% q=0.
proof.
 move=> ha hk hs.
 have hak := in_qrange768_block4 a k ha hk.
 have hz : in_qrange(poly_block_zeta k).
 + by rewrite poly_block_zeta_eq; apply block_zeta_in_qrange.
 have ht : zeta_decode(poly_block_zeta k)=terminal_value k.
 + rewrite poly_block_zeta_eq; move:(block_zeta_math_terminal_value k hk).
   by rewrite /block_zeta_math.
 have hrel:=zeta_decode_relation (poly_block_zeta k) hz.
 rewrite ht in hrel.
 have hiff:=exact_status_determinant_zero_iff (block4 a k) (poly_block_zeta k)
   (terminal_value k) hak hz hrel.
 rewrite /poly_block_status in hs; smt().
qed.

lemma terminal_failed_block_quadratic (a:W16.t Array768.t) p k r :
 in_qrange768 a => terminal_represents a p => 0<=k<192 =>
 poly_block_status a k=W64.of_int 1 => terminal_root_field k=r*r =>
 field_nonsquare r => field_nonsquare (-r) =>
 quadratic_divides r p \/ quadratic_divides (-r) p.
proof.
 move=> ha hp hk hs hr hn hneg.
 have hd:=failed_block_determinant a k ha hk hs.
 have he : lift_int(terminal_value k)=r*r by exact hr.
 have hb:=determinant_zero_quadratic_divisor (block4 a k) (terminal_value k) r he hn hneg hd.
 have hrep:=hp k hk.
 case hb=>hb.
 + left; exact(eqm4_quadratic_divisor k r p (block_poly(block4 a k)) hr hrep hb).
 right; apply(eqm4_quadratic_divisor k (-r) p (block_poly(block4 a k))) => //.
 by rewrite hr; ring.
qed.

lemma field_euler_nonsquare n :
 n^1728 %% q=3456 => field_nonsquare(lift_int n).
proof.
 move=> he.
 have hpow : CycloFq.exp (lift_int n) 1728 = -CycloFq.one.
 + rewrite /lift_int CycloFq.exp_incyclocoeff /=.
   apply CycloFq.asint_inj.
   by rewrite CycloFq.incyclocoeffK CycloFq.oppE CycloFq.oneE he /q /=.
 rewrite /field_nonsquare; move=> x; apply/negP=> hx.
 have hs : CycloFq.exp (x*x) 1728 = -CycloFq.one by rewrite hx.
 case(x=CycloFq.zero) => hx0.
 + subst x; rewrite CycloFqField.mul0r CycloFqField.expr0z /= in hs.
   move:(congr1 CycloFq.asint _ _ hs).
   by rewrite CycloFq.zeroE CycloFq.oppE CycloFq.oneE /q /=.
 have hu : CycloFq.unit x by rewrite CycloFq.unitE.
 have hf := CycloFq.exp_sub_p_1 x hu.
 have hsq : CycloFq.exp (x*x) 1728=CycloFq.one.
 + rewrite -CycloFqField.expr2 -CycloFqField.exprM.
   exact hf.
 have hbad : CycloFq.one= -CycloFq.one by smt().
 move:(congr1 CycloFq.asint _ _ hbad).
 by rewrite CycloFq.oppE CycloFq.oneE /q /=.
qed.

lemma terminal_rejected_quadratic_cover (roots:int->CycloFq.cyclocoeff) a p :
 (forall k,0<=k<192 => terminal_root_field k=roots(2*k)*roots(2*k)) =>
 (forall k,0<=k<192 => roots(2*k+1)= -roots(2*k)) =>
 (forall j,0<=j<384 => field_nonsquare(roots j)) =>
 in_qrange768 a => terminal_represents a p => !poly_blocks_succeed a 192 =>
 exists j,0<=j<384 /\ quadratic_divides(roots j) p.
proof.
 move=> hr hpair hn ha hp hs.
 have hf := contraR _ _ (poly_no_failure_blocks_succeed a 192) hs.
 rewrite /poly_has_failed in hf.
 elim hf => k [hk hfailed].
 have hn0 := hn (2*k) _; first smt().
 have hn1 : field_nonsquare(-roots(2*k)).
 + rewrite -(hpair k hk); apply hn; smt().
 have ht := terminal_failed_block_quadratic a p k (roots(2*k))
   ha hp hk hfailed (hr k hk) hn0 hn1.
 case ht=>ht.
 + exists(2*k); split; first smt().
   exact ht.
 exists(2*k+1); split; first smt().
 by rewrite (hpair k hk).
qed.

lemma keygen_f_rejected_cover (roots:int->CycloFq.cyclocoeff) buf :
 (forall k,0<=k<192 => terminal_root_field k=roots(2*k)*roots(2*k)) =>
 (forall k,0<=k<192 => roots(2*k+1)= -roots(2*k)) =>
 (forall j,0<=j<384 => field_nonsquare(roots j)) =>
 !keygen_f_accept buf =>
 exists j,0<=j<384 /\ quadratic_divides(roots j)(input_poly(keygen_f_pre_ntt_spec buf)).
proof.
 move=> hr hpair hn hs.
 apply(terminal_rejected_quadratic_cover roots (keygen_f_ntt_spec buf)
   (input_poly(keygen_f_pre_ntt_spec buf)) hr hpair hn
   (keygen_f_ntt_qrange buf)) => //.
 apply forward_ntt_algebra_terminal_represents.
 exact(keygen_f_ntt_algebra buf).
qed.
lemma keygen_g_rejected_cover (roots:int->CycloFq.cyclocoeff) buf :
 (forall k,0<=k<192 => terminal_root_field k=roots(2*k)*roots(2*k)) =>
 (forall k,0<=k<192 => roots(2*k+1)= -roots(2*k)) =>
 (forall j,0<=j<384 => field_nonsquare(roots j)) =>
 !keygen_g_accept buf =>
 exists j,0<=j<384 /\ quadratic_divides(roots j)(input_poly(keygen_g_pre_ntt_spec buf)).
proof.
 move=> hr hpair hn hs.
 apply(terminal_rejected_quadratic_cover roots (keygen_g_ntt_spec buf)
   (input_poly(keygen_g_pre_ntt_spec buf)) hr hpair hn
   (keygen_g_ntt_qrange buf)) => //.
 apply forward_ntt_algebra_terminal_represents.
 exact(keygen_g_ntt_algebra buf).
qed.
