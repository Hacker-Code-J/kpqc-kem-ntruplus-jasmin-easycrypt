require import AllCore Distr DProd StdOrder.
require import NTRUPlus768GenModel NTRUPlus768GenDistribution NTRUPlus768PKEKeyDistribution.
require import NTRUPlus768AcceptanceProbability NTRUPlus768FreshRetryLaw.
require import NTRUPlus768CyclotomicFactorization.
import RField RealOrder.

(* Only g conditioning is removed here. The f law still conditions
   1+3*f0 on being a unit, making the NTRU inverse well defined. *)
op [opaque] ow_alpha_g = mu pke_field_psi1 pke_rq_unit.
op [opaque] ow_raw_fg_law = gen_f_law `*` pke_field_psi1.
op ow_g_unit (fg:NTRUPoly.poly*NTRUPoly.poly) = pke_rq_unit fg.`2.

lemma ow_alpha_g_acceptance : ow_alpha_g=fresh_g_accept_mass.
proof. rewrite /ow_alpha_g;exact gen_g_accept_mass. qed.
lemma ow_alpha_g_lower : 5%r/8%r<=ow_alpha_g.
proof. rewrite ow_alpha_g_acceptance;exact fresh_g_accept_lower. qed.
lemma ow_alpha_g_positive : 0%r<ow_alpha_g.
proof. have h:=ow_alpha_g_lower;smt(). qed.
lemma ow_alpha_g_upper : ow_alpha_g<=1%r.
proof. rewrite /ow_alpha_g;have h:=mu_bounded pke_field_psi1 pke_rq_unit;smt(). qed.
lemma ow_raw_fg_ll : is_lossless ow_raw_fg_law.
proof. rewrite /ow_raw_fg_law dprod_ll;split;[exact gen_f_lossless|exact gen_field_psi_lossless]. qed.

lemma ow_raw_unit_mass : mu ow_raw_fg_law ow_g_unit=ow_alpha_g.
proof.
 rewrite /ow_raw_fg_law /ow_g_unit (dprodEr gen_f_law pke_field_psi1 pke_rq_unit)
  gen_f_lossless /ow_alpha_g /=.
 done.
qed.

lemma ow_conditioned_pair : gen_fg_law=dcond ow_raw_fg_law ow_g_unit.
proof.
 apply eq_distr=>fg;case fg=>f g.
 rewrite /gen_fg_law dprod1E /gen_g_law dcond1E dcond1E ow_raw_unit_mass
  /ow_raw_fg_law dprod1E /ow_g_unit /= /ow_alpha_g.
 case(pke_rq_unit g)=>hg;ring.
qed.

lemma ow_conditioned_mass (event:NTRUPoly.poly*NTRUPoly.poly->bool) :
 ow_alpha_g*mu gen_fg_law event=
 mu ow_raw_fg_law(fun fg=>ow_g_unit fg /\ event fg).
proof.
 rewrite ow_conditioned_pair dcondE ow_raw_unit_mass /predI.
 have hn:ow_alpha_g<>0%r by have h:=ow_alpha_g_positive;smt().
 field; smt().
qed.

(* The identity applies directly to a returning-win kernel. No
   coefficient independence after conditioning or game-distance
   assumption is introduced. Integrability is not an additional
   premise of the library's exact conditional-expectation identity. *)
lemma ow_conditioned_expectation (kernel:NTRUPoly.poly*NTRUPoly.poly->real) :
 ow_alpha_g*E gen_fg_law kernel=
 E ow_raw_fg_law(fun fg=>if ow_g_unit fg then kernel fg else 0%r).
proof.
 rewrite ow_conditioned_pair exp_dcond /Ec ow_raw_unit_mass.
 have hn:ow_alpha_g<>0%r by have h:=ow_alpha_g_positive;smt().
 field; smt().
qed.
