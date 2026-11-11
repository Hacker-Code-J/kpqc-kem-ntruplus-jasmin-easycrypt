require import AllCore Distr StdOrder.
from Jasmin require import JWord.
require import Array192.
require import NTRUPlus768NumericalDFRModel NTRUPlus768ROMDistributions.
require import NTRUPlus768FreshRetryLaw NTRUPlus768KeygenCompleteSpec.
require import NTRUPlus768AcceptanceProbability.
import RealOrder RField.

op [opaque] four_buffers_accept (bs:four_buffers) =
 keygen_f_accept bs.`1.`1 /\ keygen_g_accept bs.`1.`2.

lemma pair_conditioning_mass :
 mu (uniform192 `*` uniform192)
  (fun (fg:W8.t Array192.t*W8.t Array192.t) => keygen_f_accept fg.`1 /\ keygen_g_accept fg.`2)
 = fresh_f_accept_mass*fresh_g_accept_mass.
proof. by rewrite dprodE /fresh_f_accept_mass /fresh_g_accept_mass. qed.

lemma four_conditioning_mass :
 mu raw_four_law four_buffers_accept = fresh_f_accept_mass*fresh_g_accept_mass.
proof.
 have h := dprodEl (uniform192 `*` uniform192) (uniform192 `*` uniform192)
   (fun (fg:W8.t Array192.t*W8.t Array192.t) => keygen_f_accept fg.`1 /\ keygen_g_accept fg.`2).
 rewrite weight_dprod !uniform192_ll /= pair_conditioning_mass in h.
 rewrite /raw_four_law /four_buffers_accept; exact h.
qed.

lemma independent_conditioning ['a 'b]
 (da:'a distr) (db:'b distr) (pa:'a->bool) (pb:'b->bool) :
 0%r<mu da pa => 0%r<mu db pb =>
 ((dcond da pa) `*` (dcond db pb)) =
 dcond (da `*` db) (fun xy:'a*'b =>pa xy.`1 /\ pb xy.`2).
proof.
 move=>ha hb; apply eq_distr=>-[a b].
 rewrite dcond1E dprodE !dprod1E !dcond1E /=.
 case(pa a)=>hpa; case(pb b)=>hpb; rewrite ?hpa ?hpb /=; try done; field; smt().
qed.
lemma conditioning_predT ['a] (d:'a distr) :
 is_lossless d => dcond d predT=d.
proof.
 move=>hl; apply eq_distr=>x.
 by rewrite dcond1E /predT hl /=.
qed.
lemma accepted_four_as_conditional :
 accepted_four_law = dcond raw_four_law four_buffers_accept.
proof.
 have pf:=fresh_f_accept_positive; have pg:=fresh_g_accept_positive.
 have hfg:=independent_conditioning uniform192 uniform192 keygen_f_accept keygen_g_accept pf pg.
 have hll:is_lossless (uniform192 `*` uniform192)
  by rewrite dprod_ll; split; exact uniform192_ll.
 have hp:0%r<mu (uniform192 `*` uniform192)
  (fun fg:W8.t Array192.t*W8.t Array192.t=>keygen_f_accept fg.`1 /\ keygen_g_accept fg.`2).
 + rewrite pair_conditioning_mass; exact (mulr_gt0 _ _ pf pg).
 have hh:=independent_conditioning (uniform192 `*` uniform192) (uniform192 `*` uniform192)
  (fun fg:W8.t Array192.t*W8.t Array192.t=>keygen_f_accept fg.`1 /\ keygen_g_accept fg.`2)
  predT hp _; first by rewrite hll.
 rewrite (conditioning_predT _ hll) in hh.
 rewrite /accepted_four_law hfg hh /raw_four_law /four_buffers_accept /predT /=.
 done.
qed.

lemma accepted_four_probability (event:four_buffers->bool) :
 mu accepted_four_law event =
 mu raw_four_law (fun bs=>four_buffers_accept bs /\ event bs) /
  (fresh_f_accept_mass*fresh_g_accept_mass).
proof. by rewrite accepted_four_as_conditional dcondE four_conditioning_mass /predI. qed.

lemma acceptance_pair_mass_lower :
 25%r/64%r <= fresh_f_accept_mass*fresh_g_accept_mass.
proof.
 have h0:0%r<=5%r/8%r by smt().
 have he:(5%r/8%r)*(5%r/8%r)=25%r/64%r by field.
 rewrite -he.
 exact(ler_pmul (5%r/8%r) fresh_f_accept_mass (5%r/8%r) fresh_g_accept_mass
   h0 h0 fresh_f_accept_lower fresh_g_accept_lower).
qed.

lemma conditioning_ratio_bound (denom numer upper:real) :
 25%r/64%r<=denom => 0%r<=upper => numer<=upper =>
 numer/denom <= (64%r/25%r)*upper.
proof.
 move=>hd hu hn.
 have hp:0%r<denom by smt().
 rewrite(ler_pdivr_mulr denom _ _ hp).
 smt().
qed.

lemma accepted_four_event_bound (event:four_buffers->bool) :
 mu accepted_four_law event <= (64%r/25%r)*mu raw_four_law event.
proof.
 rewrite accepted_four_probability.
 have hs:mu raw_four_law (fun bs=>four_buffers_accept bs /\ event bs)
  <=mu raw_four_law event.
 + apply mu_sub; move=>bs [ha he]; exact he.
 exact(conditioning_ratio_bound _ _ _ acceptance_pair_mass_lower
   (ge0_mu raw_four_law event) hs).
qed.

lemma accepted_bad_event_bound :
 mu accepted_four_law four_buffers_bad <=
 (64%r/25%r)*mu raw_four_law four_buffers_bad.
proof. exact(accepted_four_event_bound four_buffers_bad). qed.
