require import AllCore List Distr StdBigop StdOrder.
require import Array768.
require import NTRUPlus768SRUnionModel NTRUPlus768SRMultiplicationProof.
require import NTRUPlus768INJCollision NTRUPlus768INJExistence NTRUPlus768OWUniform.
require import NTRUPlus768CyclotomicFactorization.
import RealOrder Bigreal.

op [opaque] sr_list_event (a:NTRUPoly.poly) (z:inj_pair) =
 z.`1<>inj_zero /\ inj_relation a z.`1 z.`2.

lemma sr_relation_exists_enum a : inj_relation_exists a=
 has (sr_list_event a) sr_short_pairs.
proof.
 apply eq_iff;split.
 + rewrite /inj_relation_exists;move=>[z hz].
   have hn:=sr_success_nonzero_left a z.`1 z.`2 hz.
   move:hz;rewrite /inj_short_win;move=>[hv [hw [hp hr]]].
   apply/hasP;exists z;split.
   - by rewrite sr_short_pairs_mem.
   by rewrite /sr_list_event.
 move=>/hasP [z [hz he]].
 have [hv hw]:=iffLR _ _ (sr_short_pairs_mem z) hz.
 move:he;rewrite /sr_list_event;move=>[hn hr].
 rewrite /inj_relation_exists;exists z;rewrite /inj_short_win;split;first exact hv.
 split;first exact hw.
 split;last exact hr.
 by rewrite /inj_pair_nonzero hn.
qed.
lemma sr_bad_mass_enum : inj_uniform_bad_mass=
 mu ow_uniform_rq(fun a=>has (sr_list_event a) sr_short_pairs).
proof.
 rewrite /inj_uniform_bad_mass;apply mu_eq=>a;exact(sr_relation_exists_enum a).
qed.
lemma sr_bad_mass_union : inj_uniform_bad_mass<=
 BRA.big predT (fun z=>mu ow_uniform_rq(fun a=>sr_list_event a z)) sr_short_pairs.
proof. rewrite sr_bad_mass_enum;exact(mu_has_le sr_list_event ow_uniform_rq sr_short_pairs). qed.
lemma sr_zero_left_event (z:inj_pair) : z.`1=inj_zero=>mu ow_uniform_rq(fun a=>sr_list_event a z)=0%r.
proof.
 move=>hz;rewrite /sr_list_event hz /=;exact(mu0 ow_uniform_rq).
qed.
lemma sr_list_event_sub (z:inj_pair) :
 mu ow_uniform_rq(fun a=>sr_list_event a z)<=mu ow_uniform_rq(fun a=>inj_relation a z.`1 z.`2).
proof. apply mu_le=>a;rewrite /sr_list_event;smt(). qed.

(* This is a generic finite-union theorem. The fixed-pair probability
   bound is an explicit premise, to be discharged by the separate matrix
   and determinant argument; it is not asserted as an axiom here. *)
lemma sr_uniform_from_nonzero_bound epsilon : 0%r<=epsilon=>
 (forall v w,inj_short v=>inj_short w=>v<>inj_zero=>
  mu ow_uniform_rq(fun a=>inj_relation a v w)<=epsilon)=>
 inj_uniform_bad_mass<=25%r^768*epsilon.
proof.
 move=>he hb;rewrite sr_bad_mass_enum.
 have h:=mu_has_leM sr_list_event ow_uniform_rq sr_short_pairs epsilon _.
 + move=>z hz;have [hv hw]:=iffLR _ _ (sr_short_pairs_mem z) hz.
   case(z.`1=inj_zero)=>hn.
   - by rewrite(sr_zero_left_event z hn).
   exact(ler_trans _ _ _ (sr_list_event_sub z) (hb z.`1 z.`2 hv hw hn)).
 by move:h;rewrite sr_short_pairs_size_real.
qed.
lemma sr_uniform_from_pair_bound epsilon : 0%r<=epsilon=>
 (forall (z:inj_pair),inj_short z.`1=>inj_short z.`2=>inj_pair_nonzero z.`1 z.`2=>
  mu ow_uniform_rq(fun a=>inj_relation a z.`1 z.`2)<=epsilon)=>
 inj_uniform_bad_mass<=25%r^768*epsilon.
proof.
 move=>he hb;apply(sr_uniform_from_nonzero_bound epsilon he).
 move=>v w hv hw hn;apply(hb(v,w)hv hw).
 by rewrite /inj_pair_nonzero /= hn.
qed.
