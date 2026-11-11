require import AllCore Distr.
require import NTRUPlus768INJCollision NTRUPlus768INJGames NTRUPlus768OWUniform.
require import NTRUPlus768CyclotomicFactorization.

(* A statistical event over the uniform public polynomial. Defining its
   probability supplies no numerical estimate or hardness assumption. *)
op [opaque] inj_relation_exists (a:NTRUPoly.poly) =
 exists (z:inj_pair),inj_short_win a z.
op [opaque] inj_uniform_bad_mass = mu ow_uniform_rq inj_relation_exists.

lemma inj_success_exists a z : inj_short_win a z=>inj_relation_exists a.
proof. move=>hz;rewrite /inj_relation_exists;exists z;exact hz. qed.
lemma inj_no_witness a z : !inj_relation_exists a=>!inj_short_win a z.
proof.
 move=>hn;apply/negP=>hz.
 have he:=inj_success_exists a z hz.
 by move:hn;rewrite he.
qed.

lemma inj_uniform_existence_bound (C<:INJShortAdversary) &m :
 Pr[INJShortRelationGame(C).run()@&m:res]<=inj_uniform_bad_mass.
proof.
 rewrite /inj_uniform_bad_mass.
 byphoare(_:true ==>res)=> //.
 proc;seq 1:(inj_relation_exists a)
  (mu ow_uniform_rq inj_relation_exists) 1%r 1%r 0%r true=> //.
 + rnd;auto.
 hoare;call(_:true ==>true);first by trivial.
 auto=> />;smt(inj_no_witness).
qed.
