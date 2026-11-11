require import AllCore List Distr FSet FMap Ring StdRing StdOrder.
from Jasmin require import JWord.
require import Array32 NTRUPlus768ROMDistributions NTRUPlus768ROMSeedObserver.
import RField IntOrder RealOrder.

(* Exact probability for a specified 256-bit input. It is a seed-domain
   statement and does not assert that fixed SHAKE outputs are uniform. *)
op seed_probability = (1%r / 256%r)^32.
lemma seed_probability_256 : seed_probability = 1%r / (2%r^256).
proof.
  rewrite /seed_probability !div1r exprVn //.
  have heq:256%r=2%r^8 by ring.
  by rewrite heq -exprM /=.
qed.
lemma uniform_seed_point x : mu1 uniform32 x = seed_probability.
proof. by rewrite /seed_probability uniform32_point. qed.
lemma uniform_seed_hits_cache (cache:(seed,'v) fmap) :
  mu uniform32 (mem (fdom cache)) <= (fsize cache)%r / (2%r^256).
proof.
  have h:=seed_hits_cache_bound uniform32 seed_probability cache _.
  + by move=> x; rewrite uniform_seed_point.
  by move: h; rewrite seed_probability_256 mulrA.
qed.
lemma seed_bound_format (u v:real) :
  u*seed_probability + v/2%r*seed_probability =
  u/(2%r^256) + v/(2%r*(2%r^256)).
proof.
  rewrite seed_probability_256.
  have positive: 0%r < 2%r^256 by apply expr_gt0; smt().
  rewrite invrM 1,2:/#; ring.
qed.
lemma uniform_seed_prefix_collision (A <: SeedContext {-SeedObserver})
    &m qb ab prior :
  0 <= qb => 0 <= ab =>
  Pr[SeedExperiment(A).run(uniform32,qb,ab,prior) @ &m : SeedObserver.prefixbad] <=
    (ab*qb)%r/(2%r^256) + (qb*(qb-1))%r/(2%r*(2%r^256)).
proof.
  move=> qge age.
  have h:=seed_prefix_collision A &m uniform32 qb ab prior seed_probability qge age _.
  + by move=> x; rewrite uniform_seed_point.
  by rewrite -(seed_bound_format (ab*qb)%r (qb*(qb-1))%r).
qed.
lemma uniform_seed_unrestricted_collision (A <: SeedContext {-SeedObserver})
    &m qb ab prior :
  0 <= qb => 0 <= ab =>
  Pr[SeedExperiment(A).run(uniform32,qb,ab,prior) @ &m : SeedObserver.fullbad] <=
    (ab*qb)%r/(2%r^256) + (qb*(qb-1))%r/(2%r*(2%r^256)) +
    Pr[SeedExperiment(A).run(uniform32,qb,ab,prior) @ &m :
      qb < size SeedObserver.draws \/ ab < size SeedObserver.known].
proof.
  move=> qge age.
  have h:=seed_unrestricted_collision A &m uniform32 qb ab prior seed_probability qge age _.
  + by move=> x; rewrite uniform_seed_point.
  by rewrite -(seed_bound_format (ab*qb)%r (qb*(qb-1))%r).
qed.
lemma rom_seed_collision_eof (A <: SeedContext {-SeedObserver})
    &m qb ab prior :
  0 <= qb => 0 <= ab =>
  Pr[SeedExperiment(A).run(uniform32,qb,ab,prior) @ &m : SeedObserver.fullbad] <=
    (ab*qb)%r/(2%r^256) + (qb*(qb-1))%r/(2%r*(2%r^256)) +
    Pr[SeedExperiment(A).run(uniform32,qb,ab,prior) @ &m :
      qb < size SeedObserver.draws \/ ab < size SeedObserver.known].
proof. exact(uniform_seed_unrestricted_collision A &m qb ab prior). qed.
