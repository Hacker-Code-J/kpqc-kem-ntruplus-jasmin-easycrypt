require import AllCore Distr StdOrder.
require import NTRUPlus768FreshRetryLaw NTRUPlus768ProposalSwitch.
import RealOrder RField.

(* Arithmetic certificate. Actual acceptance lower bounds are supplied by
   the separate inverse-predicate proof, not assumed as a new axiom. *)
lemma acceptance_failure_range p :
  5%r/8%r <= p <= 1%r => 0%r <= 1%r-p <= 1%r/2%r.
proof. smt(). qed.

lemma acceptance_retry_power p n :
  5%r/8%r <= p <= 1%r => 0<=n =>
  (1%r-p)^n <= 1%r/(2%r^n).
proof.
 move=> hp hn.
 have h := ler_pexp n (1%r-p) (1%r/2%r) hn (acceptance_failure_range p hp).
 have he : (1%r/2%r)^n=1%r/(2%r^n).
 + by rewrite !div1r (exprVn 2%r n hn).
 smt().
qed.

lemma acceptance_retry_pair_256 pf pg :
  5%r/8%r <= pf <= 1%r => 5%r/8%r <= pg <= 1%r =>
  (1%r-pf)^256+(1%r-pg)^256 <= 2%r/(2%r^256).
proof.
 move=> hf hg.
 have h1:=acceptance_retry_power pf 256 hf _; first smt().
 have h2:=acceptance_retry_power pg 256 hg _; first smt().
 smt().
qed.

lemma keygen_budget_collision_512 a :
 proposal_delta a 512 = (512%r*a%r+130816%r)/(2%r^256).
proof.
 rewrite /proposal_delta /=.
 have hn : 2%r^256<>0%r by rewrite expf_eq0; smt().
 rewrite fromintM /=.
 field; smt().
qed.

lemma keygen_budget_error_256 a pf pg :
 5%r/8%r<=pf<=1%r => 5%r/8%r<=pg<=1%r =>
 proposal_delta a 512 + ((1%r-pf)^256+(1%r-pg)^256)
 <= (512%r*a%r+130818%r)/(2%r^256).
proof.
 move=> hf hg.
 have ht:=acceptance_retry_pair_256 pf pg hf hg.
 rewrite keygen_budget_collision_512.
 smt().
qed.

lemma keygen_empty_cache_error_239 :
 130818%r/(2%r^256) < 1%r/(2%r^239).
proof.
 have hp : 0%r<2%r^239 by apply expr_gt0; smt().
 have he : 2%r^256=(2%r^239)*131072%r.
 + rewrite (_:256=239+17) 1:// exprD_nneg 1,2://.
   have h17:2%r^17=131072%r by ring.
   by rewrite h17.
 rewrite he.
 smt().
qed.
