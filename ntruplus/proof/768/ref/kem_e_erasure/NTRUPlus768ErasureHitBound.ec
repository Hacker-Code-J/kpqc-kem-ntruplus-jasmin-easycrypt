require import AllCore List Distr DList StdOrder StdBigop RealSeries.
require import NTRUPlus768ErasureModel NTRUPlus768ROMDistributions.
require import NTRUPlus768ROMSeedObserver NTRUPlus768ROMSeedCollision.
import IntOrder RealOrder RField.

(* Neither list must be unique. The pool contains all sampled positions,
   including any unused positions padding the bounded setup. *)
op erasure_pool_hits (pool queries:erasure_seed list) =
 has (fun seed=>seed \in queries) pool.
op [opaque] erasure_hit_bound (Q qE:int) : real = (Q*qE)%r/(2%r^256).

lemma erasure_pool_hits_sym pool queries :
 erasure_pool_hits pool queries=erasure_pool_hits queries pool.
proof. rewrite /erasure_pool_hits !hasP; smt(). qed.
lemma erasure_pool_hits_cover used pool queries :
 (forall x,x \in used=>x \in pool) =>
 erasure_pool_hits used queries =>erasure_pool_hits pool queries.
proof. rewrite /erasure_pool_hits !hasP; smt(). qed.

lemma erasure_pool_hits_used_prefix n pool queries :
 erasure_pool_hits (rev(take n pool)) queries =>erasure_pool_hits pool queries.
proof.
 apply erasure_pool_hits_cover=>x hx.
 apply(mem_take n pool x); by move:hx; rewrite mem_rev.
qed.

lemma erasure_single_seed_hits queries :
 mu uniform32 (mem queries)<=(size queries)%r*seed_probability.
proof.
 apply(seed_hits_list_bound uniform32 seed_probability queries)=>x.
 by rewrite uniform_seed_point.
qed.
lemma erasure_union_bound ['a] (d:'a distr) P Q :
 mu d(predU P Q)<=mu d P+mu d Q.
proof. rewrite mu_or; have h:=ge0_mu d(predI P Q); smt(). qed.

lemma erasure_pool_hit_bound Q queries : 0<=Q =>
 mu(dlist uniform32 Q)(fun pool=>erasure_pool_hits pool queries)<=
 erasure_hit_bound Q (size queries).
proof.
 move=>hQ.
 have h:forall n,0<=n=>mu(dlist uniform32 n)(fun pool=>erasure_pool_hits pool queries)<=
   n%r*((size queries)%r*seed_probability).
 + elim=>[|n hn ih].
   - by rewrite dlist0 // dunitE /erasure_pool_hits /=.
   rewrite dlistS 1:hn dapply_dmap dmapE /(\o) /=.
   have he:(fun (z:erasure_seed*erasure_seed list)=>erasure_pool_hits(z.`1::z.`2)queries)=
     predU (fun (z:erasure_seed*erasure_seed list)=>z.`1 \in queries)
       (fun (z:erasure_seed*erasure_seed list)=>erasure_pool_hits z.`2 queries).
   - by apply fun_ext=>z; rewrite /erasure_pool_hits /predU /=.
   rewrite he.
   have hu:=erasure_union_bound (uniform32 `*` dlist uniform32 n)
     (fun (z:erasure_seed*erasure_seed list)=>z.`1 \in queries)
     (fun (z:erasure_seed*erasure_seed list)=>erasure_pool_hits z.`2 queries).
   rewrite (dprodEl uniform32 (dlist uniform32 n) (mem queries))
     (dprodEr uniform32 (dlist uniform32 n) (fun pool=>erasure_pool_hits pool queries))
     (dlist_ll uniform32 n uniform32_ll) uniform32_ll /= in hu.
   have hs:=erasure_single_seed_hits queries.
   have hb:mu uniform32(mem queries)+mu(dlist uniform32 n)(fun pool=>erasure_pool_hits pool queries)<=
     (size queries)%r*seed_probability+n%r*((size queries)%r*seed_probability).
   - apply ler_add; assumption.
   have hsum:(n+1)%r*((size queries)%r*seed_probability)=
     (size queries)%r*seed_probability+n%r*((size queries)%r*seed_probability).
   - rewrite fromintD /=; ring.
   rewrite hsum; exact(ler_trans _ _ _ hu hb).
 have hn:=h Q hQ.
 have he:Q%r*((size queries)%r*seed_probability)=erasure_hit_bound Q (size queries).
 + rewrite /erasure_hit_bound seed_probability_256 fromintM; ring.
 by move:hn; rewrite he.
qed.

lemma erasure_hit_bound_nonnegative Q qE : 0<=Q=>0<=qE=>0%r<=erasure_hit_bound Q qE.
proof.
 move=>hQ hq; rewrite /erasure_hit_bound.
 apply divr_ge0.
 + rewrite le_fromint; smt().
 apply expr_ge0; smt().
qed.
lemma erasure_hit_bound_monotone Q q1 q2 :
 0<=Q=>q1<=q2=>erasure_hit_bound Q q1<=erasure_hit_bound Q q2.
proof.
 move=>hQ hq; rewrite /erasure_hit_bound.
 apply ler_wpmul2r; first by apply invr_ge0; apply expr_ge0; smt().
 rewrite le_fromint; smt().
qed.

(* General averaging for a partial observer/kernel. Its missing mass is
   retained; the bound does not assume that the observer returns. *)
lemma erasure_kernel_mu_bound ['a 'b] (d:'a distr) (F:'a->'b distr) P c :
 0%r<=c =>(forall x,x \in d=>mu(F x)P<=c) =>mu(dlet d F)P<=c.
proof.
 move=>hc hb.
 have hf:hasE d(fun x=>mu(F x)P).
 + apply(hasE_le d (fun x=>mu(F x)P) (fun _=>1%r)); first exact(hasEC d 1%r).
   move=>x; have [hlo hhi]:=mu_bounded(F x)P.
   rewrite normr1 (ger0_norm _ hlo); exact hhi.
 have he:mu(dlet d F)P=E d(fun x=>mu(F x)P).
 + rewrite dletE /E; apply eq_sum=>x /=; ring.
 have hle:=in_ler_exp d (fun x=>mu(F x)P)(fun _=>c) hf (hasEC d c) hb.
 rewrite expC in hle.
 have hw:weight d<=1%r by exact(le1_mu d predT).
 have hm:c*weight d<=c by rewrite -{2}(mulr1 c); apply ler_wpmul2l.
 rewrite he; exact(ler_trans _ _ _ hle hm).
qed.

op erasure_joint_after ['a] (K:'a distr) Q : ('a*erasure_seed list) distr =
 dlet K(fun z=>dmap(dlist uniform32 Q)(fun pool=>(z,pool))).
op erasure_joint_before ['a] (K:'a distr) Q : ('a*erasure_seed list) distr =
 dlet(dlist uniform32 Q)(fun pool=>dmap K(fun z=>(z,pool))).

lemma erasure_pool_commute ['a] (K:'a distr) Q :
 erasure_joint_after K Q=erasure_joint_before K Q.
proof.
 rewrite /erasure_joint_after /erasure_joint_before /dmap.
 exact(dlet_swap K (dlist uniform32 Q)(fun z pool=>dunit(z,pool))).
qed.

lemma erasure_postsample_hit_bound ['a] (K:'a distr) (queries:'a->erasure_seed list) Q qE :
 0<=Q=>0<=qE=>(forall z,z \in K=>size(queries z)<=qE) =>
 mu(erasure_joint_after K Q)(fun (zpool:'a*erasure_seed list)=>erasure_pool_hits zpool.`2 (queries zpool.`1))<=
 erasure_hit_bound Q qE.
proof.
 move=>hQ hq hqueries; rewrite /erasure_joint_after.
 apply erasure_kernel_mu_bound; first exact(erasure_hit_bound_nonnegative Q qE hQ hq).
 move=>z hz; rewrite dmapE /(\o) /=.
 have hh:=erasure_pool_hit_bound Q (queries z) hQ.
 have hm:=erasure_hit_bound_monotone Q (size(queries z)) qE hQ (hqueries z hz).
 exact(ler_trans _ _ _ hh hm).
qed.

lemma erasure_presample_hit_bound ['a] (K:'a distr) (queries:'a->erasure_seed list) Q qE :
 0<=Q=>0<=qE=>(forall z,z \in K=>size(queries z)<=qE) =>
 mu(erasure_joint_before K Q)(fun (zpool:'a*erasure_seed list)=>erasure_pool_hits zpool.`2 (queries zpool.`1))<=
 erasure_hit_bound Q qE.
proof. rewrite -erasure_pool_commute; exact(erasure_postsample_hit_bound K queries Q qE). qed.

lemma erasure_joint_hit_bound ['a] (D:('a*erasure_seed list) distr) K queries Q qE :
 D=erasure_joint_after K Q =>0<=Q=>0<=qE=>
 (forall z,z \in K=>size(queries z)<=qE) =>
 mu D(fun (zpool:'a*erasure_seed list)=>erasure_pool_hits zpool.`2 (queries zpool.`1))<=erasure_hit_bound Q qE.
proof. move=>->; exact(erasure_postsample_hit_bound K queries Q qE). qed.

lemma erasure_used_prefix_hit_bound ['a] (K:'a distr) (queries:'a->erasure_seed list)
 (used_count:'a->int) Q qE :
 0<=Q=>0<=qE=>(forall z,z \in K=>size(queries z)<=qE) =>
 mu(erasure_joint_after K Q)
   (fun (zpool:'a*erasure_seed list)=>erasure_pool_hits (rev(take(used_count zpool.`1)zpool.`2))(queries zpool.`1))<=
 erasure_hit_bound Q qE.
proof.
 move=>hQ hq hqueries.
 apply(ler_trans _ _ _ _ (erasure_postsample_hit_bound K queries Q qE hQ hq hqueries)).
 apply mu_sub=>zpool.
 exact(erasure_pool_hits_used_prefix _ _ _).
qed.
