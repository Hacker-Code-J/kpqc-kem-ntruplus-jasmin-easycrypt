"""All attempt seeds, full visible state, and fixed iid pool factorization."""
BASE='ntruplus/proof/768/ref/kem_e_erasure/'
MODEL=BASE+'NTRUPlus768ErasureModel.ec'
PREFIX=BASE+'NTRUPlus768ErasurePrefix.ec'
SETUP=BASE+'NTRUPlus768ErasureSetup.ec'
POOL=BASE+'NTRUPlus768ErasureSeedPool.ec'
TAPE=BASE+'NTRUPlus768ErasureSeedTape.ec'
HIT=BASE+'NTRUPlus768ErasureHitBound.ec'
RULES=(
 (MODEL,'pool initialization stores private seeds and does not program E entries',r'module ErasureSeedPool = { var seeds : erasure_seed list var cursor : int proc init(xs:erasure_seed list) = { seeds <- xs; cursor <- 0; } proc sample() : erasure_seed = { var x:erasure_seed; x <- nth witness seeds cursor; cursor <- cursor+1; return x; } }.'),
 (PREFIX,'programmed trace counts all f and g attempts and the preexisting prefix',r'lemma erasure_programmed_counted_length n0 : hoare[CountedKeygen(UniformSeedRNG,LoggedProgrammedExpand).run : size ErasureSeedLog.used=n0 ==> size ErasureSeedLog.used=n0+res.`2+res.`3].'),
 (PREFIX,'erased trace has the same complete count convention',r'lemma erasure_erased_counted_length n0 : hoare[CountedKeygen(UniformSeedRNG,LoggedErasedExpand).run : size ErasureSeedLog.used=n0 ==> size ErasureSeedLog.used=n0+res.`2+res.`3].'),
 (SETUP,'actual public-key coupling preserves the F cache and full log while E agrees outside used seeds',r'lemma erasure_keygen_coupling : equiv[Keygen(UniformSeedRNG,LoggedProgrammedExpand,SHAKEFROM).run ~ Keygen(UniformSeedRNG,LoggedErasedExpand,SHAKEFROM).run : ={glob ROF,ErasureSeedLog.used} /\ erasure_tables_agree ErasureSeedLog.used{1} ROE.m{1} ROE.m{2} ==> ={res,glob ROF,ErasureSeedLog.used} /\ erasure_tables_agree ErasureSeedLog.used{1} ROE.m{1} ROE.m{2}].'),
 (POOL,'pool observation retains the entire stopped output with counts and the final F table',r'type erasure_pool_observation = stopped_output * cca_f_table * erasure_seed list * erasure_seed list.'),
 (POOL,'independent reference setup observes the whole output and records only consumed pool entries',r'proc independent(qf:int,qg:int,workspace:W8.t Array14466.t) : erasure_pool_observation = { var pool:erasure_seed list; var out:stopped_output; pool <$ dlist uniform32 (qf+qg); out <@ StoppedKeygen(UniformSeedRNG,FreshExpand).run(qf,qg,workspace); ErasureSeedPool.init(pool); ErasureSeedPool.cursor <- out.`2+out.`3; ErasureSeedLog.used <- rev(take(out.`2+out.`3)pool); return(out,ROF.m,pool,ErasureSeedLog.used); }'),
 (POOL,'postsampled independent pool is drawn after the whole setup and uses only the consumed prefix',r'proc after(qf:int,qg:int,workspace:W8.t Array14466.t) : erasure_pool_observation = { var pool:erasure_seed list; var out:stopped_output; out <@ StoppedKeygen(UniformSeedRNG,FreshExpand).run(qf,qg,workspace); pool <$ dlist uniform32 (qf+qg); ErasureSeedPool.init(pool); ErasureSeedPool.cursor <- out.`2+out.`3; ErasureSeedLog.used <- rev(take(out.`2+out.`3)pool); return(out,ROF.m,pool,ErasureSeedLog.used); }'),
 (TAPE,'refresh retains every consumed seed and resamples only unread padding',r'proc refresh_raw() = { var suffix:erasure_seed list; suffix <$ dlist uniform32 (q-ErasureSeedPool.cursor); ErasureSeedPool.seeds <- take ErasureSeedPool.cursor ErasureSeedPool.seeds ++ suffix; }'),
 (HIT,'query kernel is sampled independently before the fixed-size iid seed pool',r"op erasure_joint_after ['a] (K:'a distr) Q : ('a*erasure_seed list) distr = dlet K(fun z=>dmap(dlist uniform32 Q)(fun pool=>(z,pool)))."),
 (HIT,'hit union bound counts all pool positions and all forwarded queries',r'op erasure_hit_bound (Q qE:int) : real = (Q*qE)%r/(2%r^256).'),
 (HIT,'pure prefix hit bound permits partial independent kernels',r"lemma erasure_used_prefix_hit_bound ['a] (K:'a distr) (queries:'a->erasure_seed list) (used_count:'a->int) Q qE : 0<=Q=>0<=qE=>(forall z,z \in K=>size(queries z)<=qE) => mu(erasure_joint_after K Q) (fun (zpool:'a*erasure_seed list)=>erasure_pool_hits (rev(take(used_count zpool.`1)zpool.`2))(queries zpool.`1))<= erasure_hit_bound Q qE."),
)
MUTATIONS=(
 ('unused-pool-padding-is-programmed-into-E',MODEL,'seeds <- xs; cursor <- 0;','seeds <- xs; ROE.m <- ofassoc(map(fun s=>(s,witness))xs); cursor <- 0;'),
 ('programmed-trace-length-forgets-g-attempts',PREFIX,'size ErasureSeedLog.used=n0+res.`2+res.`3].','size ErasureSeedLog.used=n0+res.`2].'),
 ('programmed-trace-length-forgets-preexisting-attempts',PREFIX,'size ErasureSeedLog.used=n0+res.`2+res.`3].','size ErasureSeedLog.used=res.`2+res.`3].'),
 ('pool-observation-keeps-key-only-and-loses-retry-counts',POOL,'type erasure_pool_observation = stopped_output * cca_f_table','type erasure_pool_observation = keygen_output option * cca_f_table'),
 ('pool-observation-drops-the-final-F-table',POOL,'type erasure_pool_observation = stopped_output * cca_f_table * erasure_seed list * erasure_seed list.','type erasure_pool_observation = stopped_output * erasure_seed list * erasure_seed list.'),
 ('used-prefix-includes-unread-padding',POOL,'ErasureSeedLog.used <- rev(take(out.`2+out.`3)pool);','ErasureSeedLog.used <- rev pool;'),
 ('tape-refresh-discards-already-consumed-seeds',TAPE,'take ErasureSeedPool.cursor ErasureSeedPool.seeds ++ suffix','[] ++ suffix'),
 ('hidden-pool-is-replaced-by-deterministic-seeds',HIT,'dmap(dlist uniform32 Q)(fun pool=>(z,pool))','dmap(dlist (dunit witness) Q)(fun pool=>(z,pool))'),
 ('hit-bound-forgets-the-number-of-hidden-proposals',HIT,'(Q*qE)%r/(2%r^256).','qE%r/(2%r^256).'),
 ('hit-bound-uses-bytes-instead-of-seed-bits',HIT,'(Q*qE)%r/(2%r^256).','(Q*qE)%r/(2%r^32).'),
)
