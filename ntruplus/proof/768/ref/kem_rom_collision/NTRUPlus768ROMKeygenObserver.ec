require import AllCore List Distr FSet FMap.
from Jasmin require import JWord.
require import Array32 Array192 Array1152 Array2336.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768KeygenCompleteAttempt NTRUPlus768KeygenCompleteRetry.
require import NTRUPlus768ROMDistributions NTRUPlus768ROMOracles NTRUPlus768ROMSeedObserver NTRUPlus768ROMSeedCollision.

module ObserverSeedPort(O:SeedQueryOracle) = {
  proc sample() : seed = { var x; x <@ O.seed32(); return x; }
}.
module ObservedExpand(O:SeedQueryOracle) = {
  proc shake(seed:W8.t Array32.t) : W8.t Array192.t = {
    var y;
    O.mark(seed);
    y <@ ROE.get(seed);
    return y;
  }
}.

(* The context executes the previously proved array KeyGen, including both
   unchanged inverse-rejection loops. Its result is private bookkeeping. *)
module ActualKeygenSeedContext(O:SeedQueryOracle) = {
  var result : W8.t Array1152.t * W8.t Array2336.t
  proc run() : unit = {
    result <@ Keygen(ObserverSeedPort(O),ObservedExpand(O),SHAKEFROM).run();
  }
}.
module ObservedActualKeygen = {
  proc run(q0:int,a0:int) : W8.t Array1152.t * W8.t Array2336.t = {
    var pk:W8.t Array1152.t; var sk:W8.t Array2336.t;
    SeedObserver.init(uniform32,q0,a0,elems(fdom ROE.m));
    (pk,sk) <@ Keygen(ObserverSeedPort(SeedObserver),ObservedExpand(SeedObserver),SHAKEFROM).run();
    return(pk,sk);
  }
}.
module PlainActualKeygen = {
  proc run(q0:int,a0:int) : W8.t Array1152.t * W8.t Array2336.t = {
    var pk:W8.t Array1152.t; var sk:W8.t Array2336.t;
    PlainSeedOracle.law <- uniform32;
    (pk,sk) <@ Keygen(ObserverSeedPort(PlainSeedOracle),ExpandROM,SHAKEFROM).run();
    return(pk,sk);
  }
}.

op observer_cache_covers (m:(seed,W8.t Array192.t) fmap) (ds ks:seed list) =
  forall x, x \in m => x \in ds \/ x \in ks.
lemma observer_initial_cache_covered m :
  observer_cache_covers m [] (undup(elems(fdom m))).
proof. rewrite /observer_cache_covers; smt(mem_undup memE mem_fdom). qed.
lemma observer_seed_preserves_coverage m0 :
  hoare[SeedObserver.seed32 :
    observer_cache_covers m0 SeedObserver.draws SeedObserver.known ==>
    observer_cache_covers m0 SeedObserver.draws SeedObserver.known].
proof. proc; auto=> />; rewrite /observer_cache_covers; smt(). qed.
lemma observer_mark_preserves_coverage m0 :
  hoare[SeedObserver.mark :
    observer_cache_covers m0 SeedObserver.draws SeedObserver.known ==>
    observer_cache_covers m0 SeedObserver.draws SeedObserver.known].
proof. proc; auto=> />; rewrite /observer_cache_covers; smt(). qed.
lemma observed_expand_cache_covered :
  hoare[ObservedExpand(SeedObserver).shake :
    observer_cache_covers ROE.m SeedObserver.draws SeedObserver.known ==>
    observer_cache_covers ROE.m SeedObserver.draws SeedObserver.known].
proof.
  proc; inline SeedObserver.mark ROE.get.
  sp 1.
  if.
  + sp 2; if; auto=> />; rewrite /observer_cache_covers; smt(FMap.mem_set).
  sp 1; if; auto=> />; rewrite /observer_cache_covers; smt(FMap.mem_set).
qed.

(* A sampled seed is pending only until its unchanged E call completes.
   At each retry boundary, the actual table is exactly the observed inputs. *)
op observer_cache_exact (m:(seed,W8.t Array192.t) fmap) (ds ks:seed list) =
  forall x, x \in m <=> x \in ds \/ x \in ks.
op observer_cache_pending (m:(seed,W8.t Array192.t) fmap)
    (ds ks:seed list) (pending:seed) =
  observer_cache_covers m ds ks /\
  forall x, x \in ds \/ x \in ks => x \in m \/ x=pending.

lemma observer_initial_cache_exact m :
  observer_cache_exact m [] (undup(elems(fdom m))).
proof. rewrite /observer_cache_exact; smt(mem_undup memE mem_fdom). qed.

lemma observer_seed_cache_pending :
  hoare[ObserverSeedPort(SeedObserver).sample :
    observer_cache_exact ROE.m SeedObserver.draws SeedObserver.known ==>
    observer_cache_pending ROE.m SeedObserver.draws SeedObserver.known res].
proof.
  rewrite /observer_cache_exact /observer_cache_pending /observer_cache_covers.
  proc; inline SeedObserver.seed32; auto=> />.
  smt(in_cons).
qed.

lemma observed_expand_cache_exact :
  hoare[ObservedExpand(SeedObserver).shake :
    observer_cache_pending ROE.m SeedObserver.draws SeedObserver.known seed ==>
    observer_cache_exact ROE.m SeedObserver.draws SeedObserver.known].
proof.
  rewrite /observer_cache_pending /observer_cache_covers /observer_cache_exact.
  proc; inline SeedObserver.mark ROE.get.
  sp 1; if.
  + sp 2.
    if.
    - auto=> />.
      move=> &hr known hcov hpend hd hk hn r hr x.
      rewrite !(FMap.mem_set ROE.m{hr} seed{hr} r x).
      have hc:=hcov x; have hp:=hpend x; smt().
    auto=> />.
    smt(in_cons).
  sp 1.
  if.
  + auto=> />.
    move=> &hr hcov hpend hm hn r hr x.
    rewrite !(FMap.mem_set ROE.m{hr} seed{hr} r x).
    have hc:=hcov x; have hp:=hpend x; smt().
  auto=> />.
  smt().
qed.

lemma observed_attempt_f_cache_exact :
  hoare[KeygenAttempt(ObservedExpand(SeedObserver)).f :
    observer_cache_pending ROE.m SeedObserver.draws SeedObserver.known seed ==>
    observer_cache_exact ROE.m SeedObserver.draws SeedObserver.known].
proof.
  proc; wp; do 4! (call (_:true); first by trivial).
  call observed_expand_cache_exact; auto.
qed.
lemma observed_attempt_g_cache_exact :
  hoare[KeygenAttempt(ObservedExpand(SeedObserver)).g :
    observer_cache_pending ROE.m SeedObserver.draws SeedObserver.known seed ==>
    observer_cache_exact ROE.m SeedObserver.draws SeedObserver.known].
proof.
  proc; wp; do 4! (call (_:true); first by trivial).
  call observed_expand_cache_exact; auto.
qed.

lemma observed_retry_f_cache_exact :
  hoare[KeygenRetry(ObserverSeedPort(SeedObserver),ObservedExpand(SeedObserver)).f :
    observer_cache_exact ROE.m SeedObserver.draws SeedObserver.known ==>
    observer_cache_exact ROE.m SeedObserver.draws SeedObserver.known].
proof.
  proc; while(observer_cache_exact ROE.m SeedObserver.draws SeedObserver.known).
  + call observed_attempt_f_cache_exact; call observer_seed_cache_pending; auto.
  auto.
qed.
lemma observed_retry_g_cache_exact :
  hoare[KeygenRetry(ObserverSeedPort(SeedObserver),ObservedExpand(SeedObserver)).g :
    observer_cache_exact ROE.m SeedObserver.draws SeedObserver.known ==>
    observer_cache_exact ROE.m SeedObserver.draws SeedObserver.known].
proof.
  proc; while(observer_cache_exact ROE.m SeedObserver.draws SeedObserver.known).
  + call observed_attempt_g_cache_exact; call observer_seed_cache_pending; auto.
  auto.
qed.

lemma observed_keygen_cache_exact :
  hoare[Keygen(ObserverSeedPort(SeedObserver),ObservedExpand(SeedObserver),SHAKEFROM).run :
    observer_cache_exact ROE.m SeedObserver.draws SeedObserver.known ==>
    observer_cache_exact ROE.m SeedObserver.draws SeedObserver.known].
proof.
  proc; inline KeygenInstrumented(ObserverSeedPort(SeedObserver),ObservedExpand(SeedObserver),SHAKEFROM).run.
  wp; do 2! (call (_:true); first by trivial).
  call observed_retry_g_cache_exact; call observed_retry_f_cache_exact; auto.
qed.

lemma actual_keygen_observer_cache_exact :
  hoare[ObservedActualKeygen.run : true ==>
    observer_cache_exact ROE.m SeedObserver.draws SeedObserver.known].
proof.
  proc; wp; call observed_keygen_cache_exact; inline SeedObserver.init; auto=> /> &hr.
  exact(observer_initial_cache_exact ROE.m{hr}).
qed.

lemma observer_mark_lossless : islossless SeedObserver.mark.
proof. by proc; auto. qed.
lemma plain_mark_lossless : islossless PlainSeedOracle.mark.
proof. by proc. qed.

lemma observed_expand_erases (O <: SeedQueryOracle {-ROE}) :
  islossless O.mark =>
  equiv[ObservedExpand(O).shake ~ ExpandROM.shake :
    ={seed,ROE.m} ==> ={res,ROE.m}].
proof.
  move=> oml; proc.
  wp; call (_: ={ROE.m}); first by sim.
  call{1} oml; auto.
qed.

lemma actual_keygen_context_erases_plain :
  equiv[Keygen(ObserverSeedPort(PlainSeedOracle),ObservedExpand(PlainSeedOracle),SHAKEFROM).run ~
        Keygen(ObserverSeedPort(PlainSeedOracle),ExpandROM,SHAKEFROM).run :
    ={PlainSeedOracle.law,ROE.m,ROF.m} ==> ={res,ROE.m,ROF.m}].
proof.
  proc; inline KeygenInstrumented(ObserverSeedPort(PlainSeedOracle),ObservedExpand(PlainSeedOracle),SHAKEFROM).run
    KeygenInstrumented(ObserverSeedPort(PlainSeedOracle),ExpandROM,SHAKEFROM).run.
  inline KeygenRetry(ObserverSeedPort(PlainSeedOracle),ObservedExpand(PlainSeedOracle)).f
    KeygenRetry(ObserverSeedPort(PlainSeedOracle),ObservedExpand(PlainSeedOracle)).g
    KeygenRetry(ObserverSeedPort(PlainSeedOracle),ExpandROM).f
    KeygenRetry(ObserverSeedPort(PlainSeedOracle),ExpandROM).g
    KeygenAttempt(ObservedExpand(PlainSeedOracle)).f KeygenAttempt(ObservedExpand(PlainSeedOracle)).g
    KeygenAttempt(ExpandROM).f KeygenAttempt(ExpandROM).g
    ObservedExpand(PlainSeedOracle).shake ExpandROM.shake PlainSeedOracle.mark.
  sim.
qed.

lemma actual_keygen_observer_projects :
  equiv[ObservedActualKeygen.run ~ PlainActualKeygen.run :
    ={q0,a0,ROE.m,ROF.m} ==> ={res,ROE.m,ROF.m}].
proof.
  proc; inline Keygen(ObserverSeedPort(SeedObserver),ObservedExpand(SeedObserver),SHAKEFROM).run
    Keygen(ObserverSeedPort(PlainSeedOracle),ExpandROM,SHAKEFROM).run.
  inline KeygenInstrumented(ObserverSeedPort(SeedObserver),ObservedExpand(SeedObserver),SHAKEFROM).run
    KeygenInstrumented(ObserverSeedPort(PlainSeedOracle),ExpandROM,SHAKEFROM).run.
  inline KeygenRetry(ObserverSeedPort(SeedObserver),ObservedExpand(SeedObserver)).f
    KeygenRetry(ObserverSeedPort(SeedObserver),ObservedExpand(SeedObserver)).g
    KeygenRetry(ObserverSeedPort(PlainSeedOracle),ExpandROM).f
    KeygenRetry(ObserverSeedPort(PlainSeedOracle),ExpandROM).g
    KeygenAttempt(ObservedExpand(SeedObserver)).f KeygenAttempt(ObservedExpand(SeedObserver)).g
    KeygenAttempt(ExpandROM).f KeygenAttempt(ExpandROM).g
    ObservedExpand(SeedObserver).shake ExpandROM.shake
    ObserverSeedPort(SeedObserver).sample ObserverSeedPort(PlainSeedOracle).sample
    SeedObserver.init SeedObserver.seed32 SeedObserver.mark PlainSeedOracle.seed32.
  sim.
qed.

lemma actual_keygen_observer_matches_context :
  equiv[ObservedActualKeygen.run ~ SeedExperiment(ActualKeygenSeedContext).run :
    ={q0,a0,ROE.m,ROF.m} /\ d{2}=uniform32 /\ prior{2}=elems(fdom ROE.m{1}) ==>
    ={glob SeedObserver,ROE.m,ROF.m} /\ res{1}=ActualKeygenSeedContext.result{2}].
proof.
  proc; inline ActualKeygenSeedContext(SeedObserver).run.
  wp; call (_: ={glob SeedObserver,ROE.m,ROF.m}); first by sim.
  inline SeedObserver.init; auto=> />; smt().
qed.

lemma actual_keygen_completed_seed_collision &m qb ab :
  0 <= qb => 0 <= ab =>
  Pr[ObservedActualKeygen.run(qb,ab) @ &m : SeedObserver.fullbad] <=
    (ab*qb)%r/(2%r^256) + (qb*(qb-1))%r/(2%r*(2%r^256)) +
    Pr[ObservedActualKeygen.run(qb,ab) @ &m :
      qb < size SeedObserver.draws \/ ab < size SeedObserver.known].
proof.
  move=> qge age.
  have H:=uniform_seed_unrestricted_collision ActualKeygenSeedContext &m qb ab
    (elems(fdom ROE.m{m})) qge age.
  have eqbad: Pr[ObservedActualKeygen.run(qb,ab) @ &m : SeedObserver.fullbad] =
    Pr[SeedExperiment(ActualKeygenSeedContext).run(uniform32,qb,ab,elems(fdom ROE.m{m})) @ &m : SeedObserver.fullbad]
    by byequiv actual_keygen_observer_matches_context.
  have eqtail: Pr[ObservedActualKeygen.run(qb,ab) @ &m :
      qb < size SeedObserver.draws \/ ab < size SeedObserver.known] =
    Pr[SeedExperiment(ActualKeygenSeedContext).run(uniform32,qb,ab,elems(fdom ROE.m{m})) @ &m :
      qb < size SeedObserver.draws \/ ab < size SeedObserver.known]
    by byequiv actual_keygen_observer_matches_context.
  by rewrite eqbad eqtail.
qed.

lemma rom_keygen_observer_eof &m qb ab :
  0 <= qb => 0 <= ab =>
  Pr[ObservedActualKeygen.run(qb,ab) @ &m : SeedObserver.fullbad] <=
    (ab*qb)%r/(2%r^256) + (qb*(qb-1))%r/(2%r*(2%r^256)) +
    Pr[ObservedActualKeygen.run(qb,ab) @ &m :
      qb < size SeedObserver.draws \/ ab < size SeedObserver.known].
proof. exact(actual_keygen_completed_seed_collision &m qb ab). qed.
