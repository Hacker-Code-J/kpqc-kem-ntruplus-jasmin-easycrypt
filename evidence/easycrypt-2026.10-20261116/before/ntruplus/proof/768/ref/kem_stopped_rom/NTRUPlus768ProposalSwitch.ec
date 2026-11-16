require import AllCore Distr FMap FSet StdOrder StdBigop FelTactic.
from Jasmin require import JWord.
require import Array32 Array192 NTRUPlus768ProposalModel.
require import NTRUPlus768ROMDistributions NTRUPlus768ROMOracles.
require import NTRUPlus768ROMSeedObserver NTRUPlus768ROMSeedCollision.
import IntOrder RealOrder RField.

(* The only caller capability is draw.  Initialization belongs to the
   experiment and the same counter covers both rejection stages. *)
module type ProposalContext(P:ProposalPort) = {
  proc run(qf:int,qg:int) : bool
}.

module ROMProposal = {
  var n,q : int
  var bad : bool
  proc init(q0:int,m0:(W8.t Array32.t,W8.t Array192.t) fmap) = {
    n <- 0; q <- q0; bad <- false; ROE.m <- m0;
  }
  proc draw() : W8.t Array32.t * W8.t Array192.t = {
    var x:W8.t Array32.t;
    var y:W8.t Array192.t;
    x <- witness; y <- witness;
    if (n < q) {
      x <$ uniform32;
      bad <- bad \/ x \in ROE.m;
      y <@ ROE.get(x);
      n <- n+1;
    }
    return (x,y);
  }
}.

module FreshProposal = {
  var n,q : int
  var bad : bool
  var m : (W8.t Array32.t,W8.t Array192.t) fmap
  proc init(q0:int,m0:(W8.t Array32.t,W8.t Array192.t) fmap) = {
    n <- 0; q <- q0; bad <- false; m <- m0;
  }
  proc draw() : W8.t Array32.t * W8.t Array192.t = {
    var x:W8.t Array32.t;
    var y:W8.t Array192.t;
    x <- witness; y <- witness;
    if (n < q) {
      x <$ uniform32;
      bad <- bad \/ x \in m;
      y <$ uniform192;
      m.[x] <- y;
      n <- n+1;
    }
    return (x,y);
  }
}.

module ROMProposalExperiment(A:ProposalContext) = {
  proc run(qf:int,qg:int,q0:int,m0:(W8.t Array32.t,W8.t Array192.t) fmap) : bool = {
    var b;
    ROMProposal.init(q0,m0);
    b <@ A(ROMProposal).run(qf,qg);
    return b;
  }
}.
module FreshProposalExperiment(A:ProposalContext) = {
  proc run(qf:int,qg:int,q0:int,m0:(W8.t Array32.t,W8.t Array192.t) fmap) : bool = {
    var b;
    FreshProposal.init(q0,m0);
    b <@ A(FreshProposal).run(qf,qg);
    return b;
  }
}.

lemma rom_proposal_ll : islossless ROMProposal.draw.
proof.
  proc; sp 2; if; last by auto.
  wp; call roe_get_ll; auto=> />; smt(uniform32_ll).
qed.
lemma fresh_proposal_ll : islossless FreshProposal.draw.
proof.
  proc; sp 2; if; auto=> />; smt(uniform32_ll uniform192_ll).
qed.

lemma rom_proposal_invariant qb ab :
  hoare[ROMProposal.draw :
    ROMProposal.q=qb /\ 0<=ROMProposal.n<=qb /\
    fsize ROE.m <= ab+ROMProposal.n ==>
    ROMProposal.q=qb /\ 0<=ROMProposal.n<=qb /\
    fsize ROE.m <= ab+ROMProposal.n].
proof.
  proc; inline ROE.get; sp 2; if; last by auto; smt().
  seq 3 : (ROMProposal.q=qb /\ 0<=ROMProposal.n<qb /\
    fsize ROE.m<=ab+ROMProposal.n); first by auto; smt().
  if.
  + auto=> /> &hr nge nlt hs hx r hr.
    rewrite fsize_set /b2i; smt().
  + auto; smt().
qed.
lemma fresh_proposal_invariant qb ab :
  hoare[FreshProposal.draw :
    FreshProposal.q=qb /\ 0<=FreshProposal.n<=qb /\
    fsize FreshProposal.m <= ab+FreshProposal.n ==>
    FreshProposal.q=qb /\ 0<=FreshProposal.n<=qb /\
    fsize FreshProposal.m <= ab+FreshProposal.n].
proof.
  proc; sp 2; if; last by auto; smt().
  auto=> /> &hr nge nle hs nlt x hx y hy.
  rewrite fsize_set /b2i.
  case (x \notin FreshProposal.m{hr}); smt().
qed.

lemma rom_proposal_cap n0 q0 m0 b0 :
  hoare[ROMProposal.draw : ROMProposal.n=n0 /\ ROMProposal.q=q0 /\
    ROE.m=m0 /\ ROMProposal.bad=b0 /\ q0<=n0 ==>
    res=(witness,witness) /\ ROMProposal.n=n0 /\ ROMProposal.q=q0 /\
    ROE.m=m0 /\ ROMProposal.bad=b0].
proof. proc; rcondf 3; auto; smt(). qed.
lemma fresh_proposal_cap n0 q0 m0 b0 :
  hoare[FreshProposal.draw : FreshProposal.n=n0 /\ FreshProposal.q=q0 /\
    FreshProposal.m=m0 /\ FreshProposal.bad=b0 /\ q0<=n0 ==>
    res=(witness,witness) /\ FreshProposal.n=n0 /\ FreshProposal.q=q0 /\
    FreshProposal.m=m0 /\ FreshProposal.bad=b0].
proof. proc; rcondf 3; auto; smt(). qed.

op proposal_delta (ab qb:int) : real =
  (ab*qb)%r/(2%r^256) + (qb*(qb-1))%r/(2%r*(2%r^256)).

lemma fresh_proposal_birthday
  (A <: ProposalContext {-FreshProposal,-ROMProposal,-ROE})
  &mem qf qg qb ab m0 :
  0<=qb => 0<=ab => fsize m0<=ab =>
  Pr[FreshProposalExperiment(A).run(qf,qg,qb,m0) @ &mem : FreshProposal.bad]
  <= proposal_delta ab qb.
proof.
  move=> qge age msize.
  fel 1 FreshProposal.n (fun c => (ab+c)%r*seed_probability) qb
    FreshProposal.bad [FreshProposal.draw : (FreshProposal.n < qb)]
    (FreshProposal.q=qb /\ 0<=FreshProposal.n<=qb /\
      fsize FreshProposal.m<=ab+FreshProposal.n)=> //.
  + rewrite (prefix_collision_sum qb ab seed_probability qge).
    by rewrite /proposal_delta seed_bound_format.
  + inline FreshProposal.init; auto; smt().
  + proc; rcondt 3; first by auto.
    wp; rnd; wp; rnd (mem (fdom FreshProposal.m)); wp; skip=> />.
    move=> &hr nge nlt nbad nq nf.
    split; last by move=> h v hv; rewrite mem_fdom.
    have hit:=seed_hits_cache_bound uniform32 seed_probability FreshProposal.m{hr} _.
    + by move=> x; rewrite uniform_seed_point.
    apply (ler_trans _ _ _ hit).
    apply ler_wpmul2r.
    + rewrite /seed_probability; apply expr_ge0; smt().
    + by rewrite le_fromint.
  + move=> c; proc; rcondt 3; first by auto; smt().
    auto=> /> &hr nc nge nle hs x hx y hy.
    rewrite fsize_set /b2i.
    case (x \notin FreshProposal.m{hr}); smt().
  + move=> b c; proc; rcondf 3; auto; smt().
qed.

lemma rom_fresh_proposal_step :
  equiv[ROMProposal.draw ~ FreshProposal.draw :
    ROMProposal.n{1}=FreshProposal.n{2} /\
    ROMProposal.q{1}=FreshProposal.q{2} /\
    !ROMProposal.bad{1} /\ !FreshProposal.bad{2} /\
    ROE.m{1}=FreshProposal.m{2} ==>
    ROMProposal.bad{1}=FreshProposal.bad{2} /\
    (!FreshProposal.bad{2} => ={res} /\
      ROMProposal.n{1}=FreshProposal.n{2} /\
      ROMProposal.q{1}=FreshProposal.q{2} /\
      ROE.m{1}=FreshProposal.m{2})].
proof.
  proc; sp 2 2; if; 1,3: by auto; smt().
  seq 2 2 : (={x} /\
    ROMProposal.n{1}=FreshProposal.n{2} /\
    ROMProposal.q{1}=FreshProposal.q{2} /\
    ROE.m{1}=FreshProposal.m{2} /\
    ROMProposal.bad{1}=FreshProposal.bad{2} /\
    (FreshProposal.bad{2} = (x{2} \in FreshProposal.m{2}))).
  + by auto=> />.
  inline ROE.get; sp 1 0; if{1}.
  + auto=> />.
    by move=> &2 hx r hr; rewrite get_set_sameE /=.
  + wp; rnd{2}; auto=> />; smt(uniform192_ll).
qed.

(* Context termination is required only for this coupling across bad.
   It is discharged separately for the actually bounded KeyGen caller. *)
lemma proposal_upto
  (A <: ProposalContext {-FreshProposal,-ROMProposal,-ROE}) :
  (forall (P <: ProposalPort {-A}),
    islossless P.draw => islossless A(P).run) =>
  equiv[ROMProposalExperiment(A).run ~ FreshProposalExperiment(A).run :
    ={qf,qg,q0,m0,glob A} ==>
    ROMProposal.bad{1}=FreshProposal.bad{2} /\
    (!FreshProposal.bad{2} => ={res})].
proof.
  move=> all; proc.
  call (_: FreshProposal.bad,
    ROMProposal.n{1}=FreshProposal.n{2} /\
    ROMProposal.q{1}=FreshProposal.q{2} /\
    ROMProposal.bad{1}=FreshProposal.bad{2} /\
    ROE.m{1}=FreshProposal.m{2},
    ROMProposal.bad{1}=FreshProposal.bad{2}).
  + conseq rom_fresh_proposal_step; smt().
  + move=> &2 h; proc; sp 2; if; last by auto; smt().
    wp; call roe_get_ll; auto=> />; smt(uniform32_ll).
  + move=> &1; proc; sp 2; if; auto=> />;
      smt(uniform32_ll uniform192_ll).
  + inline ROMProposal.init FreshProposal.init; auto; smt().
qed.

lemma rom_proposal_no_overwrite x0 y0 :
  hoare[ROMProposal.draw : ROE.m.[x0]=Some y0 ==> ROE.m.[x0]=Some y0].
proof.
  proc; sp 2; if; last by auto.
  wp; call (roe_get_preserves x0 y0); auto.
qed.

lemma rom_proposal_experiment_invariant
  (A <: ProposalContext {-ROMProposal,-ROE}) qb ab :
  0<=qb =>
  hoare[ROMProposalExperiment(A).run : q0=qb /\ fsize m0<=ab ==>
    ROMProposal.q=qb /\ 0<=ROMProposal.n<=qb /\
    fsize ROE.m<=ab+ROMProposal.n].
proof.
  move=> qge; proc.
  call (_: ROMProposal.q=qb /\ 0<=ROMProposal.n<=qb /\
    fsize ROE.m<=ab+ROMProposal.n).
  + exact (rom_proposal_invariant qb ab).
  + inline ROMProposal.init; auto; smt().
qed.
lemma fresh_proposal_experiment_invariant
  (A <: ProposalContext {-FreshProposal}) qb ab :
  0<=qb =>
  hoare[FreshProposalExperiment(A).run : q0=qb /\ fsize m0<=ab ==>
    FreshProposal.q=qb /\ 0<=FreshProposal.n<=qb /\
    fsize FreshProposal.m<=ab+FreshProposal.n].
proof.
  move=> qge; proc.
  call (_: FreshProposal.q=qb /\ 0<=FreshProposal.n<=qb /\
    fsize FreshProposal.m<=ab+FreshProposal.n).
  + exact (fresh_proposal_invariant qb ab).
  + inline FreshProposal.init; auto; smt().
qed.

lemma proposal_good_event
  (A <: ProposalContext {-FreshProposal,-ROMProposal,-ROE})
  &mem qf qg qb m0 :
  (forall (P <: ProposalPort {-A}),
    islossless P.draw => islossless A(P).run) =>
  Pr[ROMProposalExperiment(A).run(qf,qg,qb,m0) @ &mem :
    res /\ !ROMProposal.bad] =
  Pr[FreshProposalExperiment(A).run(qf,qg,qb,m0) @ &mem :
    res /\ !FreshProposal.bad].
proof.
  move=> all; byequiv (proposal_upto A all)=> //; smt().
qed.

lemma proposal_bad_event
  (A <: ProposalContext {-FreshProposal,-ROMProposal,-ROE})
  &mem qf qg qb m0 :
  (forall (P <: ProposalPort {-A}),
    islossless P.draw => islossless A(P).run) =>
  Pr[ROMProposalExperiment(A).run(qf,qg,qb,m0) @ &mem : ROMProposal.bad] =
  Pr[FreshProposalExperiment(A).run(qf,qg,qb,m0) @ &mem : FreshProposal.bad].
proof.
  move=> all; byequiv (proposal_upto A all)=> //; smt().
qed.

lemma rom_proposal_birthday
  (A <: ProposalContext {-FreshProposal,-ROMProposal,-ROE})
  &mem qf qg qb ab m0 :
  (forall (P <: ProposalPort {-A}),
    islossless P.draw => islossless A(P).run) =>
  0<=qb => 0<=ab => fsize m0<=ab =>
  Pr[ROMProposalExperiment(A).run(qf,qg,qb,m0) @ &mem : ROMProposal.bad]
  <= proposal_delta ab qb.
proof.
  move=> all qge age ms.
  rewrite (proposal_bad_event A &mem qf qg qb m0 all).
  exact (fresh_proposal_birthday A &mem qf qg qb ab m0 qge age ms).
qed.

lemma proposal_switch_distance
  (A <: ProposalContext {-FreshProposal,-ROMProposal,-ROE})
  &mem qf qg qb ab m0 :
  (forall (P <: ProposalPort {-A}),
    islossless P.draw => islossless A(P).run) =>
  0<=qb => 0<=ab => fsize m0<=ab =>
  `|Pr[ROMProposalExperiment(A).run(qf,qg,qb,m0) @ &mem : res] -
    Pr[FreshProposalExperiment(A).run(qf,qg,qb,m0) @ &mem : res]|
  <= proposal_delta ab qb.
proof.
  move=> all qge age ms.
  have good:=proposal_good_event A &mem qf qg qb m0 all.
  have rb:=rom_proposal_birthday A &mem qf qg qb ab m0 all qge age ms.
  have fb:=fresh_proposal_birthday A &mem qf qg qb ab m0 qge age ms.
  have rsub: Pr[ROMProposalExperiment(A).run(qf,qg,qb,m0) @ &mem :
    res /\ ROMProposal.bad] <=
    Pr[ROMProposalExperiment(A).run(qf,qg,qb,m0) @ &mem : ROMProposal.bad]
    by rewrite Pr[mu_sub].
  have fsub: Pr[FreshProposalExperiment(A).run(qf,qg,qb,m0) @ &mem :
    res /\ FreshProposal.bad] <=
    Pr[FreshProposalExperiment(A).run(qf,qg,qb,m0) @ &mem : FreshProposal.bad]
    by rewrite Pr[mu_sub].
  rewrite Pr[mu_split ROMProposal.bad].
  have -> : Pr[FreshProposalExperiment(A).run(qf,qg,qb,m0) @ &mem : res] =
    Pr[FreshProposalExperiment(A).run(qf,qg,qb,m0) @ &mem : res /\ FreshProposal.bad] +
    Pr[FreshProposalExperiment(A).run(qf,qg,qb,m0) @ &mem : res /\ !FreshProposal.bad]
    by rewrite Pr[mu_split FreshProposal.bad].
  smt(mu_bounded).
qed.
