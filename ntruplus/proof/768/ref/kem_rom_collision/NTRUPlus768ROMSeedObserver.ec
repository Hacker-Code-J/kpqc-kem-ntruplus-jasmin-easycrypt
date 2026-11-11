require import AllCore List Distr FSet FMap Ring StdRing StdOrder StdBigop FelTactic.
require import Mu_mem.
from Jasmin require import JWord.
require import Array32.
import RField IntOrder RealOrder.

type seed = W8.t Array32.t.

(* mark records every E input, including adversarial queries made between
   draws. seed32 always samples, even after either analysis budget is
   exceeded. Only the prefix collision observer stops at q; the caller,
   its inverse tests, and its RNG behavior are not stopped or altered. *)
module type SeedQueryOracle = {
  proc seed32() : seed
  proc mark(x:seed) : unit
}.
module type SeedContext(O:SeedQueryOracle) = { proc run() : unit }.

module SeedObserver = {
  var law : seed distr
  var q,a : int
  var draws,prefix,known : seed list
  var fullbad,prefixbad : bool

  proc init(d:seed distr,q0:int,a0:int,prior:seed list) : unit = {
    law <- d; q <- q0; a <- a0;
    draws <- []; prefix <- []; known <- undup prior;
    fullbad <- false; prefixbad <- false;
  }
  proc seed32() : seed = {
    var x;
    x <$ law;
    if (size prefix < q) {
      prefixbad <- prefixbad \/
        (size known <= a /\ (x \in known \/ x \in prefix));
      prefix <- x::prefix;
    }
    fullbad <- fullbad \/ (x \in known \/ x \in draws);
    draws <- x::draws;
    return x;
  }
  (* Inputs already sampled are covered by draws; honest E expansion
     therefore consumes no external-query budget. known remains distinct. *)
  proc mark(x:seed) : unit = {
    if (!(x \in draws) /\ !(x \in known)) known <- x::known;
  }
}.

module PlainSeedOracle = {
  var law : seed distr
  proc seed32() : seed = { var x; x <$ law; return x; }
  proc mark(x:seed) : unit = { }
}.
module SeedExperiment(A:SeedContext) = {
  proc run(d:seed distr,q0:int,a0:int,prior:seed list) : unit = {
    SeedObserver.init(d,q0,a0,prior);
    A(SeedObserver).run();
  }
}.
module PlainSeedExperiment(A:SeedContext) = {
  proc run(d:seed distr,q0:int,a0:int,prior:seed list) : unit = {
    PlainSeedOracle.law <- d;
    A(PlainSeedOracle).run();
  }
}.

lemma seed_observer_lossless (d:seed distr) :
  is_lossless d => phoare[SeedObserver.seed32 : SeedObserver.law=d ==> true] = 1%r.
proof. move=> dll; proc; auto=> /> &m; rewrite dll. qed.

lemma seed_observer_projects (A <: SeedContext {-SeedObserver,-PlainSeedOracle}) :
  equiv[SeedExperiment(A).run ~ PlainSeedExperiment(A).run :
    ={d,q0,a0,prior,glob A} ==> ={glob A}].
proof.
  proc; call (_: SeedObserver.law{1}=PlainSeedOracle.law{2}).
  + proc; inline*; sim.
  + proc; inline*; sim.
  by inline SeedObserver.init; auto.
qed.

(* At every completed call, the unrestricted collision is accounted for
   by the first-q collision latch or an explicit budget-overrun event. *)
op observer_link (q:int) (a:int) (ds ps ks:seed list) (b pb:bool) =
  0 <= size ps <= q /\
  (size ds <= q => ps=ds) /\
  (b => pb \/ q < size ds \/ a < size ks).

lemma seed_observer_link_seed q0 a0 :
  hoare[SeedObserver.seed32 :
    SeedObserver.q=q0 /\ SeedObserver.a=a0 /\
    observer_link q0 a0 SeedObserver.draws SeedObserver.prefix
      SeedObserver.known SeedObserver.fullbad SeedObserver.prefixbad ==>
    observer_link q0 a0 SeedObserver.draws SeedObserver.prefix
      SeedObserver.known SeedObserver.fullbad SeedObserver.prefixbad].
proof.
  proc; auto=> /> &m x hx; rewrite /observer_link /=; smt(size_ge0).
qed.

lemma seed_observer_link_mark q0 a0 :
  hoare[SeedObserver.mark :
    observer_link q0 a0 SeedObserver.draws SeedObserver.prefix
      SeedObserver.known SeedObserver.fullbad SeedObserver.prefixbad ==>
    observer_link q0 a0 SeedObserver.draws SeedObserver.prefix
      SeedObserver.known SeedObserver.fullbad SeedObserver.prefixbad].
proof. proc; auto=> />; rewrite /observer_link /=; smt(size_ge0). qed.

lemma seed_experiment_link (A <: SeedContext {-SeedObserver}) qbound abound :
  0 <= qbound =>
  hoare[SeedExperiment(A).run : q0=qbound /\ a0=abound ==>
    SeedObserver.fullbad => SeedObserver.prefixbad \/
    qbound < size SeedObserver.draws \/ abound < size SeedObserver.known].
proof.
  move=> qge; proc.
  call (_: SeedObserver.q=qbound /\ SeedObserver.a=abound /\
    observer_link qbound abound SeedObserver.draws SeedObserver.prefix
      SeedObserver.known SeedObserver.fullbad SeedObserver.prefixbad).
  + conseq (seed_observer_link_seed qbound abound); smt().
  + conseq (seed_observer_link_mark qbound abound); smt().
  inline SeedObserver.init; auto=> />; rewrite /observer_link /=; smt().
qed.

lemma seed_hits_list_bound (d:seed distr) (p:real) (xs:seed list) :
  (forall x, mu1 d x <= p) => mu d (mem xs) <= (size xs)%r*p.
proof. move=> point; apply (Mu_mem.mu_mem_le_size xs d p); smt(). qed.

lemma seed_hits_cache_bound (d:seed distr) (p:real) (cache:(seed,'v) fmap) :
  (forall x, mu1 d x <= p) => mu d (mem (fdom cache)) <= (fsize cache)%r*p.
proof.
  move=> point; rewrite /fsize.
  apply (Mu_mem.mu_mem_le (fdom cache) d p); smt().
qed.

lemma prefix_collision_sum q0 a0 p : 0 <= q0 =>
  Bigreal.BRA.bigi predT (fun c => (a0+c)%r*p) 0 q0 =
    (a0*q0)%r*p + (q0*(q0-1))%r/2%r*p.
proof.
  move=> qge.
  rewrite -Bigreal.BRA.mulr_suml.
  rewrite (_: (fun c => (a0+c)%r) = (fun c => a0%r+c%r)).
  + by apply fun_ext=> c; rewrite fromintD.
  rewrite -Bigreal.BRA.sumrD Bigreal.sumri_const 1:qge Bigreal.sumidE 1:qge.
  rewrite mulrDl fromintM; ring.
qed.

(* This adaptive bound counts all attempted draws. FEL also applies to
   potentially divergent callers: events are measured on completed runs.
   No inverse-rejection independence or caller losslessness is assumed. *)
lemma seed_prefix_collision (A <: SeedContext {-SeedObserver})
    &m (d:seed distr) q0 a0 prior (p:real) :
  0 <= q0 => 0 <= a0 =>
  (forall x, mu1 d x <= p) =>
  Pr[SeedExperiment(A).run(d,q0,a0,prior) @ &m : SeedObserver.prefixbad] <=
    (a0*q0)%r*p + (q0*(q0-1))%r/2%r*p.
proof.
  move=> qge age point.
  have pge: 0%r <= p by have := point witness; smt(mu_bounded).
  fel 1 (size SeedObserver.prefix) (fun c => (a0+c)%r*p) q0
    SeedObserver.prefixbad
    [SeedObserver.seed32 : (size SeedObserver.prefix < q0)]
    (SeedObserver.q=q0 /\ SeedObserver.a=a0 /\ SeedObserver.law=d /\
      size SeedObserver.prefix <= q0)=> //.
  + by rewrite (prefix_collision_sum q0 a0 p qge).
  + by inline SeedObserver.init; auto; smt().
  + proc; rcondt 2; first by auto.
    wp.
    rnd (fun x => size SeedObserver.known <= a0 /\
      (x \in SeedObserver.known \/ x \in SeedObserver.prefix)).
    skip=> /> &hr cge clt npb ic.
    case (size SeedObserver.known{hr} <= a0)=> knownsize /=.
    + have hit:=seed_hits_list_bound d p
        (SeedObserver.known{hr}++SeedObserver.prefix{hr}) point.
      have same: (fun x:seed => x \in SeedObserver.known{hr} \/ x \in SeedObserver.prefix{hr}) = mem (SeedObserver.known{hr}++SeedObserver.prefix{hr}).
      + apply fun_ext=> x; rewrite mem_cat; smt().
      rewrite same; apply (ler_trans _ _ _ hit).
      rewrite size_cat; apply ler_wpmul2r; first exact pge.
      rewrite le_fromint; smt().
    + rewrite (mu_eq _ _ pred0) 1:/# mu0; smt().
  + move=> c; proc; auto=> />; smt(size_ge0).
  + move=> b c; proc; auto=> />; smt().
qed.

lemma seed_unrestricted_collision (A <: SeedContext {-SeedObserver})
    &m (d:seed distr) qb ab prior (p:real) :
  0 <= qb => 0 <= ab => (forall x, mu1 d x <= p) =>
  Pr[SeedExperiment(A).run(d,qb,ab,prior) @ &m : SeedObserver.fullbad] <=
    (ab*qb)%r*p + (qb*(qb-1))%r/2%r*p +
    Pr[SeedExperiment(A).run(d,qb,ab,prior) @ &m :
      qb < size SeedObserver.draws \/ ab < size SeedObserver.known].
proof.
  move=> qge age point.
  have null: Pr[SeedExperiment(A).run(d,qb,ab,prior) @ &m :
    SeedObserver.fullbad /\ !(SeedObserver.prefixbad \/
      qb < size SeedObserver.draws \/ ab < size SeedObserver.known)] = 0%r.
  + byphoare (_: q0=qb /\ a0=ab ==> _) => //.
    hoare; conseq (seed_experiment_link A qb ab qge); smt().
  have upper: Pr[SeedExperiment(A).run(d,qb,ab,prior) @ &m : SeedObserver.fullbad] <=
    Pr[SeedExperiment(A).run(d,qb,ab,prior) @ &m : SeedObserver.prefixbad] +
    Pr[SeedExperiment(A).run(d,qb,ab,prior) @ &m :
      qb < size SeedObserver.draws \/ ab < size SeedObserver.known].
  + rewrite Pr[mu_split (SeedObserver.prefixbad \/
      qb < size SeedObserver.draws \/ ab < size SeedObserver.known)] null addr0.
    have sub: Pr[SeedExperiment(A).run(d,qb,ab,prior) @ &m :
      SeedObserver.fullbad /\ (SeedObserver.prefixbad \/
      qb < size SeedObserver.draws \/ ab < size SeedObserver.known)] <=
      Pr[SeedExperiment(A).run(d,qb,ab,prior) @ &m :
      SeedObserver.prefixbad \/ qb < size SeedObserver.draws \/ ab < size SeedObserver.known]
      by rewrite Pr[mu_sub]; smt().
    apply (ler_trans _ _ _ sub).
    rewrite Pr[mu_or].
    have pos: 0%r <= Pr[SeedExperiment(A).run(d,qb,ab,prior) @ &m :
      SeedObserver.prefixbad /\ (qb < size SeedObserver.draws \/ ab < size SeedObserver.known)]
      by rewrite Pr[mu_ge0].
    smt().
  have prefixbound := seed_prefix_collision A &m d qb ab prior p qge age point.
  smt().
qed.

lemma seed_observer_mark_covers x0 :
  hoare[SeedObserver.mark : x=x0 ==>
    x0 \in SeedObserver.draws \/ x0 \in SeedObserver.known].
proof. proc; auto=> />; smt(). qed.

lemma seed_experiment_known_unique (A <: SeedContext {-SeedObserver}) :
  hoare[SeedExperiment(A).run : true ==> uniq SeedObserver.known].
proof.
  proc; call (_: uniq SeedObserver.known).
  + proc; auto.
  + proc; auto=> />; smt().
  by inline SeedObserver.init; auto; smt(undup_uniq).
qed.

lemma rom_seed_observer_eof (A <: SeedContext {-SeedObserver})
    &m (d:seed distr) qb ab prior (p:real) :
  0 <= qb => 0 <= ab => (forall x, mu1 d x <= p) =>
  Pr[SeedExperiment(A).run(d,qb,ab,prior) @ &m : SeedObserver.fullbad] <=
    (ab*qb)%r*p + (qb*(qb-1))%r/2%r*p +
    Pr[SeedExperiment(A).run(d,qb,ab,prior) @ &m :
      qb < size SeedObserver.draws \/ ab < size SeedObserver.known].
proof. exact(seed_unrestricted_collision A &m d qb ab prior p). qed.
