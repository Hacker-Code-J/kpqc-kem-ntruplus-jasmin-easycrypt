require import AllCore Distr Dexcepted.
from Jasmin require import JWord.
require import Array32 Array192.

(* A proposal is a 32-byte seed. The 192-byte SHAKE output is its
   deterministic image; no uniformity of that image is assumed. *)
clone import Dexcepted.WhileSampling as SeedSampling with
  type input <- W8.t Array32.t distr,
  type t <- W8.t Array32.t,
  op dt <- (fun d => d).

op seed_reject (accept:W8.t Array32.t -> bool)
    (_:W8.t Array32.t distr) (seed:W8.t Array32.t) = !accept seed.

module SeedRejection = {
  proc sample(d:W8.t Array32.t distr,accept:W8.t Array32.t -> bool) : W8.t Array32.t = {
    var seed:W8.t Array32.t;
    seed <$ d;
    while (!accept seed) { seed <$ d; }
    return seed;
  }
  proc direct(d:W8.t Array32.t distr,accept:W8.t Array32.t -> bool) : W8.t Array32.t = {
    var seed:W8.t Array32.t;
    seed <$ dcond d accept;
    return seed;
  }
  proc flagged(d:W8.t Array32.t distr,accept:W8.t Array32.t -> bool) : W8.t Array32.t = {
    var seed:W8.t Array32.t; var success:bool;
    seed <- witness; success <- false;
    while (!success) { seed <$ d; success <- accept seed; }
    return seed;
  }
  proc expanded(d:W8.t Array32.t distr,accept:W8.t Array32.t -> bool,
      expand:W8.t Array32.t -> W8.t Array192.t) : W8.t Array192.t = {
    var seed:W8.t Array32.t;
    seed <@ sample(d,accept);
    return expand seed;
  }
}.

lemma seed_excepted_conditional d accept :
  d \ seed_reject accept d = dcond d accept.
proof.
  rewrite /seed_reject /(\) /dcond; congr; congr.
  by apply fun_ext => seed; rewrite /predC.
qed.

lemma seed_rejection_flagged :
  equiv [SeedRejection.flagged ~ SeedRejection.sample : ={d,accept} ==> ={res}].
proof.
  proc; unroll{1} 3; rcondt{1} 3; first by auto.
  while (={d,accept,seed} /\ success{1}=accept{2} seed{2}); auto => />.
qed.

lemma seed_rejection_library :
  equiv [SeedRejection.sample ~ SeedSampling.SampleW.sample :
    d{1}=i{2} /\ test{2}=seed_reject accept{1} ==> ={res}].
proof.
  proc; inline SeedSampling.SampleWi.sample.
  wp; while (seed{1}=r0{2} /\ d{1}=i0{2} /\ test0{2}=seed_reject accept{1});
    auto => />; rewrite /seed_reject; smt().
qed.

lemma seed_rejection_probability &m d accept (event:W8.t Array32.t -> bool) :
  is_lossless d =>
  Pr[SeedRejection.sample(d,accept) @ &m:event res] = mu (dcond d accept) event.
proof.
  move=> dll; rewrite -seed_excepted_conditional.
  rewrite -(@SeedSampling.pr_sampleW &m d (seed_reject accept) event dll).
  by byequiv seed_rejection_library.
qed.

lemma seed_rejection_phoare d0 accept0 (event:W8.t Array32.t -> bool) :
  is_lossless d0 =>
  phoare [SeedRejection.sample : d=d0 /\ accept=accept0 ==> event res] =
    (mu (dcond d0 accept0) event).
proof.
  move=> dll; by bypr => &m [-> ->]; apply (seed_rejection_probability &m d0 accept0 event dll).
qed.

lemma seed_rejection_lossless d0 accept0 :
  is_lossless d0 => 0%r < mu d0 accept0 =>
  phoare [SeedRejection.sample : d=d0 /\ accept=accept0 ==> true] = 1%r.
proof.
  move=> dll positive.
  have condll:=dcond_ll d0 accept0 positive.
  conseq (seed_rejection_phoare d0 accept0 predT dll); smt().
qed.

lemma seed_rejection_exact_conditional &m d accept (event:W8.t Array32.t -> bool) :
  is_lossless d =>
  Pr[SeedRejection.sample(d,accept) @ &m:event res] =
    mu d (fun seed => accept seed /\ event seed) / mu d accept.
proof.
  move=> dll; rewrite (seed_rejection_probability &m d accept event dll) dcondE.
  by rewrite /predI.
qed.

lemma seed_rejection_direct :
  equiv [SeedRejection.sample ~ SeedRejection.direct :
    ={d,accept} /\ is_lossless d{1} ==> ={res}].
proof.
  bypr (res{1}) (res{2}) => /> &1 &2 seed <- <- dll.
  rewrite (seed_rejection_probability &1 d{1} accept{1} (pred1 seed) dll).
  by byphoare (_:d=d{1} /\ accept=accept{1} ==> res=seed) => //; proc; rnd; auto.
qed.

lemma seed_expansion_probability d0 accept0 expand0 (event:W8.t Array192.t -> bool) :
  is_lossless d0 =>
  phoare [SeedRejection.expanded : d=d0 /\ accept=accept0 /\ expand=expand0 ==> event res] =
    (mu (dmap (dcond d0 accept0) expand0) event).
proof.
  move=> dll; rewrite dmapE /(\o).
  proc; call (seed_rejection_phoare d0 accept0 (fun seed => event(expand0 seed)) dll).
  by auto.
qed.

lemma seed_rejection_accepts d0 accept0 :
  is_lossless d0 => 0%r < mu d0 accept0 =>
  phoare [SeedRejection.sample : d=d0 /\ accept=accept0 ==> accept0 res] = 1%r.
proof.
  move=> dll positive.
  have same: mu d0 (predI accept0 accept0)=mu d0 accept0 by apply mu_eq => seed; rewrite /predI; smt().
  have probability: mu (dcond d0 accept0) accept0=1%r by rewrite dcondE same; smt().
  by conseq (seed_rejection_phoare d0 accept0 accept0 dll).
qed.

(* A lossless RNG alone does not imply termination: if the fixed expansion
   never yields an invertible proposal on its seed support, this loop has
   termination probability zero. *)
lemma seed_rejection_zero_acceptance d0 accept0 :
  is_lossless d0 => mu d0 accept0=0%r =>
  phoare [SeedRejection.sample : d=d0 /\ accept=accept0 ==> true] = 0%r.
proof.
  move=> dll zero; have null: dcond d0 accept0=dnull by rewrite -dcondZ.
  conseq (seed_rejection_phoare d0 accept0 predT dll); rewrite null dnullE; smt().
qed.

lemma seed_rejection_flagged_probability d0 accept0 (event:W8.t Array32.t -> bool) :
  is_lossless d0 =>
  phoare [SeedRejection.flagged : d=d0 /\ accept=accept0 ==> event res] =
    (mu (dcond d0 accept0) event).
proof.
  move=> dll; conseq seed_rejection_flagged (seed_rejection_phoare d0 accept0 event dll); smt().
qed.
