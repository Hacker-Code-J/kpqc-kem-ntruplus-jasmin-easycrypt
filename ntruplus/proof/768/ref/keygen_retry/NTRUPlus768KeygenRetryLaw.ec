require import AllCore Distr.
from Jasmin require import JWord.
require import Array32 Array192 Array768.
require import NTRUPlus768KeygenSeedLaw NTRUPlus768KeygenCompleteSpec.
require import NTRUPlus768KeygenCompleteAttempt NTRUPlus768KeygenCompleteRetry.

(* Each call makes a fresh draw from the same explicit seed law. Hash
   modules used below may not read or change this module's state. *)
module IIDSeedRNG = {
  var law:W8.t Array32.t distr
  proc sample() : W8.t Array32.t = {
    var seed; seed <$ law; return seed;
  }
}.

op keygen_f_retry_result buf =
  let v=keygen_f_attempt_result buf in (v.`1,v.`2,v.`3).
op keygen_g_retry_result buf =
  let v=keygen_g_attempt_result buf in (v.`1,v.`2,v.`3).
op keygen_f_seed_accept (expand:W8.t Array32.t -> W8.t Array192.t) seed = keygen_f_accept(expand seed).
op keygen_g_seed_accept (expand:W8.t Array32.t -> W8.t Array192.t) seed = keygen_g_accept(expand seed).

module KeygenSeedSpec = {
  proc f(expand:W8.t Array32.t -> W8.t Array192.t) : W8.t Array192.t * W16.t Array768.t * W16.t Array768.t = {
    var seed; seed <@ SeedRejection.flagged(IIDSeedRNG.law,keygen_f_seed_accept expand);
    return keygen_f_retry_result(expand seed);
  }
  proc g(expand:W8.t Array32.t -> W8.t Array192.t) : W8.t Array192.t * W16.t Array768.t * W16.t Array768.t = {
    var seed; seed <@ SeedRejection.flagged(IIDSeedRNG.law,keygen_g_seed_accept expand);
    return keygen_g_retry_result(expand seed);
  }
}.

lemma keygen_attempt_f_total (E <: KeygenExpand) expand seed0 :
  (forall x, hoare [E.shake:seed=x ==> res=expand x]) => islossless E.shake =>
  phoare [KeygenAttempt(E).f:seed=seed0 ==> res=keygen_f_attempt_result(expand seed0)] = 1%r.
proof.
  move=> he el; by conseq (keygen_attempt_f_lossless E el) (keygen_attempt_f_functional E expand seed0 he).
qed.
lemma keygen_attempt_g_total (E <: KeygenExpand) expand seed0 :
  (forall x, hoare [E.shake:seed=x ==> res=expand x]) => islossless E.shake =>
  phoare [KeygenAttempt(E).g:seed=seed0 ==> res=keygen_g_attempt_result(expand seed0)] = 1%r.
proof.
  move=> he el; by conseq (keygen_attempt_g_lossless E el) (keygen_attempt_g_functional E expand seed0 he).
qed.

lemma keygen_retry_f_iid_equiv (E <: KeygenExpand {-IIDSeedRNG}) expand0 :
  (forall x, hoare [E.shake:seed=x ==> res=expand0 x]) => islossless E.shake =>
  equiv [KeygenRetry(IIDSeedRNG,E).f ~ KeygenSeedSpec.f :
    ={glob IIDSeedRNG} /\ expand{2}=expand0 ==> ={res,glob IIDSeedRNG}].
proof.
  move=> he el; proc; inline SeedRejection.flagged.
  wp; while (={glob IIDSeedRNG} /\ d{2}=IIDSeedRNG.law{1} /\
    expand{2}=expand0 /\ accept{2}=keygen_f_seed_accept expand0 /\
    (status{1}=W64.zero <=> success{2}) /\
    (success{2} => (buf{1},ntt{1},inverse{1})=keygen_f_retry_result(expand0 seed0{2}))).
  + wp; ecall{1}(keygen_attempt_f_total E expand0 seed{1} he el).
    inline IIDSeedRNG.sample; auto => />.
    rewrite /keygen_f_retry_result /keygen_f_seed_accept.
    by move=> &1 &2 _ _ seed _; rewrite (keygen_f_attempt_accept(expand0 seed)).
  auto => />; smt(W64.to_uint0 W64.to_uint1).
qed.

lemma keygen_retry_g_iid_equiv (E <: KeygenExpand {-IIDSeedRNG}) expand0 :
  (forall x, hoare [E.shake:seed=x ==> res=expand0 x]) => islossless E.shake =>
  equiv [KeygenRetry(IIDSeedRNG,E).g ~ KeygenSeedSpec.g :
    ={glob IIDSeedRNG} /\ expand{2}=expand0 ==> ={res,glob IIDSeedRNG}].
proof.
  move=> he el; proc; inline SeedRejection.flagged.
  wp; while (={glob IIDSeedRNG} /\ d{2}=IIDSeedRNG.law{1} /\
    expand{2}=expand0 /\ accept{2}=keygen_g_seed_accept expand0 /\
    (status{1}=W64.zero <=> success{2}) /\
    (success{2} => (buf{1},ntt{1},inverse{1})=keygen_g_retry_result(expand0 seed0{2}))).
  + wp; ecall{1}(keygen_attempt_g_total E expand0 seed{1} he el).
    inline IIDSeedRNG.sample; auto => />.
    rewrite /keygen_g_retry_result /keygen_g_seed_accept.
    by move=> &1 &2 _ _ seed _; rewrite (keygen_g_attempt_accept(expand0 seed)).
  auto => />; smt(W64.to_uint0 W64.to_uint1).
qed.

lemma keygen_seed_f_probability d expand0
    (event:(W8.t Array192.t * W16.t Array768.t * W16.t Array768.t) -> bool) :
  is_lossless d =>
  phoare [KeygenSeedSpec.f : IIDSeedRNG.law=d /\ expand=expand0 ==> event res] =
    (mu (dcond d (keygen_f_seed_accept expand0))
      (fun seed => event(keygen_f_retry_result(expand0 seed)))).
proof.
  move=> dll; proc.
  call(seed_rejection_flagged_probability d (keygen_f_seed_accept expand0)
    (fun seed => event(keygen_f_retry_result(expand0 seed))) dll).
  by auto.
qed.

lemma keygen_seed_g_probability d expand0
    (event:(W8.t Array192.t * W16.t Array768.t * W16.t Array768.t) -> bool) :
  is_lossless d =>
  phoare [KeygenSeedSpec.g : IIDSeedRNG.law=d /\ expand=expand0 ==> event res] =
    (mu (dcond d (keygen_g_seed_accept expand0))
      (fun seed => event(keygen_g_retry_result(expand0 seed)))).
proof.
  move=> dll; proc.
  call(seed_rejection_flagged_probability d (keygen_g_seed_accept expand0)
    (fun seed => event(keygen_g_retry_result(expand0 seed))) dll).
  by auto.
qed.

lemma keygen_retry_f_probability (E <: KeygenExpand {-IIDSeedRNG}) d expand0
    (event:(W8.t Array192.t * W16.t Array768.t * W16.t Array768.t) -> bool) :
  (forall x, hoare [E.shake:seed=x ==> res=expand0 x]) => islossless E.shake =>
  is_lossless d =>
  phoare [KeygenRetry(IIDSeedRNG,E).f : IIDSeedRNG.law=d ==> event res] =
    (mu (dcond d (keygen_f_seed_accept expand0))
      (fun seed => event(keygen_f_retry_result(expand0 seed)))).
proof.
  move=> he el dll.
  conseq (keygen_retry_f_iid_equiv E expand0 he el) (keygen_seed_f_probability d expand0 event dll); smt().
qed.

lemma keygen_retry_g_probability (E <: KeygenExpand {-IIDSeedRNG}) d expand0
    (event:(W8.t Array192.t * W16.t Array768.t * W16.t Array768.t) -> bool) :
  (forall x, hoare [E.shake:seed=x ==> res=expand0 x]) => islossless E.shake =>
  is_lossless d =>
  phoare [KeygenRetry(IIDSeedRNG,E).g : IIDSeedRNG.law=d ==> event res] =
    (mu (dcond d (keygen_g_seed_accept expand0))
      (fun seed => event(keygen_g_retry_result(expand0 seed)))).
proof.
  move=> he el dll.
  conseq (keygen_retry_g_iid_equiv E expand0 he el) (keygen_seed_g_probability d expand0 event dll); smt().
qed.

lemma keygen_retry_f_terminates (E <: KeygenExpand {-IIDSeedRNG}) d expand0 :
  (forall x, hoare [E.shake:seed=x ==> res=expand0 x]) => islossless E.shake =>
  is_lossless d => 0%r < mu d (keygen_f_seed_accept expand0) =>
  phoare [KeygenRetry(IIDSeedRNG,E).f : IIDSeedRNG.law=d ==> true] = 1%r.
proof.
  move=> he el dll positive.
  have condll:=dcond_ll d (keygen_f_seed_accept expand0) positive.
  conseq (keygen_retry_f_probability E d expand0 predT he el dll) => />; exact condll.
qed.

lemma keygen_retry_g_terminates (E <: KeygenExpand {-IIDSeedRNG}) d expand0 :
  (forall x, hoare [E.shake:seed=x ==> res=expand0 x]) => islossless E.shake =>
  is_lossless d => 0%r < mu d (keygen_g_seed_accept expand0) =>
  phoare [KeygenRetry(IIDSeedRNG,E).g : IIDSeedRNG.law=d ==> true] = 1%r.
proof.
  move=> he el dll positive.
  have condll:=dcond_ll d (keygen_g_seed_accept expand0) positive.
  conseq (keygen_retry_g_probability E d expand0 predT he el dll) => />; exact condll.
qed.

lemma keygen_retry_f_expanded_law (E <: KeygenExpand {-IIDSeedRNG}) d expand0
    (event:W8.t Array192.t -> bool) :
  (forall x, hoare [E.shake:seed=x ==> res=expand0 x]) => islossless E.shake =>
  is_lossless d =>
  phoare [KeygenRetry(IIDSeedRNG,E).f : IIDSeedRNG.law=d ==> event res.`1] =
    (mu (dmap (dcond d (keygen_f_seed_accept expand0)) expand0) event).
proof.
  move=> he el dll; rewrite dmapE /(\o).
  conseq (keygen_retry_f_probability E d expand0 (fun (v:W8.t Array192.t * W16.t Array768.t * W16.t Array768.t) => event v.`1) he el dll) => />.
qed.

lemma keygen_retry_g_expanded_law (E <: KeygenExpand {-IIDSeedRNG}) d expand0
    (event:W8.t Array192.t -> bool) :
  (forall x, hoare [E.shake:seed=x ==> res=expand0 x]) => islossless E.shake =>
  is_lossless d =>
  phoare [KeygenRetry(IIDSeedRNG,E).g : IIDSeedRNG.law=d ==> event res.`1] =
    (mu (dmap (dcond d (keygen_g_seed_accept expand0)) expand0) event).
proof.
  move=> he el dll; rewrite dmapE /(\o).
  conseq (keygen_retry_g_probability E d expand0 (fun (v:W8.t Array192.t * W16.t Array768.t * W16.t Array768.t) => event v.`1) he el dll) => />.
qed.
