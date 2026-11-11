require import AllCore Distr FMap StdOrder.
from Jasmin require import JWord.
require import Array32 Array192 Array768 Array1152 Array2336 Array14466.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteProof.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions.
require import NTRUPlus768StoppedKeygenModel NTRUPlus768StoppedKeygenPrefix.
require import NTRUPlus768FreshRetryLaw NTRUPlus768FreshBoundedLaw.
require import NTRUPlus768SubdistributionTransfer.
require import NTRUPlus768ProposalSwitch NTRUPlus768StoppedROMGames.
import RealOrder.

lemma fresh_counted_tail_probability &m qf0 qg0 :
 0<=qf0 => 0<=qg0 =>
 0%r<fresh_f_accept_mass => 0%r<fresh_g_accept_mass =>
 Pr[CountedKeygen(UniformSeedRNG,FreshExpand).run(witness) @ &m :
   !counted_within qf0 qg0 res] <= fresh_retry_tail qf0 qg0.
proof.
 move=> hqf hqg hpf hpg.
 have hc : Pr[CountedKeygen(UniformSeedRNG,FreshExpand).run(witness) @ &m : true]=1%r
   by byphoare (fresh_counted_keygen_ll hpf hpg).
 have hs : Pr[StoppedKeygen(UniformSeedRNG,FreshExpand).run(qf0,qg0,witness) @ &m : true]=1%r
   by byphoare fresh_stopped_keygen_lossless.
 have hp := counted_stopped_prefix UniformSeedRNG FreshExpand qf0 qg0 witness
   (fun (_:keygen_output) => true) &m uniform_seed_rng_ll fresh_expand_ll.
 rewrite /stopped_event /= in hp.
 have ht := fresh_stopped_keygen_abort_probability &m qf0 qg0 witness hqf hqg.
 have hn : Pr[CountedKeygen(UniformSeedRNG,FreshExpand).run(witness) @ &m :
   !counted_within qf0 qg0 res] =
   Pr[StoppedKeygen(UniformSeedRNG,FreshExpand).run(qf0,qg0,witness) @ &m :
   !stopped_success res].
 + by rewrite /stopped_success Pr[mu_not] Pr[mu_not] hc hs hp.
 by rewrite hn.
qed.

lemma fresh_event_prefix_lower &m qf0 qg0 (event:keygen_output -> bool) :
 0<=qf0 => 0<=qg0 =>
 0%r<fresh_f_accept_mass => 0%r<fresh_g_accept_mass =>
 Pr[CountedKeygen(UniformSeedRNG,FreshExpand).run(witness) @ &m : event res.`1]
   - fresh_retry_tail qf0 qg0 <=
 Pr[StoppedKeygen(UniformSeedRNG,FreshExpand).run(qf0,qg0,witness) @ &m :
   stopped_event event res].
proof.
 move=> hqf hqg hpf hpg.
 have ht := fresh_counted_tail_probability &m qf0 qg0 hqf hqg hpf hpg.
 have hp := counted_stopped_prefix UniformSeedRNG FreshExpand qf0 qg0 witness
   event &m uniform_seed_rng_ll fresh_expand_ll.
 have hb : Pr[CountedKeygen(UniformSeedRNG,FreshExpand).run(witness) @ &m :
   event res.`1 /\ !counted_within qf0 qg0 res] <=
   Pr[CountedKeygen(UniformSeedRNG,FreshExpand).run(witness) @ &m :
   !counted_within qf0 qg0 res] by rewrite Pr[mu_sub].
 have he : Pr[CountedKeygen(UniformSeedRNG,FreshExpand).run(witness) @ &m :
   event res.`1 /\ counted_within qf0 qg0 res] =
   Pr[CountedKeygen(UniformSeedRNG,FreshExpand).run(witness) @ &m :
   counted_within qf0 qg0 res /\ event res.`1]
   by rewrite Pr[mu_eq].
 rewrite Pr[mu_split (counted_within qf0 qg0 res)] he hp.
 smt().
qed.

lemma rom_stopped_initial_cache &m qf0 qg0 cache0 (event:stopped_output -> bool) :
 ROE.m{m}=cache0 =>
 Pr[DirectROMStopped.run(qf0,qg0,cache0) @ &m : event res] =
 Pr[StoppedKeygen(UniformSeedRNG,ExpandROM).run(qf0,qg0,witness) @ &m : event res].
proof.
 move=> hm.
 byequiv (_: ={qf,qg,glob ROF} /\ m0{1}=ROE.m{2} /\ workspace{2}=witness ==> ={res}) => //; last by smt().
 proc; inline StoppedKeygen(UniformSeedRNG,ExpandROM).run.
 wp; sim (: ={glob ROE,glob ROF}); auto.
qed.
lemma fresh_stopped_direct &m qf0 qg0 (event:stopped_output -> bool) :
 Pr[DirectFreshStopped.run(qf0,qg0) @ &m : event res] =
 Pr[StoppedKeygen(UniformSeedRNG,FreshExpand).run(qf0,qg0,witness) @ &m : event res].
proof.
 byequiv (_: ={qf,qg,glob ROF} /\ workspace{2}=witness ==> ={res}) => //.
 proc; inline StoppedKeygen(UniformSeedRNG,FreshExpand).run.
 wp; sim (: ={glob ROF}); auto.
qed.
lemma raw_stopped_rom_fresh_distance &m qf0 qg0 ab m0 (event:stopped_output -> bool) :
 0<=qf0 => 0<=qg0 => 0<=ab => fsize m0<=ab => ROE.m{m}=m0 =>
 `|Pr[StoppedKeygen(UniformSeedRNG,ExpandROM).run(qf0,qg0,witness) @ &m : event res] -
   Pr[StoppedKeygen(UniformSeedRNG,FreshExpand).run(qf0,qg0,witness) @ &m : event res]|
 <= proposal_delta ab (qf0+qg0).
proof.
 move=> hqf hqg ha hm he.
 have h := stopped_rom_fresh_distance &m qf0 qg0 ab m0 event hqf hqg ha hm.
 rewrite (rom_stopped_initial_cache &m qf0 qg0 m0 event he)
   (fresh_stopped_direct &m qf0 qg0 event) in h.
 exact h.
qed.

(* One lower event estimate, used both for A and its complement. *)
lemma rom_counted_good_event_lower &m qf0 qg0 ab m0 (event:keygen_output -> bool) :
 0<=qf0 => 0<=qg0 => 0<=ab => fsize m0<=ab => ROE.m{m}=m0 =>
 0%r<fresh_f_accept_mass => 0%r<fresh_g_accept_mass =>
 Pr[CountedKeygen(UniformSeedRNG,FreshExpand).run(witness) @ &m : event res.`1] -
   (proposal_delta ab (qf0+qg0)+fresh_retry_tail qf0 qg0) <=
 Pr[CountedKeygen(UniformSeedRNG,ExpandROM).run(witness) @ &m :
   counted_within qf0 qg0 res /\ event res.`1].
proof.
 move=> hqf hqg ha hm he hpf hpg.
 have hs := raw_stopped_rom_fresh_distance &m qf0 qg0 ab m0
   (stopped_event event) hqf hqg ha hm he.
 have hf := fresh_event_prefix_lower &m qf0 qg0 event hqf hqg hpf hpg.
 have hp := counted_stopped_prefix UniformSeedRNG ExpandROM qf0 qg0 witness
   event &m uniform_seed_rng_ll ro_e_shake_ll.
 rewrite hp; rewrite ler_norml in hs; smt().
qed.
lemma rom_counted_event_lower &m qf0 qg0 ab m0 (event:keygen_output -> bool) :
 0<=qf0 => 0<=qg0 => 0<=ab => fsize m0<=ab => ROE.m{m}=m0 =>
 0%r<fresh_f_accept_mass => 0%r<fresh_g_accept_mass =>
 Pr[CountedKeygen(UniformSeedRNG,FreshExpand).run(witness) @ &m : event res.`1] -
   (proposal_delta ab (qf0+qg0)+fresh_retry_tail qf0 qg0) <=
 Pr[CountedKeygen(UniformSeedRNG,ExpandROM).run(witness) @ &m : event res.`1].
proof.
 move=> hqf hqg ha hm he hpf hpg.
 have hl := rom_counted_good_event_lower &m qf0 qg0 ab m0 event hqf hqg ha hm he hpf hpg.
 have hs : Pr[CountedKeygen(UniformSeedRNG,ExpandROM).run(witness) @ &m :
   counted_within qf0 qg0 res /\ event res.`1] <=
   Pr[CountedKeygen(UniformSeedRNG,ExpandROM).run(witness) @ &m : event res.`1]
   by rewrite Pr[mu_sub].
 smt().
qed.

lemma counted_rom_fresh_distance &m qf0 qg0 ab m0 (event:keygen_output -> bool) :
 0<=qf0 => 0<=qg0 => 0<=ab => fsize m0<=ab => ROE.m{m}=m0 =>
 0%r<fresh_f_accept_mass => 0%r<fresh_g_accept_mass =>
 `|Pr[CountedKeygen(UniformSeedRNG,ExpandROM).run(witness) @ &m : event res.`1] -
   Pr[CountedKeygen(UniformSeedRNG,FreshExpand).run(witness) @ &m : event res.`1]|
 <= proposal_delta ab (qf0+qg0)+fresh_retry_tail qf0 qg0.
proof.
 move=> hqf hqg ha hm he hpf hpg.
 have hl := rom_counted_event_lower &m qf0 qg0 ab m0 event hqf hqg ha hm he hpf hpg.
 have hn := rom_counted_event_lower &m qf0 qg0 ab m0
   (fun out => !event out) hqf hqg ha hm he hpf hpg.
 have ht : Pr[CountedKeygen(UniformSeedRNG,FreshExpand).run(witness) @ &m : true]=1%r
   by byphoare (fresh_counted_keygen_ll hpf hpg).
 have ha' : Pr[CountedKeygen(UniformSeedRNG,ExpandROM).run(witness) @ &m : event res.`1] +
   Pr[CountedKeygen(UniformSeedRNG,ExpandROM).run(witness) @ &m : !event res.`1] <= 1%r.
 + rewrite Pr[mu_not]; smt(mu_bounded).
 have hi' : Pr[CountedKeygen(UniformSeedRNG,FreshExpand).run(witness) @ &m : event res.`1] +
   Pr[CountedKeygen(UniformSeedRNG,FreshExpand).run(witness) @ &m : !event res.`1] = 1%r.
 + rewrite Pr[mu_not] ht; smt().
 exact (complementary_event_transfer _ _ _ _ _ ha' hi' hl hn).
qed.

lemma rom_counted_good_lower &m qf0 qg0 ab m0 :
 0<=qf0 => 0<=qg0 => 0<=ab => fsize m0<=ab => ROE.m{m}=m0 =>
 0%r<fresh_f_accept_mass => 0%r<fresh_g_accept_mass =>
 1%r-(proposal_delta ab (qf0+qg0)+fresh_retry_tail qf0 qg0) <=
 Pr[CountedKeygen(UniformSeedRNG,ExpandROM).run(witness) @ &m : counted_within qf0 qg0 res].
proof.
 move=> hqf hqg ha hm he hpf hpg.
 have h := rom_counted_good_event_lower &m qf0 qg0 ab m0
   (fun (_:keygen_output) => true) hqf hqg ha hm he hpf hpg.
 have ht : Pr[CountedKeygen(UniformSeedRNG,FreshExpand).run(witness) @ &m : true]=1%r
   by byphoare (fresh_counted_keygen_ll hpf hpg).
 rewrite /= in h.
 smt().
qed.

lemma rom_counted_missing_mass &m qf0 qg0 ab m0 :
 0<=qf0 => 0<=qg0 => 0<=ab => fsize m0<=ab => ROE.m{m}=m0 =>
 0%r<fresh_f_accept_mass => 0%r<fresh_g_accept_mass =>
 0%r <= 1%r-Pr[CountedKeygen(UniformSeedRNG,ExpandROM).run(witness) @ &m : true]
 <= proposal_delta ab (qf0+qg0)+fresh_retry_tail qf0 qg0.
proof.
 move=> hqf hqg ha hm he hpf hpg.
 have hg := rom_counted_good_lower &m qf0 qg0 ab m0 hqf hqg ha hm he hpf hpg.
 have hb : Pr[CountedKeygen(UniformSeedRNG,ExpandROM).run(witness) @ &m : true]<=1%r
   by smt(mu_bounded).
 have hs : Pr[CountedKeygen(UniformSeedRNG,ExpandROM).run(witness) @ &m :
   counted_within qf0 qg0 res] <=
   Pr[CountedKeygen(UniformSeedRNG,ExpandROM).run(witness) @ &m : true]
   by rewrite Pr[mu_sub].
 exact (subdistribution_missing_mass _ _ _ hb hs hg).
qed.

(* The two terms on the left distinguish late returns from nontermination. *)
lemma rom_counted_late_or_divergent &m qf0 qg0 ab m0 :
 0<=qf0 => 0<=qg0 => 0<=ab => fsize m0<=ab => ROE.m{m}=m0 =>
 0%r<fresh_f_accept_mass => 0%r<fresh_g_accept_mass =>
 (Pr[CountedKeygen(UniformSeedRNG,ExpandROM).run(witness) @ &m : !counted_within qf0 qg0 res] +
   (1%r-Pr[CountedKeygen(UniformSeedRNG,ExpandROM).run(witness) @ &m : true]) =
   1%r-Pr[CountedKeygen(UniformSeedRNG,ExpandROM).run(witness) @ &m : counted_within qf0 qg0 res]) /\
 0%r <= 1%r-Pr[CountedKeygen(UniformSeedRNG,ExpandROM).run(witness) @ &m : counted_within qf0 qg0 res]
 <= proposal_delta ab (qf0+qg0)+fresh_retry_tail qf0 qg0.
proof.
 move=> hqf hqg ha hm he hpf hpg.
 have hg := rom_counted_good_lower &m qf0 qg0 ab m0 hqf hqg ha hm he hpf hpg.
 split.
 + rewrite Pr[mu_not]; smt().
 smt(mu_bounded).
qed.

lemma counted_instrumented_probability (E<:KeygenExpand {-ROF}) &m
 (event:keygen_output -> bool) :
 Pr[CountedKeygen(UniformSeedRNG,E).run(witness) @ &m : event res.`1] =
 Pr[KeygenInstrumented(UniformSeedRNG,E,SHAKEFROM).run(witness) @ &m : event res].
proof. by byequiv (counted_keygen_erasure UniformSeedRNG E) => //. qed.

(* Public theorem refers to the unchanged, pre-existing implementation.
   The memory premise records the cache present before the first attempt. *)
lemma keygen_rom_fresh_distance &m qf0 qg0 ab m0 (event:keygen_output -> bool) :
 0<=qf0 => 0<=qg0 => 0<=ab => fsize m0<=ab => ROE.m{m}=m0 =>
 0%r<fresh_f_accept_mass => 0%r<fresh_g_accept_mass =>
 `|Pr[KeygenInstrumented(UniformSeedRNG,ExpandROM,SHAKEFROM).run(witness) @ &m : event res] -
   Pr[KeygenInstrumented(UniformSeedRNG,FreshExpand,SHAKEFROM).run(witness) @ &m : event res]|
 <= proposal_delta ab (qf0+qg0)+fresh_retry_tail qf0 qg0.
proof.
 move=> hqf hqg ha hm he hpf hpg.
 have h := counted_rom_fresh_distance &m qf0 qg0 ab m0 event hqf hqg ha hm he hpf hpg.
 rewrite (counted_instrumented_probability ExpandROM &m event)
   (counted_instrumented_probability FreshExpand &m event) in h.
 exact h.
qed.
lemma keygen_rom_missing_mass &m qf0 qg0 ab m0 :
 0<=qf0 => 0<=qg0 => 0<=ab => fsize m0<=ab => ROE.m{m}=m0 =>
 0%r<fresh_f_accept_mass => 0%r<fresh_g_accept_mass =>
 0%r <= 1%r-Pr[KeygenInstrumented(UniformSeedRNG,ExpandROM,SHAKEFROM).run(witness) @ &m : true]
 <= proposal_delta ab (qf0+qg0)+fresh_retry_tail qf0 qg0.
proof.
 move=> hqf hqg ha hm he hpf hpg.
 have h := rom_counted_missing_mass &m qf0 qg0 ab m0 hqf hqg ha hm he hpf hpg.
 have hp := counted_instrumented_probability ExpandROM &m (fun (_:keygen_output) => true).
 rewrite /= in hp; smt().
qed.

lemma keygen_public_instrumented_probability (E<:KeygenExpand {-ROF}) &m
 (event:W8.t Array1152.t * W8.t Array2336.t -> bool) :
 Pr[Keygen(UniformSeedRNG,E,SHAKEFROM).run() @ &m : event res] =
 Pr[KeygenInstrumented(UniformSeedRNG,E,SHAKEFROM).run(witness) @ &m :
   event (res.`1.`kg_pk,res.`1.`kg_sk)].
proof.
 byequiv (_: ={glob E,glob ROF} /\ workspace{2}=witness ==>
   res{1}=(res.`1.`kg_pk,res.`1.`kg_sk){2}) => //.
 proc; inline KeygenInstrumented(UniformSeedRNG,E,SHAKEFROM).run.
 wp; conseq (_: _ ==> ={pk,sk}) => //.
 sim (: ={glob E,glob ROF}); auto.
qed.

lemma keygen_public_rom_fresh_distance &m qf0 qg0 ab m0
 (event:W8.t Array1152.t * W8.t Array2336.t -> bool) :
 0<=qf0 => 0<=qg0 => 0<=ab => fsize m0<=ab => ROE.m{m}=m0 =>
 0%r<fresh_f_accept_mass => 0%r<fresh_g_accept_mass =>
 `|Pr[Keygen(UniformSeedRNG,ExpandROM,SHAKEFROM).run() @ &m : event res] -
   Pr[Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run() @ &m : event res]|
 <= proposal_delta ab (qf0+qg0)+fresh_retry_tail qf0 qg0.
proof.
 move=> hqf hqg ha hm he hpf hpg.
 have h := keygen_rom_fresh_distance &m qf0 qg0 ab m0
   (fun (out:keygen_output) => event(out.`1.`kg_pk,out.`1.`kg_sk)) hqf hqg ha hm he hpf hpg.
 rewrite -(keygen_public_instrumented_probability ExpandROM &m event)
   -(keygen_public_instrumented_probability FreshExpand &m event) in h.
 exact h.
qed.
