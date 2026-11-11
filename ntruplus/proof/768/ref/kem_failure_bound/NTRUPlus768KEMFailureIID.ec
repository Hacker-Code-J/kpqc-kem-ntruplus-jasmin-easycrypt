require import AllCore Distr.
from Jasmin require import JWord.
require import Array32 Array96.
require import NTRUPlus768KEMFailureModel NTRUPlus768KEMFailureProof.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteProof NTRUPlus768KeygenCompleteRetry.
require import NTRUPlus768KeygenRetryLaw NTRUPlus768KeygenIIDProof.
require import NTRUPlus768EncapCompleteRNG NTRUPlus768EncapCompleteProof NTRUPlus768EncapCompleteHash.
require import NTRUPlus768DecapMessageSpec NTRUPlus768DecapCompleteHash NTRUPlus768DecapCompleteProof.
require import NTRUPlus768EncapClearCoinsProof.

lemma encap_instrumented_lossless (F<:EncapSHAKEF) (G<:MessageSHAKE) (H<:CompleteSHAKEH) (Q<:EncapRNG) :
  islossless Q.sample => islossless F.shake => islossless G.shake => islossless H.shake =>
  islossless EncapRandomInstrumented(F,G,H,Q).run.
proof.
  move=> ql fl gl hl; proc; call encap_clear_coins_lossless;
    call(encap_derand_lossless F G H fl gl hl); wp; call ql; by auto.
qed.

(* Termination is separate from event inclusion. These generic premises may
   be established for a shared stateful RNG; mere termination of each seed
   draw does not imply termination of the rejection loops. *)
lemma correctness_public_lossless (R<:KeygenSeedRNG) (E<:KeygenExpand) (F<:EncapSHAKEF)
    (G<:MessageSHAKE) (H<:CompleteSHAKEH) (Q<:EncapRNG) :
  islossless KeygenRetry(R,E).f => islossless KeygenRetry(R,E).g =>
  islossless Q.sample => islossless F.shake => islossless G.shake => islossless H.shake =>
  islossless KEMCorrectness(R,E,F,G,H,Q).run.
proof.
  move=> fr gr ql fl gl hl; proc; call(complete_lossless G H gl hl);
    call(encap_random_lossless Q F G H ql fl gl hl);
    call(keygen_public_lossless R E F fr gr fl); by auto.
qed.

lemma correctness_instrumented_lossless (R<:KeygenSeedRNG) (E<:KeygenExpand) (F<:EncapSHAKEF)
    (G<:MessageSHAKE) (H<:CompleteSHAKEH) (Q<:EncapRNG) :
  islossless KeygenRetry(R,E).f => islossless KeygenRetry(R,E).g =>
  islossless Q.sample => islossless F.shake => islossless G.shake => islossless H.shake =>
  islossless KEMCorrectnessInstrumented(R,E,F,G,H,Q).run.
proof.
  move=> fr gr ql fl gl hl; proc; call(complete_lossless G H gl hl);
    call(encap_instrumented_lossless F G H Q ql fl gl hl);
    call(keygen_instrumented_lossless R E F fr gr fl); by auto.
qed.

(* Only this specialization assumes IID seed32 draws with fixed law d.
   E and F cannot access that law. The accepted expansion distribution
   remains dmap (dcond d (accept composed with expand0)) expand0, as proved
   by KeygenRetryLaw; no uniform or independent 192-byte proposal is used.
   Q is still arbitrary and may access IIDSeedRNG after KeyGen returns. *)
lemma correctness_iid_public_terminates (E<:KeygenExpand {-IIDSeedRNG}) (F<:EncapSHAKEF {-IIDSeedRNG})
    (G<:MessageSHAKE) (H<:CompleteSHAKEH) (Q<:EncapRNG) d expand0 :
  (forall x,hoare[E.shake:seed=x ==> res=expand0 x]) =>
  islossless E.shake => islossless F.shake => islossless G.shake => islossless H.shake => islossless Q.sample =>
  is_lossless d => 0%r < mu d (keygen_f_seed_accept expand0) => 0%r < mu d (keygen_g_seed_accept expand0) =>
  phoare[KEMCorrectness(IIDSeedRNG,E,F,G,H,Q).run:IIDSeedRNG.law=d ==> true]=1%r.
proof.
  move=> he el fl gl hl ql dll pf pg; proc.
  call(complete_lossless G H gl hl); call(encap_random_lossless Q F G H ql fl gl hl).
  call(keygen_iid_public_terminates E F d expand0 he el fl dll pf pg); by auto.
qed.

lemma correctness_iid_instrumented_terminates (E<:KeygenExpand {-IIDSeedRNG}) (F<:EncapSHAKEF {-IIDSeedRNG})
    (G<:MessageSHAKE) (H<:CompleteSHAKEH) (Q<:EncapRNG) d expand0 :
  (forall x,hoare[E.shake:seed=x ==> res=expand0 x]) =>
  islossless E.shake => islossless F.shake => islossless G.shake => islossless H.shake => islossless Q.sample =>
  is_lossless d => 0%r < mu d (keygen_f_seed_accept expand0) => 0%r < mu d (keygen_g_seed_accept expand0) =>
  phoare[KEMCorrectnessInstrumented(IIDSeedRNG,E,F,G,H,Q).run:IIDSeedRNG.law=d ==> true]=1%r.
proof.
  move=> he el fl gl hl ql dll pf pg; proc.
  call(complete_lossless G H gl hl); call(encap_instrumented_lossless F G H Q ql fl gl hl).
  call(keygen_iid_instrumented_terminates E F d expand0 he el fl dll pf pg); by auto.
qed.

(* Concrete fixed SHAKE functions and a separate arbitrary 96-byte law.
   These closed hash modules cannot alter either RNG law. This explicit
   distribution specialization is not a DRBG-independence assertion. *)
module MathematicalCorrectness = KEMCorrectness(IIDSeedRNG,MathematicalKeygenExpand,MathematicalSHAKEF,
  MathematicalSHAKE,MathematicalSHAKEH,DistributionRNG).
module MathematicalCorrectnessInstrumented = KEMCorrectnessInstrumented(IIDSeedRNG,MathematicalKeygenExpand,
  MathematicalSHAKEF,MathematicalSHAKE,MathematicalSHAKEH,DistributionRNG).

lemma mathematical_correctness_terminates (d:W8.t Array32.t distr) (coinslaw:W8.t Array96.t distr) :
  is_lossless d => is_lossless coinslaw =>
  0%r < mu d (keygen_f_seed_accept keygen_seed_expansion) =>
  0%r < mu d (keygen_g_seed_accept keygen_seed_expansion) =>
  phoare[MathematicalCorrectness.run:IIDSeedRNG.law=d /\ DistributionRNG.law=coinslaw ==> true]=1%r.
proof.
  move=> dll cll pf pg; proc.
  call(complete_lossless MathematicalSHAKE MathematicalSHAKEH mathematical_shake_lossless complete_mathematical_h_lossless).
  inline EncapRandom(MathematicalSHAKEF,MathematicalSHAKE,MathematicalSHAKEH,DistributionRNG).run.
  wp; call encap_clear_coins_lossless.
  call(encap_derand_lossless MathematicalSHAKEF MathematicalSHAKE MathematicalSHAKEH
    encap_mathematical_f_lossless mathematical_shake_lossless complete_mathematical_h_lossless).
  inline DistributionRNG.sample; wp; rnd; wp.
  call(keygen_iid_public_terminates MathematicalKeygenExpand MathematicalSHAKEF d keygen_seed_expansion
    mathematical_keygen_expand_functional mathematical_keygen_expand_lossless encap_mathematical_f_lossless dll pf pg).
  by auto.
qed.

lemma mathematical_correctness_failure_bound &m :
  Pr[MathematicalCorrectness.run() @ &m:res] <=
  Pr[MathematicalCorrectnessInstrumented.run() @ &m:res.`2].
proof.
  exact(correctness_independent_failure_bound IIDSeedRNG DistributionRNG MathematicalKeygenExpand MathematicalSHAKEF MathematicalSHAKE
    MathematicalSHAKEH &m encap_mathematical_f_functional mathematical_shake_functional
    complete_mathematical_h_functional).
qed.

(* Fixed mathematical SHAKE with a shared, arbitrary stateful byte source.
   This bound needs neither IID seed draws nor independent encapsulation
   coins; termination, when needed, is established separately. *)
lemma mathematical_shared_correctness_failure_bound (B<:KEMRNG) &m :
  Pr[KEMCorrectness(KeygenRNGPort(B),MathematicalKeygenExpand,MathematicalSHAKEF,
    MathematicalSHAKE,MathematicalSHAKEH,EncapRNGPort(B)).run() @ &m:res] <=
  Pr[KEMCorrectnessInstrumented(KeygenRNGPort(B),MathematicalKeygenExpand,MathematicalSHAKEF,
    MathematicalSHAKE,MathematicalSHAKEH,EncapRNGPort(B)).run() @ &m:res.`2].
proof.
  exact(correctness_failure_bound B MathematicalKeygenExpand MathematicalSHAKEF MathematicalSHAKE
    MathematicalSHAKEH &m encap_mathematical_f_functional mathematical_shake_functional
    complete_mathematical_h_functional).
qed.

(* Any separately supplied bound on the actual no-wrap event transfers.
   This theorem supplies no numerical DFR and makes no random-oracle or
   IND-CCA claim. Its probabilities use exactly the same initial memory. *)
lemma mathematical_correctness_epsilon (d:W8.t Array32.t distr) (coinslaw:W8.t Array96.t distr) epsilon &m :
  is_lossless d => is_lossless coinslaw =>
  0%r < mu d (keygen_f_seed_accept keygen_seed_expansion) =>
  0%r < mu d (keygen_g_seed_accept keygen_seed_expansion) =>
  IIDSeedRNG.law{m}=d => DistributionRNG.law{m}=coinslaw =>
  Pr[MathematicalCorrectnessInstrumented.run() @ &m:res.`2] <= epsilon =>
  Pr[MathematicalCorrectness.run() @ &m:res] <= epsilon /\
  Pr[MathematicalCorrectness.run() @ &m:true]=1%r.
proof.
  move=> dll cll pf pg hd hc hb; split.
  + have h:=mathematical_correctness_failure_bound &m; smt().
  by byphoare(mathematical_correctness_terminates d coinslaw dll cll pf pg).
qed.
