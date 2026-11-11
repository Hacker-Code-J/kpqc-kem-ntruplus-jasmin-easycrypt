require import AllCore Distr FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array1152 Array2336.
require import NTRUPlus768SimModel NTRUPlus768SimGames NTRUPlus768SimPorts.
require import NTRUPlus768FOModel NTRUPlus768FOChallengeBridge NTRUPlus768FOChallenge NTRUPlus768FOSetupDistribution.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768PKEModel NTRUPlus768PKEAlgebra.
require import NTRUPlus768ROMKeygen.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions NTRUPlus768RawXOFStreams.
require import NTRUPlus768CCADecapOracle NTRUPlus768FOKEMGame NTRUPlus768ACWC2Oracle.
require import NTRUPlus768DecapCompleteSpec NTRUPlus768KEMFailureModel.

lemma sim_challenge_initial_state w g fm gm :
 rom_key_relation w fm=>acwc2_cache_matches g gm=>
 hoare[FOChallengeEncap.run:
 pk=w.`kg_pk /\ FOContext.w=w /\ FOContext.g=g /\ ROF.m=fm /\ ROG.m=gm /\ ROH.m=empty ==>
 FOContext.w=w /\ FOContext.g=g /\ ROF.m=fm /\ ROG.m=gm /\
 fo_challenge_invariant w g FOContext.challenge_h FOContext.challenge_hash FOContext.challenge_ct ROH.m /\
 sim_h_cover empty ROH.m FOContext.challenge_h /\
 FOContext.challenge_ct=res.`1].
proof.
 move=>hk hg;proc;inline FOContext.challenge;wp.
 call(fo_encap_instrumented_witness w g fm gm hk hg).
 auto=> />;rewrite /fo_challenge_invariant /sim_h_cover.
 smt(get_set_sameE mem_set mem_empty).
qed.

(* Every fact needed by the adaptive proof follows from the actual joint
   setup support, before any attacker query. No cached-H independence is
   inferred merely from the absence of a public-history record. *)
lemma sim_observed_setup_state s0 : fo_setup_valid s0=>
 hoare[SimObservedSetup.run:s=s0 ==>
 FOContext.w=s0.`1.`1 /\ FOContext.g=acwc2_gfun s0.`3 /\
 pke_key_relation FOContext.w /\
 SimPublic.pk=FOContext.w.`kg_pk /\ SimPublic.suffix=complete_sk_suffix FOContext.w.`kg_sk /\
 SimPublic.cstar=Some FOContext.challenge_ct /\ SimPublic.count=0 /\
 CCADecapOracle.sk=FOContext.w.`kg_sk /\ CCADecapOracle.cstar=SimPublic.cstar /\ CCADecapOracle.count=0 /\
 FOPublicKey.pk=SimPublic.pk /\ SimHistory.h=empty /\
 !SimBad.hidden /\ !SimBad.corr /\ SimBad.selected_calls=0 /\
 SimPhaseInput.pk=SimPublic.pk /\ SimPhaseInput.ct=FOContext.challenge_ct /\
 acwc2_cache_matches FOContext.g ROG.m /\
 sim_log_included SimHistory.h ROH.m /\
 sim_h_cover SimHistory.h ROH.m FOContext.challenge_h /\
 fo_challenge_invariant FOContext.w FOContext.g FOContext.challenge_h FOContext.challenge_hash FOContext.challenge_ct ROH.m].
proof.
 move=>hv;have [hk [hclear [hp [hpads hg]]]]:=hv.
 proc;inline SimPhaseInput.init SimBad.init SimHistory.init SimPublic.init FOPublicKey.init CCADecapOracle.init.
 wp;rnd;rnd.
 call(sim_challenge_initial_state s0.`1.`1 (acwc2_gfun s0.`3) s0.`2 (acwc2_g_cache s0.`3) hk hg).
 inline FOContext.init CCADecapOracle.reset RawXOFStreams.init ROH.init ROG.init ROE.init;auto=> />.
 move=>result ex hs hm hc hvh random hrandom bit hbit.
 exact(sim_log_empty hm).
qed.

lemma sim_observed_setup_correct s0 : fo_setup_valid s0=>
 phoare[SimObservedSetup.run:s=s0 ==>
 FOContext.w=s0.`1.`1 /\ FOContext.g=acwc2_gfun s0.`3 /\
 pke_key_relation FOContext.w /\ SimPublic.pk=FOContext.w.`kg_pk /\
 SimPublic.suffix=complete_sk_suffix FOContext.w.`kg_sk /\
 SimPublic.cstar=Some FOContext.challenge_ct /\ SimPublic.count=0 /\
 CCADecapOracle.sk=FOContext.w.`kg_sk /\
 SimPhaseInput.pk=SimPublic.pk /\ SimPhaseInput.ct=FOContext.challenge_ct /\
 SimHistory.h=empty /\ !SimBad.hidden /\ !SimBad.corr /\ SimBad.selected_calls=0 /\
 acwc2_cache_matches FOContext.g ROG.m /\ sim_log_included SimHistory.h ROH.m /\
 sim_h_cover SimHistory.h ROH.m FOContext.challenge_h /\
 fo_challenge_invariant FOContext.w FOContext.g FOContext.challenge_h FOContext.challenge_hash FOContext.challenge_ct ROH.m]=1%r.
proof.
 move=>hv;have hh:=sim_observed_setup_state s0 hv.
 clear hv.
 conseq sim_observed_setup_ll hh=> />;smt().
qed.
