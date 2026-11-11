require import AllCore Distr FMap DBool.
from Jasmin require import JWord.
require import Array32 Array1152 Array2336.
require import NTRUPlus768SimModel NTRUPlus768SimSampling NTRUPlus768SimPorts NTRUPlus768SimGames NTRUPlus768SimLookup NTRUPlus768SimOracles NTRUPlus768SimSetupBridge.
require import NTRUPlus768FOModel NTRUPlus768FOGAdapters NTRUPlus768FOEagerG NTRUPlus768FOChallengeBridge NTRUPlus768FOChallenge NTRUPlus768FOSetupDistribution.
require import NTRUPlus768NumericalDFRModel.
require import NTRUPlus768ROMOracles NTRUPlus768ROMKeygen NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768DecapCompleteSpec NTRUPlus768EncapCompleteRNG NTRUPlus768ACWC2Oracle.
require import NTRUPlus768CCAGame NTRUPlus768CCADecapOracle NTRUPlus768FOKEMGame NTRUPlus768KEMFailureModel.

lemma sim_lookup_f_cached fm pk suffix :
 phoare[ROF.get:ROF.m=fm /\ input=pk /\ fm.[pk]=Some suffix ==>res=suffix /\ ROF.m=fm]=1%r.
proof. conseq rof_get_ll (rof_get_cached fm pk suffix);smt(). qed.

lemma sim_lookup_encap_observed w g fm gm :
 rom_key_relation w fm=>acwc2_cache_matches g gm=>
 equiv[EncapRandom(SHAKEFROM,FOGHash(FOGActual),SimHShake(SimHActual),UniformCoins).run ~ FOChallengeEncap.run:
 ={pk,workspace,ROF.m,ROG.m,ROH.m} /\ pk{1}=w.`kg_pk /\
 ROF.m{1}=fm /\ ROG.m{1}=gm /\ ROH.m{1}=empty /\ FOContext.w{2}=w /\ FOContext.g{2}=g ==>
 ={res,ROF.m,ROG.m,ROH.m} /\ ROF.m{1}=fm].
proof.
 move=>hk hg.
 transitivity EncapRandom(SHAKEFROM,SHAKEGROM,SHAKEHROM,UniformCoins).run
  (={arg,ROF.m,ROG.m,ROH.m} ==> ={res,ROF.m,ROG.m,ROH.m})
  (={arg,ROF.m,ROG.m,ROH.m} /\ pk{2}=w.`kg_pk /\ ROF.m{2}=fm /\ ROG.m{2}=gm /\ ROH.m{2}=empty /\
   FOContext.w{2}=w /\ FOContext.g{2}=g ==> ={res,ROF.m,ROG.m,ROH.m} /\ ROF.m{1}=fm).
 + smt().
 + smt().
 + by sim.
 conseq fo_challenge_encap_projection _ (sim_challenge_initial_state w g fm gm hk hg);smt().
qed.

lemma sim_lookup_observed_public
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOContext,-SimPublic,-SimHistory,-SimBad,-SimPhaseInput}) s0 :
 fo_setup_valid s0=>
 equiv[SimPublicKernel(A).guess ~ SimObservedLookupKernel(A).guess:
 s{1}=s0 /\ s{2}=s0 /\ ={glob A} ==> ={res,glob A}].
proof.
 move=>hv;have [hk [hclear [hp [hpads hg]]]]:=hv.
 have hf:s0.`2.[s0.`1.`1.`kg_pk]=Some(complete_sk_suffix s0.`1.`1.`kg_sk)
  by move:hk;rewrite /rom_key_relation;smt().
 proc;inline{1} SimPublicChallenge(A,FOGActual,SimHActual).run.
 inline{2} SimObservedSetup.run SimDirectPhase(A,SimOracles(FOGActual,SimHActual),SimLookup(FOGActual)).distinguish.
 inline SimPhaseInput.init SimBad.init SimHistory.init SimPublic.init FOPublicKey.init CCADecapOracle.init.
 wp;call(_: ={ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h});1..6:by sim.
 wp;ecall{1}(sim_lookup_f_cached s0.`2 s0.`1.`1.`kg_pk (complete_sk_suffix s0.`1.`1.`kg_sk)).
 rnd;rnd.
 call(sim_lookup_encap_observed s0.`1.`1 (acwc2_gfun s0.`3) s0.`2 (acwc2_g_cache s0.`3) hk hg).
 inline FOContext.init CCADecapOracle.reset RawXOFStreams.init ROH.init ROG.init ROE.init;auto.
qed.

lemma sim_lookup_observed_public_probability
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOContext,-SimPublic,-SimHistory,-SimBad,-SimPhaseInput})
 s0 &m (event:bool->bool) : fo_setup_valid s0=>
 Pr[SimObservedLookupKernel(A).guess(s0) @ &m:event res]=
 Pr[SimPublicKernel(A).guess(s0) @ &m:event res].
proof. move=>hv;apply/eq_sym;by byequiv(sim_lookup_observed_public A s0 hv)=> //. qed.
