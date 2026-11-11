require import AllCore Distr DBool FMap.
from Jasmin require import JWord.
require import Array32 Array1152 Array2336.
require import NTRUPlus768SimModel NTRUPlus768SimSampling NTRUPlus768SimAnswer NTRUPlus768SimOracles.
require import NTRUPlus768SimPrefix NTRUPlus768SimPorts NTRUPlus768SimGames NTRUPlus768SimRealBridge.
require import NTRUPlus768FOSetupDistribution NTRUPlus768FOModel NTRUPlus768FOEagerG NTRUPlus768FOGAdapters NTRUPlus768FOProcedures.
require import NTRUPlus768FOKEMGame NTRUPlus768FOJointGames NTRUPlus768FOChallengeBridge.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions NTRUPlus768RawXOF NTRUPlus768RawXOFStreams.
require import NTRUPlus768CCAGame NTRUPlus768CCADecapOracle NTRUPlus768CCAOraclePorts.

module SimObservedDirectRealKernel(A:CCAExtendedAdversary) = {
 proc guess(s:fo_setup_observation) : bool = {
  var win;
  SimObservedSetup.run(s);
  win<@SimDirectPhase(A,SimOracles(FOGActual,SimHActual),SimRealDecap(FOGActual,SimHActual)).distinguish(s);
  return win;
 }
}.

lemma sim_leak_real_complete :
 equiv[SimLeakDecaps(SimLeaksBackend(FOGActual,SimHActual),SimAnswerReal(FOGActual,SimHActual)).decap ~
 SimRealDecap(FOGActual,SimHActual).decap:
 ={ct,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,glob FOContext,CCADecapOracle.sk} ==>
 ={res,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,glob FOContext,CCADecapOracle.sk}].
proof.
 proc;inline{1} SimLeaksBackend(FOGActual,SimHActual).leaks;sp.
 match{1};1..5:by exfalso=> />;smt().
 inline{1} SimPrepare(FOGActual,SimHActual).run.
 inline{2} SimCore(FOGActual,SimAnswerReal(FOGActual,SimHActual)).run.
 sp;if;first by auto=> />;smt().
 + sp 0 3.
   seq 1 2:(request0{1}=request{2} /\ result{1}=None /\ result{2}=None /\
    ={ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,glob FOContext,CCADecapOracle.sk}).
   - wp;call(_: ={arg,ROG.m} ==> ={res,ROG.m});first by sim.
     auto=> />;smt().
   if;first by auto.
   - sp 1 0;if{1}.
     + rcondf{1} 7.
       - move=> &m;wp;call(_:true ==>true);first by trivial. auto=> />;rewrite /sim_out_decap;done.
       wp;call(_: ={arg,ROG.m,ROH.m} ==> ={res,ROG.m,ROH.m});first by sim.
       auto=> />;rewrite /sim_out_decap;auto.
     rcondt{1} 5;first by auto=> />;rewrite /sim_out_decap;auto.
     wp;call(_: ={arg,ROG.m,ROH.m} ==> ={res,ROG.m,ROH.m});first by sim.
     auto=> />;rewrite /sim_out_decap;auto.
   rcondf{1} 5;first by auto=> />;rewrite /sim_out_decap;auto.
   auto=> />;rewrite /sim_out_decap;auto.
 rcondf{1} 5;first by auto=> />;rewrite /sim_out_decap;auto.
 auto=> />;rewrite /sim_out_decap;auto.
qed.

lemma sim_leak_e_complete :
 equiv[SimLeakHashes(SimLeaksBackend(FOGActual,SimHActual)).e ~ SimOracles(FOGActual,SimHActual).e:
 ={arg,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,glob FOContext,glob CCADecapOracle,FOPublicKey.pk,glob SimBad,glob SimPhaseInput} ==> ={res,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,glob FOContext,glob CCADecapOracle,FOPublicKey.pk,glob SimBad,glob SimPhaseInput}].
proof.
 proc*;inline{1} SimLeakHashes(SimLeaksBackend(FOGActual,SimHActual)).e SimLeaksBackend(FOGActual,SimHActual).leaks;sp;wp.
 match{1};2,3,4,5,6:by exfalso=> />;smt().
 wp;call(_: ={arg,glob ROE} ==> ={res,glob ROE});first by sim.
 auto=> />;rewrite /sim_out192;smt().
qed.

lemma sim_leak_f_complete :
 equiv[SimLeakHashes(SimLeaksBackend(FOGActual,SimHActual)).f ~ SimOracles(FOGActual,SimHActual).f:
 ={arg,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,glob FOContext,glob CCADecapOracle,FOPublicKey.pk,glob SimBad,glob SimPhaseInput} ==> ={res,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,glob FOContext,glob CCADecapOracle,FOPublicKey.pk,glob SimBad,glob SimPhaseInput}].
proof.
 proc*;inline{1} SimLeakHashes(SimLeaksBackend(FOGActual,SimHActual)).f SimLeaksBackend(FOGActual,SimHActual).leaks;sp;wp.
 match{1};1,3,4,5,6:by exfalso=> />;smt().
 wp;call(_: ={arg,glob ROF} ==> ={res,glob ROF});first by sim.
 auto=> />;rewrite /sim_out32;smt().
qed.

lemma sim_leak_g_complete :
 equiv[SimLeakHashes(SimLeaksBackend(FOGActual,SimHActual)).g ~ SimOracles(FOGActual,SimHActual).g:
 ={arg,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,glob FOContext,glob CCADecapOracle,FOPublicKey.pk,glob SimBad,glob SimPhaseInput} ==> ={res,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,glob FOContext,glob CCADecapOracle,FOPublicKey.pk,glob SimBad,glob SimPhaseInput}].
proof.
 proc*;inline{1} SimLeakHashes(SimLeaksBackend(FOGActual,SimHActual)).g SimLeaksBackend(FOGActual,SimHActual).leaks;sp;wp.
 match{1};1,2,4,5,6:by exfalso=> />;smt().
 wp;call(_: ={arg,glob ROG} ==> ={res,glob ROG});first by sim.
 auto=> />;rewrite /sim_out192;smt().
qed.

lemma sim_leak_h_complete :
 equiv[SimLeakHashes(SimLeaksBackend(FOGActual,SimHActual)).h ~ SimOracles(FOGActual,SimHActual).h:
 ={arg,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,glob FOContext,glob CCADecapOracle,FOPublicKey.pk,glob SimBad,glob SimPhaseInput} ==> ={res,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,glob FOContext,glob CCADecapOracle,FOPublicKey.pk,glob SimBad,glob SimPhaseInput}].
proof.
 proc*;inline{1} SimLeakHashes(SimLeaksBackend(FOGActual,SimHActual)).h SimLeaksBackend(FOGActual,SimHActual).leaks;sp;wp.
 match{1};1,2,3,5,6:by exfalso=> />;smt().
 wp;call(_: ={arg,glob ROH,SimHistory.h} ==> ={res,glob ROH,SimHistory.h});first by sim.
 auto=> />;rewrite /sim_out224;smt().
qed.

lemma sim_leak_raw_complete :
 equiv[SimLeakHashes(SimLeaksBackend(FOGActual,SimHActual)).raw ~ SimOracles(FOGActual,SimHActual).raw:
 ={arg,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,glob FOContext,glob CCADecapOracle,FOPublicKey.pk,glob SimBad,glob SimPhaseInput} ==> ={res,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,glob FOContext,glob CCADecapOracle,FOPublicKey.pk,glob SimBad,glob SimPhaseInput}].
proof.
 proc*;inline{1} SimLeakHashes(SimLeaksBackend(FOGActual,SimHActual)).raw SimLeaksBackend(FOGActual,SimHActual).leaks;sp;wp.
 match{1};1,2,3,4,6:by exfalso=> />;smt().
 wp;call(_: ={arg,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SimHistory.h} ==> ={res,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SimHistory.h});first by sim.
 auto=> />;rewrite /sim_out_raw;smt().
qed.

lemma sim_real_phase_projection
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOContext,-SimPublic,-SimHistory,-SimBad,-SimPhaseInput}) :
 equiv[SimAdaptive(A,SimLeaksBackend(FOGActual,SimHActual),SimAnswerReal(FOGActual,SimHActual)).distinguish ~
 SimDirectPhase(A,SimOracles(FOGActual,SimHActual),SimRealDecap(FOGActual,SimHActual)).distinguish:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,glob FOContext,glob CCADecapOracle,FOPublicKey.pk,glob SimBad,glob SimPhaseInput} ==>
 ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,glob FOContext,glob CCADecapOracle,FOPublicKey.pk,glob SimBad,glob SimPhaseInput}].
proof.
 proc;call(_: ={ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,glob FOContext,glob CCADecapOracle,FOPublicKey.pk,glob SimBad,glob SimPhaseInput}).
 + conseq sim_leak_e_complete;smt().
 + conseq sim_leak_f_complete;smt().
 + conseq sim_leak_g_complete;smt().
 + conseq sim_leak_h_complete;smt().
 + conseq sim_leak_raw_complete;smt().
 + conseq sim_leak_real_complete;smt().
 auto=> />;smt().
qed.

lemma sim_observed_real_direct
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOContext,-SimPublic,-SimHistory,-SimBad,-SimPhaseInput}) :
 equiv[SimObservedRealKernel(A).guess ~ SimObservedDirectRealKernel(A).guess:
 ={s,glob A} ==> ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,CCADecapOracle.sk,CCADecapOracle.cstar,FOPublicKey.pk}].
proof.
 proc;call(sim_real_phase_projection A).
 call(_: ={arg} ==> ={ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,glob FOContext,glob CCADecapOracle,FOPublicKey.pk,glob SimBad,glob SimPhaseInput});first by sim.
 auto.
qed.

lemma sim_observed_direct_plain
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOContext,-SimPublic,-SimHistory,-SimBad,-SimPhaseInput}) :
 equiv[SimObservedDirectRealKernel(A).guess ~ FOPlainKernel(A,FOReencryptDecap(SHAKEGROM,SHAKEHROM)).guess:
 ={s,glob A} ==> ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,CCADecapOracle.sk,CCADecapOracle.cstar,FOPublicKey.pk}].
proof.
 proc;inline{1} SimObservedSetup.run SimDirectPhase(A,SimOracles(FOGActual,SimHActual),SimRealDecap(FOGActual,SimHActual)).distinguish.
 inline{2} FOCCAChallenge(SHAKEGROM,SHAKEHROM,SharedCCAExtendedOracles,FOReencryptDecap(SHAKEGROM,SHAKEHROM),A).run.
 wp;call(_: ={ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,CCADecapOracle.sk,CCADecapOracle.cstar,FOPublicKey.pk} /\
  SimPublic.pk{1}=FOPublicKey.pk{2} /\ SimPublic.cstar{1}=CCADecapOracle.cstar{2}).
 + conseq sim_oracle_e_actual;smt().
 + conseq sim_oracle_f_actual;smt().
 + conseq sim_oracle_g_actual;smt().
 + conseq sim_oracle_h_actual;smt().
 + conseq sim_raw_actual;smt().
 + conseq sim_real_decap_original;smt().
 inline SimPhaseInput.init SimBad.init SimHistory.init SimPublic.init FOPublicKey.init CCADecapOracle.init.
 wp;rnd;rnd.
 call(_: ={arg,ROF.m,ROG.m,ROH.m} ==> ={res,ROF.m,ROG.m,ROH.m}).
 + symmetry;conseq fo_challenge_encap_projection;smt().
 inline FOContext.init ROE.init ROG.init ROH.init RawXOFStreams.init CCADecapOracle.reset;auto.
qed.

lemma sim_observed_real_plain
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOContext,-SimPublic,-SimHistory,-SimBad,-SimPhaseInput}) :
 equiv[SimObservedRealKernel(A).guess ~ FOPlainKernel(A,FOReencryptDecap(SHAKEGROM,SHAKEHROM)).guess:
 ={s,glob A} ==> ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,CCADecapOracle.sk,CCADecapOracle.cstar,FOPublicKey.pk}].
proof.
 transitivity SimObservedDirectRealKernel(A).guess
 (={s,glob A} ==> ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,CCADecapOracle.sk,CCADecapOracle.cstar,FOPublicKey.pk})
 (={s,glob A} ==> ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,CCADecapOracle.sk,CCADecapOracle.cstar,FOPublicKey.pk})=> //.
 + smt().
 + exact(sim_observed_real_direct A).
 exact(sim_observed_direct_plain A).
qed.

lemma sim_observed_real_plain_probability
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOContext,-SimPublic,-SimHistory,-SimBad,-SimPhaseInput}) &m s0 (event:bool->bool) :
 Pr[SimObservedRealKernel(A).guess(s0) @ &m:event res]=
 Pr[FOPlainKernel(A,FOReencryptDecap(SHAKEGROM,SHAKEHROM)).guess(s0) @ &m:event res].
proof. by byequiv(sim_observed_real_plain A)=> //. qed.
