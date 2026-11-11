require import AllCore Distr FMap SDist.
from Jasmin require import JWord.
require import NTRUPlus768SimGames NTRUPlus768SimModel NTRUPlus768SimSampling NTRUPlus768SimOracles NTRUPlus768SimLookup.
require import NTRUPlus768FOGAdapters NTRUPlus768FOGCompletion NTRUPlus768FOEagerG NTRUPlus768FOJointGames.
require import NTRUPlus768FOSetupDistribution NTRUPlus768ACWC2Oracle.
require import NTRUPlus768ROMOracles NTRUPlus768ROMKeygen NTRUPlus768NumericalDFRModel.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768FreshRetryLaw NTRUPlus768StoppedKeygenModel.
require import NTRUPlus768CCAGame NTRUPlus768CCAOraclePorts NTRUPlus768CCADecapOracle NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.

(* G is completed only on the finite trit image. The public simulator still
   receives ordinary query ports, and may be a partial computation. *)
lemma sim_public_setup_eager
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-SimPublic,-SimHistory,-FOGRO.RO,-FOGRO.FRO}) :
 equiv[SimPublicEagerGame(A).run ~ FOGSetupGame(SimPublicGContext(A)).run:
 ={glob A,glob SimPublic,glob SimHistory} ==> ={res,glob A}].
proof.
 proc; call(fo_g_actual_partial_eager (SimPublicGContext(A))).
 call(_: ={workspace,ROF.m} ==> ={res,ROF.m}); first by sim.
 inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init CCADecapOracle.reset; auto.
qed.

lemma sim_public_context_challenge
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-SimPublic,-SimHistory,-FOGRO.RO,-FOGRO.FRO}) :
 equiv[SimPublicGContext(A,FOGActual).run ~ SimPublicChallenge(A,FOGActual,SimHActual).run:
 out{1}.`1.`kg_pk=pk{2} /\
 ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams} ==>
 ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,glob SimHistory}].
proof.
 proc.
 inline{1} SimPublicChallenge(A,FOGActual,SimHActual).run.
 wp.
 call(_: ={ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,
   SimPublic.pk,SimPublic.suffix,SimPublic.cstar,SimPublic.count,SimHistory.h}); 1..6:by sim.
 inline SimPublic.init SimHistory.init; wp.
 call(_: ={input,ROF.m} ==> ={res,ROF.m}); first by sim.
 rnd; rnd.
 call(_: ={pk,workspace,ROF.m,ROG.m,ROH.m} ==> ={res,ROF.m,ROG.m,ROH.m}); first by sim.
 auto.
qed.

lemma sim_public_game_actual
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-SimPublic,-SimHistory,-FOGRO.RO,-FOGRO.FRO}) :
 equiv[FOGSetupGame(SimPublicGContext(A)).run ~ SimPublicFreshGame(A).run:
 ={glob A} ==> ={res,glob A}].
proof.
 proc; call(sim_public_context_challenge A).
 inline{2} Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run; wp.
 call(_: ={workspace,ROF.m} ==> ={res,ROF.m}); first by sim.
 inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init CCADecapOracle.reset; auto.
qed.

lemma sim_public_eager_probability
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-SimPublic,-SimHistory,-FOGRO.RO,-FOGRO.FRO}) &m (event:bool->bool) :
 Pr[SimPublicFreshGame(A).run() @ &m:event res]=
 Pr[SimPublicEagerGame(A).run() @ &m:event res].
proof.
 have he:Pr[SimPublicEagerGame(A).run() @ &m:event res]=
   Pr[FOGSetupGame(SimPublicGContext(A)).run() @ &m:event res].
 + by byequiv(sim_public_setup_eager A)=> //.
 rewrite he; apply/eq_sym; by byequiv(sim_public_game_actual A)=> //.
qed.

(* The joint observation retains the actual fresh key and its F cache.
   Only the independent G pads are sampled after that complete observation. *)
lemma sim_public_eager_joint
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-SimPublic,-SimHistory,-FOGRO.RO,-FOGRO.FRO}) :
 equiv[SimPublicEagerGame(A).run ~ SimPublicJointGame(A).run:
 ={glob A} ==> ={res,glob A}].
proof.
 proc.
 inline{1} FOGPreparedContext(SimPublicGContext(A)).run FOGIIDSetup.run ACWC2EagerOracle.prepare.
 inline{2} FOSetupSource.guess FOSetupKeySource.guess SimPublicKernel(A).guess.
 wp; call(sim_public_context_challenge A).
 inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init CCADecapOracle.reset.
 wp; rnd; wp.
 call(_: ={workspace,ROF.m} ==> ={res,ROF.m}); first by sim.
 auto=> />; smt(fo_g_cache_empty_join).
qed.

lemma sim_public_kernel_initial_state
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-SimPublic,-SimHistory,-FOGRO.RO,-FOGRO.FRO}) :
 equiv[SimPublicKernel(A).guess ~ SimPublicKernel(A).guess:
 ={s,glob A} ==> ={res,glob A}].
proof.
 proc; call(_: ={pk,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams} ==> ={res,glob A}); first by sim.
 inline ROE.init ROG.init ROH.init RawXOFStreams.init; auto.
qed.

lemma sim_public_joint_reified
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-SimPublic,-SimHistory,-FOGRO.RO,-FOGRO.FRO}) &m (event:bool->bool) :
 Pr[SimPublicJointGame(A).run() @ &m:event res]=
 Pr[FOJointDist.Sample(SimPublicKernel(A)).main(
  mk(fun s=>Pr[FOSetupSource.guess(witness) @ &m:res=s])) @ &m:event res].
proof.
 byequiv(_: ROF.m{1}=ROF.m{m} /\ ={glob A} /\
 d{2}=mk(fun s=>Pr[FOSetupSource.guess(witness) @ &m:res=s]) ==> ={res})=> //.
 proc; call(sim_public_kernel_initial_state A).
 outline{2} 1 ~ FOSetupDist.S.sample.
 call(fo_setup_source_sample FOSetupSource &m witness); auto.
qed.

lemma sim_public_eager_joint_probability
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-SimPublic,-SimHistory,-FOGRO.RO,-FOGRO.FRO}) &m (event:bool->bool) :
 Pr[SimPublicEagerGame(A).run() @ &m:event res]=
 Pr[SimPublicJointGame(A).run() @ &m:event res].
proof. by byequiv(sim_public_eager_joint A)=> //. qed.

lemma sim_public_joint_mu
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-SimPublic,-SimHistory,-FOGRO.RO,-FOGRO.FRO}) &m :
 Pr[SimPublicJointGame(A).run() @ &m:res]=
 mu1(dlet(mk(fun s=>Pr[FOSetupSource.guess(witness) @ &m:res=s]))
   (fun s=>mk(fun b=>Pr[SimPublicKernel(A).guess(s) @ &m:res=b])))true.
proof.
 rewrite(sim_public_joint_reified A &m (fun b=>b)) /=.
 exact(FOJointDist.Sample_dlet (SimPublicKernel(A)) &m _).
qed.

lemma sim_public_eager_mu
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-SimPublic,-SimHistory,-FOGRO.RO,-FOGRO.FRO}) &m :
 Pr[SimPublicEagerGame(A).run() @ &m:res]=
 mu1(dlet(mk(fun s=>Pr[FOSetupSource.guess(witness) @ &m:res=s]))
   (fun s=>mk(fun b=>Pr[SimPublicKernel(A).guess(s) @ &m:res=b])))true.
proof.
 rewrite(sim_public_eager_joint_probability A &m (fun b=>b)) /=.
 exact(sim_public_joint_mu A &m).
qed.

lemma sim_public_fresh_mu
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-SimPublic,-SimHistory,-FOGRO.RO,-FOGRO.FRO}) &m :
 Pr[SimPublicFreshGame(A).run() @ &m:res]=
 mu1(dlet(mk(fun s=>Pr[FOSetupSource.guess(witness) @ &m:res=s]))
   (fun s=>mk(fun b=>Pr[SimPublicKernel(A).guess(s) @ &m:res=b])))true.
proof.
 rewrite(sim_public_eager_probability A &m (fun b=>b)) /=.
 exact(sim_public_eager_mu A &m).
qed.
