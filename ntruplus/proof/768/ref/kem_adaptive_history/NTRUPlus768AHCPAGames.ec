require import AllCore List Distr DBool FMap SDist.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152.
require import NTRUPlus768CPAModel NTRUPlus768CPAReduction.
require import NTRUPlus768SecModel NTRUPlus768SecChallengeBridge.
require import NTRUPlus768SimModel NTRUPlus768SimLookup NTRUPlus768SimSampling.
require import NTRUPlus768FOModel NTRUPlus768FOEagerG NTRUPlus768FOGAdapters.
require import NTRUPlus768FOGCompletion NTRUPlus768FOJointGames.
require import NTRUPlus768FOSetupDistribution NTRUPlus768ACWC2Oracle.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions.
require import NTRUPlus768RawXOFStreams NTRUPlus768RawXOF NTRUPlus768CCAGame.
require import NTRUPlus768CCADecapOracle NTRUPlus768CCAOraclePorts.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768FreshRetryLaw.
require import NTRUPlus768StoppedKeygenModel.

(* The challenge and every later direct/raw/internal G call use one port.
   The reduction's two messages and final H-membership answer are retained. *)
module AHCPAContext(A:CCAExtendedAdversary,G:FOGPort) = {
 proc run(out:keygen_output):bool = {
  var target,other:W8.t Array96.t;var bit,guess:bool;
  var hout:W8.t Array224.t;var enc:W8.t Array1152.t option;
  target<$uniform96;other<$uniform96;bit<$dbool;hout<$uniform224;
  enc<@SimEncrypt(G).run(out.`1.`kg_pk,if bit then other else target,hout);
  guess<@SecRun(A,G).run(out.`1.`kg_pk,oget enc,target);
  return guess=bit;
 }
}.
module AHCPAEagerGame(A:CCAExtendedAdversary)=FOGEagerGame(AHCPAContext(A)).
module AHCPAKernel(A:CCAExtendedAdversary) = {
 proc guess(s:fo_setup_observation):bool = {
  var win:bool;
  ROE.init();ROG.init();ROH.init();RawXOFStreams.init();
  ROF.m<-s.`2;ROG.m<-acwc2_g_cache s.`3;
  win<@AHCPAContext(A,FOGActual).run(s.`1);
  return win;
 }
}.
module AHCPAJointGame(A:CCAExtendedAdversary) = {
 proc run():bool = {
  var s:fo_setup_observation;var win:bool;
  s<@FOSetupSource.guess(witness);win<@AHCPAKernel(A).guess(s);
  return win;
 }
}.

lemma ah_cpa_setup_actual
 (A<:CCAExtendedAdversary {-CPAReduction,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,
  -CCADecapOracle,-SimPublic,-SimHistory,-FOGRO.RO,-FOGRO.FRO}) :
 equiv[CPAGame(CPAReduction(A)).run ~ FOGSetupGame(AHCPAContext(A)).run:
 ={glob A,glob SimPublic,SimHistory.h} ==> ={res,glob A}].
proof.
 proc;inline{1} CPAReduction(A).choose CPACipher.run;
 inline{2} AHCPAContext(A,FOGActual).run.
 wp;call(sec_reduction_run A).
 wp;call(_: ={arg,ROG.m} ==> ={res,ROG.m});first by sim.
 rnd;wp;rnd;wp;rnd;wp;rnd;wp.
 inline{1} Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run;wp.
 call(_: ={workspace,ROF.m} ==> ={res,ROF.m});first by sim.
 inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init CCADecapOracle.reset.
 auto.
qed.

lemma ah_cpa_setup_eager
 (A<:CCAExtendedAdversary {-CPAReduction,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,
  -CCADecapOracle,-SimPublic,-SimHistory,-FOGRO.RO,-FOGRO.FRO}) :
 equiv[AHCPAEagerGame(A).run ~ FOGSetupGame(AHCPAContext(A)).run:
 ={glob A,glob SimPublic,SimHistory.h} ==> ={res,glob A}].
proof.
 proc;call(fo_g_actual_partial_eager (AHCPAContext(A))).
 call(_: ={workspace,ROF.m} ==> ={res,ROF.m});first by sim.
 inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init CCADecapOracle.reset.
 auto.
qed.

lemma ah_cpa_eager_probability
 (A<:CCAExtendedAdversary {-CPAReduction,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,
  -CCADecapOracle,-SimPublic,-SimHistory,-FOGRO.RO,-FOGRO.FRO}) &m (event:bool->bool) :
 Pr[CPAGame(CPAReduction(A)).run()@&m:event res]=
 Pr[AHCPAEagerGame(A).run()@&m:event res].
proof.
 have ha:Pr[CPAGame(CPAReduction(A)).run()@&m:event res]=
  Pr[FOGSetupGame(AHCPAContext(A)).run()@&m:event res]
  by byequiv(ah_cpa_setup_actual A)=> //.
 rewrite ha;apply/eq_sym;byequiv(ah_cpa_setup_eager A)=> //.
qed.

lemma ah_cpa_context_same
 (A<:CCAExtendedAdversary {-CPAReduction,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,
  -CCADecapOracle,-SimPublic,-SimHistory,-FOGRO.RO,-FOGRO.FRO}) :
 equiv[AHCPAContext(A,FOGActual).run ~ AHCPAContext(A,FOGActual).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h} ==>
 ={res,glob A}].
proof. proc;sim. qed.

lemma ah_cpa_eager_joint
 (A<:CCAExtendedAdversary {-CPAReduction,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,
  -CCADecapOracle,-SimPublic,-SimHistory,-FOGRO.RO,-FOGRO.FRO}) :
 equiv[AHCPAEagerGame(A).run ~ AHCPAJointGame(A).run:
 ={glob A,glob SimPublic,SimHistory.h} ==> ={res,glob A}].
proof.
 proc.
 inline{1} FOGPreparedContext(AHCPAContext(A)).run FOGIIDSetup.run ACWC2EagerOracle.prepare.
 inline{2} FOSetupSource.guess FOSetupKeySource.guess AHCPAKernel(A).guess.
 wp;call(ah_cpa_context_same A).
 inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init CCADecapOracle.reset.
 wp;rnd;wp.
 call(_: ={workspace,ROF.m} ==> ={res,ROF.m});first by sim.
 auto=> />;smt(fo_g_cache_empty_join).
qed.

lemma ah_cpa_kernel_initial
 (A<:CCAExtendedAdversary {-CPAReduction,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,
  -CCADecapOracle,-SimPublic,-SimHistory,-FOGRO.RO,-FOGRO.FRO}) :
 equiv[AHCPAKernel(A).guess ~ AHCPAKernel(A).guess:
 ={s,glob A,glob SimPublic,SimHistory.h} ==> ={res,glob A}].
proof.
 proc;call(ah_cpa_context_same A).
 inline ROE.init ROG.init ROH.init RawXOFStreams.init;auto.
qed.

lemma ah_cpa_joint_reified
 (A<:CCAExtendedAdversary {-CPAReduction,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,
  -CCADecapOracle,-SimPublic,-SimHistory,-FOGRO.RO,-FOGRO.FRO}) &m :
 Pr[AHCPAJointGame(A).run()@&m:res]=
 Pr[FOJointDist.Sample(AHCPAKernel(A)).main
  (mk(fun s=>Pr[FOSetupSource.guess(witness)@&m:res=s]))@&m:res].
proof.
 byequiv(_: ROF.m{1}=ROF.m{m} /\ ={glob A,glob SimPublic,SimHistory.h} /\
 d{2}=mk(fun s=>Pr[FOSetupSource.guess(witness)@&m:res=s]) ==> ={res})=> //.
 proc;call(ah_cpa_kernel_initial A).
 outline{2} 1 ~ FOSetupDist.S.sample.
 call(fo_setup_source_sample FOSetupSource &m witness);auto.
qed.

lemma ah_cpa_actual_mu
 (A<:CCAExtendedAdversary {-CPAReduction,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,
  -CCADecapOracle,-SimPublic,-SimHistory,-FOGRO.RO,-FOGRO.FRO}) &m :
 Pr[CPAGame(CPAReduction(A)).run()@&m:res]=
 mu1(dlet(mk(fun s=>Pr[FOSetupSource.guess(witness)@&m:res=s]))
  (fun s=>mk(fun b=>Pr[AHCPAKernel(A).guess(s)@&m:res=b])))true.
proof.
 rewrite(ah_cpa_eager_probability A &m (fun b=>b)) /=.
 have he:Pr[AHCPAEagerGame(A).run()@&m:res]=Pr[AHCPAJointGame(A).run()@&m:res]
  by byequiv(ah_cpa_eager_joint A)=> //.
 rewrite he(ah_cpa_joint_reified A &m).
 exact(FOJointDist.Sample_dlet (AHCPAKernel(A)) &m _).
qed.
