require import AllCore Distr FMap SDist.
from Jasmin require import JWord.
require import Array192 Array14466.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768FreshRetryLaw.
require import NTRUPlus768ROMOracles NTRUPlus768NumericalDFRModel.
require import NTRUPlus768CCAGame NTRUPlus768CCAOraclePorts NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
require import NTRUPlus768CCADecapOracle NTRUPlus768CCAStatusAdapter NTRUPlus768FOEagerG.
require import NTRUPlus768FOSetupDistribution NTRUPlus768FOGAdapters NTRUPlus768FOKEMGame.
require import NTRUPlus768FOGCompletion NTRUPlus768ACWC2Oracle.

(* The snapshot is private. The adversary receives the same public key,
   challenge and oracle ports, and keeps its original private state. *)
module FOPlainKernel(A:CCAExtendedAdversary,D:CCADecapPort) = {
 proc guess(s:fo_setup_observation) : bool = {
  var win;
  ROE.init(); ROG.init(); ROH.init(); RawXOFStreams.init(); CCADecapOracle.reset();
  ROF.m <- s.`2;
  ROG.m <- acwc2_g_cache s.`3;
  win <@ FOCCAChallenge(SHAKEGROM,SHAKEHROM,SharedCCAExtendedOracles,D,A).run(s.`1.`1.`kg_pk,s.`1.`1.`kg_sk);
  return win;
 }
}.
module FOJointGame(A:CCAExtendedAdversary,D:CCADecapPort) = {
 proc run() : bool = {
  var s:fo_setup_observation; var win;
  s <@ FOSetupSource.guess(witness);
  win <@ FOPlainKernel(A,D).guess(s);
  return win;
 }
}.
module FONativeJointGame(A:CCAExtendedAdversary) =
 FOJointGame(A,FONativeDecap(SHAKEGROM,SHAKEHROM)).
module FOFullJointGame(A:CCAExtendedAdversary) =
 FOJointGame(A,FOReencryptDecap(SHAKEGROM,SHAKEHROM)).
clone SDist.Dist as FOJointDist with type a <- fo_setup_observation proof *.

lemma fo_native_eager_joint
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOGRO.RO,-FOGRO.FRO}) :
 equiv[FOGEagerNativeGame(A).run ~ FONativeJointGame(A).run :
 ={glob A,FOPublicKey.pk} ==> ={res,glob A}].
proof.
 proc.
 inline{1} FOGPreparedContext(FOGNativeContext(A)).run FOGIIDSetup.run ACWC2EagerOracle.prepare.
 inline{2} FOSetupSource.guess FOSetupKeySource.guess FOPlainKernel(A,FONativeDecap(SHAKEGROM,SHAKEHROM)).guess.
 wp; call(fo_g_native_context_challenge A).
 inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init CCADecapOracle.reset.
 wp; rnd; wp.
 call(_: ={workspace,ROF.m} ==> ={res,ROF.m}); first by sim.
 auto=> />; smt(fo_g_cache_empty_join).
qed.

lemma fo_native_kernel_initial_state
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOGRO.RO,-FOGRO.FRO}) :
 equiv[FOPlainKernel(A,FONativeDecap(SHAKEGROM,SHAKEHROM)).guess ~
       FOPlainKernel(A,FONativeDecap(SHAKEGROM,SHAKEHROM)).guess :
 ={s,glob A} ==> ={res,glob A}].
proof.
 proc; call(_: ={pk,sk,glob A,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,
  CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count} ==>
  ={res,glob A}); first by sim.
 inline ROE.init ROG.init ROH.init RawXOFStreams.init CCADecapOracle.reset; auto.
qed.

lemma fo_native_joint_reified
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOGRO.RO,-FOGRO.FRO}) &m (event:bool->bool) :
 Pr[FONativeJointGame(A).run() @ &m:event res]=
 Pr[FOJointDist.Sample(FOPlainKernel(A,FONativeDecap(SHAKEGROM,SHAKEHROM))).main(
  mk(fun s=>Pr[FOSetupSource.guess(witness) @ &m:res=s])) @ &m:event res].
proof.
 byequiv(_: ROF.m{1}=ROF.m{m} /\ ={glob A} /\
 d{2}=mk(fun s=>Pr[FOSetupSource.guess(witness) @ &m:res=s]) ==> ={res})=> //.
 proc; call(fo_native_kernel_initial_state A).
 outline{2} 1 ~ FOSetupDist.S.sample.
 call(fo_setup_source_sample FOSetupSource &m witness); auto.
qed.

lemma fo_full_eager_joint
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOGRO.RO,-FOGRO.FRO}) :
 equiv[FOGEagerFullGame(A).run ~ FOFullJointGame(A).run :
 ={glob A,FOPublicKey.pk} ==> ={res,glob A}].
proof.
 proc.
 inline{1} FOGPreparedContext(FOGFullContext(A)).run FOGIIDSetup.run ACWC2EagerOracle.prepare.
 inline{2} FOSetupSource.guess FOSetupKeySource.guess FOPlainKernel(A,FOReencryptDecap(SHAKEGROM,SHAKEHROM)).guess.
 wp; call(fo_g_full_context_challenge A).
 inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init CCADecapOracle.reset.
 wp; rnd; wp.
 call(_: ={workspace,ROF.m} ==> ={res,ROF.m}); first by sim.
 auto=> />; smt(fo_g_cache_empty_join).
qed.

lemma fo_full_kernel_initial_state
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOGRO.RO,-FOGRO.FRO}) :
 equiv[FOPlainKernel(A,FOReencryptDecap(SHAKEGROM,SHAKEHROM)).guess ~
       FOPlainKernel(A,FOReencryptDecap(SHAKEGROM,SHAKEHROM)).guess :
 ={s,glob A} ==> ={res,glob A}].
proof.
 proc; call(_: ={pk,sk,glob A,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,
  CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count} ==>
  ={res,glob A}); first by sim.
 inline ROE.init ROG.init ROH.init RawXOFStreams.init CCADecapOracle.reset; auto.
qed.

lemma fo_full_joint_reified
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOGRO.RO,-FOGRO.FRO}) &m (event:bool->bool) :
 Pr[FOFullJointGame(A).run() @ &m:event res]=
 Pr[FOJointDist.Sample(FOPlainKernel(A,FOReencryptDecap(SHAKEGROM,SHAKEHROM))).main(
  mk(fun s=>Pr[FOSetupSource.guess(witness) @ &m:res=s])) @ &m:event res].
proof.
 byequiv(_: ROF.m{1}=ROF.m{m} /\ ={glob A} /\
 d{2}=mk(fun s=>Pr[FOSetupSource.guess(witness) @ &m:res=s]) ==> ={res})=> //.
 proc; call(fo_full_kernel_initial_state A).
 outline{2} 1 ~ FOSetupDist.S.sample.
 call(fo_setup_source_sample FOSetupSource &m witness); auto.
qed.

lemma fo_native_eager_joint_probability
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOGRO.RO,-FOGRO.FRO}) &m (event:bool->bool) :
 Pr[FOGEagerNativeGame(A).run() @ &m:event res]=
 Pr[FONativeJointGame(A).run() @ &m:event res].
proof. by byequiv(fo_native_eager_joint A)=> //. qed.

lemma fo_native_joint_mu
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOGRO.RO,-FOGRO.FRO}) &m :
 Pr[FONativeJointGame(A).run() @ &m:res]=
 mu1(dlet(mk(fun s=>Pr[FOSetupSource.guess(witness) @ &m:res=s]))
   (fun s=>mk(fun b=>Pr[FOPlainKernel(A,FONativeDecap(SHAKEGROM,SHAKEHROM)).guess(s) @ &m:res=b])))true.
proof.
 rewrite(fo_native_joint_reified A &m (fun b=>b)) /=.
 exact(FOJointDist.Sample_dlet (FOPlainKernel(A,FONativeDecap(SHAKEGROM,SHAKEHROM))) &m _).
qed.

lemma fo_native_eager_mu
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOGRO.RO,-FOGRO.FRO}) &m :
 Pr[FOGEagerNativeGame(A).run() @ &m:res]=
 mu1(dlet(mk(fun s=>Pr[FOSetupSource.guess(witness) @ &m:res=s]))
   (fun s=>mk(fun b=>Pr[FOPlainKernel(A,FONativeDecap(SHAKEGROM,SHAKEHROM)).guess(s) @ &m:res=b])))true.
proof.
 rewrite(fo_native_eager_joint_probability A &m (fun b=>b)) /=.
 exact(fo_native_joint_mu A &m).
qed.

lemma fo_full_eager_joint_probability
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOGRO.RO,-FOGRO.FRO}) &m (event:bool->bool) :
 Pr[FOGEagerFullGame(A).run() @ &m:event res]=
 Pr[FOFullJointGame(A).run() @ &m:event res].
proof. by byequiv(fo_full_eager_joint A)=> //. qed.

lemma fo_full_joint_mu
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOGRO.RO,-FOGRO.FRO}) &m :
 Pr[FOFullJointGame(A).run() @ &m:res]=
 mu1(dlet(mk(fun s=>Pr[FOSetupSource.guess(witness) @ &m:res=s]))
   (fun s=>mk(fun b=>Pr[FOPlainKernel(A,FOReencryptDecap(SHAKEGROM,SHAKEHROM)).guess(s) @ &m:res=b])))true.
proof.
 rewrite(fo_full_joint_reified A &m (fun b=>b)) /=.
 exact(FOJointDist.Sample_dlet (FOPlainKernel(A,FOReencryptDecap(SHAKEGROM,SHAKEHROM))) &m _).
qed.

lemma fo_full_eager_mu
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOGRO.RO,-FOGRO.FRO}) &m :
 Pr[FOGEagerFullGame(A).run() @ &m:res]=
 mu1(dlet(mk(fun s=>Pr[FOSetupSource.guess(witness) @ &m:res=s]))
   (fun s=>mk(fun b=>Pr[FOPlainKernel(A,FOReencryptDecap(SHAKEGROM,SHAKEHROM)).guess(s) @ &m:res=b])))true.
proof.
 rewrite(fo_full_eager_joint_probability A &m (fun b=>b)) /=.
 exact(fo_full_joint_mu A &m).
qed.
