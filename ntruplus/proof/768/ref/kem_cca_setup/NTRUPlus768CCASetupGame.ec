require import AllCore Distr FMap SDist.
from Jasmin require import JWord.
require import Array32 Array192 Array1152 Array2336 Array14466.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteProof.
require import NTRUPlus768FreshRetryLaw NTRUPlus768ROMOracles.
require import NTRUPlus768ROMCorrectness NTRUPlus768CCAGame.
require import NTRUPlus768CCADecapOracle NTRUPlus768RawXOFStreams.
require import NTRUPlus768CCASetupState NTRUPlus768CCASetupDistribution.

(* Both games keep the actual unbounded KeyGen. Only its expansion port
   changes; the existing challenge, raw/typed oracles and decapsulation are
   exactly the same. No fallback outcome is assigned to divergence. *)
module CCASharedSetupGame(E:KeygenExpand,A:CCAExtendedAdversary) = {
 proc run() : bool = {
  var pk:W8.t Array1152.t; var sk:W8.t Array2336.t; var win:bool;
  ROMInit.init(); RawXOFStreams.init(); CCADecapOracle.reset();
  (pk,sk) <@ Keygen(UniformSeedRNG,E,SHAKEFROM).run();
  win <@ CCAChallengeOriginal(A).run(pk,sk);
  return win;
 }
}.
module CCAProgrammedFreshGame(A:CCAExtendedAdversary) =
 CCASharedSetupGame(ProgrammedFreshExpand,A).

(* The snapshot is private proof data. The adversary still receives only
   pk, the challenge ciphertext and the selected challenge key. *)
module CCASetupObserver(A:CCAExtendedAdversary) = {
 proc guess(s:cca_setup_state) : bool = {
  var win:bool;
  ROG.init(); ROH.init(); RawXOFStreams.init(); CCADecapOracle.reset();
  ROE.m <- s.`2; ROF.m <- s.`3;
  win <@ CCAChallengeOriginal(A).run(s.`1.`1.`kg_pk,s.`1.`1.`kg_sk);
  return win;
 }
}.
module CCASetupSequential(E:KeygenExpand,A:CCAExtendedAdversary) = {
 proc run() : bool = {
  var s:cca_setup_state; var win:bool;
  s <@ JointSetupSource(E).guess(witness);
  win <@ CCASetupObserver(A).guess(s);
  return win;
 }
}.

lemma cca_setup_original_equiv
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams}) :
 equiv[CCAOriginalGame(A).run ~ CCASharedSetupGame(ExpandROM,A).run : ={glob A} ==>
  ={res,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob CCADecapOracle,glob RawXOFStreams}].
proof. proc; sim. qed.

lemma cca_setup_sequential_equiv_rom
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams}) :
 equiv[CCASharedSetupGame(ExpandROM,A).run ~ CCASetupSequential(ExpandROM,A).run :
  ={glob ROE,glob A} ==>
  ={res,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob CCADecapOracle,glob RawXOFStreams}].
proof.
 proc; inline CCASetupObserver(A).guess JointSetupSource(ExpandROM).guess JointSetup(ExpandROM).run
  Keygen(UniformSeedRNG,ExpandROM,SHAKEFROM).run
  ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init CCADecapOracle.reset.
 wp; call (_: ={glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob CCADecapOracle,glob RawXOFStreams}); first by sim.
 wp; call (_: ={workspace,glob ROE,glob ROF} ==> ={res,glob ROE,glob ROF}); first by sim.
 auto.
qed.

lemma cca_setup_sequential_reified_rom
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams}) &m :
 Pr[CCASetupSequential(ExpandROM,A).run() @ &m:res]=
 Pr[CCASetupObserverDist.Sample(CCASetupObserver(A)).main(
  mk(fun z=>Pr[JointSetupSource(ExpandROM).guess(witness) @ &m:res=z])) @ &m:res].
proof.
 byequiv (_: (glob ROE){1}=(glob ROE){m} /\ ROE.m{1}=ROE.m{m} /\ ROF.m{1}=ROF.m{m} /\ ={glob A} /\
  d{2}=mk(fun z=>Pr[JointSetupSource(ExpandROM).guess(witness) @ &m:res=z]) ==> ={res}) => //.
 proc; call (_: ={s,glob A} ==> ={res}); first by sim.
 outline{2} 1 ~ CCASetupDist.S.sample.
 call(cca_setup_source_sample (JointSetupSource(ExpandROM)) &m); auto.
qed.

lemma cca_setup_game_reified_rom
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams}) &m :
 Pr[CCASharedSetupGame(ExpandROM,A).run() @ &m:res]=
 Pr[CCASetupObserverDist.Sample(CCASetupObserver(A)).main(
  mk(fun z=>Pr[JointSetupSource(ExpandROM).guess(witness) @ &m:res=z])) @ &m:res].
proof.
 have he:Pr[CCASharedSetupGame(ExpandROM,A).run() @ &m:res]=
  Pr[CCASetupSequential(ExpandROM,A).run() @ &m:res].
 + by byequiv(cca_setup_sequential_equiv_rom A)=> //.
 by rewrite he (cca_setup_sequential_reified_rom A &m).
qed.

lemma cca_setup_sequential_equiv_programmed
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams}) :
 equiv[CCASharedSetupGame(ProgrammedFreshExpand,A).run ~ CCASetupSequential(ProgrammedFreshExpand,A).run :
  ={glob ROE,glob A} ==>
  ={res,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob CCADecapOracle,glob RawXOFStreams}].
proof.
 proc; inline CCASetupObserver(A).guess JointSetupSource(ProgrammedFreshExpand).guess JointSetup(ProgrammedFreshExpand).run
  Keygen(UniformSeedRNG,ProgrammedFreshExpand,SHAKEFROM).run
  ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init CCADecapOracle.reset.
 wp; call (_: ={glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob CCADecapOracle,glob RawXOFStreams}); first by sim.
 wp; call (_: ={workspace,glob ROE,glob ROF} ==> ={res,glob ROE,glob ROF}); first by sim.
 auto.
qed.

lemma cca_setup_sequential_reified_programmed
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams}) &m :
 Pr[CCASetupSequential(ProgrammedFreshExpand,A).run() @ &m:res]=
 Pr[CCASetupObserverDist.Sample(CCASetupObserver(A)).main(
  mk(fun z=>Pr[JointSetupSource(ProgrammedFreshExpand).guess(witness) @ &m:res=z])) @ &m:res].
proof.
 byequiv (_: (glob ROE){1}=(glob ROE){m} /\ ROE.m{1}=ROE.m{m} /\ ROF.m{1}=ROF.m{m} /\ ={glob A} /\
  d{2}=mk(fun z=>Pr[JointSetupSource(ProgrammedFreshExpand).guess(witness) @ &m:res=z]) ==> ={res}) => //.
 proc; call (_: ={s,glob A} ==> ={res}); first by sim.
 outline{2} 1 ~ CCASetupDist.S.sample.
 call(cca_setup_source_sample (JointSetupSource(ProgrammedFreshExpand)) &m); auto.
qed.

lemma cca_setup_game_reified_programmed
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams}) &m :
 Pr[CCASharedSetupGame(ProgrammedFreshExpand,A).run() @ &m:res]=
 Pr[CCASetupObserverDist.Sample(CCASetupObserver(A)).main(
  mk(fun z=>Pr[JointSetupSource(ProgrammedFreshExpand).guess(witness) @ &m:res=z])) @ &m:res].
proof.
 have he:Pr[CCASharedSetupGame(ProgrammedFreshExpand,A).run() @ &m:res]=
  Pr[CCASetupSequential(ProgrammedFreshExpand,A).run() @ &m:res].
 + by byequiv(cca_setup_sequential_equiv_programmed A)=> //.
 by rewrite he (cca_setup_sequential_reified_programmed A &m).
qed.

lemma cca_original_setup_probability
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams}) &m :
 Pr[CCAOriginalGame(A).run() @ &m:res]=
 Pr[CCASharedSetupGame(ExpandROM,A).run() @ &m:res].
proof. by byequiv(cca_setup_original_equiv A)=> //. qed.
