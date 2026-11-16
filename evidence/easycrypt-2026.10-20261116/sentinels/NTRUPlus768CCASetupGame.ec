

lemma __cca_setup_eof_7
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams}) &m :
 Pr[CCASharedSetupGame(ProgrammedFreshExpand,A).run() @ &m:res]=
 Pr[CCASetupObserverDist.Sample(CCASetupObserver(A)).main(
  mk(fun z=>Pr[JointSetupSource(ProgrammedFreshExpand).guess(witness) @ &m:res=z])) @ &m:res].
proof. exact (cca_setup_game_reified_programmed A &m). qed.
