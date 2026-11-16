

lemma __cca_setup_eof_8
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams}) &m :
 `|Pr[CCAOriginalGame(A).run() @ &m:res]-
   Pr[CCAProgrammedFreshGame(A).run() @ &m:res]| < 1%r/(2%r^239).
proof. exact (cca_original_programmed_setup_distance_239 A &m). qed.
