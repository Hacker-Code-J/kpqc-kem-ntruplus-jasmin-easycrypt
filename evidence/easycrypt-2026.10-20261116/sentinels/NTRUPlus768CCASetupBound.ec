

lemma __cca_setup_eof_5 &m (event:cca_setup_state->bool) :
 `|Pr[JointSetupSource(ExpandROM).guess(witness) @ &m:event res]-
   Pr[JointSetupSource(ProgrammedFreshExpand).guess(witness) @ &m:event res]|
 <1%r/(2%r^239).
proof. exact (cca_setup_source_distance_239 &m event). qed.
