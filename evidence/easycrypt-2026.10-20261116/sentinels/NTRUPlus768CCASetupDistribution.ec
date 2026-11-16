

lemma __cca_setup_eof_6 (E1<:KeygenExpand) (E2<:KeygenExpand) &m eps :
 (forall (event:cca_setup_state->bool),
  `|Pr[JointSetupSource(E1).guess(witness) @ &m:event res]-
    Pr[JointSetupSource(E2).guess(witness) @ &m:event res]|<=eps) =>
 sdist (mk(fun z=>Pr[JointSetupSource(E1).guess(witness) @ &m:res=z]))
       (mk(fun z=>Pr[JointSetupSource(E2).guess(witness) @ &m:res=z])) <= eps.
proof. exact (cca_setup_event_sdist E1 E2 &m eps). qed.
