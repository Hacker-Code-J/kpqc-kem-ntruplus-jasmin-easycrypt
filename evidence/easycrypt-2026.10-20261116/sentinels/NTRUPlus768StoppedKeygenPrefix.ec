
lemma __stopped_prefix_eof (R <: KeygenSeedRNG {-ROF,-PrefixBad})
 (E <: KeygenExpand {-ROF,-PrefixBad,-R}) (qf0 qg0:int)
 (w:W8.t Array14466.t) (event:keygen_output -> bool) &m :
 0<=qf0 => 0<=qg0 => islossless R.sample => islossless E.shake =>
 Pr[CountedKeygen(R,E).run(w) @ &m : (res.`2<=qf0 /\ res.`3<=qg0) /\ event res.`1] =
 Pr[StoppedKeygen(R,E).run(qf0,qg0,w) @ &m : res.`1<>None /\ event (oget res.`1)].
proof. exact (counted_stopped_prefix_nonnegative R E qf0 qg0 w event &m). qed.
