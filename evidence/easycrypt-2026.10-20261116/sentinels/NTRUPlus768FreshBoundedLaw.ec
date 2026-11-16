
lemma __stopped_fresh_tail_eof &m qf0 qg0 workspace0 :
 0<=qf0 => 0<=qg0 =>
 Pr[StoppedKeygen(UniformSeedRNG,FreshExpand).run(qf0,qg0,workspace0) @ &m :
   !stopped_success res] <= fresh_retry_tail qf0 qg0.
proof. exact (fresh_stopped_keygen_abort_probability &m qf0 qg0 workspace0). qed.
