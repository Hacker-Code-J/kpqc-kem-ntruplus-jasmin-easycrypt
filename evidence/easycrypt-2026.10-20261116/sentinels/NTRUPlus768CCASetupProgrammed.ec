

lemma __cca_setup_eof_1 &m qf0 qg0 workspace0 :
 0<=qf0 => 0<=qg0 =>
 Pr[CountedKeygen(UniformSeedRNG,ProgrammedFreshExpand).run(workspace0) @ &m:
 !counted_within qf0 qg0 res] <= fresh_retry_tail qf0 qg0.
proof. exact (programmed_counted_tail &m qf0 qg0 workspace0). qed.
