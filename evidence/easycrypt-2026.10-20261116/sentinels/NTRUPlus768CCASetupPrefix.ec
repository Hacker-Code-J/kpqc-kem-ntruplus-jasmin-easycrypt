

lemma __cca_setup_eof_4 &m qf0 qg0 m0 f0 (event:cca_setup_state->bool) :
 Pr[CCAConfiguredCountedSetup(ProgrammedFreshExpand).run(m0,f0) @ &m:
   counted_joint_within qf0 qg0 res /\ counted_joint_event event res] =
 Pr[CCAStoppedJoint(ProgrammedFreshExpand).run(qf0,qg0,m0,f0) @ &m:
   stopped_success_event event res].
proof. exact (cca_configured_counted_stopped_prefix_programmed &m qf0 qg0 m0 f0 event). qed.
