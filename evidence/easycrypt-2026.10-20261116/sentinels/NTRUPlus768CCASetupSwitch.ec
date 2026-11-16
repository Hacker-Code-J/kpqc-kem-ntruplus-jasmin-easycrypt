

lemma __cca_setup_eof_3 &mem qf qg a m0 f0 (event:cca_stopped_state->bool) :
 0<=qf =>0<=qg =>0<=a =>fsize m0<=a =>
 `|Pr[CCAStoppedJoint(ExpandROM).run(qf,qg,m0,f0) @ &mem:event res]-
   Pr[CCAStoppedJoint(ProgrammedFreshExpand).run(qf,qg,m0,f0) @ &mem:event res]|
 <=proposal_delta a(qf+qg).
proof. exact (cca_stopped_joint_distance &mem qf qg a m0 f0 event). qed.
