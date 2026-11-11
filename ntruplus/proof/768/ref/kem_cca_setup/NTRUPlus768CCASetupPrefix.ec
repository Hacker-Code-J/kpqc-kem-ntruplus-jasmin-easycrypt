require import AllCore Distr FMap.
from Jasmin require import JWord.
require import Array32 Array192 Array1152 Array14466.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteAttempt.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768ROMOracles.
require import NTRUPlus768StoppedKeygenModel NTRUPlus768StoppedKeygenPrefix.
require import NTRUPlus768FreshRetryLaw.
require import NTRUPlus768CCASetupState.

(* On success the complete expansion and F states agree. On exhaustion the
   prefix-only diagnostic may make extra calls, so no bad-state equality is used. *)
lemma cca_prefix_only_stopped_state (R<:KeygenSeedRNG {-ROF,-PrefixBad})
 (E<:KeygenExpand {-ROF,-PrefixBad,-R}) :
 islossless R.sample => islossless E.shake =>
 equiv[PrefixOnlyKeygen(R,E).run ~ StoppedKeygen(R,E).run :
 ={qf,qg,workspace,glob R,glob E,glob ROF} ==>
 (!PrefixBad.bad{1} = stopped_success res{2}) /\
 (!PrefixBad.bad{1} => res.`1{1}=oget res.`1{2} /\ ={glob R,glob E,glob ROF})].
proof.
 move=> hR hE; proc.
 seq 2 3 : (={fv,qg,workspace,glob R,glob E,glob ROF} /\
   !PrefixBad.bad{1} /\ result{2}=None).
 + call (_: ={glob R,glob E}); first by sim.
   auto => />.
 if{2}.
 + rcondf{1} 1; first by auto => />.
   seq 1 1 : (={fv,gv,workspace,glob R,glob E,glob ROF} /\
     !PrefixBad.bad{1} /\ result{2}=None).
   - call (_: ={glob R,glob E}); first by sim.
     auto => />.
   if{2}.
   - rcondf{1} 1; first by auto => />.
     wp; call (_: ={glob ROF}); first by sim.
     by auto => />; rewrite /stopped_success /=.
   rcondt{1} 1; first by auto => />.
   call{1} observed_finish_lossless; by auto => />; rewrite /stopped_success /=.
 rcondt{1} 1; first by auto => />.
 seq 2 0 : (PrefixBad.bad{1} /\ result{2}=None).
 + call{1}(bounded_g_lossless R E hR hE); auto => />.
 call{1} observed_finish_lossless; if{1}; by auto => />; rewrite /stopped_success /=.
qed.

lemma cca_resumed_prefix_state_upto (R<:KeygenSeedRNG {-PrefixBad})
 (E<:KeygenExpand {-PrefixBad,-R}) (qf qg:int) (w:W8.t Array14466.t)
 (event:keygen_output -> (glob E) -> cca_f_table -> bool) &m :
 Pr[ResumedKeygen(R,E).run(qf,qg,w) @ &m :
   event res.`1 (glob E) ROF.m /\ !PrefixBad.bad] =
 Pr[PrefixOnlyKeygen(R,E).run(qf,qg,w) @ &m :
   event res.`1 (glob E) ROF.m /\ !PrefixBad.bad].
proof. byupto. qed.

lemma cca_counted_stopped_state_prefix (R<:KeygenSeedRNG {-ROF,-PrefixBad})
 (E<:KeygenExpand {-ROF,-PrefixBad,-R}) (qf0 qg0:int)
 (w:W8.t Array14466.t)
 (event:keygen_output -> (glob E) -> cca_f_table -> bool) &m :
 islossless R.sample => islossless E.shake =>
 Pr[CountedKeygen(R,E).run(w) @ &m : counted_within qf0 qg0 res /\
   event res.`1 (glob E) ROF.m] =
 Pr[StoppedKeygen(R,E).run(qf0,qg0,w) @ &m : stopped_success res /\
   event (oget res.`1) (glob E) ROF.m].
proof.
 move=> hR hE.
 have h1 : Pr[CountedKeygen(R,E).run(w) @ &m : counted_within qf0 qg0 res /\ event res.`1 (glob E) ROF.m] =
   Pr[SplitKeygen(R,E).run(qf0,qg0,w) @ &m : counted_within qf0 qg0 res /\ event res.`1 (glob E) ROF.m].
 + by byequiv (counted_keygen_split R E qf0 qg0) => //.
 have h2 : Pr[SplitKeygen(R,E).run(qf0,qg0,w) @ &m : counted_within qf0 qg0 res /\ event res.`1 (glob E) ROF.m] =
   Pr[ResumedKeygen(R,E).run(qf0,qg0,w) @ &m : counted_within qf0 qg0 res /\ event res.`1 (glob E) ROF.m].
 + by byequiv (split_keygen_resumed R E) => //.
 have h3 : Pr[ResumedKeygen(R,E).run(qf0,qg0,w) @ &m : counted_within qf0 qg0 res /\ event res.`1 (glob E) ROF.m] =
   Pr[ResumedKeygen(R,E).run(qf0,qg0,w) @ &m : event res.`1 (glob E) ROF.m /\ !PrefixBad.bad].
 + byequiv (_: ={qf,qg,workspace,glob R,glob E,glob ROF} /\ qf{2}=qf0 /\ qg{2}=qg0 ==>
     ={res,PrefixBad.bad,glob E,glob ROF} /\ counted_within qf0 qg0 res{2}=!PrefixBad.bad{2}) => //; last by smt().
   conseq (_: ={qf,qg,workspace,glob R,glob E,glob ROF} ==> ={res,PrefixBad.bad,glob E,glob ROF})
     _ (resumed_counted_within R E qf0 qg0) => //.
   proc; sim.
 have h4 := cca_resumed_prefix_state_upto R E qf0 qg0 w event &m.
 have h5 : Pr[PrefixOnlyKeygen(R,E).run(qf0,qg0,w) @ &m : event res.`1 (glob E) ROF.m /\ !PrefixBad.bad] =
   Pr[StoppedKeygen(R,E).run(qf0,qg0,w) @ &m : stopped_success res /\ event (oget res.`1) (glob E) ROF.m].
 + by byequiv (cca_prefix_only_stopped_state R E hR hE) => //; smt().
 by rewrite h1 h2 h3 h4 h5.
qed.

require import NTRUPlus768CCASetupSwitch.

type cca_counted_state = counted_output * cca_e_table * cca_f_table.
op stopped_success_event (event:cca_setup_state->bool) (s:cca_stopped_state) =
 stopped_success s.`1 /\ event (oget s.`1.`1,s.`2,s.`3).
op counted_joint_within qf qg (s:cca_counted_state) = counted_within qf qg s.`1.
op counted_joint_event (event:cca_setup_state->bool) (s:cca_counted_state) =
 event (s.`1.`1,s.`2,s.`3).

module CCAConfiguredSetup(E:KeygenExpand) = {
 proc run(m0:cca_e_table,f0:cca_f_table) : cca_setup_state = {
  var out:cca_setup_state;
  ROE.m <- m0; ROF.m <- f0;
  out <@ JointSetup(E).run(witness);
  return out;
 }
}.
module CCAConfiguredCountedSetup(E:KeygenExpand) = {
 proc run(m0:cca_e_table,f0:cca_f_table) : cca_counted_state = {
  var out:counted_output;
  ROE.m <- m0; ROF.m <- f0;
  out <@ CountedKeygen(UniformSeedRNG,E).run(witness);
  return(out,ROE.m,ROF.m);
 }
}.
module CCAConfiguredSplitSetup(E:KeygenExpand) = {
 proc run(qf:int,qg:int,m0:cca_e_table,f0:cca_f_table) : cca_counted_state = {
  var out:counted_output;
  ROE.m <- m0; ROF.m <- f0;
  out <@ SplitKeygen(UniformSeedRNG,E).run(qf,qg,witness);
  return(out,ROE.m,ROF.m);
 }
}.
module CCAConfiguredResumedSetup(E:KeygenExpand) = {
 proc run(qf:int,qg:int,m0:cca_e_table,f0:cca_f_table) : cca_counted_state = {
  var out:counted_output;
  ROE.m <- m0; ROF.m <- f0;
  out <@ ResumedKeygen(UniformSeedRNG,E).run(qf,qg,witness);
  return(out,ROE.m,ROF.m);
 }
}.
module CCAConfiguredPrefixSetup(E:KeygenExpand) = {
 proc run(qf:int,qg:int,m0:cca_e_table,f0:cca_f_table) : cca_counted_state = {
  var out:counted_output;
  ROE.m <- m0; ROF.m <- f0;
  out <@ PrefixOnlyKeygen(UniformSeedRNG,E).run(qf,qg,witness);
  return(out,ROE.m,ROF.m);
 }
}.

(* These two analysis procedures expose the bad initialization to byupto.
   Their equivalence to the wrappers is proved below by inlining only. *)
module CCAFlatResumedSetup(E:KeygenExpand) = {
 proc run(qf:int,qg:int,m0:cca_e_table,f0:cca_f_table) : cca_counted_state = {
  var qf0,qg0:int; var workspace:W8.t Array14466.t;
  var fv,gv:retry_state; var out0:keygen_output; var out:counted_output;
  ROE.m <- m0; ROF.m <- f0;
  qf0 <- qf; qg0 <- qg; workspace <- witness;
  PrefixBad.bad <- false;
  fv <@ BoundedRetry(UniformSeedRNG,E).f(qf0);
  if (!fv.`rs_ok) { PrefixBad.bad <- true; fv <@ CountedRetry(UniformSeedRNG,E).f_from(fv); }
  gv <@ BoundedRetry(UniformSeedRNG,E).g(qg0);
  if (!gv.`rs_ok) { PrefixBad.bad <- true; gv <@ CountedRetry(UniformSeedRNG,E).g_from(gv); }
  out0 <@ ObservedFinish.run(fv,gv,workspace);
  out <- (out0,fv.`rs_count,gv.`rs_count);
  return(out,ROE.m,ROF.m);
 }
}.
module CCAFlatPrefixOnlySetup(E:KeygenExpand) = {
 proc run(qf:int,qg:int,m0:cca_e_table,f0:cca_f_table) : cca_counted_state = {
  var qf0,qg0:int; var workspace:W8.t Array14466.t;
  var fv,gv:retry_state; var out0:keygen_output; var out:counted_output;
  ROE.m <- m0; ROF.m <- f0;
  qf0 <- qf; qg0 <- qg; workspace <- witness;
  PrefixBad.bad <- false;
  fv <@ BoundedRetry(UniformSeedRNG,E).f(qf0);
  if (!fv.`rs_ok) { PrefixBad.bad <- true; }
  gv <@ BoundedRetry(UniformSeedRNG,E).g(qg0);
  if (!gv.`rs_ok) { PrefixBad.bad <- true; }
  out0 <@ ObservedFinish.run(fv,gv,workspace);
  out <- (out0,fv.`rs_count,gv.`rs_count);
  return(out,ROE.m,ROF.m);
 }
}.

lemma cca_configured_resumed_within_rom qf0 qg0 :
 hoare[CCAConfiguredResumedSetup(ExpandROM).run : qf=qf0 /\ qg=qg0 ==>
   counted_joint_within qf0 qg0 res = !PrefixBad.bad].
proof. proc; call(resumed_counted_within UniformSeedRNG ExpandROM qf0 qg0); auto=> />; rewrite /counted_joint_within. qed.

lemma cca_configured_resumed_prefix_upto_rom
 qf qg m0 f0
 (event:cca_setup_state->bool) &m :
 Pr[CCAConfiguredResumedSetup(ExpandROM).run(qf,qg,m0,f0) @ &m:
    counted_joint_event event res /\ !PrefixBad.bad] =
 Pr[CCAConfiguredPrefixSetup(ExpandROM).run(qf,qg,m0,f0) @ &m:
    counted_joint_event event res /\ !PrefixBad.bad].
proof.
 have h1 : Pr[CCAConfiguredResumedSetup(ExpandROM).run(qf,qg,m0,f0) @ &m:
    counted_joint_event event res /\ !PrefixBad.bad] =
   Pr[CCAFlatResumedSetup(ExpandROM).run(qf,qg,m0,f0) @ &m:
    counted_joint_event event res /\ !PrefixBad.bad].
 + byequiv (_: ={qf,qg,m0,f0} ==> ={res,PrefixBad.bad})=> //.
   proc; inline ResumedKeygen(UniformSeedRNG,ExpandROM).run; wp; sp; sim; auto.
 have h2 : Pr[CCAFlatResumedSetup(ExpandROM).run(qf,qg,m0,f0) @ &m:
    counted_joint_event event res /\ !PrefixBad.bad] =
   Pr[CCAFlatPrefixOnlySetup(ExpandROM).run(qf,qg,m0,f0) @ &m:
    counted_joint_event event res /\ !PrefixBad.bad] by byupto.
 have h3 : Pr[CCAFlatPrefixOnlySetup(ExpandROM).run(qf,qg,m0,f0) @ &m:
    counted_joint_event event res /\ !PrefixBad.bad] =
   Pr[CCAConfiguredPrefixSetup(ExpandROM).run(qf,qg,m0,f0) @ &m:
    counted_joint_event event res /\ !PrefixBad.bad].
 + byequiv (_: ={qf,qg,m0,f0} ==> ={res,PrefixBad.bad})=> //.
   proc; inline PrefixOnlyKeygen(UniformSeedRNG,ExpandROM).run; wp; sp; sim; auto.
 by rewrite h1 h2 h3.
qed.

lemma cca_configured_resumed_within_programmed qf0 qg0 :
 hoare[CCAConfiguredResumedSetup(ProgrammedFreshExpand).run : qf=qf0 /\ qg=qg0 ==>
   counted_joint_within qf0 qg0 res = !PrefixBad.bad].
proof. proc; call(resumed_counted_within UniformSeedRNG ProgrammedFreshExpand qf0 qg0); auto=> />; rewrite /counted_joint_within. qed.

lemma cca_configured_resumed_prefix_upto_programmed
 qf qg m0 f0
 (event:cca_setup_state->bool) &m :
 Pr[CCAConfiguredResumedSetup(ProgrammedFreshExpand).run(qf,qg,m0,f0) @ &m:
    counted_joint_event event res /\ !PrefixBad.bad] =
 Pr[CCAConfiguredPrefixSetup(ProgrammedFreshExpand).run(qf,qg,m0,f0) @ &m:
    counted_joint_event event res /\ !PrefixBad.bad].
proof.
 have h1 : Pr[CCAConfiguredResumedSetup(ProgrammedFreshExpand).run(qf,qg,m0,f0) @ &m:
    counted_joint_event event res /\ !PrefixBad.bad] =
   Pr[CCAFlatResumedSetup(ProgrammedFreshExpand).run(qf,qg,m0,f0) @ &m:
    counted_joint_event event res /\ !PrefixBad.bad].
 + byequiv (_: ={qf,qg,m0,f0} ==> ={res,PrefixBad.bad})=> //.
   proc; inline ResumedKeygen(UniformSeedRNG,ProgrammedFreshExpand).run; wp; sp; sim; auto.
 have h2 : Pr[CCAFlatResumedSetup(ProgrammedFreshExpand).run(qf,qg,m0,f0) @ &m:
    counted_joint_event event res /\ !PrefixBad.bad] =
   Pr[CCAFlatPrefixOnlySetup(ProgrammedFreshExpand).run(qf,qg,m0,f0) @ &m:
    counted_joint_event event res /\ !PrefixBad.bad] by byupto.
 have h3 : Pr[CCAFlatPrefixOnlySetup(ProgrammedFreshExpand).run(qf,qg,m0,f0) @ &m:
    counted_joint_event event res /\ !PrefixBad.bad] =
   Pr[CCAConfiguredPrefixSetup(ProgrammedFreshExpand).run(qf,qg,m0,f0) @ &m:
    counted_joint_event event res /\ !PrefixBad.bad].
 + byequiv (_: ={qf,qg,m0,f0} ==> ={res,PrefixBad.bad})=> //.
   proc; inline PrefixOnlyKeygen(UniformSeedRNG,ProgrammedFreshExpand).run; wp; sp; sim; auto.
 by rewrite h1 h2 h3.
qed.

lemma cca_configured_counted_erasure_rom :
 equiv[CCAConfiguredCountedSetup(ExpandROM).run ~ CCAConfiguredSetup(ExpandROM).run :
   ={m0,f0} ==> (res.`1.`1{1},res.`2{1},res.`3{1})=res{2} /\ ={glob ROE,glob ROF}].
proof.
 proc; inline JointSetup(ExpandROM).run; wp.
 call(counted_keygen_erasure UniformSeedRNG ExpandROM); auto.
qed.
lemma cca_configured_counted_erasure_probability_rom &m m0 f0 (event:cca_setup_state->bool) :
 Pr[CCAConfiguredCountedSetup(ExpandROM).run(m0,f0) @ &m: counted_joint_event event res] =
 Pr[CCAConfiguredSetup(ExpandROM).run(m0,f0) @ &m: event res].
proof. by byequiv cca_configured_counted_erasure_rom=> //; rewrite /counted_joint_event; smt(). qed.

lemma cca_configured_counted_stopped_prefix_rom &m qf0 qg0 m0 f0 (event:cca_setup_state->bool) :
 Pr[CCAConfiguredCountedSetup(ExpandROM).run(m0,f0) @ &m:
   counted_joint_within qf0 qg0 res /\ counted_joint_event event res] =
 Pr[CCAStoppedJoint(ExpandROM).run(qf0,qg0,m0,f0) @ &m:
   stopped_success_event event res].
proof.
 have h1 : Pr[CCAConfiguredCountedSetup(ExpandROM).run(m0,f0) @ &m:
   counted_joint_within qf0 qg0 res /\ counted_joint_event event res] =
   Pr[CCAConfiguredSplitSetup(ExpandROM).run(qf0,qg0,m0,f0) @ &m:
   counted_joint_within qf0 qg0 res /\ counted_joint_event event res].
 + byequiv (_: ={m0,f0} /\ qf{2}=qf0 /\ qg{2}=qg0 ==> ={res})=> //.
   proc; call(counted_keygen_split UniformSeedRNG ExpandROM qf0 qg0); auto.
 have h2 : Pr[CCAConfiguredSplitSetup(ExpandROM).run(qf0,qg0,m0,f0) @ &m:
   counted_joint_within qf0 qg0 res /\ counted_joint_event event res] =
   Pr[CCAConfiguredResumedSetup(ExpandROM).run(qf0,qg0,m0,f0) @ &m:
   counted_joint_within qf0 qg0 res /\ counted_joint_event event res].
 + byequiv (_: ={qf,qg,m0,f0} ==> ={res})=> //.
   proc; call(split_keygen_resumed UniformSeedRNG ExpandROM); auto.
 have h3 : Pr[CCAConfiguredResumedSetup(ExpandROM).run(qf0,qg0,m0,f0) @ &m:
   counted_joint_within qf0 qg0 res /\ counted_joint_event event res] =
   Pr[CCAConfiguredResumedSetup(ExpandROM).run(qf0,qg0,m0,f0) @ &m:
   counted_joint_event event res /\ !PrefixBad.bad].
 + byequiv (_: ={qf,qg,m0,f0} /\ qf{2}=qf0 /\ qg{2}=qg0 ==>
    ={res,PrefixBad.bad} /\ counted_joint_within qf0 qg0 res{2}=!PrefixBad.bad{2})=> //; last by smt().
   conseq (_: ={qf,qg,m0,f0} ==> ={res,PrefixBad.bad})
    _ (cca_configured_resumed_within_rom qf0 qg0)=> //.
   proc; sim.
 have h4 := cca_configured_resumed_prefix_upto_rom qf0 qg0 m0 f0 event &m.
 have h5 : Pr[CCAConfiguredPrefixSetup(ExpandROM).run(qf0,qg0,m0,f0) @ &m:
   counted_joint_event event res /\ !PrefixBad.bad] =
   Pr[CCAStoppedJoint(ExpandROM).run(qf0,qg0,m0,f0) @ &m: stopped_success_event event res].
 + byequiv (_: ={qf,qg,m0,f0} ==>
     (counted_joint_event event res{1} /\ !PrefixBad.bad{1})=stopped_success_event event res{2})=> //; last by smt().
   proc; call(cca_prefix_only_stopped_state UniformSeedRNG ExpandROM uniform_seed_rng_ll ro_e_shake_ll).
   auto=> />; rewrite /counted_joint_event /stopped_success_event; smt().
 by rewrite h1 h2 h3 h4 h5.
qed.

lemma cca_configured_counted_erasure_programmed :
 equiv[CCAConfiguredCountedSetup(ProgrammedFreshExpand).run ~ CCAConfiguredSetup(ProgrammedFreshExpand).run :
   ={m0,f0} ==> (res.`1.`1{1},res.`2{1},res.`3{1})=res{2} /\ ={glob ROE,glob ROF}].
proof.
 proc; inline JointSetup(ProgrammedFreshExpand).run; wp.
 call(counted_keygen_erasure UniformSeedRNG ProgrammedFreshExpand); auto.
qed.
lemma cca_configured_counted_erasure_probability_programmed &m m0 f0 (event:cca_setup_state->bool) :
 Pr[CCAConfiguredCountedSetup(ProgrammedFreshExpand).run(m0,f0) @ &m: counted_joint_event event res] =
 Pr[CCAConfiguredSetup(ProgrammedFreshExpand).run(m0,f0) @ &m: event res].
proof. by byequiv cca_configured_counted_erasure_programmed=> //; rewrite /counted_joint_event; smt(). qed.

lemma cca_configured_counted_stopped_prefix_programmed &m qf0 qg0 m0 f0 (event:cca_setup_state->bool) :
 Pr[CCAConfiguredCountedSetup(ProgrammedFreshExpand).run(m0,f0) @ &m:
   counted_joint_within qf0 qg0 res /\ counted_joint_event event res] =
 Pr[CCAStoppedJoint(ProgrammedFreshExpand).run(qf0,qg0,m0,f0) @ &m:
   stopped_success_event event res].
proof.
 have h1 : Pr[CCAConfiguredCountedSetup(ProgrammedFreshExpand).run(m0,f0) @ &m:
   counted_joint_within qf0 qg0 res /\ counted_joint_event event res] =
   Pr[CCAConfiguredSplitSetup(ProgrammedFreshExpand).run(qf0,qg0,m0,f0) @ &m:
   counted_joint_within qf0 qg0 res /\ counted_joint_event event res].
 + byequiv (_: ={m0,f0} /\ qf{2}=qf0 /\ qg{2}=qg0 ==> ={res})=> //.
   proc; call(counted_keygen_split UniformSeedRNG ProgrammedFreshExpand qf0 qg0); auto.
 have h2 : Pr[CCAConfiguredSplitSetup(ProgrammedFreshExpand).run(qf0,qg0,m0,f0) @ &m:
   counted_joint_within qf0 qg0 res /\ counted_joint_event event res] =
   Pr[CCAConfiguredResumedSetup(ProgrammedFreshExpand).run(qf0,qg0,m0,f0) @ &m:
   counted_joint_within qf0 qg0 res /\ counted_joint_event event res].
 + byequiv (_: ={qf,qg,m0,f0} ==> ={res})=> //.
   proc; call(split_keygen_resumed UniformSeedRNG ProgrammedFreshExpand); auto.
 have h3 : Pr[CCAConfiguredResumedSetup(ProgrammedFreshExpand).run(qf0,qg0,m0,f0) @ &m:
   counted_joint_within qf0 qg0 res /\ counted_joint_event event res] =
   Pr[CCAConfiguredResumedSetup(ProgrammedFreshExpand).run(qf0,qg0,m0,f0) @ &m:
   counted_joint_event event res /\ !PrefixBad.bad].
 + byequiv (_: ={qf,qg,m0,f0} /\ qf{2}=qf0 /\ qg{2}=qg0 ==>
    ={res,PrefixBad.bad} /\ counted_joint_within qf0 qg0 res{2}=!PrefixBad.bad{2})=> //; last by smt().
   conseq (_: ={qf,qg,m0,f0} ==> ={res,PrefixBad.bad})
    _ (cca_configured_resumed_within_programmed qf0 qg0)=> //.
   proc; sim.
 have h4 := cca_configured_resumed_prefix_upto_programmed qf0 qg0 m0 f0 event &m.
 have h5 : Pr[CCAConfiguredPrefixSetup(ProgrammedFreshExpand).run(qf0,qg0,m0,f0) @ &m:
   counted_joint_event event res /\ !PrefixBad.bad] =
   Pr[CCAStoppedJoint(ProgrammedFreshExpand).run(qf0,qg0,m0,f0) @ &m: stopped_success_event event res].
 + byequiv (_: ={qf,qg,m0,f0} ==>
     (counted_joint_event event res{1} /\ !PrefixBad.bad{1})=stopped_success_event event res{2})=> //; last by smt().
   proc; call(cca_prefix_only_stopped_state UniformSeedRNG ProgrammedFreshExpand uniform_seed_rng_ll programmed_fresh_expand_ll).
   auto=> />; rewrite /counted_joint_event /stopped_success_event; smt().
 by rewrite h1 h2 h3 h4 h5.
qed.
