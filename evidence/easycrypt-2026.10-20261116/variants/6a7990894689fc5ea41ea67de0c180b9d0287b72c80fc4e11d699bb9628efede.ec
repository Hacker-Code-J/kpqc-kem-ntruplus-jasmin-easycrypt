require import AllCore Distr FMap StdOrder.
from Jasmin require import JWord.
require import Array32 Array192 Array1152 Array14466.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteProof.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions.
require import NTRUPlus768StoppedKeygenModel NTRUPlus768FreshRetryLaw.
require import NTRUPlus768SubdistributionTransfer NTRUPlus768ProposalSwitch.
require import NTRUPlus768AcceptanceBudget NTRUPlus768AcceptanceROMBound.
require import NTRUPlus768CCASetupState NTRUPlus768CCASetupProgrammed.
require import NTRUPlus768CCASetupSwitch NTRUPlus768CCASetupPrefix.
import RealOrder.

(* Only the programmed fresh setup is proved lossless below, through the
   established actual acceptance theorem. The ROM setup remains a sublaw. *)
lemma cca_programmed_counted_joint_ll :
 islossless CCAConfiguredCountedSetup(ProgrammedFreshExpand).run.
proof. proc; call programmed_counted_ll; auto. qed.

lemma cca_programmed_joint_tail &m qf qg m0 f0 :
 0<=qf => 0<=qg =>
 Pr[CCAConfiguredCountedSetup(ProgrammedFreshExpand).run(m0,f0) @ &m:
  !counted_joint_within qf qg res] <= fresh_retry_tail qf qg.
proof.
 move=>hf hg.
 have ht:phoare[CountedKeygen(UniformSeedRNG,ProgrammedFreshExpand).run:
   true ==> !counted_within qf qg res] <= (fresh_retry_tail qf qg).
 + bypr=> &mm _; exact(programmed_counted_tail &mm qf qg workspace{mm} hf hg).
 byphoare (_: true ==> _) => //.
 proc; call ht; auto.
qed.

lemma cca_programmed_joint_prefix_lower &m qf qg m0 f0
 (event:cca_setup_state->bool) :
 0<=qf => 0<=qg =>
 Pr[CCAConfiguredCountedSetup(ProgrammedFreshExpand).run(m0,f0) @ &m:
   counted_joint_event event res]-fresh_retry_tail qf qg <=
 Pr[CCAStoppedJoint(ProgrammedFreshExpand).run(qf,qg,m0,f0) @ &m:
   stopped_success_event event res].
proof.
 move=>hf hg.
 have ht:=cca_programmed_joint_tail &m qf qg m0 f0 hf hg.
 have hp:=cca_configured_counted_stopped_prefix_programmed &m qf qg m0 f0 event.
 have hb:Pr[CCAConfiguredCountedSetup(ProgrammedFreshExpand).run(m0,f0) @ &m:
   counted_joint_event event res /\ !counted_joint_within qf qg res] <=
   Pr[CCAConfiguredCountedSetup(ProgrammedFreshExpand).run(m0,f0) @ &m:
   !counted_joint_within qf qg res] by rewrite Pr[mu_sub].
 have he:Pr[CCAConfiguredCountedSetup(ProgrammedFreshExpand).run(m0,f0) @ &m:
   counted_joint_event event res /\ counted_joint_within qf qg res]=
   Pr[CCAConfiguredCountedSetup(ProgrammedFreshExpand).run(m0,f0) @ &m:
   counted_joint_within qf qg res /\ counted_joint_event event res]
   by rewrite Pr[mu_eq].
 rewrite Pr[mu_split (counted_joint_within qf qg res)] he hp.
 smt().
qed.

lemma cca_rom_joint_good_event_lower &m qf qg a m0 f0
 (event:cca_setup_state->bool) :
 0<=qf => 0<=qg => 0<=a => fsize m0<=a =>
 Pr[CCAConfiguredCountedSetup(ProgrammedFreshExpand).run(m0,f0) @ &m:
   counted_joint_event event res]-(proposal_delta a (qf+qg)+fresh_retry_tail qf qg) <=
 Pr[CCAConfiguredCountedSetup(ExpandROM).run(m0,f0) @ &m:
   counted_joint_within qf qg res /\ counted_joint_event event res].
proof.
 move=>hf hg ha hm.
 have hs:=cca_stopped_joint_distance &m qf qg a m0 f0
   (stopped_success_event event) hf hg ha hm.
 have hp:=cca_configured_counted_stopped_prefix_rom &m qf qg m0 f0 event.
 have hi:=cca_programmed_joint_prefix_lower &m qf qg m0 f0 event hf hg.
 rewrite hp; rewrite ler_norml in hs; smt().
qed.

lemma cca_rom_joint_event_lower &m qf qg a m0 f0
 (event:cca_setup_state->bool) :
 0<=qf => 0<=qg => 0<=a => fsize m0<=a =>
 Pr[CCAConfiguredCountedSetup(ProgrammedFreshExpand).run(m0,f0) @ &m:
   counted_joint_event event res]-(proposal_delta a (qf+qg)+fresh_retry_tail qf qg) <=
 Pr[CCAConfiguredCountedSetup(ExpandROM).run(m0,f0) @ &m:
   counted_joint_event event res].
proof.
 move=>hf hg ha hm.
 have hl:=cca_rom_joint_good_event_lower &m qf qg a m0 f0 event hf hg ha hm.
 have hs:Pr[CCAConfiguredCountedSetup(ExpandROM).run(m0,f0) @ &m:
   counted_joint_within qf qg res /\ counted_joint_event event res] <=
   Pr[CCAConfiguredCountedSetup(ExpandROM).run(m0,f0) @ &m:
   counted_joint_event event res] by rewrite Pr[mu_sub].
 smt().
qed.

(* Complementary events pay the same error once, even if ROM execution can
   diverge. There is no normalization by its return probability. *)
lemma cca_counted_joint_distance &m qf qg a m0 f0
 (event:cca_setup_state->bool) :
 0<=qf => 0<=qg => 0<=a => fsize m0<=a =>
 `|Pr[CCAConfiguredCountedSetup(ExpandROM).run(m0,f0) @ &m:
   counted_joint_event event res]-
   Pr[CCAConfiguredCountedSetup(ProgrammedFreshExpand).run(m0,f0) @ &m:
   counted_joint_event event res]| <=
 proposal_delta a (qf+qg)+fresh_retry_tail qf qg.
proof.
 move=>hf hg ha hm.
 have hl:=cca_rom_joint_event_lower &m qf qg a m0 f0 event hf hg ha hm.
 have hn:=cca_rom_joint_event_lower &m qf qg a m0 f0 (fun out=>!event out) hf hg ha hm.
 have ht:Pr[CCAConfiguredCountedSetup(ProgrammedFreshExpand).run(m0,f0) @ &m:true]=1%r
   by byphoare cca_programmed_counted_joint_ll.
 have ha':Pr[CCAConfiguredCountedSetup(ExpandROM).run(m0,f0) @ &m:
   counted_joint_event event res]+
   Pr[CCAConfiguredCountedSetup(ExpandROM).run(m0,f0) @ &m:
   !counted_joint_event event res]<=1%r.
 + rewrite Pr[mu_not]; smt(mu_bounded).
 have hi':Pr[CCAConfiguredCountedSetup(ProgrammedFreshExpand).run(m0,f0) @ &m:
   counted_joint_event event res]+
   Pr[CCAConfiguredCountedSetup(ProgrammedFreshExpand).run(m0,f0) @ &m:
   !counted_joint_event event res]=1%r.
 + rewrite Pr[mu_not] ht; smt().
 exact(complementary_event_transfer _ _ _ _ _ ha' hi' hl hn).
qed.

lemma cca_configured_setup_distance &m qf qg a m0 f0
 (event:cca_setup_state->bool) :
 0<=qf => 0<=qg => 0<=a => fsize m0<=a =>
 `|Pr[CCAConfiguredSetup(ExpandROM).run(m0,f0) @ &m:event res]-
   Pr[CCAConfiguredSetup(ProgrammedFreshExpand).run(m0,f0) @ &m:event res]| <=
 proposal_delta a (qf+qg)+fresh_retry_tail qf qg.
proof.
 move=>hf hg ha hm.
 have h:=cca_counted_joint_distance &m qf qg a m0 f0 event hf hg ha hm.
 rewrite cca_configured_counted_erasure_probability_rom
   cca_configured_counted_erasure_probability_programmed in h.
 exact h.
qed.

lemma cca_configured_setup_initial_rom &m cache0 fcache0
 (event:cca_setup_state->bool) :
 ROE.m{m}=cache0 => ROF.m{m}=fcache0 =>
 Pr[CCAConfiguredSetup(ExpandROM).run(cache0,fcache0) @ &m:event res]=
 Pr[JointSetup(ExpandROM).run(witness) @ &m:event res].
proof.
 move=>he hf.
 byequiv (_: m0{1}=ROE.m{2} /\ f0{1}=ROF.m{2} /\
   workspace{2}=witness ==> ={res}) => //; last by smt().
 proc; inline JointSetup(ExpandROM).run.
 wp; sim (: ={glob ROE,glob ROF}); auto.
qed.

lemma cca_configured_setup_initial_programmed &m cache0 fcache0
 (event:cca_setup_state->bool) :
 ROE.m{m}=cache0 => ROF.m{m}=fcache0 =>
 Pr[CCAConfiguredSetup(ProgrammedFreshExpand).run(cache0,fcache0) @ &m:event res]=
 Pr[JointSetup(ProgrammedFreshExpand).run(witness) @ &m:event res].
proof.
 move=>he hf.
 byequiv (_: m0{1}=ROE.m{2} /\ f0{1}=ROF.m{2} /\
   workspace{2}=witness ==> ={res}) => //; last by smt().
 proc; inline JointSetup(ProgrammedFreshExpand).run.
 wp; sim (: ={glob ROE,glob ROF}); auto.
qed.

(* The returned observation includes the keygen witness, cleared workspace,
   and both final tables; the initial F table is arbitrary and shared. *)
lemma cca_setup_rom_programmed_distance &m qf qg a m0
 (event:cca_setup_state->bool) :
 0<=qf => 0<=qg => 0<=a => fsize m0<=a => ROE.m{m}=m0 =>
 `|Pr[JointSetup(ExpandROM).run(witness) @ &m:event res]-
   Pr[JointSetup(ProgrammedFreshExpand).run(witness) @ &m:event res]| <=
 proposal_delta a (qf+qg)+fresh_retry_tail qf qg.
proof.
 move=>hf hg ha hm he.
 have h:=cca_configured_setup_distance &m qf qg a m0 ROF.m{m} event hf hg ha hm.
 have hr:Pr[CCAConfiguredSetup(ExpandROM).run(m0,ROF.m{m}) @ &m:event res]=
   Pr[JointSetup(ExpandROM).run(witness) @ &m:event res].
 + apply cca_configured_setup_initial_rom; done.
 have hi:Pr[CCAConfiguredSetup(ProgrammedFreshExpand).run(m0,ROF.m{m}) @ &m:event res]=
   Pr[JointSetup(ProgrammedFreshExpand).run(witness) @ &m:event res].
 + apply cca_configured_setup_initial_programmed; done.
 smt().
qed.

lemma cca_setup_rom_missing_mass &m qf qg a m0 :
 0<=qf => 0<=qg => 0<=a => fsize m0<=a => ROE.m{m}=m0 =>
 0%r<=1%r-Pr[JointSetup(ExpandROM).run(witness) @ &m:true]<=
 proposal_delta a (qf+qg)+fresh_retry_tail qf qg.
proof.
 move=>hf hg ha hm he.
 have h:=cca_setup_rom_programmed_distance &m qf qg a m0 predT hf hg ha hm he.
 have ht:Pr[JointSetup(ProgrammedFreshExpand).run(witness) @ &m:true]=1%r
   by byphoare programmed_joint_setup_ll.
 move:h ht; rewrite /predT ler_norml; smt(mu_bounded).
qed.

lemma cca_setup_source_configured_rom &m
 (event:cca_setup_state->bool) :
 Pr[JointSetupSource(ExpandROM).guess(witness) @ &m:event res]=
 Pr[CCAConfiguredSetup(ExpandROM).run(empty,empty) @ &m:event res].
proof.
 byequiv (_: workspace{1}=witness /\ m0{2}=empty /\ f0{2}=empty ==>
   ={res}) => //.
 proc; call (_: ={workspace,glob ROE,glob ROF} ==> ={res}); first by sim.
 inline ROE.init ROF.init; auto.
qed.

lemma cca_setup_source_configured_programmed &m
 (event:cca_setup_state->bool) :
 Pr[JointSetupSource(ProgrammedFreshExpand).guess(witness) @ &m:event res]=
 Pr[CCAConfiguredSetup(ProgrammedFreshExpand).run(empty,empty) @ &m:event res].
proof.
 byequiv (_: workspace{1}=witness /\ m0{2}=empty /\ f0{2}=empty ==>
   ={res}) => //.
 proc; call (_: ={workspace,glob ROE,glob ROF} ==> ={res}); first by sim.
 inline ROE.init ROF.init; auto.
qed.

lemma cca_setup_source_distance &m qf qg (event:cca_setup_state->bool) :
 0<=qf => 0<=qg =>
 `|Pr[JointSetupSource(ExpandROM).guess(witness) @ &m:event res]-
   Pr[JointSetupSource(ProgrammedFreshExpand).guess(witness) @ &m:event res]| <=
 proposal_delta 0 (qf+qg)+fresh_retry_tail qf qg.
proof.
 move=>hf hg.
 rewrite (cca_setup_source_configured_rom &m event)
   (cca_setup_source_configured_programmed &m event).
 apply(cca_configured_setup_distance &m qf qg 0 empty empty event hf hg);
   smt(fsize_empty).
qed.

lemma cca_setup_rom_programmed_distance_256 &m a m0
 (event:cca_setup_state->bool) :
 0<=a => fsize m0<=a => ROE.m{m}=m0 =>
 `|Pr[JointSetup(ExpandROM).run(witness) @ &m:event res]-
   Pr[JointSetup(ProgrammedFreshExpand).run(witness) @ &m:event res]| <=
 (512%r*a%r+130818%r)/(2%r^256).
proof.
 move=>ha hm he.
 have h:=cca_setup_rom_programmed_distance &m 256 256 a m0 event _ _ ha hm he;
  first 2 smt().
 have hb:=certified_keygen_error_256 a; smt().
qed.

(* This numerical specialization uses the new joint-state comparison, then
   reuses only the already certified scalar budget calculation. *)
lemma cca_setup_source_distance_256 &m (event:cca_setup_state->bool) :
 `|Pr[JointSetupSource(ExpandROM).guess(witness) @ &m:event res]-
   Pr[JointSetupSource(ProgrammedFreshExpand).guess(witness) @ &m:event res]| <=
 130818%r/(2%r^256).
proof.
 have h:=cca_setup_source_distance &m 256 256 event _ _; first 2 smt().
 have hb:=certified_keygen_error_256 0; smt().
qed.

lemma cca_setup_source_missing_mass_256 &m :
 0%r<=1%r-Pr[JointSetupSource(ExpandROM).guess(witness) @ &m:true]<=
 130818%r/(2%r^256).
proof.
 have h:=cca_setup_source_distance_256 &m predT.
 have ht:Pr[JointSetupSource(ProgrammedFreshExpand).guess(witness) @ &m:true]=1%r
   by byphoare programmed_joint_source_ll.
 move:h ht; rewrite /predT ler_norml; smt(mu_bounded).
qed.

lemma cca_setup_source_distance_239 &m (event:cca_setup_state->bool) :
 `|Pr[JointSetupSource(ExpandROM).guess(witness) @ &m:event res]-
   Pr[JointSetupSource(ProgrammedFreshExpand).guess(witness) @ &m:event res]|
 <1%r/(2%r^239).
proof.
 have h:=cca_setup_source_distance_256 &m event.
 have hb:=keygen_empty_cache_error_239; smt().
qed.
