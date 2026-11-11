require import AllCore List Distr FMap SDist RealSeries.
from Jasmin require import JWord.
require import Array192 Array14466.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768KeygenClearProof.
require import NTRUPlus768StoppedKeygenModel NTRUPlus768FreshRetryLaw.
require import NTRUPlus768ROMOracles NTRUPlus768ROMKeygen NTRUPlus768CCASetupState.
require import NTRUPlus768AcceptanceProbability NTRUPlus768PKEModel.
require import NTRUPlus768ACWC2Oracle.

type fo_setup_key_observation = keygen_output * cca_f_table.
type fo_setup_observation = keygen_output * cca_f_table * W8.t Array192.t list.

(* F is initialized here, rather than silently reusing an arbitrary initial
   cache. Its final value is retained with the actual key output. *)
module FOSetupKeySource = {
 proc guess(workspace:W8.t Array14466.t) : fo_setup_key_observation = {
  var out:keygen_output;
  ROF.init();
  out <@ KeygenInstrumented(UniformSeedRNG,FreshExpand,SHAKEFROM).run(workspace);
  return(out,ROF.m);
 }
}.
module FOSetupSource = {
 proc guess(workspace:W8.t Array14466.t) : fo_setup_observation = {
  var key:fo_setup_key_observation; var pads:W8.t Array192.t list;
  key <@ FOSetupKeySource.guess(workspace);
  pads <$ acwc2_gpads_law;
  return(key.`1,key.`2,pads);
 }
}.

op fo_setup_valid (x:fo_setup_observation) =
 rom_key_relation x.`1.`1 x.`2 /\ x.`1.`2=keygen_clear_zero_spec /\
 pke_key_relation x.`1.`1 /\ x.`3 \in acwc2_gpads_law /\
 acwc2_cache_matches(acwc2_gfun x.`3)(acwc2_g_cache x.`3).
op fo_setup_joint_law (dk:fo_setup_key_observation distr) =
 dlet dk(fun (key:fo_setup_key_observation)=>dmap acwc2_gpads_law(fun pads=>(key.`1,key.`2,pads))).

clone SDist.GenDist as FOSetupKeyDist with
 type in_t <- W8.t Array14466.t,
 type out_t <- fo_setup_key_observation
 proof *.
clone SDist.GenDist as FOSetupDist with
 type in_t <- W8.t Array14466.t,
 type out_t <- fo_setup_observation
 proof *.

lemma fo_setup_key_lossless : islossless FOSetupKeySource.guess.
proof.
 proc; call(fresh_keygen_instrumented_ll fresh_f_accept_positive fresh_g_accept_positive).
 call rof_init_ll; auto.
qed.
lemma fo_setup_source_lossless : islossless FOSetupSource.guess.
proof. proc; rnd; call fo_setup_key_lossless; auto=> />; exact acwc2_gpads_lossless. qed.
lemma fo_setup_key_valid : hoare[FOSetupKeySource.guess:true ==>
 rom_key_relation res.`1.`1 res.`2 /\ res.`1.`2=keygen_clear_zero_spec /\ ROF.m=res.`2].
proof. proc; call(rom_keygen_instrumented UniformSeedRNG FreshExpand); call rof_init_empty; auto. qed.
lemma fo_setup_source_valid : hoare[FOSetupSource.guess:true ==>
 fo_setup_valid res /\ ROF.m=res.`2].
proof.
 proc; rnd; call fo_setup_key_valid; auto=> />.
 move=> result hrom hclear pads hp.
 split; first exact(pke_key_from_rom _ _ hrom).
 exact(acwc2_g_cache_matches pads).
qed.

(* No E/G/H table is initialized or modified by this source. *)
lemma fo_setup_source_frame em gm hm : hoare[FOSetupSource.guess:
 ROE.m=em /\ ROG.m=gm /\ ROH.m=hm ==> ROE.m=em /\ ROG.m=gm /\ ROH.m=hm].
proof. proc; rnd; call(_:true ==>true); first by trivial. auto. qed.
lemma fo_setup_source_initial_state : equiv[FOSetupSource.guess ~ FOSetupSource.guess:
 ={workspace} ==> ={res,glob ROF}].
proof.
 proc; rnd; inline FOSetupKeySource.guess; wp.
 call(_: ={workspace,glob ROF} ==> ={res,glob ROF}); first by sim.
 inline ROF.init; auto.
qed.

lemma fo_setup_key_sample (S<:FOSetupKeyDist.Distinguisher) &m workspace0 :
 equiv[S.guess ~ FOSetupKeyDist.S.sample:
 x{1}=workspace0 /\ (glob S){1}=(glob S){m} /\
 d{2}=mk(fun z=>Pr[S.guess(workspace0) @ &m:res=z]) ==> ={res}].
proof.
 bypr(res{1})(res{2})=> // &1 &2 z [hx [hg hd]].
 rewrite hx hd FOSetupKeyDist.sampleE -(FOSetupKeyDist.adv_mu1 S &m z workspace0).
 byequiv(_: ={x,glob S} ==> ={res})=> //; proc true; auto.
qed.
lemma fo_setup_source_sample (S<:FOSetupDist.Distinguisher) &m workspace0 :
 equiv[S.guess ~ FOSetupDist.S.sample:
 x{1}=workspace0 /\ (glob S){1}=(glob S){m} /\
 d{2}=mk(fun z=>Pr[S.guess(workspace0) @ &m:res=z]) ==> ={res}].
proof.
 bypr(res{1})(res{2})=> // &1 &2 z [hx [hg hd]].
 rewrite hx hd FOSetupDist.sampleE -(FOSetupDist.adv_mu1 S &m z workspace0).
 byequiv(_: ={x,glob S} ==> ={res})=> //; proc true; auto.
qed.
lemma fo_setup_key_mu &m workspace0 (event:fo_setup_key_observation->bool) :
 Pr[FOSetupKeySource.guess(workspace0) @ &m:event res]=
 mu(mk(fun z=>Pr[FOSetupKeySource.guess(workspace0) @ &m:res=z]))event.
proof.
 have hs:Pr[FOSetupKeyDist.S.sample(mk(fun z=>Pr[FOSetupKeySource.guess(workspace0) @ &m:res=z]))
  @ &m:event res]=mu(mk(fun z=>Pr[FOSetupKeySource.guess(workspace0) @ &m:res=z]))event.
 + byphoare(_:d=mk(fun z=>Pr[FOSetupKeySource.guess(workspace0) @ &m:res=z]) ==>event res)=> //.
   proc; rnd; auto.
 rewrite -hs; by byequiv(fo_setup_key_sample FOSetupKeySource &m workspace0)=> //.
qed.
lemma fo_setup_key_law_lossless &m workspace0 :
 is_lossless(mk(fun z=>Pr[FOSetupKeySource.guess(workspace0) @ &m:res=z])).
proof.
 rewrite /is_lossless -(fo_setup_key_mu &m workspace0 predT).
 by byphoare fo_setup_key_lossless.
qed.
lemma fo_setup_source_mu &m workspace0 (event:fo_setup_observation->bool) :
 Pr[FOSetupSource.guess(workspace0) @ &m:event res]=
 mu(mk(fun z=>Pr[FOSetupSource.guess(workspace0) @ &m:res=z]))event.
proof.
 have hs:Pr[FOSetupDist.S.sample(mk(fun z=>Pr[FOSetupSource.guess(workspace0) @ &m:res=z]))
  @ &m:event res]=mu(mk(fun z=>Pr[FOSetupSource.guess(workspace0) @ &m:res=z]))event.
 + byphoare(_:d=mk(fun z=>Pr[FOSetupSource.guess(workspace0) @ &m:res=z]) ==>event res)=> //.
   proc; rnd; auto.
 rewrite -hs; by byequiv(fo_setup_source_sample FOSetupSource &m workspace0)=> //.
qed.
lemma fo_setup_law_lossless &m workspace0 :
 is_lossless(mk(fun z=>Pr[FOSetupSource.guess(workspace0) @ &m:res=z])).
proof.
 rewrite /is_lossless -(fo_setup_source_mu &m workspace0 predT).
 by byphoare fo_setup_source_lossless.
qed.
lemma fo_setup_law_support &m workspace0 x :
 x \in mk(fun z=>Pr[FOSetupSource.guess(workspace0) @ &m:res=z]) =>fo_setup_valid x.
proof.
 move=>hx.
 have hz:Pr[FOSetupSource.guess(workspace0) @ &m:!fo_setup_valid res]=0%r.
 + byphoare(_:true ==>!fo_setup_valid res)=> //; hoare; conseq fo_setup_source_valid; smt().
 have hd:mu(mk(fun z=>Pr[FOSetupSource.guess(workspace0) @ &m:res=z]))
   (fun y=>!fo_setup_valid y)=0%r.
 + rewrite -(fo_setup_source_mu &m workspace0 (fun y=>!fo_setup_valid y)); exact hz.
 have h:=eq0_mu _ _ hd x hx; smt().
qed.

module FOSetupReified = {
 proc run(d:fo_setup_key_observation distr) : fo_setup_observation = {
  var key:fo_setup_key_observation; var pads:W8.t Array192.t list;
  key <$ d;
  pads <$ acwc2_gpads_law;
  return(key.`1,key.`2,pads);
 }
}.
lemma fo_setup_reified_probability &m dk (event:fo_setup_observation->bool) :
 Pr[FOSetupReified.run(dk) @ &m:event res]=mu(fo_setup_joint_law dk)event.
proof.
 byphoare(_:d=dk ==>event res)=> //.
 proc; rndsem 0.
 rnd (fun (z:fo_setup_key_observation*W8.t Array192.t list)=>event(z.`1.`1,z.`1.`2,z.`2)).
 skip=> />.
 rewrite /fo_setup_joint_law !dletE.
 apply eq_sum=>key /=; rewrite !dmapE /(\o) /=; ring.
qed.
lemma fo_setup_joint_distribution &m workspace0 :
 mk(fun z=>Pr[FOSetupSource.guess(workspace0) @ &m:res=z])=
 fo_setup_joint_law(mk(fun (key:fo_setup_key_observation)=>Pr[FOSetupKeySource.guess(workspace0) @ &m:res=key])).
proof.
 apply eq_distr=>z.
 rewrite -(FOSetupDist.adv_mu1 FOSetupSource &m z workspace0)
   -(fo_setup_reified_probability &m _ (pred1 z)).
 byequiv(_:workspace{1}=workspace0 /\ (glob FOSetupKeySource){1}=(glob FOSetupKeySource){m} /\
   d{2}=mk(fun (key:fo_setup_key_observation)=>Pr[FOSetupKeySource.guess(workspace0) @ &m:res=key]) ==> ={res})=> //.
 proc; rnd; outline{2} 1 ~ FOSetupKeyDist.S.sample.
 call(fo_setup_key_sample FOSetupKeySource &m workspace0); auto.
qed.
