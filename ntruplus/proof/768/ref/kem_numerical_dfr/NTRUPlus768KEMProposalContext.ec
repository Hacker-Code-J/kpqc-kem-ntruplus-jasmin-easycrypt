require import AllCore Distr FMap SDist.
from Jasmin require import JWord.
require import Array32 Array192 Array768 Array1152 Array2336 Array14466.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteProof.
require import NTRUPlus768KeygenClearProof NTRUPlus768ROMKeygen.
require import NTRUPlus768ROMDistributions NTRUPlus768ROMOracles.
require import NTRUPlus768FreshRetryLaw NTRUPlus768StoppedKeygenModel.
require import NTRUPlus768AcceptanceProbability.
require import NTRUPlus768PolyCBD1Algebra NTRUPlus768ValidKeyM1Recovery.

type kem_keygen_observation = keygen_output * W8.t Array192.t * W8.t Array192.t.
op honest_no_wrap (x:kem_keygen_observation) =
 sampled_m1_no_wrap x.`1.`1.`kg_fbuf x.`1.`1.`kg_gbuf
   (poly_cbd1_spec x.`2) (poly_cbd1_spec x.`3).
op keygen_observer_error = 130818%r/(2%r^256).

module KeygenThenUniform(E:KeygenExpand) = {
 proc run() : kem_keygen_observation = {
  var out:keygen_output; var rbuf,mbuf:W8.t Array192.t;
  out <@ KeygenInstrumented(UniformSeedRNG,E,SHAKEFROM).run(witness);
  rbuf <$ uniform192;
  mbuf <$ uniform192;
  return(out,rbuf,mbuf);
 }
}.

(* The postprocessor reads only the returned witness and its own new coins. *)
module NoWrapObserver = {
 proc guess(x:keygen_output) : bool = {
  var rbuf,mbuf:W8.t Array192.t;
  rbuf <$ uniform192; mbuf <$ uniform192;
  return honest_no_wrap(x,rbuf,mbuf);
 }
}.
module KeygenSource(E:KeygenExpand) = {
 proc guess(x:W8.t Array14466.t) : keygen_output = {
  var out:keygen_output;
  out <@ KeygenInstrumented(UniformSeedRNG,E,SHAKEFROM).run(x);
  return out;
 }
}.

clone SDist.GenDist as KeygenDist with
 type in_t <- W8.t Array14466.t,
 type out_t <- keygen_output
 proof *.
clone SDist.Dist as NoWrapDist with type a <- keygen_output proof *.

module ReifiedKeygenThenUniform = {
 proc run(d:keygen_output distr) : kem_keygen_observation = {
  var out:keygen_output; var rbuf,mbuf:W8.t Array192.t;
  out <@ KeygenDist.S.sample(d);
  rbuf <$ uniform192; mbuf <$ uniform192;
  return(out,rbuf,mbuf);
 }
}.

lemma no_wrap_observer_lossless : islossless NoWrapObserver.guess.
proof. proc; rnd; rnd; auto => />; smt(uniform192_ll). qed.
lemma fresh_keygen_then_uniform_lossless :
 islossless KeygenThenUniform(FreshExpand).run.
proof.
 proc; rnd; rnd; call(fresh_keygen_instrumented_ll
   NTRUPlus768AcceptanceProbability.fresh_f_accept_positive
   NTRUPlus768AcceptanceProbability.fresh_g_accept_positive).
 auto => />; smt(uniform192_ll).
qed.

lemma keygen_then_uniform_rom_valid (E<:KeygenExpand {-ROF}) :
 hoare[KeygenThenUniform(E).run : true ==>
 rom_key_relation res.`1.`1 ROF.m /\ res.`1.`2=keygen_clear_zero_spec].
proof.
 proc; rnd; rnd; call(rom_keygen_instrumented UniformSeedRNG E); auto.
qed.
lemma keygen_then_uniform_gh_frame (E<:KeygenExpand {-ROG,-ROH}) gm hm :
 hoare[KeygenThenUniform(E).run : ROG.m=gm /\ ROH.m=hm ==>
 ROG.m=gm /\ ROH.m=hm].
proof. proc; rnd; rnd; call (_:true ==> true); first by trivial. auto. qed.

lemma keygen_source_probability (E<:KeygenExpand {-ROF}) &m x0 (event:keygen_output -> bool) :
 Pr[KeygenSource(E).guess(x0) @ &m : event res] =
 Pr[KeygenInstrumented(UniformSeedRNG,E,SHAKEFROM).run(x0) @ &m : event res].
proof.
 byequiv (_: x{1}=workspace{2} /\ ={glob E,glob ROF} ==> ={res}) => //.
 proc; inline KeygenInstrumented(UniformSeedRNG,E,SHAKEFROM).run; wp.
 sim (: ={glob E,glob ROF}); auto.
qed.

lemma source_sample_equiv (A<:KeygenDist.Distinguisher) &m x0 :
 equiv[A.guess ~ KeygenDist.S.sample :
 x{1}=x0 /\ (glob A){1}=(glob A){m} /\
 d{2}=mk(fun z=>Pr[A.guess(x0) @ &m : res=z]) ==> ={res}].
proof.
 bypr(res{1})(res{2}) => // &1 &2 z [hx [hg hd]].
 rewrite hx hd KeygenDist.sampleE -(KeygenDist.adv_mu1 A &m z x0).
 byequiv (_: ={x,glob A} ==> ={res}) => //.
 proc true; auto.
qed.

lemma keygen_source_mu (E<:KeygenExpand {-ROF}) &m x0 (event:keygen_output -> bool) :
 Pr[KeygenSource(E).guess(x0) @ &m : event res] =
 mu (mk(fun z=>Pr[KeygenSource(E).guess(x0) @ &m : res=z])) event.
proof.
 have hs : Pr[KeygenDist.S.sample(mk(fun z=>Pr[KeygenSource(E).guess(x0) @ &m : res=z]))
   @ &m : event res] = mu (mk(fun z=>Pr[KeygenSource(E).guess(x0) @ &m : res=z])) event.
 + byphoare (_: d=mk(fun z=>Pr[KeygenSource(E).guess(x0) @ &m : res=z]) ==> _) => //.
   proc; rnd; auto.
 rewrite -hs.
 by byequiv(source_sample_equiv (KeygenSource(E)) &m x0) => //.
qed.

lemma keygen_then_uniform_reified (E<:KeygenExpand {-ROF}) &m (event:kem_keygen_observation -> bool) :
 Pr[KeygenThenUniform(E).run() @ &m : event res] =
 Pr[ReifiedKeygenThenUniform.run(mk(fun z=>Pr[KeygenSource(E).guess(witness) @ &m : res=z]))
   @ &m : event res].
proof.
 byequiv (_: (glob E){1}=(glob E){m} /\ ROF.m{1}=ROF.m{m} /\
 d{2}=mk(fun z=>Pr[KeygenSource(E).guess(witness) @ &m : res=z]) ==> ={res}) => //.
 proc; rnd; rnd.
 outline{1} 1 ~ KeygenSource(E).guess.
 call(source_sample_equiv (KeygenSource(E)) &m witness); auto.
qed.

lemma reified_no_wrap_sample &m d0 :
 Pr[ReifiedKeygenThenUniform.run(d0) @ &m : honest_no_wrap res] =
 Pr[NoWrapDist.Sample(NoWrapObserver).main(d0) @ &m : res].
proof.
 byequiv (_: ={d} ==> honest_no_wrap res{1}=res{2}) => //.
 proc; inline KeygenDist.S.sample NoWrapObserver.guess.
 wp; rnd; rnd; wp; rnd; auto.
qed.
