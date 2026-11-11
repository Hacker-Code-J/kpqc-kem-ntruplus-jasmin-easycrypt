require import AllCore Distr FMap.
from Jasmin require import JWord.
require import Array192 Array14466.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteAttempt.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768KeygenCompleteRetry.
require import NTRUPlus768EncapCompleteRNG NTRUPlus768KEMFailureModel.
require import NTRUPlus768DecapCompleteProof NTRUPlus768ValidKeyM1Recovery.
require import NTRUPlus768PolyCBD1Algebra NTRUPlus768PolySOTPEncodeAlgebra.
require import NTRUPlus768ROMOracles NTRUPlus768ROMKeygen NTRUPlus768ROMCorrectness.
require import NTRUPlus768KEMPayloadSpec NTRUPlus768FreshRetryLaw.
require import NTRUPlus768StoppedKeygenModel NTRUPlus768NumericalDFRModel.
require import NTRUPlus768KEMProposalContext NTRUPlus768EncapFreshBridge.

module ROMKeygenEncapObservation = {
 proc run() : kem_keygen_observation = {
  var out:keygen_output; var rm:W8.t Array192.t*W8.t Array192.t;
  ROE.init(); ROF.init(); ROG.init(); ROH.init();
  out <@ KeygenInstrumented(UniformSeedRNG,ExpandROM,SHAKEFROM).run(witness);
  rm <@ EncapBufferObservation.run(out.`1);
  return(out,rm.`1,rm.`2);
 }
}.
module InitializedKeygenThenUniform(E:KeygenExpand) = {
 proc run() : kem_keygen_observation = {
  var x;
  ROE.init(); ROF.init(); ROG.init(); ROH.init();
  x <@ KeygenThenUniform(E).run(); return x;
 }
}.

lemma keygen_uniform_rng_equiv :
 equiv[KeygenInstrumented(KeygenRNGPort(UniformKEMRNG),ExpandROM,SHAKEFROM).run ~
       KeygenInstrumented(UniformSeedRNG,ExpandROM,SHAKEFROM).run :
 ={workspace,glob ROE,glob ROF} ==> ={res,glob ROE,glob ROF}].
proof.
 proc; inline KeygenRetry(KeygenRNGPort(UniformKEMRNG),ExpandROM).f
   KeygenRetry(KeygenRNGPort(UniformKEMRNG),ExpandROM).g
   KeygenRetry(UniformSeedRNG,ExpandROM).f KeygenRetry(UniformSeedRNG,ExpandROM).g
   KeygenRNGPort(UniformKEMRNG).sample UniformKEMRNG.seed32 UniformSeedRNG.sample.
 sim (: ={glob ROE,glob ROF}).
qed.
lemma encap_uniform_rng_equiv :
 equiv[EncapRandomInstrumented(SHAKEFROM,SHAKEGROM,SHAKEHROM,EncapRNGPort(UniformKEMRNG)).run ~
       EncapRandomInstrumented(SHAKEFROM,SHAKEGROM,SHAKEHROM,UniformCoins).run :
 ={pk,workspace,glob ROF,glob ROG,glob ROH} ==> ={res,glob ROF,glob ROG,glob ROH}].
proof.
 proc; inline EncapRNGPort(UniformKEMRNG).sample UniformKEMRNG.coins96 UniformCoins.sample.
 sim (: ={glob ROF,glob ROG,glob ROH}).
qed.

lemma rom_private_encap_observation :
 equiv[KEMROMPrivate(UniformKEMRNG).run ~ ROMKeygenEncapObservation.run :
 true ==> res.`2{1}= !honest_no_wrap res{2}].
proof.
 proc; inline{2} EncapBufferObservation.run.
 seq 5 5 : (w{1}=out.`1{2} /\ cleared{1}=out.`2{2} /\
   ={glob ROE,glob ROF,glob ROG,glob ROH}).
 + call keygen_uniform_rng_equiv.
   inline ROE.init ROF.init ROG.init ROH.init; auto.
 call{1}(complete_lossless SHAKEGROM SHAKEHROM ro_g_shake_ll ro_h_shake_ll).
 wp; call encap_uniform_rng_equiv.
 by auto=> />; rewrite /honest_no_wrap /payload_r /payload_m /poly_sotp_encode_spec /=.
qed.

lemma keygen_uniform_valid_equiv :
 equiv[KeygenInstrumented(UniformSeedRNG,ExpandROM,SHAKEFROM).run ~
       KeygenInstrumented(UniformSeedRNG,ExpandROM,SHAKEFROM).run :
 ={workspace,glob ROE,glob ROF} ==>
 ={res,glob ROE,glob ROF} /\ rom_key_relation res.`1{1} ROF.m{1}].
proof.
 conseq (_: _ ==> ={res,glob ROE,glob ROF})
   (rom_keygen_instrumented UniformSeedRNG ExpandROM) _ => />.
 sim.
qed.

lemma rom_encap_uniform_observation :
 equiv[ROMKeygenEncapObservation.run ~ InitializedKeygenThenUniform(ExpandROM).run :
 true ==> ={res}].
proof.
 proc; inline{2} KeygenThenUniform(ExpandROM).run.
 seq 5 5 : (out{1}=out{2} /\ ={glob ROE,glob ROF} /\
   rom_key_relation out.`1{1} ROF.m{1} /\ ROG.m{1}=empty /\ ROH.m{1}=empty).
 + call keygen_uniform_valid_equiv.
   inline ROE.init ROF.init ROG.init ROH.init; auto.
 outline{2} [1 .. 2] ~ UniformPayloadBuffers.sample.
 wp; ecall(encap_observation_uniform out.`1{1} ROF.m{1}); auto.
qed.

lemma rom_private_uniform_observation :
 equiv[KEMROMPrivate(UniformKEMRNG).run ~ InitializedKeygenThenUniform(ExpandROM).run :
 true ==> res.`2{1}= !honest_no_wrap res{2}].
proof.
 transitivity ROMKeygenEncapObservation.run
  (true ==> res.`2{1}= !honest_no_wrap res{2}) (true ==> ={res}) => //.
 + exact rom_private_encap_observation.
 + exact rom_encap_uniform_observation.
qed.
lemma initialized_rom_observation :
 equiv[InitializedKeygenThenUniform(ExpandROM).run ~ KeygenThenUniform(ExpandROM).run :
 ROE.m{2}=empty /\ ROF.m{2}=empty ==> ={res}].
proof.
 proc; inline{1} KeygenThenUniform(ExpandROM).run ROE.init ROF.init ROG.init ROH.init.
 wp; rnd; rnd; call (_: ={workspace,glob ROE,glob ROF} ==> ={res}); first by sim.
 auto.
qed.
lemma initialized_rom_bad_probability &m :
 Pr[KEMROMPrivate(UniformKEMRNG).run() @ &m : res.`2] =
 Pr[InitializedKeygenThenUniform(ExpandROM).run() @ &m : !honest_no_wrap res].
proof. byequiv rom_private_uniform_observation=> //; smt(). qed.
lemma initialized_rom_return_mass &m :
 Pr[KEMROMPrivate(UniformKEMRNG).run() @ &m : true] =
 Pr[InitializedKeygenThenUniform(ExpandROM).run() @ &m : true].
proof. byequiv rom_private_uniform_observation=> //; smt(). qed.
lemma rom_private_bad_probability &m : ROE.m{m}=empty => ROF.m{m}=empty =>
 Pr[KEMROMPrivate(UniformKEMRNG).run() @ &m : res.`2] =
 Pr[KeygenThenUniform(ExpandROM).run() @ &m : !honest_no_wrap res].
proof.
 move=> he hf; rewrite initialized_rom_bad_probability.
 byequiv initialized_rom_observation=> //; smt().
qed.
lemma rom_private_return_mass &m : ROE.m{m}=empty => ROF.m{m}=empty =>
 Pr[KEMROMPrivate(UniformKEMRNG).run() @ &m : true] =
 Pr[KeygenThenUniform(ExpandROM).run() @ &m : true].
proof.
 move=> he hf; rewrite initialized_rom_return_mass.
 byequiv initialized_rom_observation=> //; smt().
qed.
