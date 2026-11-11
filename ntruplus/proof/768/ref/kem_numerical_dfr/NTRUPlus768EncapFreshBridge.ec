require import AllCore Distr DProd FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array768 Array1152 Array1153 Array129 Array13634.
require import NTRUPlus768ROMDistributions NTRUPlus768ROMOracles NTRUPlus768ROMDomains.
require import NTRUPlus768ROMPayloadHash NTRUPlus768ROMEncap NTRUPlus768ROMKeygen.
require import NTRUPlus768KEMPayloadSpec NTRUPlus768KEMPayloadAlgebra.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteProof NTRUPlus768DecapCompleteSpec.
require import NTRUPlus768EncapCompleteHash NTRUPlus768EncapCompleteBody NTRUPlus768EncapCompleteProof.
require import NTRUPlus768EncapCompleteRNG NTRUPlus768KEMFailureModel NTRUPlus768EncapGuardProof.
require import NTRUPlus768EncapGuardSpec NTRUPlus768EncapClearProof NTRUPlus768EncapClearCoinsProof.
require import NTRUPlus768EncapHashFPrepareProof NTRUPlus768DecapHashHPrepareProof.
require import NTRUPlus768PolyCBD1CheckedProof NTRUPlus768PolyCBD1Algebra.
require import NTRUPlus768NTTProof NTRUPlus768DecapMessagePrepareProof.
require import NTRUPlus768PolySOTPEncodeCheckedProof NTRUPlus768PolySOTPEncodeAlgebra.
require import NTRUPlus768PolyBasemulProof NTRUPlus768PolyCenteredAddCorrectness.
require import NTRUPlus768PolyToBytesProof NTRUPlus768PolyToBytesAlgebra NTRUPlus768EncapCopyKeyProof.
require import NTRUPlus768NumericalDFRModel NTRUPlus768HashPayloadSampling.

module FreshHDraw = { proc sample() : W8.t Array224.t = {
 var x; x <$ uniform224; return x;
} }.
module FreshGDraw = { proc sample() : W8.t Array192.t = {
 var x; x <$ uniform192; return x;
} }.
module UniformPayloadBuffers = { proc sample() : W8.t Array192.t * W8.t Array192.t = {
 var r,m; r <$ uniform192; m <$ uniform192; return(r,m);
} }.
module FreshPayloadBuffers = {
 proc sample(coins:W8.t Array96.t) : W8.t Array192.t * W8.t Array192.t = {
  var h,p; var out:W8.t Array192.t*W8.t Array192.t;
  h <$ uniform224; p <$ uniform192;
  out <- (complete_hash_tail h,poly_sotp_encode_input coins p); return out;
 }
 proc run() : W8.t Array192.t * W8.t Array192.t = {
  var coins; var out:W8.t Array192.t*W8.t Array192.t;
  coins <$ uniform96; out <@ sample(coins); return out;
 }
}.
module EncapBufferObservation = {
 proc run(w:keygen_witness) : W8.t Array192.t * W8.t Array192.t = {
  var er:encap_result; var coins:W8.t Array96.t;
  var h:W8.t Array224.t; var p:W8.t Array192.t;
  (er,coins) <@ EncapRandomInstrumented(SHAKEFROM,SHAKEGROM,SHAKEHROM,UniformCoins).run(w.`kg_pk,witness);
  h <- oget ROH.m.[(coins,complete_sk_suffix w.`kg_sk)];
  p <- oget ROG.m.[payload_serialized h];
  return(complete_hash_tail h,poly_sotp_encode_input coins p);
 }
}.
module FreshEncapCore = {
 proc run(pk:W8.t Array1152.t,coins:W8.t Array96.t) : W8.t Array224.t*W8.t Array192.t = {
  var h,p; h <@ FreshHDraw.sample(); p <@ FreshGDraw.sample(); return(h,p);
 }
}.
module FreshEncapDerand = {
 proc run(pk:W8.t Array1152.t,coins:W8.t Array96.t) : W8.t Array224.t*W8.t Array192.t = {
  var hp; hp <@ FreshEncapCore.run(pk,coins); return hp;
 }
}.
module FreshEncapRandom = {
 proc run(pk:W8.t Array1152.t) : W8.t Array96.t*W8.t Array224.t*W8.t Array192.t = {
  var coins:W8.t Array96.t; var hp:W8.t Array224.t*W8.t Array192.t;
  coins <@ UniformCoins.sample(); hp <@ FreshEncapDerand.run(pk,coins);
  return(coins,hp.`1,hp.`2);
 }
}.
module FreshEncapObservation = {
 proc run(w:keygen_witness) : W8.t Array192.t*W8.t Array192.t = {
  var chp; chp <@ FreshEncapRandom.run(w.`kg_pk);
  return(complete_hash_tail chp.`2,poly_sotp_encode_input chp.`1 chp.`3);
 }
}.

lemma rom_f_cached_correct pk0 suffix0 fm0 : fm0.[pk0]=Some suffix0 =>
 phoare[SHAKEFROM.shake:input=encap_hash_f_input_spec pk0 /\ ROF.m=fm0 ==>
 res=suffix0 /\ ROF.m=fm0]=1%r.
proof. move=> hc; by conseq ro_f_shake_ll (rom_f_cached pk0 suffix0 fm0 hc). qed.

lemma encap_seed_fresh pk0 coins0 suffix0 fm0 : fm0.[pk0]=Some suffix0 =>
 equiv[EncapSeed(SHAKEFROM,SHAKEHROM).run ~ FreshHDraw.sample :
 pk{1}=pk0 /\ coins{1}=coins0 /\ ROF.m{1}=fm0 /\ ROH.m{1}=empty ==>
 ={res} /\ ROF.m{1}=fm0 /\ ROH.m{1}.[(coins0,suffix0)]=Some res{2}].
proof.
 move=> hc; proc.
 seq 3 0 : (inputh{1}=hash_h_prepare_spec coins0 suffix0 /\ ROF.m{1}=fm0 /\ ROH.m{1}=empty).
 + ecall{1}(hash_h_prepare_correct witness coins0 suffix0).
   ecall{1}(rom_f_cached_correct pk0 suffix0 fm0 hc).
   ecall{1}(encap_hash_f_prepare_correct witness pk0); auto.
 inline SHAKEHROM.shake ROH.get; sp.
 rcondt{1} 1; first by auto; smt(mem_empty).
 auto=> />.
 by move=>r hr; rewrite payload_h_preparation peel_encode_h !get_set_sameE /=.
qed.

lemma encap_body_fresh h0 :
 equiv[EncapBody(SHAKEGROM).run ~ FreshGDraw.sample :
 hashout{1}=h0 /\ ROG.m{1}=empty ==>
 ROG.m{1}.[payload_serialized h0]=Some res{2}].
proof.
 proc.
 seq 3 0 : (input{1}=message_hash_input(payload_serialized h0) /\ ROG.m{1}=empty).
 + ecall{1}(message_prepare_correct witness witness (payload_rhat h0) (payload_rhat_range h0)).
   ecall{1}(ntt_correct witness(payload_r h0)).
   ecall{1}(poly_cbd1_correct witness(complete_hash_tail h0)).
   auto=> />; by rewrite payload_rE payload_rhatE poly_tobytes_procedure_specE payload_serializedE.
 call{1} encap_copy_key_lossless; call{1} poly_tobytes_lossless;
 call{1} poly_centered_add_lossless; call{1} poly_basemul_lossless;
 call{1} ntt_lossless; call{1} poly_sotp_encode_lossless.
 inline SHAKEGROM.shake ROG.get; sp.
 rcondt{1} 1; first by auto; smt(mem_empty).
 auto=> />.
 by move=>r hr; rewrite payload_g_preparation peel_encode_g !get_set_sameE /=.
qed.

lemma fresh_payload_dlet coins :
 dlet uniform224 (fun h=>dmap uniform192 (fun p=>
   (complete_hash_tail h,poly_sotp_encode_input coins p))) =
 (uniform192 `*` uniform192).
proof.
 rewrite -(fresh_payload_buffer_pair_law coins) dprod_dlet dmap_dlet.
 apply eq_dlet=> // h.
 change (dmap uniform192 (fun p=>(complete_hash_tail h,poly_sotp_encode_input coins p)) =
   dmap (dmap uniform192 (fun p=>(h,p)))
    (fun hp:W8.t Array224.t*W8.t Array192.t =>
      (complete_hash_tail hp.`1,poly_sotp_encode_input coins hp.`2))).
 by rewrite (dmap_comp (fun p:W8.t Array192.t=>(h,p))
  (fun hp:W8.t Array224.t*W8.t Array192.t =>
   (complete_hash_tail hp.`1,poly_sotp_encode_input coins hp.`2)) uniform192) /(\o) /=.
qed.
lemma fresh_payload_buffers_uniform :
 equiv[FreshPayloadBuffers.sample ~ UniformPayloadBuffers.sample : true ==> ={res}].
proof.
 proc; rnd : *0 *0 => /=; auto=> /> &1.
 rewrite fresh_payload_dlet -dprod_dlet.
 split; first done.
 by move=> _ [r m] ho; split=> //.
qed.

lemma encap_core_fresh pk0 coins0 suffix0 fm0 :
 encap_key_canonical pk0 => fm0.[pk0]=Some suffix0 =>
 equiv[EncapCore(SHAKEFROM,SHAKEGROM,SHAKEHROM).run ~ FreshEncapCore.run :
 pk{1}=pk0 /\ coins{1}=coins0 /\ ROF.m{1}=fm0 /\ ROG.m{1}=empty /\ ROH.m{1}=empty ==>
 ROF.m{1}=fm0 /\ ROH.m{1}.[(coins0,suffix0)]=Some res.`1{2} /\
 ROG.m{1}.[payload_serialized res.`1{2}]=Some res.`2{2}].
proof.
 move=> hk hc; proc; rcondt{1} 2.
 + move=> &m; call(encap_guard_canonical_functional witness encap_zero_ct encap_zero_ss pk0 hk); auto.
 ecall(encap_body_fresh h{2}).
 call(encap_seed_fresh pk0 coins0 suffix0 fm0 hc).
 call{1} encap_guard_lossless; auto.
qed.
lemma encap_derand_fresh pk0 coins0 suffix0 fm0 :
 encap_key_canonical pk0 => fm0.[pk0]=Some suffix0 =>
 equiv[EncapDerand(SHAKEFROM,SHAKEGROM,SHAKEHROM).run ~ FreshEncapDerand.run :
 pk{1}=pk0 /\ coins{1}=coins0 /\ ROF.m{1}=fm0 /\ ROG.m{1}=empty /\ ROH.m{1}=empty ==>
 ROF.m{1}=fm0 /\ ROH.m{1}.[(coins0,suffix0)]=Some res.`1{2} /\
 ROG.m{1}.[payload_serialized res.`1{2}]=Some res.`2{2}].
proof.
 move=> hk hc; proc; call{1} encap_clear_lossless.
 call(encap_core_fresh pk0 coins0 suffix0 fm0 hk hc); auto.
qed.
lemma encap_instrumented_fresh pk0 suffix0 fm0 :
 encap_key_canonical pk0 => fm0.[pk0]=Some suffix0 =>
 equiv[EncapRandomInstrumented(SHAKEFROM,SHAKEGROM,SHAKEHROM,UniformCoins).run ~ FreshEncapRandom.run :
 pk{1}=pk0 /\ ROF.m{1}=fm0 /\ ROG.m{1}=empty /\ ROH.m{1}=empty ==>
 res.`2{1}=res.`1{2} /\ ROF.m{1}=fm0 /\
 ROH.m{1}.[(res.`1{2},suffix0)]=Some res.`2{2} /\
 ROG.m{1}.[payload_serialized res.`2{2}]=Some res.`3{2}].
proof.
 move=> hk hc; proc; call{1} encap_clear_coins_lossless.
 ecall(encap_derand_fresh pk0 coins{2} suffix0 fm0 hk hc).
 wp; call (_:true ==> ={res}); first by sim.
 auto.
qed.

lemma encap_observation_fresh w0 fm0 :
 equiv[EncapBufferObservation.run ~ FreshEncapObservation.run :
 w{1}=w0 /\ ROF.m{1}=fm0 /\ rom_key_relation w0 fm0 /\
 ROG.m{1}=empty /\ ROH.m{1}=empty ==> ={res}].
proof.
 case(rom_key_relation w0 fm0)=>hk.
 + rewrite /rom_key_relation in hk; have [hkey hf]:=hk.
   have hcan:=payload_key_canonical _ _ _ _ _ _ _ _ hkey.
   move:hcan=>[hpk hsk].
   proc; wp; call(encap_instrumented_fresh w0.`kg_pk (complete_sk_suffix w0.`kg_sk) fm0 hpk hf).
   auto=> />.
   by move=> rl rr gm hm he hh hg; rewrite he hh /= hg /=.
 + conseq (_:false ==> true)=> //; smt().
qed.

lemma fresh_observation_payload :
 equiv[FreshEncapObservation.run ~ FreshPayloadBuffers.run : true ==> ={res}].
proof.
 proc; inline FreshEncapRandom.run FreshEncapDerand.run FreshEncapCore.run UniformCoins.sample
   FreshHDraw.sample FreshGDraw.sample FreshPayloadBuffers.sample.
 auto.
qed.
lemma fresh_payload_run_uniform :
 equiv[FreshPayloadBuffers.run ~ UniformPayloadBuffers.sample : true ==> ={res}].
proof.
 proc; outline{2} [1 .. 2] ~ UniformPayloadBuffers.sample.
 call fresh_payload_buffers_uniform; rnd{1}; auto=> />; smt(uniform96_ll).
qed.

lemma encap_observation_uniform w0 fm0 :
 equiv[EncapBufferObservation.run ~ UniformPayloadBuffers.sample :
 w{1}=w0 /\ ROF.m{1}=fm0 /\ rom_key_relation w0 fm0 /\
 ROG.m{1}=empty /\ ROH.m{1}=empty ==> ={res}].
proof.
 transitivity FreshEncapObservation.run
  (w{1}=w0 /\ ROF.m{1}=fm0 /\ rom_key_relation w0 fm0 /\
   ROG.m{1}=empty /\ ROH.m{1}=empty ==> ={res})
  (true ==> ={res}) => //.
 + exact(encap_observation_fresh w0 fm0).
 transitivity FreshPayloadBuffers.run (true ==> ={res}) (true ==> ={res}) => //.
 + exact fresh_observation_payload.
 + exact fresh_payload_run_uniform.
qed.
lemma encap_instrumented_uniform_lossless :
 islossless EncapRandomInstrumented(SHAKEFROM,SHAKEGROM,SHAKEHROM,UniformCoins).run.
proof.
 proc; call encap_clear_coins_lossless.
 call(encap_derand_lossless SHAKEFROM SHAKEGROM SHAKEHROM
   ro_f_shake_ll ro_g_shake_ll ro_h_shake_ll).
 wp; call uniform_coins_ll; auto.
qed.
lemma encap_buffer_observation_lossless : islossless EncapBufferObservation.run.
proof. proc; wp; call encap_instrumented_uniform_lossless; auto. qed.
