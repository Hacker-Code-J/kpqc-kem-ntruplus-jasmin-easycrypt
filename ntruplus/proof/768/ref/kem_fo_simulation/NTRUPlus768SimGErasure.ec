require import AllCore Distr FMap.
from Jasmin require import JWord.
require import Array32 Array192 Array1152 Array2336.
require import NTRUPlus768FOModel NTRUPlus768FOSetupDistribution.
require import NTRUPlus768FOEagerG NTRUPlus768FOGAdapters.
require import NTRUPlus768CCAStatusAdapter NTRUPlus768CCADecapOracle.
require import NTRUPlus768ROMOracles NTRUPlus768RawXOFStreams NTRUPlus768RawXOF NTRUPlus768CCAOraclePorts.
require import NTRUPlus768SimOracles.
require import NTRUPlus768SimModel NTRUPlus768SimSampling NTRUPlus768SimPrefix NTRUPlus768SimLookup.
require import NTRUPlus768DecapMessageProof NTRUPlus768DecapR2CompCaller.
require import NTRUPlus768PolySOTPDecodeCheckedLossless.

(* This adapter discards the oracle response. It is used only inside a
   prefix whose complete result is discarded before the public lookup. *)
module SimGSampleGet(G:SimGRO.RO) : FOGPort = {
 proc get(input:W8.t Array1152.t) : W8.t Array192.t = {
  G.sample(input);return witness;
 }
}.
module SimGhostLookup(G:FOGPort) : CCADecapPort = {
 proc decap(ct:W8.t Array1152.t) : cca_reply = {
  var request:sim_request option;var result:cca_reply;
  if(SimPublic.cstar<>Some ct){
   request <@ SimPrefix(G).run(SimPublic.pk,ct,CCADecapOracle.sk);
  }
  result <@ SimLookup(G).decap(ct);
  return result;
 }
}.
module SimGhostSampleLookup(G:SimGRO.RO) : CCADecapPort = {
 proc decap(ct:W8.t Array1152.t) : cca_reply = {
  var request:sim_request option;var result:cca_reply;
  if(SimPublic.cstar<>Some ct){
   request <@ SimPrefix(SimGSampleGet(G)).run(SimPublic.pk,ct,CCADecapOracle.sk);
  }
  result <@ SimLookup(SimGPROMGet(G)).decap(ct);
  return result;
 }
}.

module type SimGDecapContext(O:CCAExtendedOraclePort,D:CCADecapPort) = {
 proc distinguish(s:fo_setup_observation) : bool {O.e,O.f,O.g,O.h,O.raw,D.decap}
}.
module SimGGetWorld(C:SimGDecapContext,G:FOGPort) = {
 proc distinguish(s:fo_setup_observation) : bool = {
  var b;b <@ C(SimOracles(G,SimHActual),SimGhostLookup(G)).distinguish(s);return b;
 }
}.
module SimGSampleWorld(C:SimGDecapContext,G:SimGRO.RO) = {
 proc distinguish(s:fo_setup_observation) : bool = {
  var b;b <@ C(SimOracles(SimGPROMGet(G),SimHActual),SimGhostSampleLookup(G)).distinguish(s);return b;
 }
}.
module SimGLookupWorld(C:SimGDecapContext,G:FOGPort) = {
 proc distinguish(s:fo_setup_observation) : bool = {
  var b;b <@ C(SimOracles(G,SimHActual),SimLookup(G)).distinguish(s);return b;
 }
}.

lemma sim_ghost_lookup_ll (G<:FOGPort) :
 islossless G.get=>islossless SimGhostLookup(G).decap.
proof.
 move=>hg;proc;call(sim_lookup_lossless G hg);if;last by auto.
 call(sim_prefix_ll G hg);auto.
qed.

lemma sim_g_get_sample_discard :
 equiv[SimGPROMGet(SimGRO.RO).get ~ SimGSampleGet(SimGRO.RO).get:
 ={input,SimGRO.RO.m} ==> ={SimGRO.RO.m}].
proof.
 proc;inline{2} SimGRO.RO.sample;wp.
 call(_: ={x,SimGRO.RO.m} ==> ={res,SimGRO.RO.m});first by sim.
 auto.
qed.
lemma sim_g_message_discard :
 equiv[DecapMessage(FOGHash(SimGPROMGet(SimGRO.RO))).run ~
       DecapMessage(FOGHash(SimGSampleGet(SimGRO.RO))).run:
 ={arg,SimGRO.RO.m} ==> ={SimGRO.RO.m}].
proof.
 proc;call{1} poly_sotp_decode_lossless;call{2} poly_sotp_decode_lossless.
 inline FOGHash(SimGPROMGet(SimGRO.RO)).shake FOGHash(SimGSampleGet(SimGRO.RO)).shake.
 wp;call sim_g_get_sample_discard;wp.
 call(_: ={arg} ==> ={res});first by sim.
 auto.
qed.
lemma sim_g_prefix_discard :
 equiv[SimPrefix(SimGPROMGet(SimGRO.RO)).run ~ SimPrefix(SimGSampleGet(SimGRO.RO)).run:
 ={arg,SimGRO.RO.m} ==> ={SimGRO.RO.m}].
proof.
 proc;seq 2 2:(={pk,ct,sk,rp,mp,status,SimGRO.RO.m}).
 + wp;call(_: ={arg} ==> ={res});first by sim. auto.
 if;first by auto.
 + wp;call sim_g_message_discard;auto.
 auto.
qed.
lemma sim_g_sample_lazy_ll : islossless SimGSampleGet(SimGRO.LRO).get.
proof. proc;inline SimGRO.LRO.sample;auto. qed.
lemma sim_g_ghost_sample :
 equiv[SimGhostLookup(SimGPROMGet(SimGRO.RO)).decap ~ SimGhostSampleLookup(SimGRO.RO).decap:
 ={ct,SimGRO.RO.m,glob SimPublic,SimHistory.h,CCADecapOracle.sk} ==>
 ={res,SimGRO.RO.m,glob SimPublic,SimHistory.h,CCADecapOracle.sk}].
proof.
 proc;call(_: ={arg,SimGRO.RO.m,glob SimPublic,SimHistory.h} ==>
  ={res,SimGRO.RO.m,glob SimPublic,SimHistory.h});first by sim.
 if;first by auto.
 + call sim_g_prefix_discard;auto.
 auto.
qed.
lemma sim_g_sample_lookup :
 equiv[SimGhostSampleLookup(SimGRO.LRO).decap ~ SimLookup(SimGPROMGet(SimGRO.RO)).decap:
 ={ct,SimGRO.RO.m,glob SimPublic,SimHistory.h,CCADecapOracle.sk} ==>
 ={res,SimGRO.RO.m,glob SimPublic,SimHistory.h,CCADecapOracle.sk}].
proof.
 proc*;inline{1} SimGhostSampleLookup(SimGRO.LRO).decap.
 wp;call(_: ={arg,SimGRO.RO.m,glob SimPublic,SimHistory.h} ==>
  ={res,SimGRO.RO.m,glob SimPublic,SimHistory.h});first by sim.
 sp 1 0;if{1};last by auto.
 call{1}(sim_prefix_ll (SimGSampleGet(SimGRO.LRO)) sim_g_sample_lazy_ll);auto.
qed.

lemma sim_g_ghost_sample_context
 (C<:SimGDecapContext {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-CCADecapOracle,-SimGRO.RO,-SimGRO.FRO}) :
 equiv[SimGGetWorld(C,SimGPROMGet(SimGRO.RO)).distinguish ~ SimGSampleWorld(C,SimGRO.RO).distinguish:
 ={arg,glob C,SimGRO.RO.m,ROE.m,ROF.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,glob SimPublic,SimHistory.h,CCADecapOracle.sk} ==>
 ={res,glob C,SimGRO.RO.m,ROE.m,ROF.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,glob SimPublic,SimHistory.h,CCADecapOracle.sk}].
proof.
 proc;call(_: ={SimGRO.RO.m,ROE.m,ROF.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,glob SimPublic,SimHistory.h,CCADecapOracle.sk}).
 + by sim.
 + by sim.
 + by sim.
 + by sim.
 + by sim.
 + conseq sim_g_ghost_sample;smt().
 auto.
qed.
lemma sim_g_sample_world_erase
 (C<:SimGDecapContext {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-CCADecapOracle,-SimGRO.RO,-SimGRO.FRO}) :
 equiv[SimGSampleWorld(C,SimGRO.RO).distinguish ~ SimGSampleWorld(C,SimGRO.LRO).distinguish:
 ={arg,glob C,SimGRO.RO.m,ROE.m,ROF.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,glob SimPublic,SimHistory.h,CCADecapOracle.sk} ==>
 ={res,glob C,ROE.m,ROF.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,glob SimPublic,SimHistory.h,CCADecapOracle.sk}].
proof. conseq(sim_g_sampling_erase (SimGSampleWorld(C)));smt(). qed.
lemma sim_g_sample_lookup_context
 (C<:SimGDecapContext {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-CCADecapOracle,-SimGRO.RO,-SimGRO.FRO}) :
 equiv[SimGSampleWorld(C,SimGRO.LRO).distinguish ~ SimGLookupWorld(C,SimGPROMGet(SimGRO.RO)).distinguish:
 ={arg,glob C,SimGRO.RO.m,ROE.m,ROF.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,glob SimPublic,SimHistory.h,CCADecapOracle.sk} ==>
 ={res,glob C,SimGRO.RO.m,ROE.m,ROF.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,glob SimPublic,SimHistory.h,CCADecapOracle.sk}].
proof.
 proc;call(_: ={SimGRO.RO.m,ROE.m,ROF.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,glob SimPublic,SimHistory.h,CCADecapOracle.sk}).
 + by sim.
 + by sim.
 + by sim.
 + by sim.
 + by sim.
 + conseq sim_g_sample_lookup;smt().
 auto.
qed.

(* The private clone starts from the actual, possibly nonempty cache.
   No input is resampled or treated as fresh by this initialization. *)
module SimGGetInitialized(C:SimGDecapContext) = {
 proc distinguish(s:fo_setup_observation) : bool = {
  var b;SimGRO.RO.m<-ROG.m;
  b<@SimGGetWorld(C,SimGPROMGet(SimGRO.RO)).distinguish(s);return b;
 }
}.
module SimGSampleInitialized(C:SimGDecapContext,G:SimGRO.RO) = {
 proc distinguish(s:fo_setup_observation) : bool = {
  var b;SimGRO.RO.m<-ROG.m;
  b<@SimGSampleWorld(C,G).distinguish(s);return b;
 }
}.
module SimGLookupInitialized(C:SimGDecapContext) = {
 proc distinguish(s:fo_setup_observation) : bool = {
  var b;SimGRO.RO.m<-ROG.m;
  b<@SimGLookupWorld(C,SimGPROMGet(SimGRO.RO)).distinguish(s);return b;
 }
}.

lemma sim_g_get_initialize
 (C<:SimGDecapContext {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-CCADecapOracle,-SimGRO.RO,-SimGRO.FRO}) :
 equiv[SimGGetWorld(C,FOGActual).distinguish ~ SimGGetInitialized(C).distinguish:
 ={arg,glob C,ROG.m,ROE.m,ROF.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,glob SimPublic,SimHistory.h,CCADecapOracle.sk} ==> ={res,glob C,ROE.m,ROF.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,glob SimPublic,SimHistory.h,CCADecapOracle.sk}].
proof.
 proc*;inline{2} SimGGetInitialized(C).distinguish;wp.
 call(sim_g_query_context_adapter (SimGGetWorld(C)));auto.
qed.

lemma sim_g_lookup_initialize
 (C<:SimGDecapContext {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-CCADecapOracle,-SimGRO.RO,-SimGRO.FRO}) :
 equiv[SimGLookupWorld(C,FOGActual).distinguish ~ SimGLookupInitialized(C).distinguish:
 ={arg,glob C,ROG.m,ROE.m,ROF.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,glob SimPublic,SimHistory.h,CCADecapOracle.sk} ==> ={res,glob C,ROE.m,ROF.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,glob SimPublic,SimHistory.h,CCADecapOracle.sk}].
proof.
 proc*;inline{2} SimGLookupInitialized(C).distinguish;wp.
 call(sim_g_query_context_adapter (SimGLookupWorld(C)));auto.
qed.

lemma sim_g_initialized_sample_probability
 (C<:SimGDecapContext {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-CCADecapOracle,-SimGRO.RO,-SimGRO.FRO}) &m s0 (event:bool->bool) :
 Pr[SimGGetInitialized(C).distinguish(s0) @ &m:event res]=
 Pr[SimGSampleInitialized(C,SimGRO.RO).distinguish(s0) @ &m:event res].
proof.
 byequiv(_: ={arg,glob C,ROG.m,ROE.m,ROF.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,glob SimPublic,SimHistory.h,CCADecapOracle.sk} ==> ={res})=> //.
 proc;call(sim_g_ghost_sample_context C);auto.
qed.
lemma sim_g_initialized_erase_probability
 (C<:SimGDecapContext {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-CCADecapOracle,-SimGRO.RO,-SimGRO.FRO}) &m s0 (event:bool->bool) :
 Pr[SimGSampleInitialized(C,SimGRO.RO).distinguish(s0) @ &m:event res]=
 Pr[SimGSampleInitialized(C,SimGRO.LRO).distinguish(s0) @ &m:event res].
proof.
 byequiv(_: ={arg,glob C,ROG.m,ROE.m,ROF.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,glob SimPublic,SimHistory.h,CCADecapOracle.sk} ==> ={res})=> //.
 proc;call(sim_g_sample_world_erase C);auto.
qed.
lemma sim_g_initialized_lookup_probability
 (C<:SimGDecapContext {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-CCADecapOracle,-SimGRO.RO,-SimGRO.FRO}) &m s0 (event:bool->bool) :
 Pr[SimGSampleInitialized(C,SimGRO.LRO).distinguish(s0) @ &m:event res]=
 Pr[SimGLookupInitialized(C).distinguish(s0) @ &m:event res].
proof.
 byequiv(_: ={arg,glob C,ROG.m,ROE.m,ROF.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,glob SimPublic,SimHistory.h,CCADecapOracle.sk} ==> ={res})=> //.
 proc;call(sim_g_sample_lookup_context C);auto.
qed.

(* All adaptive continuation is inside C. In particular this equality does
   not assert equality of the final physical G-cache domains. *)
lemma sim_g_ghost_lookup_probability
 (C<:SimGDecapContext {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-CCADecapOracle,-SimGRO.RO,-SimGRO.FRO}) &m s0 (event:bool->bool) :
 Pr[SimGGetWorld(C,FOGActual).distinguish(s0) @ &m:event res]=
 Pr[SimGLookupWorld(C,FOGActual).distinguish(s0) @ &m:event res].
proof.
 have hg:Pr[SimGGetWorld(C,FOGActual).distinguish(s0) @ &m:event res]=
  Pr[SimGGetInitialized(C).distinguish(s0) @ &m:event res]
  by byequiv(sim_g_get_initialize C)=> //.
 have hl:Pr[SimGLookupWorld(C,FOGActual).distinguish(s0) @ &m:event res]=
  Pr[SimGLookupInitialized(C).distinguish(s0) @ &m:event res]
  by byequiv(sim_g_lookup_initialize C)=> //.
 rewrite hg hl (sim_g_initialized_sample_probability C &m s0 event)
  (sim_g_initialized_erase_probability C &m s0 event).
 exact(sim_g_initialized_lookup_probability C &m s0 event).
qed.
