require import AllCore Distr FMap.
from Jasmin require import JWord.
require import Array129 Array192 Array224 Array1152.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions NTRUPlus768ROMDomains.
require import NTRUPlus768FOModel NTRUPlus768FOSetupDistribution NTRUPlus768DecapCompleteHash.
require import NTRUPlus768FOEagerG NTRUPlus768FOGAdapters NTRUPlus768SimModel.

module SimHActual : SimHPort = {proc get=ROH.get}.
module SimGActual = FOGActual.
module SimHPROMGet(H:SimHRO.RO) : SimHPort = {
 proc get(input:fo_h_input) : W8.t Array224.t = {
  var y; y <@ H.get(input); return y;
 }
}.
module SimGPROMGet(G:SimGRO.RO) : FOGPort = {
 proc get(input:W8.t Array1152.t) : W8.t Array192.t = {
  var y; y <@ G.get(input); return y;
 }
}.
module SimHShake(H:SimHPort) : CompleteSHAKEH = {
 proc shake(input:W8.t Array129.t) : W8.t Array224.t = {
  var y; y <@ H.get(peel_h input); return y;
 }
}.

module type SimHQueryContext(H:SimHPort) = {
 proc distinguish(s:fo_setup_observation) : bool {H.get}
}.
module type SimGQueryContext(G:FOGPort) = {
 proc distinguish(s:fo_setup_observation) : bool {G.get}
}.
(* sample returns no value. Any computation observing a hidden response
   must be projected or bounded before using these erasure contracts. *)
module type SimHSamplingContext(H:SimHRO.RO) = {
 proc distinguish(s:fo_setup_observation) : bool {H.get,H.sample}
}.
module type SimGSamplingContext(G:SimGRO.RO) = {
 proc distinguish(s:fo_setup_observation) : bool {G.get,G.sample}
}.

lemma sim_h_prom_get_adapter :
 equiv[ROH.get ~ SimHRO.RO.get:
 input{1}=x{2} /\ ROH.m{1}=SimHRO.RO.m{2} ==>
 ={res} /\ ROH.m{1}=SimHRO.RO.m{2}].
proof.
 proc; case(input{1} \in ROH.m{1}).
 + rcondf{1} 1; first by auto.
   rcondf{2} 2; first by auto.
   rnd{2}; auto=> />; by rewrite uniform224_ll.
 rcondt{1} 1; first by auto.
 rcondt{2} 2; first by auto.
 auto.
qed.
lemma sim_g_prom_get_adapter :
 equiv[ROG.get ~ SimGRO.RO.get:
 input{1}=x{2} /\ ROG.m{1}=SimGRO.RO.m{2} ==>
 ={res} /\ ROG.m{1}=SimGRO.RO.m{2}].
proof.
 proc; case(input{1} \in ROG.m{1}).
 + rcondf{1} 1; first by auto.
   rcondf{2} 2; first by auto.
   rnd{2}; auto=> />; by rewrite uniform192_ll.
 rcondt{1} 1; first by auto.
 rcondt{2} 2; first by auto.
 auto.
qed.
lemma sim_hshake_actual :
 equiv[SimHShake(SimHActual).shake ~ SHAKEHROM.shake:
 ={arg,ROH.m} ==> ={res,ROH.m}].
proof. proc; sim. qed.
lemma sim_hshake_lossless (H<:SimHPort) : islossless H.get=>islossless SimHShake(H).shake.
proof. move=>h; proc; call h; auto. qed.
lemma sim_h_prom_get_lossless : islossless SimHPROMGet(SimHRO.RO).get.
proof.
 proc; call(SimHRO.RO_get_ll _); first by move=>x; exact uniform224_ll.
 auto.
qed.
lemma sim_g_prom_get_lossless : islossless SimGPROMGet(SimGRO.RO).get.
proof.
 proc; call(SimGRO.RO_get_ll _); first by move=>x; exact uniform192_ll.
 auto.
qed.

lemma sim_h_query_context_adapter
 (C<:SimHQueryContext {-ROH,-SimHRO.RO,-SimHRO.FRO}) :
 equiv[C(SimHActual).distinguish ~ C(SimHPROMGet(SimHRO.RO)).distinguish:
 ={arg,glob C} /\ ROH.m{1}=SimHRO.RO.m{2} ==>
 ={res,glob C} /\ ROH.m{1}=SimHRO.RO.m{2}].
proof.
 proc(ROH.m{1}=SimHRO.RO.m{2})=> //.
 proc*; inline{2} SimHPROMGet(SimHRO.RO).get; wp.
 call sim_h_prom_get_adapter; auto.
qed.
lemma sim_g_query_context_adapter
 (C<:SimGQueryContext {-ROG,-SimGRO.RO,-SimGRO.FRO}) :
 equiv[C(SimGActual).distinguish ~ C(SimGPROMGet(SimGRO.RO)).distinguish:
 ={arg,glob C} /\ ROG.m{1}=SimGRO.RO.m{2} ==>
 ={res,glob C} /\ ROG.m{1}=SimGRO.RO.m{2}].
proof.
 proc(ROG.m{1}=SimGRO.RO.m{2})=> //.
 proc*; inline{2} SimGPROMGet(SimGRO.RO).get; wp.
 call sim_g_prom_get_adapter; auto.
qed.

(* Only the public result and context state are preserved. Internal lazy
   cache domains may differ after removing unobserved sample calls. *)
lemma sim_h_sampling_erase
 (C<:SimHSamplingContext {-ROH,-SimHRO.RO,-SimHRO.FRO}) :
 equiv[C(SimHRO.RO).distinguish ~ C(SimHRO.LRO).distinguish:
 ={arg,glob C,SimHRO.RO.m} ==> ={res,glob C}].
proof.
 have hl:forall (_:fo_h_input),is_lossless uniform224 by move=>x; exact uniform224_ll.
 conseq(SimHRO.FullEager.RO_LRO_D C hl); smt().
qed.
lemma sim_g_sampling_erase
 (C<:SimGSamplingContext {-ROG,-SimGRO.RO,-SimGRO.FRO}) :
 equiv[C(SimGRO.RO).distinguish ~ C(SimGRO.LRO).distinguish:
 ={arg,glob C,SimGRO.RO.m} ==> ={res,glob C}].
proof.
 have hl:forall (_:W8.t Array1152.t),is_lossless uniform192 by move=>x; exact uniform192_ll.
 conseq(SimGRO.FullEager.RO_LRO_D C hl); smt().
qed.
lemma sim_h_sampling_probability
 (C<:SimHSamplingContext {-ROH,-SimHRO.RO,-SimHRO.FRO}) &m s0 (event:bool->bool) :
 Pr[C(SimHRO.RO).distinguish(s0) @ &m:event res]=
 Pr[C(SimHRO.LRO).distinguish(s0) @ &m:event res].
proof. by byequiv(sim_h_sampling_erase C)=> //. qed.
lemma sim_g_sampling_probability
 (C<:SimGSamplingContext {-ROG,-SimGRO.RO,-SimGRO.FRO}) &m s0 (event:bool->bool) :
 Pr[C(SimGRO.RO).distinguish(s0) @ &m:event res]=
 Pr[C(SimGRO.LRO).distinguish(s0) @ &m:event res].
proof. by byequiv(sim_g_sampling_erase C)=> //. qed.
