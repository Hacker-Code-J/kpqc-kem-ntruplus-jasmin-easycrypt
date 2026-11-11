require import AllCore Distr FMap.
from Jasmin require import JWord.
require import Array32 Array224 Array1152.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions.
require import NTRUPlus768FOModel NTRUPlus768FOSetupDistribution.
require import NTRUPlus768SimModel NTRUPlus768SimSampling NTRUPlus768SimOracles.

(* This private flag records every public typed/raw H request, including
   repeated requests and requests whose raw output length is zero. *)
module CPAHitState = {
 var target:fo_h_input
 var hit:bool
 proc init(x:fo_h_input) = {target<-x;hit<-false;}
}.
module CPAHitH : SimHPort = {
 proc get(input:fo_h_input) : W8.t Array224.t = {
  var y;
  CPAHitState.hit<-CPAHitState.hit || input=CPAHitState.target;
  y<@ROH.get(input);
  return y;
 }
}.
module type CPAHContext(H:SimHPort) = {
 proc run(pk:W8.t Array1152.t,ct:W8.t Array1152.t,key:W8.t Array32.t) : bool {H.get}
}.
op cpa_h_outside (x:fo_h_input)
 (m1 m2:(fo_h_input,W8.t Array224.t)fmap) =
 forall z,z<>x=>m1.[z]=m2.[z].

lemma cpa_hit_init_ll : islossless CPAHitState.init.
proof. proc;auto. qed.
lemma cpa_hit_h_ll : islossless CPAHitH.get.
proof. proc;call roh_get_ll;auto. qed.
lemma cpa_hit_h_projection :
 equiv[CPAHitH.get ~ SimHActual.get :
 ={arg,ROH.m} ==> ={res,ROH.m}].
proof. proc*;inline{1} CPAHitH.get;wp;call(_: ={arg,ROH.m} ==> ={res,ROH.m});first by sim. auto. qed.
lemma cpa_hit_h_latched :
 hoare[CPAHitH.get : CPAHitState.hit ==> CPAHitState.hit].
proof. proc;call(_:true ==>true);first by trivial. auto;smt(). qed.
lemma cpa_hit_h_exact x0 b0 input0 :
 hoare[CPAHitH.get : CPAHitState.target=x0 /\ CPAHitState.hit=b0 /\ input=input0 ==>
 CPAHitState.target=x0 /\ CPAHitState.hit=(b0 || input0=x0)].
proof. proc;call(_:true ==>true);first by trivial. auto. qed.

lemma cpa_h_outside_refl x m : cpa_h_outside x m m.
proof. by rewrite /cpa_h_outside. qed.
lemma cpa_h_outside_empty_single x y : cpa_h_outside x empty empty.[x<-y].
proof. rewrite /cpa_h_outside=>z hz;rewrite get_setE hz;done. qed.
lemma cpa_h_outside_set x m1 m2 z y :
 cpa_h_outside x m1 m2=>cpa_h_outside x m1.[z<-y] m2.[z<-y].
proof. rewrite /cpa_h_outside=>h v hv;rewrite !get_setE;smt(). qed.

lemma cpa_hit_h_step :
 equiv[CPAHitH.get ~ CPAHitH.get :
 ={arg,glob CPAHitState} /\ cpa_h_outside CPAHitState.target{1} ROH.m{1} ROH.m{2} ==>
 ={glob CPAHitState} /\ (!CPAHitState.hit{2} =>
 ={res} /\ cpa_h_outside CPAHitState.target{1} ROH.m{1} ROH.m{2})].
proof.
 proc;seq 1 1:(={input,glob CPAHitState} /\
 cpa_h_outside CPAHitState.target{1} ROH.m{1} ROH.m{2} /\
 (!CPAHitState.hit{2}=>input{1}<>CPAHitState.target{1}));first by auto;smt().
 case(CPAHitState.hit{2}).
 + call{1} roh_get_ll;call{2} roh_get_ll;auto.
 inline ROH.get;sp.
 if;first by auto;smt(domE).
 + auto=> /> &1 &2 ho hn hh hf r hr.
   rewrite !get_set_sameE /=.
   exact(cpa_h_outside_set _ _ _ _ _ ho).
 auto=> /> &1 &2 ho hn hh hf.
 move:ho;rewrite /cpa_h_outside=>ho.
 rewrite(ho input{2} (hn hh));done.
qed.

lemma cpa_hit_context_projection (C<:CPAHContext {-ROH,-CPAHitState}) :
 equiv[C(CPAHitH).run ~ C(SimHActual).run :
 ={arg,glob C,ROH.m} ==> ={res,glob C,ROH.m}].
proof. proc(={ROH.m})=> //. conseq cpa_hit_h_projection=> //. qed.

lemma cpa_hit_context_coupling (C<:CPAHContext {-ROH,-CPAHitState}) :
 (forall(H<:SimHPort {-C}),islossless H.get=>islossless C(H).run)=>
 equiv[C(CPAHitH).run ~ C(CPAHitH).run :
 ={arg,glob C,glob CPAHitState} /\
 cpa_h_outside CPAHitState.target{1} ROH.m{1} ROH.m{2} ==>
 ={CPAHitState.hit} /\ (!CPAHitState.hit{2}=>
 ={res,glob C,glob CPAHitState} /\
 cpa_h_outside CPAHitState.target{1} ROH.m{1} ROH.m{2})].
proof.
 move=>all.
 have cl:=all CPAHitH cpa_hit_h_ll.
 proc*;call(_:CPAHitState.hit,
 ={glob CPAHitState} /\ cpa_h_outside CPAHitState.target{1} ROH.m{1} ROH.m{2},
 ={CPAHitState.hit}).
 + conseq cpa_hit_h_step;smt().
 + move=> &2 h;conseq cpa_hit_h_ll cpa_hit_h_latched;smt().
 + move=> &1;conseq cpa_hit_h_ll cpa_hit_h_latched;smt().
 auto;smt().
qed.
