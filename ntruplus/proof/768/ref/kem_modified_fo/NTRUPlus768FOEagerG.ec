require import AllCore List Distr DList FMap PROM.
from Jasmin require import JWord.
require import Array192 Array1152.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768StoppedKeygenModel.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions.
require import NTRUPlus768RRecCodec NTRUPlus768PKEModel.
require import NTRUPlus768ACWC2Domains NTRUPlus768ACWC2Oracle.

module type FOGPort = {
 proc get(input:W8.t Array1152.t) : W8.t Array192.t
}.
module type FOGContext(G:FOGPort) = {
 proc run(out:keygen_output) : bool {G.get}
}.
module FOGActual : FOGPort = { proc get=ROG.get }.

clone PROM.FullRO as FOGRO with
 type in_t <- W8.t Array1152.t,
 type out_t <- W8.t Array192.t,
 op dout <- (fun _=>uniform192),
 type d_in_t <- keygen_output,
 type d_out_t <- bool.

module FOGPROMGet(G:FOGRO.RO) : FOGPort = {
 proc get(input:W8.t Array1152.t) : W8.t Array192.t = {
  var y; y <@ G.get(input); return y;
 }
}.

op [opaque] fo_g_inputs = map rr_G_input acwc2_r_enum.
lemma fo_g_inputs_size : size fo_g_inputs=size acwc2_r_enum.
proof. by rewrite /fo_g_inputs size_map. qed.
lemma fo_g_inputs_uniq : uniq fo_g_inputs.
proof.
 have hi:forall x y,x \in acwc2_r_enum=>y \in acwc2_r_enum=>rr_G_input x=rr_G_input y=>x=y.
 + move=>x y hx hy he; apply(rr_G_input_injective x y) => //;
   by rewrite -acwc2_r_enum_domain.
 by rewrite /fo_g_inputs (map_inj_in_uniq rr_G_input acwc2_r_enum hi) acwc2_r_enum_uniq.
qed.
lemma fo_g_inputs_image x : x \in fo_g_inputs <=>
 exists r,pke_domain r /\ x=rr_G_input r.
proof.
 rewrite /fo_g_inputs mapP; split.
 + move=>[r [hr he]]; exists r; split; last exact he.
   by move:hr; rewrite acwc2_r_enum_domain.
 move=>[r [hr he]]; exists r; split; last exact he.
 by rewrite acwc2_r_enum_domain.
qed.

(* The completion loop is private; a continuation receives only get. *)
module FOGComplete(G:FOGRO.RO) = {
 proc run() = {
  var todo:W8.t Array1152.t list;
  todo <- fo_g_inputs;
  while(todo<>[]){
   G.sample(head witness todo);
   todo <- behead todo;
  }
 }
}.
module FOGCompletedContext(C:FOGContext,G:FOGRO.RO) = {
 proc distinguish(out:keygen_output) : bool = {
  var b:bool;
  FOGComplete(G).run();
  b <@ C(FOGPROMGet(G)).run(out);
  return b;
 }
}.

lemma fo_g_prom_get_adapter :
 equiv[ROG.get ~ FOGRO.RO.get : input{1}=x{2} /\ ROG.m{1}=FOGRO.RO.m{2} ==>
   ={res} /\ ROG.m{1}=FOGRO.RO.m{2}].
proof.
 proc; case(input{1} \in ROG.m{1}).
 + rcondf{1} 1; first by auto.
   rcondf{2} 2; first by auto.
   rnd{2}; auto=> />; by rewrite uniform192_ll.
 rcondt{1} 1; first by auto.
 rcondt{2} 2; first by auto.
 auto.
qed.

lemma fo_g_actual_context_adapter
 (C<:FOGContext {-ROG,-FOGRO.RO,-FOGRO.FRO}) :
 equiv[C(FOGActual).run ~ C(FOGPROMGet(FOGRO.RO)).run :
   ={arg,glob C} /\ ROG.m{1}=FOGRO.RO.m{2} ==>
   ={res,glob C} /\ ROG.m{1}=FOGRO.RO.m{2}].
proof.
 proc(ROG.m{1}=FOGRO.RO.m{2})=> //.
 proc*; inline{2} FOGPROMGet(FOGRO.RO).get; wp.
 call fo_g_prom_get_adapter; auto.
qed.

lemma fo_g_completion_lazy_ll : islossless FOGComplete(FOGRO.LRO).run.
proof.
 proc; while true (size todo).
 + move=>z; inline FOGRO.LRO.sample; auto=> />; smt(size_behead size_eq0 size_ge0).
 auto=> />; smt(size_ge0 size_eq0).
qed.

lemma fo_g_partial_completion
 (C<:FOGContext {-FOGRO.RO,-FOGRO.FRO}) :
 equiv[FOGCompletedContext(C,FOGRO.RO).distinguish ~
       FOGCompletedContext(C,FOGRO.LRO).distinguish :
   ={arg,glob C,FOGRO.RO.m} ==> ={res,glob C}].
proof.
 have hl:forall (_:W8.t Array1152.t),is_lossless uniform192 by move=>x; exact uniform192_ll.
 conseq(FOGRO.FullEager.RO_LRO_D (FOGCompletedContext(C)) hl); smt().
qed.

lemma fo_g_lazy_completion_skip
 (C<:FOGContext {-FOGRO.RO,-FOGRO.FRO}) :
 equiv[FOGCompletedContext(C,FOGRO.LRO).distinguish ~ C(FOGPROMGet(FOGRO.LRO)).run :
   ={arg,glob C,FOGRO.RO.m} ==> ={res,glob C,FOGRO.RO.m}].
proof.
 proc*; inline{1} FOGCompletedContext(C,FOGRO.LRO).distinguish; wp.
 call (_: ={FOGRO.RO.m}); first by sim.
 call{1} fo_g_completion_lazy_ll; auto.
qed.

lemma fo_g_lazy_getter_same
 (C<:FOGContext {-FOGRO.RO,-FOGRO.FRO}) :
 equiv[C(FOGPROMGet(FOGRO.LRO)).run ~ C(FOGPROMGet(FOGRO.RO)).run :
   ={arg,glob C,FOGRO.RO.m} ==> ={res,glob C,FOGRO.RO.m}].
proof. proc(={FOGRO.RO.m})=> //; proc; sim. qed.

lemma fo_g_partial_eager
 (C<:FOGContext {-FOGRO.RO,-FOGRO.FRO}) :
 equiv[FOGCompletedContext(C,FOGRO.RO).distinguish ~ C(FOGPROMGet(FOGRO.RO)).run :
   ={arg,glob C,FOGRO.RO.m} ==> ={res,glob C}].
proof.
 transitivity FOGCompletedContext(C,FOGRO.LRO).distinguish
   (={arg,glob C,FOGRO.RO.m} ==> ={res,glob C})
   (={arg,glob C,FOGRO.RO.m} ==> ={res,glob C})=> //.
 + by move=> &1 &2 [ha [hc hm]]; exists (glob C){1} FOGRO.RO.m{1} arg{1}; smt().
 + exact(fo_g_partial_completion C).
 transitivity C(FOGPROMGet(FOGRO.LRO)).run
   (={arg,glob C,FOGRO.RO.m} ==> ={res,glob C,FOGRO.RO.m})
   (={arg,glob C,FOGRO.RO.m} ==> ={res,glob C,FOGRO.RO.m})=> //.
 + by move=> &1 &2 [ha [hc hm]]; exists (glob C){1} FOGRO.RO.m{1} arg{1}; smt().
 + exact(fo_g_lazy_completion_skip C).
 exact(fo_g_lazy_getter_same C).
qed.
