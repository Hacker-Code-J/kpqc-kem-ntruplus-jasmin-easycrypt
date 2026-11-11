require import AllCore Distr FMap List.
from Jasmin require import JWord.
require import Array96 Array192 Array1152.
require import NTRUPlus768SecModel NTRUPlus768FOGAdapters NTRUPlus768FOEagerG.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions.

(* Only calls routed through this adaptive-phase wrapper are recorded.
   Repeated calls are retained, including raw output length zero and G
   calls performed internally by the public decapsulation lookup. *)
module SecGHistory = {
 var queries:W8.t Array1152.t list
 proc init() = {queries<-[];}
}.
module SecGLogged(G:FOGPort) : FOGPort = {
 proc get(input:W8.t Array1152.t) : W8.t Array192.t = {
  var y;
  SecGHistory.queries<-input::SecGHistory.queries;
  y<@G.get(input);
  return y;
 }
}.
module SecGMark = {
 var target:W8.t Array1152.t
 var hit:bool
 proc init(x:W8.t Array1152.t) = {target<-x;hit<-false;}
}.
module SecGMarked(G:FOGPort) : FOGPort = {
 proc get(input:W8.t Array1152.t) : W8.t Array192.t = {
  var y;
  SecGMark.hit<-SecGMark.hit || input=SecGMark.target;
  y<@SecGLogged(G).get(input);
  return y;
 }
}.
op sec_g_outside (x:W8.t Array1152.t)
 (m1 m2:(W8.t Array1152.t,W8.t Array192.t)fmap) =
 forall z,z<>x=>m1.[z]=m2.[z].

lemma sec_g_history_init_ll : islossless SecGHistory.init.
proof. proc;auto. qed.
lemma sec_g_mark_init_ll : islossless SecGMark.init.
proof. proc;auto. qed.
lemma sec_g_logged_ll (G<:FOGPort) : islossless G.get=>islossless SecGLogged(G).get.
proof. move=>gl;proc;call gl;auto. qed.
lemma sec_g_marked_ll (G<:FOGPort) : islossless G.get=>islossless SecGMarked(G).get.
proof. move=>gl;proc;call(sec_g_logged_ll G gl);auto. qed.

lemma sec_g_logged_projection (G<:FOGPort {-SecGHistory}) :
 equiv[SecGLogged(G).get ~ G.get : ={arg,glob G} ==> ={res,glob G}].
proof.
 proc*;inline{1} SecGLogged(G).get;wp.
 call(_: ={arg,glob G} ==> ={res,glob G});first by proc true;auto.
 auto.
qed.
lemma sec_g_marked_projection (G<:FOGPort {-SecGMark,-SecGHistory}) :
 equiv[SecGMarked(G).get ~ SecGLogged(G).get :
 ={arg,glob G,SecGHistory.queries} ==> ={res,glob G,SecGHistory.queries}].
proof.
 proc*;inline{1} SecGMarked(G).get;wp.
 call(_: ={arg,glob G,SecGHistory.queries} ==> ={res,glob G,SecGHistory.queries});first by sim.
 auto.
qed.
lemma sec_g_logged_exact (G<:FOGPort {-SecGHistory}) q0 x0 :
 hoare[SecGLogged(G).get : SecGHistory.queries=q0 /\ input=x0 ==>
 SecGHistory.queries=x0::q0].
proof. proc;call(_:true ==>true);first by trivial. auto. qed.
lemma sec_g_marked_latched (G<:FOGPort {-SecGMark}) :
 hoare[SecGMarked(G).get : SecGMark.hit ==> SecGMark.hit].
proof. proc;call(_:true ==>true);first by trivial. auto;smt(). qed.
lemma sec_g_marked_exact (G<:FOGPort {-SecGMark,-SecGHistory}) x0 b0 input0 q0 :
 hoare[SecGMarked(G).get : SecGMark.target=x0 /\ SecGMark.hit=b0 /\
 input=input0 /\ SecGHistory.queries=q0 ==>
 SecGMark.target=x0 /\ SecGMark.hit=(b0 || input0=x0) /\ SecGHistory.queries=input0::q0].
proof. proc;call(sec_g_logged_exact G q0 input0);auto. qed.
lemma sec_g_marked_history (G<:FOGPort {-SecGMark,-SecGHistory}) :
 hoare[SecGMarked(G).get : SecGMark.hit=(SecGMark.target \in SecGHistory.queries) ==>
 SecGMark.hit=(SecGMark.target \in SecGHistory.queries)].
proof.
 proc;inline SecGLogged(G).get;wp;call(_:true ==>true);first by trivial.
 auto;smt(in_cons).
qed.

lemma sec_g_outside_refl x m : sec_g_outside x m m.
proof. by rewrite /sec_g_outside. qed.
lemma sec_g_outside_empty_single x y : sec_g_outside x empty empty.[x<-y].
proof. rewrite /sec_g_outside=>z hz;rewrite get_setE hz;done. qed.
lemma sec_g_outside_set x m1 m2 z y :
 sec_g_outside x m1 m2=>sec_g_outside x m1.[z<-y] m2.[z<-y].
proof. rewrite /sec_g_outside=>h v hv;rewrite !get_setE;smt(). qed.

lemma sec_g_marked_step :
 equiv[SecGMarked(FOGActual).get ~ SecGMarked(FOGActual).get :
 ={arg,glob SecGMark,SecGHistory.queries} /\
 sec_g_outside SecGMark.target{1} ROG.m{1} ROG.m{2} ==>
 ={glob SecGMark} /\ (!SecGMark.hit{2} =>
 ={res,SecGHistory.queries} /\ sec_g_outside SecGMark.target{1} ROG.m{1} ROG.m{2})].
proof.
 proc;seq 1 1:(={input,glob SecGMark,SecGHistory.queries} /\
 sec_g_outside SecGMark.target{1} ROG.m{1} ROG.m{2} /\
 (!SecGMark.hit{2}=>input{1}<>SecGMark.target{1}));first by auto;smt().
 case(SecGMark.hit{2}).
 + call{1}(sec_g_logged_ll FOGActual rog_get_ll);call{2}(sec_g_logged_ll FOGActual rog_get_ll);auto.
 inline SecGLogged(FOGActual).get FOGActual.get ROG.get;sp.
 if;first by auto;smt(domE).
 + auto=> /> &1 &2 ho hn hh hf r hr.
   rewrite !get_set_sameE /=.
   exact(sec_g_outside_set _ _ _ _ _ ho).
 auto=> /> &1 &2 ho hn hh hf.
 move:ho;rewrite /sec_g_outside=>ho.
 rewrite(ho input{2} (hn hh));done.
qed.

lemma sec_g_context_marked_logged
 (G<:FOGPort {-SecGMark,-SecGHistory})
 (C<:SecGContext {-G,-SecGMark,-SecGHistory}) :
 equiv[C(SecGMarked(G)).run ~ C(SecGLogged(G)).run :
 ={arg,glob C,glob G,SecGHistory.queries} ==> ={res,glob C,glob G,SecGHistory.queries}].
proof. proc(={glob G,SecGHistory.queries})=> //. conseq(sec_g_marked_projection G)=> //. qed.
lemma sec_g_context_logged_plain
 (G<:FOGPort {-SecGMark,-SecGHistory})
 (C<:SecGContext {-G,-SecGMark,-SecGHistory}) :
 equiv[C(SecGLogged(G)).run ~ C(G).run :
 ={arg,glob C,glob G} ==> ={res,glob C,glob G}].
proof. proc(={glob G})=> //. conseq(sec_g_logged_projection G)=> //. qed.
lemma sec_g_context_history
 (G<:FOGPort {-SecGMark,-SecGHistory})
 (C<:SecGContext {-G,-SecGMark,-SecGHistory}) :
 hoare[C(SecGMarked(G)).run :
 SecGMark.hit=(SecGMark.target \in SecGHistory.queries) ==>
 SecGMark.hit=(SecGMark.target \in SecGHistory.queries)].
proof.
 proc(SecGMark.hit=(SecGMark.target \in SecGHistory.queries))=> //.
 exact(sec_g_marked_history G).
qed.

lemma sec_g_context_coupling (C<:SecGContext {-ROG,-SecGMark,-SecGHistory}) :
 (forall(G<:FOGPort {-C}),islossless G.get=>islossless C(G).run)=>
 equiv[C(SecGMarked(FOGActual)).run ~ C(SecGMarked(FOGActual)).run :
 ={arg,glob C,glob SecGMark,SecGHistory.queries} /\
 sec_g_outside SecGMark.target{1} ROG.m{1} ROG.m{2} ==>
 ={SecGMark.hit} /\ (!SecGMark.hit{2}=>
 ={res,glob C,glob SecGMark,SecGHistory.queries} /\
 sec_g_outside SecGMark.target{1} ROG.m{1} ROG.m{2})].
proof.
 move=>all.
 have gl:=sec_g_marked_ll FOGActual rog_get_ll.
 have cl:=all (SecGMarked(FOGActual)) gl.
 proc*;call(_:SecGMark.hit,
 ={glob SecGMark,SecGHistory.queries} /\ sec_g_outside SecGMark.target{1} ROG.m{1} ROG.m{2},
 ={SecGMark.hit}).
 + conseq sec_g_marked_step;smt().
 + move=> &2 h;conseq gl (sec_g_marked_latched FOGActual);smt().
 + move=> &1;conseq gl (sec_g_marked_latched FOGActual);smt().
 auto;smt().
qed.
