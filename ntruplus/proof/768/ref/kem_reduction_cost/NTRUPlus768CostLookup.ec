require import AllCore List Distr FMap FSet.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152.
require import NTRUPlus768SimLookup NTRUPlus768SimModel NTRUPlus768FOModel.
require import NTRUPlus768FOEagerG NTRUPlus768FOGAdapters NTRUPlus768FOProcedures.
require import NTRUPlus768CCADecapOracle NTRUPlus768CCAStatusAdapter.
require import NTRUPlus768KEMPayloadSpec NTRUPlus768ROMOracles NTRUPlus768SecGOracles.

(* The original lookup, augmented only with local returned counters.
   Enumeration and map operations retain their original expressions: these
   are loop/call counts, not a unit-cost implementation of finite maps. *)
module CostLookup(G:FOGPort) = {
 proc decap(ct:W8.t Array1152.t) : cca_reply*int*int = {
  var answer:cca_reply;var star:W8.t Array1152.t option;
  var pk:W8.t Array1152.t;var suffix:W8.t Array32.t;
  var log:(fo_h_input,W8.t Array224.t)fmap;var todo:fo_h_input list;
  var input:fo_h_input;var hout:W8.t Array224.t;var candidate:W8.t Array1152.t option;
  var visited,encrypted:int;
  answer<-None;
  SimPublic.count<-SimPublic.count+1;
  star<-SimPublic.cstar;
  visited<-0;encrypted<-0;
  if(star<>Some ct){
   pk<-SimPublic.pk;suffix<-SimPublic.suffix;log<-SimHistory.h;
   todo<-elems(fdom log);
   while(todo<>[] /\ answer=None){
    input<-head witness todo;todo<-behead todo;visited<-visited+1;
    if(input.`2=suffix){
     hout<-oget log.[input];
     candidate<@SimEncrypt(G).run(pk,input.`1,hout);
     encrypted<-encrypted+1;
     if(candidate=Some ct){answer<-Some(payload_shared_key hout);}
    }
   }
  }
  return(answer,visited,encrypted);
 }
}.
module CostLookupReply(G:FOGPort) : CCADecapPort = {
 proc decap(ct:W8.t Array1152.t) : cca_reply = {
  var out:cca_reply*int*int;
  out<@CostLookup(G).decap(ct);return out.`1;
 }
}.

module type CostEncryptPort = {
 proc run(pk:W8.t Array1152.t,msg:W8.t Array96.t,hout:W8.t Array224.t):W8.t Array1152.t option
}.
lemma cost_encrypt_same (M<:CostEncryptPort) :
 equiv[M.run ~ M.run: ={arg,glob M} ==> ={res,glob M}].
proof. proc true;auto. qed.

lemma cost_lookup_projection (G<:FOGPort {-SimPublic,-SimHistory}) :
 equiv[CostLookup(G).decap ~ SimLookup(G).decap:
 ={arg,glob G,glob SimPublic,glob SimHistory} ==>
 res{1}.`1=res{2} /\ ={glob G,glob SimPublic,glob SimHistory}].
proof.
 proc.
 conseq (_: _ ==> ={answer,glob G,glob SimPublic,glob SimHistory})=> //.
 sim (: ={glob G,glob SimPublic,glob SimHistory});auto.
qed.

lemma cost_lookup_reply_projection (G<:FOGPort {-SimPublic,-SimHistory}) :
 equiv[CostLookupReply(G).decap ~ SimLookup(G).decap:
 ={arg,glob G,glob SimPublic,glob SimHistory} ==>
 ={res,glob G,glob SimPublic,glob SimHistory}].
proof.
 proc*;inline{1} CostLookupReply(G).decap;wp;call(cost_lookup_projection G);auto.
qed.

lemma cost_lookup_logged_projection :
 equiv[CostLookup(SecGLogged(FOGActual)).decap ~ SimLookup(SecGLogged(FOGActual)).decap:
 ={arg,ROG.m,SecGHistory.queries,glob SimPublic,SimHistory.h} ==>
 res{1}.`1=res{2} /\ ={ROG.m,SecGHistory.queries,glob SimPublic,SimHistory.h}].
proof. conseq(cost_lookup_projection (SecGLogged(FOGActual)));auto. qed.
lemma cost_lookup_logged_reply_projection :
 equiv[CostLookupReply(SecGLogged(FOGActual)).decap ~ SimLookup(SecGLogged(FOGActual)).decap:
 ={arg,ROG.m,SecGHistory.queries,glob SimPublic,SimHistory.h} ==>
 ={res,ROG.m,SecGHistory.queries,glob SimPublic,SimHistory.h}].
proof. conseq(cost_lookup_reply_projection (SecGLogged(FOGActual)));auto. qed.

lemma cost_lookup_bounds (G<:FOGPort) log0 :
 hoare[CostLookup(G).decap:SimHistory.h=log0 ==>
 0<=res.`3 /\ res.`3<=res.`2 /\ res.`2<=size(elems(fdom log0))].
proof.
 proc;sp 5;if;last by auto=> />;smt(size_ge0).
 while(log=log0 /\ 0<=encrypted /\ encrypted<=visited /\
       visited+size todo<=size(elems(fdom log0))).
 + sp 3;if.
   - wp;call(_:true ==>true);first by trivial.
     auto=> />;smt(sim_behead_decreases).
   auto=> />;smt(sim_behead_decreases).
 auto=> />;smt(size_ge0).
qed.

lemma cost_lookup_challenge (G<:FOGPort) ct0 :
 phoare[CostLookup(G).decap:ct=ct0 /\ SimPublic.cstar=Some ct0 ==>
 res=(None,0,0)]=1%r.
proof. proc;rcondf 6;auto. qed.

lemma cost_lookup_lossless (G<:FOGPort) :
 islossless G.get=>islossless CostLookup(G).decap.
proof.
 move=>hg;proc;sp 5;if;last by auto.
 while true (size todo).
 + move=>z;sp 3;if.
   - wp;call(sim_encrypt_lossless G hg);auto=> />;smt(sim_behead_decreases).
   auto=> />;smt(sim_behead_decreases).
 auto=> />;smt(size_ge0).
qed.

(* This equality counts actual wrapper calls, including repeated cached
   G inputs, by the existing transcript. No new global counter is used. *)
lemma cost_g_logged_length n0 :
 hoare[SecGLogged(FOGActual).get:size SecGHistory.queries=n0 ==>
 size SecGHistory.queries=n0+1].
proof.
 proc;call(_:true ==>true);first by trivial.
 auto=> />;smt().
qed.
lemma cost_g_shake_length n0 :
 hoare[FOGHash(SecGLogged(FOGActual)).shake:size SecGHistory.queries=n0 ==>
 size SecGHistory.queries=n0+1].
proof. proc;call(cost_g_logged_length n0);auto. qed.
lemma cost_hash_g_length n0 :
 hoare[FOHashG(FOGHash(SecGLogged(FOGActual))).run:size SecGHistory.queries=n0 ==>
 size SecGHistory.queries=n0+1].
proof.
 proc;call(cost_g_shake_length n0);call(_:true ==>true);first by trivial.
 auto.
qed.
lemma cost_encrypt_g_length n0 :
 hoare[SimEncrypt(SecGLogged(FOGActual)).run:size SecGHistory.queries=n0 ==>
 size SecGHistory.queries=n0+1].
proof.
 proc;call(_:true ==>true);first by trivial.
 call(_:true ==>true);first by trivial.
 call(cost_hash_g_length n0);call(_:true ==>true);first by trivial.
 auto.
qed.

lemma cost_lookup_g_calls n0 :
 hoare[CostLookup(SecGLogged(FOGActual)).decap:size SecGHistory.queries=n0 ==>
 size SecGHistory.queries=n0+res.`3].
proof.
 proc;sp 5;if;last by auto.
 while(size SecGHistory.queries=n0+encrypted).
 + sp 3;if;last by auto.
   wp;ecall(cost_encrypt_g_length (n0+encrypted));auto=> />;smt().
 auto.
qed.
lemma cost_lookup_logged_lossless : islossless CostLookup(SecGLogged(FOGActual)).decap.
proof.
 apply(cost_lookup_lossless (SecGLogged(FOGActual)));
 apply(sec_g_logged_ll FOGActual);exact rog_get_ll.
qed.
