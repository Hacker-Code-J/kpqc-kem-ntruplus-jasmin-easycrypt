require import AllCore List Distr.
from Jasmin require import JWord.
require import Array768 Array1152.
require import NTRUPlus768PKEModel NTRUPlus768SecExtractModel NTRUPlus768SecExtract.
require import NTRUPlus768SimLookup.

(* A visit counts one actual SecCandidate call. This is a call count,
   not a machine-time model; the original candidate calls Decode once
   and calls MRec only when Decode returns a candidate. *)
op cost_first_visits ['a] (eligible:'a->bool) (queries:'a list) : int =
 with queries=[] => 0
 with queries=q::qs => if eligible q then 1 else 1+cost_first_visits eligible qs.

lemma cost_first_visits_bounds ['a] (p:'a->bool) xs :
 0<=cost_first_visits p xs<=size xs.
proof.
 elim:xs=>[|x xs ih] //=;case(p x)=>hx;smt(size_ge0).
qed.
lemma cost_first_visits_find ['a] (p:'a->bool) xs :
 cost_first_visits p xs=if has p xs then find p xs+1 else size xs.
proof.
 elim:xs=>[|x xs ih] //=;case(p x)=>hx //=;rewrite ih;case(has p xs);smt().
qed.
lemma cost_first_visits_step ['a] (p:'a->bool) xs : xs<>[]=>
 cost_first_visits p xs=if p(head witness xs) then 1 else 1+cost_first_visits p(behead xs).
proof. by case xs=> // x xs _. qed.

module CostExtract = {
 proc run(pk ct:W8.t Array1152.t,excluded:pke_poly option,queries:W8.t Array1152.t list)
 : ((pke_poly*pke_poly) option)*int = {
  var todo:W8.t Array1152.t list;var query:W8.t Array1152.t;
  var candidate,answer:(pke_poly*pke_poly) option;var visited:int;
  todo<-queries;answer<-None;visited<-0;
  while(todo<>[] /\ answer=None){
   query<-head witness todo;todo<-behead todo;
   candidate<@SecCandidate.run(pk,ct,query);
   visited<-visited+1;
   if(candidate<>None /\ (excluded=None \/ (oget candidate).`2<>oget excluded)){
    answer<-candidate;
   }
  }
  return (answer,visited);
 }
}.

lemma cost_extract_ll : islossless CostExtract.run.
proof.
 proc;while true (size todo).
 + move=>z;wp;call sec_candidate_ll;auto=> />;smt(sim_behead_decreases).
 auto=> />;smt(size_ge0).
qed.

(* Both sides call the same stateless concrete SecCandidate and preserve
   every global by their empty write footprint. The counter is local. *)
lemma cost_extract_projection :
 equiv[CostExtract.run ~ SecExtract.run:
 ={pk,ct,excluded,queries} ==> res{1}.`1=res{2}].
proof.
 proc;while(={pk,ct,excluded,todo,answer}).
 + wp;call(_:true);first by sim.
   auto.
 auto.
qed.

lemma cost_extract_visits pk0 ct0 excluded0 queries0 :
 hoare[CostExtract.run:pk=pk0 /\ ct=ct0 /\ excluded=excluded0 /\ queries=queries0 ==>
 res.`2=cost_first_visits (sec_eligible pk0 ct0 excluded0) queries0].
proof.
 proc;while(pk=pk0 /\ ct=ct0 /\ excluded=excluded0 /\
 visited+(if answer=None then cost_first_visits (sec_eligible pk0 ct0 excluded0) todo else 0)=
 cost_first_visits (sec_eligible pk0 ct0 excluded0) queries0).
 + sp 2;wp;ecall(sec_candidate_functional pk0 ct0 query).
   auto=> /> &hr todo0 hi hn.
   move:hi;rewrite(cost_first_visits_step (sec_eligible pk{hr} ct{hr} excluded{hr}) todo0 hn) /sec_eligible.
   case(sec_candidate pk{hr} ct{hr} (head witness todo0)<>None /\
    (excluded{hr}=None \/ (oget(sec_candidate pk{hr} ct{hr} (head witness todo0))).`2<>oget excluded{hr}));smt().
 auto=> />;smt().
qed.

lemma cost_extract_answer pk0 ct0 excluded0 queries0 :
 hoare[CostExtract.run:pk=pk0 /\ ct=ct0 /\ excluded=excluded0 /\ queries=queries0 ==>
 res.`1=sec_extract_spec pk0 ct0 excluded0 queries0].
proof.
 conseq cost_extract_projection (sec_extract_functional pk0 ct0 excluded0 queries0);smt().
qed.
lemma cost_extract_bounds pk0 ct0 excluded0 queries0 :
 hoare[CostExtract.run:pk=pk0 /\ ct=ct0 /\ excluded=excluded0 /\ queries=queries0 ==>
 0<=res.`2<=size queries0].
proof.
 conseq(cost_extract_visits pk0 ct0 excluded0 queries0);smt(cost_first_visits_bounds).
qed.
lemma cost_extract_exact pk0 ct0 excluded0 queries0 :
 hoare[CostExtract.run:pk=pk0 /\ ct=ct0 /\ excluded=excluded0 /\ queries=queries0 ==>
 res.`1=sec_extract_spec pk0 ct0 excluded0 queries0 /\
 res.`2=(if has(sec_eligible pk0 ct0 excluded0)queries0
 then find(sec_eligible pk0 ct0 excluded0)queries0+1 else size queries0)].
proof.
 conseq(cost_extract_answer pk0 ct0 excluded0 queries0)
       (cost_extract_visits pk0 ct0 excluded0 queries0);smt(cost_first_visits_find).
qed.
lemma cost_extract_correct pk0 ct0 excluded0 queries0 :
 phoare[CostExtract.run:pk=pk0 /\ ct=ct0 /\ excluded=excluded0 /\ queries=queries0 ==>
 res.`1=sec_extract_spec pk0 ct0 excluded0 queries0 /\
 0<=res.`2<=size queries0 /\
 res.`2=cost_first_visits(sec_eligible pk0 ct0 excluded0)queries0]=1%r.
proof.
 conseq cost_extract_ll (cost_extract_exact pk0 ct0 excluded0 queries0);
 smt(cost_first_visits_find cost_first_visits_bounds).
qed.
