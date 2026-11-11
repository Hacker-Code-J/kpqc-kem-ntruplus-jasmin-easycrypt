require import AllCore List Distr.
from Jasmin require import JWord.
require import Array768 Array1152.
require import NTRUPlus768SecExtractModel NTRUPlus768MRecModel NTRUPlus768MRecCalls NTRUPlus768MRecDecode.
require import NTRUPlus768PKEModel NTRUPlus768SimLookup.

module SecCandidate = {
 proc run(pk ct query:W8.t Array1152.t):(pke_poly*pke_poly) option = {
  var ro,mo:pke_poly option;var result:(pke_poly*pke_poly) option;
  ro<@MRecDecode.run(query);result<-None;
  if(ro<>None){
   mo<@MRec.run(pk,oget ro,ct);
   if(mo<>None){result<-Some(oget mo,oget ro);}
  }
  return result;
 }
}.
module SecExtract = {
 proc run(pk ct:W8.t Array1152.t,excluded:pke_poly option,queries:W8.t Array1152.t list)
 : (pke_poly*pke_poly) option = {
  var todo:W8.t Array1152.t list;var query:W8.t Array1152.t;
  var candidate,answer:(pke_poly*pke_poly) option;
  todo<-queries;answer<-None;
  while(todo<>[] /\ answer=None){
   query<-head witness todo;todo<-behead todo;
   candidate<@SecCandidate.run(pk,ct,query);
   if(candidate<>None /\ (excluded=None \/ (oget candidate).`2<>oget excluded)){
    answer<-candidate;
   }
  }
  return answer;
 }
}.

lemma sec_candidate_ll : islossless SecCandidate.run.
proof.
 proc;seq 2:true;1,4,5:by auto.
 + wp;call mrec_decode_ll;auto.
 if;last by auto.
 wp;call mrec_lossless;auto.
qed.
lemma sec_candidate_functional pk0 ct0 query0 :
 hoare[SecCandidate.run:pk=pk0 /\ ct=ct0 /\ query=query0 ==>
 res=sec_candidate pk0 ct0 query0].
proof.
 proc;seq 2:(pk=pk0 /\ ct=ct0 /\ query=query0 /\ ro=mrec_decode_randomness query0 /\ result=None).
 + wp;call(mrec_decode_functional query0);auto.
 if.
 + wp;call(mrec_functional pk0 (oget(mrec_decode_randomness query0)) ct0).
   auto=> />;rewrite /sec_candidate;smt().
 auto=> />;rewrite /sec_candidate;smt().
qed.
lemma sec_candidate_correct pk0 ct0 query0 :
 phoare[SecCandidate.run:pk=pk0 /\ ct=ct0 /\ query=query0 ==>
 res=sec_candidate pk0 ct0 query0]=1%r.
proof. by conseq sec_candidate_ll (sec_candidate_functional pk0 ct0 query0). qed.

lemma sec_extract_ll : islossless SecExtract.run.
proof.
 proc;while true (size todo).
 + move=>z;wp;call sec_candidate_ll;auto=> />;smt(sim_behead_decreases).
 auto=> />;smt(size_ge0).
qed.
lemma sec_extract_step pk ct excluded todo : todo<>[]=>
 sec_extract_spec pk ct excluded todo=
 if sec_eligible pk ct excluded (head witness todo)
 then sec_candidate pk ct (head witness todo)
 else sec_extract_spec pk ct excluded (behead todo).
proof.
 move=>hn;rewrite /sec_extract_spec (sim_first_step _ _ todo hn).
 case(sec_eligible pk ct excluded (head witness todo))=>he //.
 apply/eq_sym;apply some_oget;move:he;rewrite /sec_eligible;smt().
qed.
lemma sec_extract_functional pk0 ct0 excluded0 queries0 :
 hoare[SecExtract.run:pk=pk0 /\ ct=ct0 /\ excluded=excluded0 /\ queries=queries0 ==>
 res=sec_extract_spec pk0 ct0 excluded0 queries0].
proof.
 proc;while(pk=pk0 /\ ct=ct0 /\ excluded=excluded0 /\
 (if answer=None then sec_extract_spec pk0 ct0 excluded0 todo else answer)=
 sec_extract_spec pk0 ct0 excluded0 queries0).
 + sp 2;wp;ecall(sec_candidate_functional pk0 ct0 query).
   auto=> /> &hr todo0 hi hn.
   move:hi;rewrite(sec_extract_step pk{hr} ct{hr} excluded{hr} todo0 hn) /sec_eligible.
   case(sec_candidate pk{hr} ct{hr} (head witness todo0)<>None /\
    (excluded{hr}=None \/ (oget(sec_candidate pk{hr} ct{hr} (head witness todo0))).`2<>oget excluded{hr}));smt().
 auto=> />;rewrite /sec_extract_spec;smt(sim_first_stop).
qed.
lemma sec_extract_correct pk0 ct0 excluded0 queries0 :
 phoare[SecExtract.run:pk=pk0 /\ ct=ct0 /\ excluded=excluded0 /\ queries=queries0 ==>
 res=sec_extract_spec pk0 ct0 excluded0 queries0]=1%r.
proof. by conseq sec_extract_ll (sec_extract_functional pk0 ct0 excluded0 queries0). qed.
