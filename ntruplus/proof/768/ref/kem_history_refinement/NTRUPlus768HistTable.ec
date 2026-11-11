require import AllCore List Distr FMap.
from Jasmin require import JWord.
require import Array224.
require import NTRUPlus768FOModel NTRUPlus768HistModel NTRUPlus768HistKey.

(* Concrete list operations. No finite-map enumeration, choice, filtering
   or reversal operation occurs in these procedure bodies. Key comparison
   is the actual 128-byte loop, rather than abstract tuple equality. *)
module HistKeep = {
 proc run(x:fo_h_input,xs:hist_table) : hist_table*int*int = {
  var todo,kept:hist_table;var entry:hist_entry;var cmp:bool*int;
  var visits,comparisons:int;
  todo<-xs;kept<-[];visits<-0;comparisons<-0;
  while(todo<>[]){
   entry<-head (x,hist_zero_value) todo;todo<-behead todo;
   cmp<@HistKey.equal(entry.`1,x);
   visits<-visits+1;comparisons<-comparisons+cmp.`2;
   if(!cmp.`1){kept<-entry::kept;}
  }
  return(kept,visits,comparisons);
 }
}.
module HistReverse = {
 proc run(d:hist_entry,xs:hist_table) : hist_table*int = {
  var todo,output:hist_table;var entry:hist_entry;var visits:int;
  todo<-xs;output<-[];visits<-0;
  while(todo<>[]){
   entry<-head d todo;todo<-behead todo;
   output<-entry::output;visits<-visits+1;
  }
  return(output,visits);
 }
}.
module HistTable = {
 proc get(x:fo_h_input,xs:hist_table) : (W8.t Array224.t option)*int*int = {
  var todo:hist_table;var entry:hist_entry;var cmp:bool*int;
  var answer:W8.t Array224.t option;var visits,comparisons:int;
  todo<-xs;answer<-None;visits<-0;comparisons<-0;
  while(todo<>[] /\ answer=None){
   entry<-head (x,hist_zero_value) todo;todo<-behead todo;
   cmp<@HistKey.equal(entry.`1,x);
   visits<-visits+1;comparisons<-comparisons+cmp.`2;
   if(cmp.`1){answer<-Some entry.`2;}
  }
  return(answer,visits,comparisons);
 }
 proc put(x:fo_h_input,y:W8.t Array224.t,xs:hist_table) : hist_table*int*int = {
  var kept:hist_table*int*int;var ordered:hist_table*int;
  var output:hist_table;var visits:int;
  kept<@HistKeep.run(x,xs);
  ordered<@HistReverse.run((x,y),kept.`1);
  output<-(x,y)::ordered.`1;visits<-kept.`2+ordered.`2;
  return(output,visits,kept.`3);
 }
}.

lemma hist_keep_lossless : islossless HistKeep.run.
proof.
 proc;while true(size todo).
 + move=>z;wp;call hist_key_lossless;auto=> />;smt(hist_behead_exact).
 auto=> />;smt(size_ge0).
qed.
lemma hist_reverse_lossless : islossless HistReverse.run.
proof.
 proc;while true(size todo).
 + move=>z;auto=> />;smt(hist_behead_exact).
 auto=> />;smt(size_ge0).
qed.
lemma hist_keep_spec x0 xs0 :
 hoare[HistKeep.run:x=x0 /\ xs=xs0 ==>
 res.`1=rev(hist_keep x0 xs0) /\ res.`2=size xs0 /\ res.`3=128*size xs0].
proof.
 proc;while(x=x0 /\ rev kept++hist_keep x0 todo=hist_keep x0 xs0 /\
  visits+size todo=size xs0 /\ comparisons=128*visits).
 + wp;ecall(hist_key_spec entry.`1 x0);auto=> />;
   smt(hist_keep_reverse_step hist_behead_exact).
 auto=> />;smt(hist_keep_nil rev_nil cats0 revK).
qed.
lemma hist_reverse_spec xs0 :
 hoare[HistReverse.run:xs=xs0 ==>res.`1=rev xs0 /\ res.`2=size xs0].
proof.
 proc;while(rev todo++output=rev xs0 /\ visits+size todo=size xs0).
 + auto=> />;smt(hist_reverse_step hist_behead_exact).
 auto=> />;smt(rev_nil cats0 cat0s).
qed.
lemma hist_table_get_lossless : islossless HistTable.get.
proof.
 proc;while true(size todo).
 + move=>z;wp;call hist_key_lossless;auto=> />;smt(hist_behead_exact).
 auto=> />;smt(size_ge0).
qed.
lemma hist_table_get_spec x0 xs0 :
 hoare[HistTable.get:x=x0 /\ xs=xs0 ==>
 res.`1=hist_get x0 xs0 /\ 0<=res.`2<=size xs0 /\ res.`3=128*res.`2].
proof.
 proc;while(x=x0 /\
  (if answer=None then hist_get x0 todo else answer)=hist_get x0 xs0 /\
  0<=visits /\ visits+size todo=size xs0 /\ comparisons=128*visits).
 + wp;ecall(hist_key_spec entry.`1 x0);auto=> />;
   smt(hist_get_step hist_behead_exact).
 auto=> />;smt(hist_get_stop size_ge0).
qed.
lemma hist_table_put_lossless : islossless HistTable.put.
proof. proc;wp;call hist_reverse_lossless;call hist_keep_lossless;auto. qed.
lemma hist_table_put_spec x0 y0 xs0 :
 hoare[HistTable.put:x=x0 /\ y=y0 /\ xs=xs0 ==>
 res.`1=hist_put x0 y0 xs0 /\
 res.`2=size xs0+size(hist_keep x0 xs0) /\ res.`3=128*size xs0].
proof.
 proc;wp;ecall(hist_reverse_spec kept.`1);call(hist_keep_spec x0 xs0).
 auto=> />;rewrite /hist_put;smt(revK size_rev).
qed.
lemma hist_table_get_correct x0 xs0 :
 phoare[HistTable.get:x=x0 /\ xs=xs0 ==>
 res.`1=hist_get x0 xs0 /\ 0<=res.`2<=size xs0 /\ res.`3=128*res.`2]=1%r.
proof. by conseq hist_table_get_lossless(hist_table_get_spec x0 xs0). qed.
lemma hist_table_put_correct x0 y0 xs0 :
 phoare[HistTable.put:x=x0 /\ y=y0 /\ xs=xs0 ==>
 res.`1=hist_put x0 y0 xs0 /\
 res.`2=size xs0+size(hist_keep x0 xs0) /\ res.`3=128*size xs0]=1%r.
proof. by conseq hist_table_put_lossless(hist_table_put_spec x0 y0 xs0). qed.
lemma hist_table_get_refinement x0 xs0 m0 : hist_rep xs0 m0=>
 phoare[HistTable.get:x=x0 /\ xs=xs0 ==>
 res.`1=m0.[x0] /\ 0<=res.`2<=size xs0 /\ 0<=res.`3<=128*size xs0]=1%r.
proof.
 move=>hr.
 have hh:hoare[HistTable.get:x=x0 /\ xs=xs0 ==>
 res.`1=m0.[x0] /\ 0<=res.`2<=size xs0 /\ 0<=res.`3<=128*size xs0].
 + conseq(hist_table_get_spec x0 xs0)=> //.
   have h:=hist_rep_get x0 xs0 m0 hr;smt().
 by conseq hist_table_get_lossless hh.
qed.
lemma hist_table_put_refinement x0 y0 xs0 m0 : hist_rep xs0 m0=>
 phoare[HistTable.put:x=x0 /\ y=y0 /\ xs=xs0 ==>
 hist_rep res.`1 m0.[x0<-y0] /\ size res.`1<=size xs0+1 /\
 0<=res.`2<=2*size xs0 /\ res.`3=128*size xs0]=1%r.
proof.
 move=>hr.
 have hh:hoare[HistTable.put:x=x0 /\ y=y0 /\ xs=xs0 ==>
 hist_rep res.`1 m0.[x0<-y0] /\ size res.`1<=size xs0+1 /\
 0<=res.`2<=2*size xs0 /\ res.`3=128*size xs0].
 + conseq(hist_table_put_spec x0 y0 xs0)=> //.
   have hp:=hist_rep_put x0 y0 xs0 m0 hr.
   have hs:=hist_put_size_bound x0 y0 xs0.
   have hk:=hist_keep_size x0 xs0;have hn:=size_ge0 xs0;smt().
 by conseq hist_table_put_lossless hh.
qed.
