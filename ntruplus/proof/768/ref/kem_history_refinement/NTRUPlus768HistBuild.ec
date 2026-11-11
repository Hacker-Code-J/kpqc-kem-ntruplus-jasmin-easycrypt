require import AllCore List Distr FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152.
require import NTRUPlus768FOModel NTRUPlus768FOError NTRUPlus768FOHMonitor.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768ACWC2Oracle.
require import NTRUPlus768HistModel NTRUPlus768HistTable.

(* This monitor is a proof experiment, not the public implementation:
   w/g are fixed proof data, and rows/bad are local procedure values.
   Each request uses the actual shared ROH, including cache hits. *)
module HistBuild = {
 proc step(w:keygen_witness,g:acwc2_g_function,rows:hist_table,bad:bool,input:fo_h_input)
 : hist_table*bool = {
  var hout:W8.t Array224.t;var updated:hist_table*int*int;
  hout<@ROH.get(input);
  updated<@HistTable.put(input,hout,rows);
  rows<-updated.`1;
  bad<-bad \/ fo_base_bad w g input.`1 hout;
  return(rows,bad);
 }
 proc run(w:keygen_witness,g:acwc2_g_function,qs:fo_h_input list):hist_table*bool = {
  var todo:fo_h_input list;var input:fo_h_input;
  var rows:hist_table;var bad:bool;var out:hist_table*bool;
  ROH.init();todo<-qs;rows<-[];bad<-false;
  while(todo<>[]){
   input<-head witness todo;todo<-behead todo;
   out<@step(w,g,rows,bad,input);
   rows<-out.`1;bad<-out.`2;
  }
  return(rows,bad);
 }
}.

lemma hist_build_roh_update table0 input0 :
 hoare[ROH.get:ROH.m=table0 /\ input=input0 ==>ROH.m=table0.[input0<-res]].
proof.
 proc;if;auto=> />.
 + move=>_ hout _;by rewrite get_set_sameE.
 move=>hc;apply/eq_sym;apply get_set_id;apply some_oget;move:hc;by rewrite domE.
qed.

lemma hist_build_update w g rows table bad input hout :
 hist_rep rows table=>(!bad=>fo_hcache_good w g None table)=>
 hist_rep(hist_put input hout rows)table.[input<-hout] /\
 size(hist_put input hout rows)<=size rows+1 /\
 (!(bad \/ fo_base_bad w g input.`1 hout)=>fo_hcache_good w g None table.[input<-hout]).
proof.
 move=>hr hg;split;first exact(hist_rep_put input hout rows table hr).
 split;first exact(hist_put_size_bound input hout rows).
 move=>/negb_or[hb hx];apply(fo_hcache_set w g None table input hout (hg hb));by right.
qed.

lemma hist_build_step_ll : islossless HistBuild.step.
proof. proc;wp;call hist_table_put_lossless;call roh_get_ll;auto. qed.

lemma hist_build_step_value w0 g0 rows0 bad0 input0 table0 :
 hoare[HistBuild.step:
 w=w0 /\ g=g0 /\ rows=rows0 /\ bad=bad0 /\ input=input0 /\ ROH.m=table0 ==>
 exists hout, ROH.m=table0.[input0<-hout] /\
 res=(hist_put input0 hout rows0,bad0 \/ fo_base_bad w0 g0 input0.`1 hout)].
proof.
 proc;wp;ecall(hist_table_put_spec input hout rows).
 call(hist_build_roh_update table0 input0);auto=> />.
 move=> hout updated hrows _ _;exists hout;by rewrite hrows.
qed.

lemma hist_build_step_invariant w0 g0 rows0 bad0 input0 table0 :
 hoare[HistBuild.step:
 w=w0 /\ g=g0 /\ rows=rows0 /\ bad=bad0 /\ input=input0 /\ ROH.m=table0 /\
 hist_rep rows0 table0 /\ (!bad0=>fo_hcache_good w0 g0 None table0) ==>
 hist_rep res.`1 ROH.m /\ size res.`1<=size rows0+1 /\
 (!res.`2=>fo_hcache_good w0 g0 None ROH.m)].
proof.
 conseq(hist_build_step_value w0 g0 rows0 bad0 input0 table0)=> //.
 move=> &hr hpre result m [hout [-> ->]].
 apply(hist_build_update w0 g0 rows0 table0 bad0 input0 hout);smt().
qed.

lemma hist_build_lossless : islossless HistBuild.run.
proof.
 proc;while true (size todo).
 + move=>z;wp;call hist_build_step_ll;auto=> />;smt(size_behead size_ge0 size_eq0).
 wp;call roh_init_ll;auto;smt(size_ge0).
qed.

lemma hist_build_invariant w0 g0 qs0 :
 hoare[HistBuild.run:w=w0 /\ g=g0 /\ qs=qs0 ==>
 hist_rep res.`1 ROH.m /\ size res.`1<=size qs0 /\
 (!res.`2=>fo_hcache_good w0 g0 None ROH.m)].
proof.
 proc;while(w=w0 /\ g=g0 /\ hist_rep rows ROH.m /\
 size rows+size todo<=size qs0 /\ (!bad=>fo_hcache_good w0 g0 None ROH.m)).
 + wp;ecall(hist_build_step_invariant w0 g0 rows bad input ROH.m).
   auto=> />;smt(size_behead size_ge0).
 wp;call roh_init_empty;auto=> />;smt(hist_rep_empty fo_hcache_empty size_ge0).
qed.
