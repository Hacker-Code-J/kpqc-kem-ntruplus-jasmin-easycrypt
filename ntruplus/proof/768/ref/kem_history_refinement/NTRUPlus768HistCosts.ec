require import AllCore List StdOrder.
import IntOrder.

(* Costs of the concrete history operations only. Ideal ROH evaluation,
   allocation of a native representation, and the arithmetic kernels are
   separate from these explicitly counted visits and byte comparisons. *)
op hist_build_visit_bound (q:int) = q*(q-1).
op hist_build_byte_bound (q:int) = 64*q*(q-1).

lemma hist_build_zero_bounds :
 hist_build_visit_bound 0=0 /\ hist_build_byte_bound 0=0.
proof. by rewrite /hist_build_visit_bound /hist_build_byte_bound. qed.
lemma hist_build_step_bounds i n : 0<=n<=i=>
 hist_build_visit_bound i+2*n<=hist_build_visit_bound(i+1) /\
 hist_build_byte_bound i+128*n<=hist_build_byte_bound(i+1).
proof. rewrite /hist_build_visit_bound /hist_build_byte_bound;smt(). qed.
lemma hist_build_bounds_nonnegative q : 0<=q=>
 0<=hist_build_visit_bound q /\ 0<=hist_build_byte_bound q.
proof. rewrite /hist_build_visit_bound /hist_build_byte_bound;smt(). qed.

require import Distr FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array224.
require import NTRUPlus768FOModel NTRUPlus768ROMOracles.
require import NTRUPlus768HistModel NTRUPlus768HistTable.

op [opaque] hist_public_zero_input : fo_h_input =
 (Array96.init(fun _=>W8.zero),Array32.init(fun _=>W8.zero)).

(* This builder takes no secret key, prepared G function or error flag.
   Its only oracle calls are the actual ideal ROH calls. The fresh table
   initialization is part of this finite-query experiment, not a claim
   that the original KEM adversary can reset its cached random oracle. *)
module HistBuildPublic = {
 proc run(queries:fo_h_input list):hist_table*int*int*int = {
  var todo:fo_h_input list;var rows:hist_table;var input:fo_h_input;
  var hout:W8.t Array224.t;var updated:hist_table*int*int;
  var visits,comparisons,requests:int;
  ROH.init();todo<-queries;rows<-[];
  visits<-0;comparisons<-0;requests<-0;
  while(todo<>[]){
   input<-head hist_public_zero_input todo;todo<-behead todo;
   hout<@ROH.get(input);
   updated<@HistTable.put(input,hout,rows);
   rows<-updated.`1;
   visits<-visits+updated.`2;
   comparisons<-comparisons+updated.`3;
   requests<-requests+1;
  }
  return(rows,visits,comparisons,requests);
 }
}.

lemma hist_put_counted x0 y0 xs0 :
 hoare[HistTable.put:x=x0 /\ y=y0 /\ xs=xs0 ==>
 size res.`1<=size xs0+1 /\
 0<=res.`2<=2*size xs0 /\ 0<=res.`3<=128*size xs0].
proof.
 conseq(hist_table_put_spec x0 y0 xs0)=> //.
 have hs:=hist_put_size_bound x0 y0 xs0.
 have hk:=hist_keep_size x0 xs0;have hn:=size_ge0 xs0;smt().
qed.

lemma hist_public_build_lossless : islossless HistBuildPublic.run.
proof.
 proc;while true(size todo).
 + move=>z;wp;call hist_table_put_lossless;call roh_get_ll;
   auto=> />;smt(hist_behead_exact size_ge0).
 inline ROH.init;auto=> />;smt(size_ge0).
qed.

lemma hist_public_build_bounds qs0 :
 hoare[HistBuildPublic.run:queries=qs0 ==>
 size res.`1<=size qs0 /\
 0<=res.`2<=hist_build_visit_bound(size qs0) /\
 0<=res.`3<=hist_build_byte_bound(size qs0) /\
 res.`4=size qs0].
proof.
 proc;while(0<=requests /\ size todo+requests=size qs0 /\
 size rows<=requests /\ 0<=visits<=hist_build_visit_bound requests /\
 0<=comparisons<=hist_build_byte_bound requests).
 + sp 2;wp;ecall(hist_put_counted input hout rows).
   call(_:true ==>true);first by trivial.
   auto=> />;smt(hist_behead_exact size_ge0 hist_build_step_bounds).
 inline ROH.init;auto=> />;
 smt(size_ge0 hist_build_zero_bounds).
qed.

lemma hist_public_build_correct qs0 :
 phoare[HistBuildPublic.run:queries=qs0 ==>
 size res.`1<=size qs0 /\
 0<=res.`2<=hist_build_visit_bound(size qs0) /\
 0<=res.`3<=hist_build_byte_bound(size qs0) /\
 res.`4=size qs0]=1%r.
proof. by conseq hist_public_build_lossless(hist_public_build_bounds qs0). qed.

require import NTRUPlus768HistBuild.

(* Secret-key-dependent error bookkeeping exists only in the proof
   monitor. It changes neither the generated table nor the actual ROH. *)
lemma hist_public_build_projection :
 equiv[HistBuildPublic.run ~ HistBuild.run:
 queries{1}=qs{2} ==>res{1}.`1=res{2}.`1 /\ ={ROH.m}].
proof.
 proc;while(={todo,rows,ROH.m}).
 + inline{2} HistBuild.step;wp.
   call(_: ={arg} ==> ={res});first by sim.
   call(_: ={arg,ROH.m} ==> ={res,ROH.m});first by sim.
   auto=> />;smt(hist_behead_exact head_behead).
 inline ROH.init;auto.
qed.

require import Array1152 NTRUPlus768CCAStatusAdapter.
require import NTRUPlus768FOEagerG NTRUPlus768HistLookup.

op hist_public_comparison_bound q = hist_build_byte_bound q+1184*q+1152.

(* Public inputs only. This code does not construct an eager G table;
   its G requests use the existing ideal oracle state. Returned counts
   cover history traversal and key/ciphertext comparisons, with actual
   SimEncrypt invocations reported separately. *)
module HistPublicLookup = {
 proc run(pk:W8.t Array1152.t,suffix:W8.t Array32.t,
          qs:fo_h_input list,ct:W8.t Array1152.t):cca_reply*int*int*int*int = {
  var built:hist_table*int*int*int;var out:cca_reply*int*int*int;
  built<@HistBuildPublic.run(qs);
  out<@HistLookup(FOGActual).run(built.`1,pk,suffix,None,ct);
  return(out.`1,built.`2+out.`2,built.`3+out.`4,built.`4,out.`3);
 }
}.

lemma hist_public_lookup_lossless : islossless HistPublicLookup.run.
proof.
 proc;call(hist_lookup_lossless FOGActual rog_get_ll);
 call hist_public_build_lossless;auto.
qed.

lemma hist_public_lookup_bounds qs0 :
 hoare[HistPublicLookup.run:qs=qs0 ==>
 0<=res.`2<=size qs0*size qs0 /\
 0<=res.`3<=hist_public_comparison_bound(size qs0) /\
 res.`4=size qs0 /\ 0<=res.`5<=size qs0].
proof.
 proc;ecall(hist_lookup_bounds FOGActual built.`1).
 call(hist_public_build_bounds qs0);auto=> />.
 rewrite /hist_build_visit_bound /hist_public_comparison_bound;smt(size_ge0).
qed.

require import NTRUPlus768HistBound NTRUPlus768DecapCompleteSpec.

(* The right side additionally initializes specification-only map state
   and error bookkeeping. The public code receives no witness or error
   function, and its G cache is related to the prepared proof input. *)
lemma hist_public_lookup_projection :
 equiv[HistPublicLookup.run ~ HistLookupAfterBuild.run:
 pk{1}=w{2}.`kg_pk /\ suffix{1}=complete_sk_suffix w{2}.`kg_sk /\
 ={qs,ct} /\ ROG.m{1}=gm{2} /\ which{2} ==>
 res{1}.`1=res{2}.`1 /\ ={ROG.m,ROH.m}].
proof.
 proc;rcondt{2} 8.
 + move=> &m;wp;call(_:true ==>true);first by trivial.
   auto.
 wp;call(_: ={arg,ROG.m} ==> ={res,ROG.m});first by sim.
 wp;call hist_public_build_projection;auto.
qed.
