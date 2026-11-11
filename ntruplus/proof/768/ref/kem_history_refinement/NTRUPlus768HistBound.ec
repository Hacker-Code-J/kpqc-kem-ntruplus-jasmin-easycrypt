require import AllCore List Distr FMap StdOrder StdBigop.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152.
require import NTRUPlus768FOModel NTRUPlus768FOError NTRUPlus768FOHMonitor NTRUPlus768FOBadBound.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768ACWC2Oracle.
import RealOrder StdBigop.Bigreal.BRA.

(* Proof-only monitor for a fixed finite query experiment. It is absent
   from both builders and never calls an adversary. Its initialization is
   explicit, and the local monitored builder is coupled to it below. *)
module HistProofMonitor = {
 var w:keygen_witness
 var g:acwc2_g_function
 var bad:bool
 var n:int
 proc init(w0:keygen_witness,g0:acwc2_g_function) = {
  w<-w0;g<-g0;bad<-false;n<-0;ROH.init();
 }
 proc get(input:fo_h_input):W8.t Array224.t = {
  var hout:W8.t Array224.t;
  hout<@ROH.get(input);
  bad<-bad \/ fo_base_bad w g input.`1 hout;
  n<-n+1;
  return hout;
 }
}.
module HistProofExperiment = {
 proc run(w0:keygen_witness,g0:acwc2_g_function,qs:fo_h_input list) = {
  var todo:fo_h_input list;var input:fo_h_input;var hout:W8.t Array224.t;
  HistProofMonitor.init(w0,g0);todo<-qs;
  while(todo<>[]){
   input<-head witness todo;todo<-behead todo;
   hout<@HistProofMonitor.get(input);
  }
 }
}.

lemma hist_proof_get_ll : islossless HistProofMonitor.get.
proof. proc;wp;call roh_get_ll;auto. qed.
lemma hist_proof_get_state w0 g0 n0 b0 input0 :
 hoare[HistProofMonitor.get:
 HistProofMonitor.w=w0 /\ HistProofMonitor.g=g0 /\
 HistProofMonitor.n=n0 /\ HistProofMonitor.bad=b0 /\ input=input0 ==>
 HistProofMonitor.w=w0 /\ HistProofMonitor.g=g0 /\
 HistProofMonitor.n=n0+1 /\
 HistProofMonitor.bad=(b0 \/ fo_base_bad w0 g0 input0.`1 res)].
proof. proc;wp;call(_:true ==>true);first by trivial. auto. qed.

lemma hist_proof_get_invariant w0 g0 n0 :
 hoare[HistProofMonitor.get:
 HistProofMonitor.w=w0 /\ HistProofMonitor.g=g0 /\ HistProofMonitor.n=n0 /\
 (!HistProofMonitor.bad=>fo_hcache_good w0 g0 None ROH.m) ==>
 HistProofMonitor.w=w0 /\ HistProofMonitor.g=g0 /\ HistProofMonitor.n=n0+1 /\
 (!HistProofMonitor.bad=>fo_hcache_good w0 g0 None ROH.m)].
proof.
 proc;inline ROH.get;sp;if.
 + auto=> />;rewrite ?get_set_sameE /=.
   move=> &hr hgood hfresh hout _ hb.
   rewrite get_set_sameE /= negb_or in hb.
   apply(fo_hcache_set w0 g0 None ROH.m{hr} input{hr} hout);smt().
 auto;smt().
qed.

lemma hist_proof_get_bad w0 g0 :
 phoare[HistProofMonitor.get:
 HistProofMonitor.w=w0 /\ HistProofMonitor.g=g0 /\ !HistProofMonitor.bad /\
 fo_hcache_good w0 g0 None ROH.m ==>HistProofMonitor.bad]<=(fo_error w0 g0).
proof.
 have [he _]:=fo_error_range w0 g0.
 proc;inline ROH.get;sp 1;if.
 + wp;rnd(fo_base_bad w0 g0 input.`1);skip=> />.
   rewrite ?get_set_sameE /=.
   move=> &hr _ _ _;split.
   - exact(fo_base_bad_bound w0 g0 input{hr}.`1).
   move=>_ hout _;by rewrite get_set_sameE /=.
 conseq(_: _ ==> _ : <=0%r)=> //;hoare;auto=> />.
 rewrite /fo_hcache_good;move=> &hr _ hgood hcached.
 have hv:=some_oget ROH.m{hr}.[input{hr}] hcached.
 apply(hgood input{hr} (oget ROH.m{hr}.[input{hr}]) hv);done.
qed.

lemma hist_proof_experiment_state w1 g1 qs1 :
 hoare[HistProofExperiment.run:w0=w1 /\ g0=g1 /\ qs=qs1 ==>
 HistProofMonitor.w=w1 /\ HistProofMonitor.g=g1 /\
 HistProofMonitor.n=size qs1 /\
 (!HistProofMonitor.bad=>fo_hcache_good w1 g1 None ROH.m)].
proof.
 proc;while(w0=w1 /\ g0=g1 /\
 HistProofMonitor.w=w1 /\ HistProofMonitor.g=g1 /\
 HistProofMonitor.n+size todo=size qs1 /\
 (!HistProofMonitor.bad=>fo_hcache_good w1 g1 None ROH.m)).
 + ecall(hist_proof_get_invariant w1 g1 HistProofMonitor.n).
   auto=> />;smt(size_behead).
 inline HistProofMonitor.init ROH.init;auto=> />;smt(fo_hcache_empty size_ge0).
qed.

lemma hist_proof_experiment_bounded w0 g0 qs0 &m :
 Pr[HistProofExperiment.run(w0,g0,qs0)@&m:
 HistProofMonitor.bad /\ HistProofMonitor.n<=size qs0] <= (size qs0)%r*fo_error w0 g0.
proof.
 fel 1 HistProofMonitor.n (fun _=>fo_error w0 g0) (size qs0) HistProofMonitor.bad []
 (HistProofMonitor.w=w0 /\ HistProofMonitor.g=g0 /\
 (!HistProofMonitor.bad=>fo_hcache_good w0 g0 None ROH.m))=> //.
 + by rewrite(fo_fel_cost_sum (size qs0) (fo_error w0 g0) (size_ge0 qs0)).
 + inline HistProofMonitor.init ROH.init;auto=> />;smt(fo_hcache_empty).
 + conseq(hist_proof_get_bad w0 g0)=> /#.
 move=>c;conseq(hist_proof_get_invariant w0 g0 c)=> /#.
qed.

require import NTRUPlus768HistModel NTRUPlus768HistTable NTRUPlus768HistBuild.

lemma hist_build_step_monitor n0 :
 equiv[HistBuild.step ~ HistProofMonitor.get:
 w{1}=HistProofMonitor.w{2} /\ g{1}=HistProofMonitor.g{2} /\
 bad{1}=HistProofMonitor.bad{2} /\ HistProofMonitor.n{2}=n0 /\ ={input,ROH.m} ==>
 res{1}.`2=HistProofMonitor.bad{2} /\ HistProofMonitor.n{2}=n0+1 /\ ={ROH.m}].
proof.
 proc;wp;call{1} hist_table_put_lossless.
 call(_: ={arg,ROH.m} ==> ={res,ROH.m});first by sim.
 auto.
qed.

lemma hist_build_monitor w1 g1 qs1 :
 equiv[HistBuild.run ~ HistProofExperiment.run:
 w{1}=w1 /\ g{1}=g1 /\ qs{1}=qs1 /\ w0{2}=w1 /\ g0{2}=g1 /\ qs{2}=qs1 ==>
 res{1}.`2=HistProofMonitor.bad{2} /\ HistProofMonitor.n{2}=size qs1 /\ ={ROH.m}].
proof.
 proc;while(w{1}=w1 /\ g{1}=g1 /\
 HistProofMonitor.w{2}=w1 /\ HistProofMonitor.g{2}=g1 /\
 bad{1}=HistProofMonitor.bad{2} /\
 HistProofMonitor.n{2}+size todo{2}=size qs1 /\ ={todo,ROH.m}).
 + wp;ecall(hist_build_step_monitor HistProofMonitor.n{2}).
   auto=> />;smt(size_behead).
 inline HistProofMonitor.init ROH.init;auto.
qed.

lemma hist_build_bad_bound w0 g0 qs0 &m :
 Pr[HistBuild.run(w0,g0,qs0)@&m:res.`2] <= (size qs0)%r*fo_error w0 g0.
proof.
 have ->:Pr[HistBuild.run(w0,g0,qs0)@&m:res.`2]=
 Pr[HistProofExperiment.run(w0,g0,qs0)@&m:HistProofMonitor.bad /\ HistProofMonitor.n<=size qs0].
 + byequiv(hist_build_monitor w0 g0 qs0)=> //;smt().
 exact(hist_proof_experiment_bounded w0 g0 qs0 &m).
qed.

require import NTRUPlus768HistLookup NTRUPlus768HistOrder.
require import NTRUPlus768SimLookup NTRUPlus768SimModel NTRUPlus768SimSampling.
require import NTRUPlus768FOGAdapters NTRUPlus768FOEagerG NTRUPlus768CCADecapOracle.
require import NTRUPlus768DecapCompleteSpec NTRUPlus768CCAStatusAdapter NTRUPlus768PKEModel.

(* One actual lookup after the actual finite public-query experiment.
   which=true selects the concrete list, false the original map scan.
   The prepared G map is proof setup; this is not a whole-adversary game. *)
module HistLookupAfterBuild = {
 proc run(w:keygen_witness,g:acwc2_g_function,
          gm:(W8.t Array1152.t,W8.t Array192.t)fmap,
          qs:fo_h_input list,ct:W8.t Array1152.t,which:bool):cca_reply*bool = {
  var built:hist_table*bool;var out:cca_reply*int*int*int;var reply:cca_reply;
  ROG.m<-gm;
  built<@HistBuild.run(w,g,qs);
  SimHistory.h<-ROH.m;
  SimPublic.pk<-w.`kg_pk;SimPublic.suffix<-complete_sk_suffix w.`kg_sk;
  SimPublic.cstar<-None;SimPublic.count<-0;
  if(which){
   out<@HistLookup(FOGActual).run(built.`1,w.`kg_pk,complete_sk_suffix w.`kg_sk,None,ct);
   reply<-out.`1;
  }else{
   reply<@SimLookup(FOGActual).decap(ct);
  }
  return(reply,built.`2);
 }
}.

lemma hist_lookup_after_build_ll : islossless HistLookupAfterBuild.run.
proof.
 proc;seq 2:true;1,4,5:by auto.
 + call hist_build_lossless;auto.
 sp 5;if.
 + wp;call(hist_lookup_lossless FOGActual rog_get_ll);auto.
 call(sim_lookup_lossless FOGActual rog_get_ll);auto.
qed.

module HistBuildBad = {
 proc run(w:keygen_witness,g:acwc2_g_function,qs:fo_h_input list):bool = {
  var built:hist_table*bool;
  built<@HistBuild.run(w,g,qs);return built.`2;
 }
}.

lemma hist_build_bad_probability w0 g0 qs0 &m :
 Pr[HistBuildBad.run(w0,g0,qs0)@&m:res]=Pr[HistBuild.run(w0,g0,qs0)@&m:res.`2].
proof.
 byequiv(_: ={arg,ROH.m} ==>res{1}=res{2}.`2)=> //.
 proc*;inline{1} HistBuildBad.run;wp.
 call(_: ={arg,ROH.m} ==> ={res,ROH.m});first by sim.
 auto.
qed.

lemma hist_lookup_after_build_bad_probability w0 g0 gm0 qs0 ct0 which0 &m :
 Pr[HistLookupAfterBuild.run(w0,g0,gm0,qs0,ct0,which0)@&m:res.`2]=
 Pr[HistBuild.run(w0,g0,qs0)@&m:res.`2].
proof.
 rewrite -(hist_build_bad_probability w0 g0 qs0 &m).
 byequiv(_: w{1}=w0 /\ g{1}=g0 /\ gm{1}=gm0 /\ qs{1}=qs0 /\ ct{1}=ct0 /\ which{1}=which0 /\
 w{2}=w0 /\ g{2}=g0 /\ qs{2}=qs0 /\ ={ROH.m} ==>res{1}.`2=res{2})=> //.
 proc;seq 2 1:(={built}).
 + call(_: ={arg,ROH.m} ==> ={res});first by sim.
   auto.
 sp 5 0;if{1}.
 + wp;call{1}(hist_lookup_lossless FOGActual rog_get_ll);auto.
 call{1}(sim_lookup_lossless FOGActual rog_get_ll);auto.
qed.

lemma hist_build_coupled w0 g0 qs0 :
 equiv[HistBuild.run ~ HistBuild.run:
 ={arg,ROH.m} /\ w{1}=w0 /\ g{1}=g0 /\ qs{1}=qs0 ==>
 ={res,ROH.m} /\ hist_rep res{1}.`1 ROH.m{1} /\
 (!res{1}.`2=>fo_hcache_good w0 g0 None ROH.m{1})].
proof.
 conseq(_: ={arg,ROH.m} ==> ={res,ROH.m}) (hist_build_invariant w0 g0 qs0) _=> //.
 by sim.
qed.

lemma hist_lookup_after_build_coupled w0 g0 gm0 qs0 ct0 :
 pke_key_relation w0=>acwc2_cache_matches g0 gm0=>
 equiv[HistLookupAfterBuild.run ~ HistLookupAfterBuild.run:
 ={w,g,gm,qs,ct,ROH.m} /\ w{1}=w0 /\ g{1}=g0 /\ gm{1}=gm0 /\ qs{1}=qs0 /\ ct{1}=ct0 /\
 which{1} /\ !which{2} ==>
 res{1}.`2=res{2}.`2 /\ (!res{1}.`2=>res{1}.`1=res{2}.`1)].
proof.
 move=>hk hg;proc.
 seq 2 2:(={w,g,qs,ct,built,ROH.m} /\ w{1}=w0 /\ g{1}=g0 /\ qs{1}=qs0 /\ ct{1}=ct0 /\
 ROG.m{1}=gm0 /\ ROG.m{2}=gm0 /\ hist_rep built{1}.`1 ROH.m{1} /\
 (!built{1}.`2=>fo_hcache_good w0 g0 None ROH.m{1}) /\ which{1} /\ !which{2}).
 + call(hist_build_coupled w0 g0 qs0);auto.
 rcondt{1} 6;first by auto.
 rcondf{2} 6;first by auto.
 wp;ecall{1}(hist_lookup_correct w0.`kg_pk (complete_sk_suffix w0.`kg_sk) None built{1}.`1 ct0 g0 gm0 hg).
 ecall{2}(sim_lookup_correct w0.`kg_pk (complete_sk_suffix w0.`kg_sk) None ROH.m{2} 0 ct0 g0 gm0 hg).
 auto=> />;smt(hist_lookup_order_good).
qed.

lemma hist_probability_split_distance (p q s t b c:real) :
 s=t=>0%r<=p=>0%r<=q=>p<=b=>q<=b=>b<=c=>`|p+s-(q+t)|<=c.
proof. rewrite ler_norml;smt(). qed.

lemma hist_lookup_after_build_distance w0 g0 gm0 qs0 ct0 &m (event:cca_reply->bool) :
 pke_key_relation w0=>acwc2_cache_matches g0 gm0=>
 `|Pr[HistLookupAfterBuild.run(w0,g0,gm0,qs0,ct0,true)@&m:event res.`1]-
 Pr[HistLookupAfterBuild.run(w0,g0,gm0,qs0,ct0,false)@&m:event res.`1]|
 <=(size qs0)%r*fo_error w0 g0.
proof.
 move=>hk hg;have eqv:=hist_lookup_after_build_coupled w0 g0 gm0 qs0 ct0 hk hg.
 have hgood:Pr[HistLookupAfterBuild.run(w0,g0,gm0,qs0,ct0,true)@&m:event res.`1 /\ !res.`2]=
 Pr[HistLookupAfterBuild.run(w0,g0,gm0,qs0,ct0,false)@&m:event res.`1 /\ !res.`2].
 + byequiv eqv=> //;clear hk hg eqv;smt().
 have hbad:Pr[HistLookupAfterBuild.run(w0,g0,gm0,qs0,ct0,true)@&m:res.`2]=
 Pr[HistLookupAfterBuild.run(w0,g0,gm0,qs0,ct0,false)@&m:res.`2].
 + byequiv eqv=> //;clear hk hg eqv;smt().
 have hl:Pr[HistLookupAfterBuild.run(w0,g0,gm0,qs0,ct0,true)@&m:event res.`1 /\ res.`2]<=
 Pr[HistLookupAfterBuild.run(w0,g0,gm0,qs0,ct0,true)@&m:res.`2] by rewrite Pr[mu_sub].
 have hr:Pr[HistLookupAfterBuild.run(w0,g0,gm0,qs0,ct0,false)@&m:event res.`1 /\ res.`2]<=
 Pr[HistLookupAfterBuild.run(w0,g0,gm0,qs0,ct0,false)@&m:res.`2] by rewrite Pr[mu_sub].
 have hb:Pr[HistLookupAfterBuild.run(w0,g0,gm0,qs0,ct0,true)@&m:res.`2]<=(size qs0)%r*fo_error w0 g0.
 + rewrite hist_lookup_after_build_bad_probability;exact(hist_build_bad_bound w0 g0 qs0 &m).
 rewrite Pr[mu_split res.`2].
 have ->:Pr[HistLookupAfterBuild.run(w0,g0,gm0,qs0,ct0,false)@&m:event res.`1]=
 Pr[HistLookupAfterBuild.run(w0,g0,gm0,qs0,ct0,false)@&m:event res.`1 /\ res.`2]+
 Pr[HistLookupAfterBuild.run(w0,g0,gm0,qs0,ct0,false)@&m:event res.`1 /\ !res.`2]
 by rewrite Pr[mu_split res.`2].
 have hp:0%r<=Pr[HistLookupAfterBuild.run(w0,g0,gm0,qs0,ct0,true)@&m:event res.`1 /\ res.`2]
 by rewrite Pr[mu_ge0].
 have hq:0%r<=Pr[HistLookupAfterBuild.run(w0,g0,gm0,qs0,ct0,false)@&m:event res.`1 /\ res.`2]
 by rewrite Pr[mu_ge0].
 have hr2:Pr[HistLookupAfterBuild.run(w0,g0,gm0,qs0,ct0,false)@&m:event res.`1 /\ res.`2]<=
 Pr[HistLookupAfterBuild.run(w0,g0,gm0,qs0,ct0,true)@&m:res.`2] by rewrite hbad;exact hr.
 exact(hist_probability_split_distance _ _ _ _ _ _ hgood hp hq hl hr2 hb).
qed.
