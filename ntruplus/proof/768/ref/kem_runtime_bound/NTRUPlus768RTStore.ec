require import AllCore List Distr FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array224 Array1152.
require import NTRUPlus768FOModel NTRUPlus768AHState.
require import NTRUPlus768HistModel NTRUPlus768HistTable NTRUPlus768RTModel.

(* There is deliberately no global store implementation. The final
   section declares its st/profile variables after the original A.
   init resets only protocol rows/context; reset_cost occurs once at the
   reduction entry. Existing AHStore methods retain their signatures. *)
module type RTHistory = {
 proc init(pk:W8.t Array1152.t,suffix:W8.t Array32.t,cstar:W8.t Array1152.t option):unit
 proc snapshot():ah_state
 proc record(input:fo_h_input,hout:W8.t Array224.t):unit
 proc reset_cost():unit
 proc metrics():rt_profile
 proc charge_call(is_g:bool,bytes:int):unit
 proc charge_decap(visits encryptions comparisons:int):unit
 proc charge_extract(visits:int):unit
}.
op rt_store_ok (st:ah_state) (p:rt_profile) =
 hist_unique st.`ah_rows /\ p.`rp_size=size st.`ah_rows /\ rt_cost_ok p.

op rt_record_cost (st:ah_state) (p:rt_profile) (input:fo_h_input) =
 rt_record p (size st.`ah_rows+size(hist_keep input st.`ah_rows)) (128*size st.`ah_rows).

module RTStoreOps = {
 proc reset_cost():rt_profile = {return rt_zero;}
 proc init(p:rt_profile,pk:W8.t Array1152.t,suffix:W8.t Array32.t,cstar:W8.t Array1152.t option)
 :ah_state*rt_profile = {
  var st:ah_state;
  st<-{|ah_rows=[];ah_pk=pk;ah_suffix=suffix;ah_cstar=cstar|};
  return(st,p);
 }
 proc record(st:ah_state,p:rt_profile,input:fo_h_input,hout:W8.t Array224.t):ah_state*rt_profile = {
  var updated:hist_table*int*int;
  updated<@HistTable.put(input,hout,st.`ah_rows);
  st<-{|st with ah_rows=updated.`1|};
  p<-rt_record p updated.`2 updated.`3;
  return(st,p);
 }
 proc charge_call(p:rt_profile,is_g:bool,bytes:int):rt_profile = {return rt_call p is_g bytes;}
 proc charge_decap(p:rt_profile,visits encryptions comparisons:int):rt_profile = {
  return rt_decap p visits encryptions comparisons;
 }
 proc charge_extract(p:rt_profile,visits:int):rt_profile = {return rt_extract p visits;}
}.


lemma rt_put_size_monotone x y xs : hist_unique xs=>size xs<=size(hist_put x y xs).
proof.
 move=>hu.
 have hr:hist_rep xs (ofassoc xs) by rewrite /hist_rep;smt().
 have hn:=hist_rep_put x y xs (ofassoc xs) hr.
 rewrite(hist_rep_size xs (ofassoc xs) hr)
 (hist_rep_size (hist_put x y xs) (ofassoc xs).[x<-y] hn) fsize_set.
 case(x \in ofassoc xs);smt().
qed.
lemma rt_initial_store_ok pk suffix star p : rt_cost_ok p=>p.`rp_size=0=>
 rt_store_ok(ah_initial pk suffix star)p.
proof. rewrite /rt_store_ok /ah_initial /hist_unique /hist_keys /=;smt(). qed.
lemma rt_record_cost_size st p x : p.`rp_size=size st.`ah_rows=>
 (rt_record_cost st p x).`rp_size=1+size(hist_keep x st.`ah_rows).
proof. rewrite /rt_record_cost /rt_record /=;smt(). qed.
lemma rt_record_cost_alloc st p x : p.`rp_size=size st.`ah_rows=>
 (rt_record_cost st p x).`rp_alloc=p.`rp_alloc+2*size(hist_keep x st.`ah_rows)+1.
proof. rewrite /rt_record_cost /rt_record /=;smt(). qed.
lemma rt_record_store_ok st p x y : rt_store_ok st p=>
 rt_store_ok(ah_record_state st x y)(rt_record_cost st p x).
proof.
 rewrite /rt_store_ok;move=>[hu [hn hp]].
 have hk:=hist_keep_size x st.`ah_rows.
 have hm:=rt_put_size_monotone x y st.`ah_rows hu.
 rewrite hist_put_size in hm.
 have hk':0<=size(hist_keep x st.`ah_rows)<=p.`rp_size by smt().
 have hm':p.`rp_size<=size(hist_keep x st.`ah_rows)+1 by smt().
 have hc:=rt_record_ok p (size(hist_keep x st.`ah_rows)) hp hk' hm'.
 rewrite /ah_record_state /ah_with_rows /=;split.
 + exact(hist_put_unique x y st.`ah_rows hu).
 split.
 + rewrite(rt_record_cost_size st p x hn) hist_put_size;done.
 by rewrite /rt_record_cost -hn.
qed.
lemma rt_call_store_ok st p is_g bytes : rt_store_ok st p=>0<=bytes=>
 rt_store_ok st (rt_call p is_g bytes).
proof.
 rewrite /rt_store_ok;move=>[hu [hn hp]] hb;split;first exact hu.
 split;first by rewrite /rt_call.
 exact(rt_call_ok p is_g bytes hp hb).
qed.
lemma rt_decap_store_ok st p v k c : rt_store_ok st p=>
 0<=k<=v=>v<=size st.`ah_rows=>0<=c<=1152+32*v+1152*k=>
 rt_store_ok st (rt_decap p v k c).
proof.
 rewrite /rt_store_ok;move=>[hu [hn hp]] hk hv hc;split;first exact hu.
 split;first by rewrite /rt_decap.
 apply(rt_decap_ok p v k c hp hk _ hc);smt().
qed.
lemma rt_extract_store_ok st p v : rt_store_ok st p=>0<=v<=rt_g_length p=>
 rt_store_ok st (rt_extract p v).
proof.
 rewrite /rt_store_ok;move=>[hu [hn hp]] hv;split;first exact hu.
 split;first by rewrite /rt_extract.
 exact(rt_extract_ok p v hp hv).
qed.

lemma rt_ops_reset_ll : islossless RTStoreOps.reset_cost.
proof. proc;auto. qed.
lemma rt_ops_init_ll : islossless RTStoreOps.init.
proof. proc;auto. qed.
lemma rt_ops_record_ll : islossless RTStoreOps.record.
proof. proc;wp;call hist_table_put_lossless;auto. qed.
lemma rt_ops_call_ll : islossless RTStoreOps.charge_call.
proof. proc;auto. qed.
lemma rt_ops_decap_ll : islossless RTStoreOps.charge_decap.
proof. proc;auto. qed.
lemma rt_ops_extract_ll : islossless RTStoreOps.charge_extract.
proof. proc;auto. qed.

lemma rt_ops_reset_spec : hoare[RTStoreOps.reset_cost:true ==>res=rt_zero].
proof. proc;auto. qed.
lemma rt_ops_init_spec p0 pk0 suffix0 star0 :
 hoare[RTStoreOps.init:p=p0 /\ pk=pk0 /\ suffix=suffix0 /\ cstar=star0 ==>
 res=(ah_initial pk0 suffix0 star0,p0)].
proof. proc;auto=> />;by rewrite /ah_initial. qed.
lemma rt_ops_record_spec st0 p0 input0 hout0 :
 hoare[RTStoreOps.record:st=st0 /\ p=p0 /\ input=input0 /\ hout=hout0 ==>
 res.`1=ah_record_state st0 input0 hout0 /\ res.`2=rt_record_cost st0 p0 input0].
proof.
 proc;wp;call(hist_table_put_spec input0 hout0 st0.`ah_rows).
 auto=> />;rewrite /ah_record_state /ah_with_rows /rt_record_cost;smt().
qed.
lemma rt_ops_call_spec p0 g0 b0 :
 hoare[RTStoreOps.charge_call:p=p0 /\ is_g=g0 /\ bytes=b0 ==>res=rt_call p0 g0 b0].
proof. proc;auto. qed.
lemma rt_ops_decap_spec p0 v0 k0 c0 :
 hoare[RTStoreOps.charge_decap:p=p0 /\ visits=v0 /\ encryptions=k0 /\ comparisons=c0 ==>
 res=rt_decap p0 v0 k0 c0].
proof. proc;auto. qed.
lemma rt_ops_extract_spec p0 v0 :
 hoare[RTStoreOps.charge_extract:p=p0 /\ visits=v0 ==>res=rt_extract p0 v0].
proof. proc;auto. qed.

lemma rt_ops_record_correct st0 p0 input0 hout0 :
 phoare[RTStoreOps.record:st=st0 /\ p=p0 /\ input=input0 /\ hout=hout0 ==>
 res.`1=ah_record_state st0 input0 hout0 /\ res.`2=rt_record_cost st0 p0 input0]=1%r.
proof. by conseq rt_ops_record_ll (rt_ops_record_spec st0 p0 input0 hout0). qed.
lemma rt_ops_record_invariant st0 p0 input0 hout0 : rt_store_ok st0 p0=>
 phoare[RTStoreOps.record:st=st0 /\ p=p0 /\ input=input0 /\ hout=hout0 ==>
 rt_store_ok res.`1 res.`2]=1%r.
proof.
 move=>hi;conseq rt_ops_record_ll (rt_ops_record_spec st0 p0 input0 hout0);
 smt(rt_record_store_ok).
qed.
