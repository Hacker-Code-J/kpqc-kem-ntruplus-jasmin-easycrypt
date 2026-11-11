require import AllCore Distr.
from Jasmin require import JWord.
require import Array96 Array192 Array224 Array768 Array1152 Array1153.
require import NTRUPlus768PKEModel NTRUPlus768PKEProcedures NTRUPlus768PKECallProof.
require import NTRUPlus768SimLookup NTRUPlus768FOEagerG NTRUPlus768FOGAdapters NTRUPlus768FOProcedures.
require import NTRUPlus768ACWC2HashG NTRUPlus768SOTPContracts NTRUPlus768DecapCompleteSpec NTRUPlus768ROMDomains.
require import NTRUPlus768PolyCBD1Checked NTRUPlus768PolySOTPEncodeChecked NTRUPlus768DecapMessagePrepare.
require import NTRUPlus768RTKernelCosts NTRUPlus768RTFixedCBD NTRUPlus768RTFixedGPrepare NTRUPlus768RTFixedSOTPEncode.
require import NTRUPlus768RTFixedNTT.

(* The finite copies implement the two array comprehensions in the old
   specification. Input/return arrays use owned buffers, charged at 3N.
   Counter updates are proof observations and are erased. *)
op rt_kernel_tail_bound:int = 2981.
op rt_kernel_peel_bound:int = 17288.
module RTKernelBytes = {
 proc tail(h:W8.t Array224.t):W8.t Array192.t*int = {
  var output:W8.t Array192.t;var i,work:int;
  work<-672;
  output<-witness;work<-work+193;
  i<-0;work<-work+1;
  work<-work+2;
  while(i<192){
   output.[i]<-h.[32+i];work<-work+4;
   i<-i+1;work<-work+2;
   work<-work+2;
  }
  work<-work+577;return(output,work);
 }
 proc peel(input:W8.t Array1153.t):W8.t Array1152.t*int = {
  var output:W8.t Array1152.t;var i,work:int;
  work<-3459;
  output<-witness;work<-work+1153;
  i<-0;work<-work+1;
  work<-work+2;
  while(i<1152){
   output.[i]<-input.[i+1];work<-work+4;
   i<-i+1;work<-work+2;
   work<-work+2;
  }
  work<-work+3457;return(output,work);
 }
}.
lemma rt_kernel_tail_ll : islossless RTKernelBytes.tail.
proof. proc;wp;while true(192-i);auto=> />;smt(). qed.
lemma rt_kernel_peel_ll : islossless RTKernelBytes.peel.
proof. proc;wp;while true(1152-i);auto=> />;smt(). qed.
lemma rt_kernel_tail_spec h0 :
 hoare[RTKernelBytes.tail:h=h0 ==>res=(complete_hash_tail h0,rt_kernel_tail_bound)].
proof.
 proc;wp;while(h=h0 /\ 0<=i<=192 /\ work=868+8*i /\
 forall j,0<=j<i=>output.[j]=h0.[32+j]).
 + auto=> />;smt(Array192.get_setE).
 auto=> />;rewrite /rt_kernel_tail_bound /complete_hash_tail;
 smt(Array192.tP Array192.initiE).
qed.
lemma rt_kernel_peel_spec input0 :
 hoare[RTKernelBytes.peel:input=input0 ==>res=(peel1153 input0,rt_kernel_peel_bound)].
proof.
 proc;wp;while(input=input0 /\ 0<=i<=1152 /\ work=4615+8*i /\
 forall j,0<=j<i=>output.[j]=input0.[j+1]).
 + auto=> />;smt(Array1152.get_setE).
 auto=> />;rewrite /rt_kernel_peel_bound /peel1153;
 smt(Array1152.tP Array1152.initiE).
qed.
lemma rt_kernel_tail_correct h0 :
 phoare[RTKernelBytes.tail:h=h0 ==>res=(complete_hash_tail h0,rt_kernel_tail_bound)]=1%r.
proof. by conseq rt_kernel_tail_ll(rt_kernel_tail_spec h0). qed.
lemma rt_kernel_peel_correct input0 :
 phoare[RTKernelBytes.peel:input=input0 ==>res=(peel1153 input0,rt_kernel_peel_bound)]=1%r.
proof. by conseq rt_kernel_peel_ll(rt_kernel_peel_spec input0). qed.

(* The backend returns its own actual work; it is neither a new global
   counter nor an assumed price for an entire reduction. Its projection
   preserves all backend state. A concrete backend bound is needed only
   when converting the local bound into a bound on the total. *)
module type RTKernelCostGPort = {
 proc get(input:W8.t Array1152.t):W8.t Array192.t*int
}.
module RTKernelGValue(G:RTKernelCostGPort):FOGPort = {
 proc get(input:W8.t Array1152.t):W8.t Array192.t = {
  var out:W8.t Array192.t*int;out<@G.get(input);return out.`1;
 }
}.
lemma rt_kernel_g_projection (G<:RTKernelCostGPort) :
 equiv[G.get ~ RTKernelGValue(G).get:
 ={arg,glob G} ==>res{1}.`1=res{2} /\ ={glob G}].
proof. proc*;inline{2} RTKernelGValue(G).get;wp;call(_:true);auto. qed.

op rt_kernel_sim_encrypt_bound:int =
 4416 + (579+rt_kernel_tail_bound) + (3076+rt_fixed_cbd_bound) +
 (3076+rt_fixed_ntt_bound) + (9225+rt_fixed_gprepare_bound) +
 (3459+rt_kernel_peel_bound) + 579 +
 (3077+rt_fixed_sotpencode_bound) + (3461+rt_kernel_pkeenc_bound) + 3457.
module RTKernelSimEncrypt(G:RTKernelCostGPort) = {
 proc run(pk:W8.t Array1152.t,msg:W8.t Array96.t,hout:W8.t Array224.t)
 :W8.t Array1152.t option*int*int = {
  var r,code,rhat:pke_poly;
  var serialized:W8.t Array1152.t;var input:W8.t Array1153.t;
  var tail,pad:W8.t Array192.t;var payload:W8.t Array1152.t;
  var ct:W8.t Array1152.t option;
  var bt:W8.t Array192.t*int;var bq:W8.t Array1152.t*int;
  var poly:pke_poly*int;var prepared:(W8.t Array1152.t*W8.t Array1153.t)*int;
  var ciphertext:W8.t Array1152.t option*int;
  var work,backend:int;
  work<-4416;
  bt<@RTKernelBytes.tail(hout);tail<-bt.`1;work<-work+bt.`2+579;
  poly<@RTFixedCBD.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(witness,tail);
  r<-poly.`1;work<-work+poly.`2+3076;
  poly<@RTFixedNTT.jade_ntruplus_ntruplus768_amd64_ref_ntt(witness,r);
  rhat<-poly.`1;work<-work+poly.`2+3076;
  prepared<@RTFixedGPrepare.jade_ntruplus_ntruplus768_amd64_ref_decap_message_prepare(witness,witness,rhat);
  (serialized,input)<-prepared.`1;work<-work+prepared.`2+9225;
  bq<@RTKernelBytes.peel(input);payload<-bq.`1;work<-work+bq.`2+3459;
  bt<@G.get(payload);pad<-bt.`1;backend<-bt.`2;work<-work+backend+579;
  poly<@RTFixedSOTPEncode.jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_encode(witness,msg,pad);
  code<-poly.`1;work<-work+poly.`2+3077;
  ciphertext<@RTKernelPKEEnc.run(pk,code,r);ct<-ciphertext.`1;work<-work+ciphertext.`2+3461;
  work<-work+3457;
  return(ct,work,backend);
 }
}.

module RTKernelSimPlain(G:FOGPort) = {
 proc run(pk:W8.t Array1152.t,msg:W8.t Array96.t,hout:W8.t Array224.t):W8.t Array1152.t option = {
  var r,code,rhat:pke_poly;var pad:W8.t Array192.t;
  var serialized:W8.t Array1152.t;var input:W8.t Array1153.t;
  var ct:W8.t Array1152.t option;
  r<@NTRUPlus768PolyCBD1Checked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(witness,complete_hash_tail hout);
  rhat<@NTRUPlus768NTT.M.jade_ntruplus_ntruplus768_amd64_ref_ntt(witness,r);
  (serialized,input)<@NTRUPlus768DecapMessagePrepare.M.jade_ntruplus_ntruplus768_amd64_ref_decap_message_prepare(witness,witness,rhat);
  pad<@G.get(peel1153 input);
  code<@NTRUPlus768PolySOTPEncodeChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_encode(witness,msg,pad);
  ct<@PKEEnc.run(pk,code,r);
  return ct;
 }
}.
lemma rt_kernel_sim_plain_projection (G<:FOGPort) :
 equiv[RTKernelSimPlain(G).run ~ SimEncrypt(G).run:
 ={arg,glob G} ==> ={res,glob G}].
proof.
 proc;inline{2} FOHashG(FOGHash(G)).run ACWC2GPrepare.run FOGHash(G).shake SOTPEncode.run.
 sim (: ={glob G});auto.
qed.
lemma rt_kernel_sim_measured_projection (G<:RTKernelCostGPort) :
 equiv[RTKernelSimEncrypt(G).run ~ RTKernelSimPlain(RTKernelGValue(G)).run:
 ={arg,glob G} ==>res{1}.`1=res{2} /\ ={glob G}].
proof.
 proc;sp 1 0;
 seq 6 1:(={pk,msg,hout,r,glob G}).
 + wp;call rt_fixed_cbd_jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1_projection.
   wp;ecall{1}(rt_kernel_tail_correct hout{1});auto.
 seq 3 1:(={pk,msg,hout,r,rhat,glob G}).
 + wp;call rt_fixed_ntt_jade_ntruplus_ntruplus768_amd64_ref_ntt_projection;auto.
 seq 3 1:(={pk,msg,hout,r,rhat,serialized,input,glob G}).
 + wp;call rt_fixed_gprepare_jade_ntruplus_ntruplus768_amd64_ref_decap_message_prepare_projection;auto.
 seq 7 1:(={pk,msg,hout,r,pad,glob G}).
 + wp;call(rt_kernel_g_projection G).
   wp;ecall{1}(rt_kernel_peel_correct input{1});auto.
 seq 3 1:(={pk,msg,hout,r,code,glob G}).
 + wp;call rt_fixed_sotpencode_jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_encode_projection;auto.
 wp;call rt_kernel_pkeenc_projection;auto.
qed.
lemma rt_kernel_sim_encrypt_projection (G<:RTKernelCostGPort) :
 equiv[RTKernelSimEncrypt(G).run ~ SimEncrypt(RTKernelGValue(G)).run:
 ={arg,glob G} ==>res{1}.`1=res{2} /\ ={glob G}].
proof.
 transitivity RTKernelSimPlain(RTKernelGValue(G)).run
 (={arg,glob G} ==>res{1}.`1=res{2} /\ ={glob G})
 (={arg,glob G} ==> ={res,glob G}).
 + move=> &1 &2 [ha hg];exists (glob G){1} arg{1};smt().
 + smt().
 + exact(rt_kernel_sim_measured_projection G).
 exact(rt_kernel_sim_plain_projection (RTKernelGValue(G))).
qed.
lemma rt_kernel_sim_encrypt_ll (G<:RTKernelCostGPort) :
 islossless G.get=>islossless RTKernelSimEncrypt(G).run.
proof.
 move=>hG;have hv:islossless RTKernelGValue(G).get by proc;call hG;auto.
 conseq(rt_kernel_sim_encrypt_projection G)(sim_encrypt_lossless (RTKernelGValue(G)) hv);smt().
qed.
lemma rt_kernel_sim_encrypt_local_cost (G<:RTKernelCostGPort) :
 hoare[RTKernelSimEncrypt(G).run:true ==>
 0<=res.`2-res.`3<=rt_kernel_sim_encrypt_bound].
proof.
 proc;seq 1:(work=4416);first by auto.
 seq 3:(0<=work<=4416+579+rt_kernel_tail_bound).
 + wp;ecall(rt_kernel_tail_spec hout);auto=> />;smt().
 seq 3:(0<=work<=4416+579+rt_kernel_tail_bound+3076+rt_fixed_cbd_bound).
 + wp;call rt_fixed_cbd_bound_cost;auto=> />;smt().
 seq 3:(0<=work<=4416+579+rt_kernel_tail_bound+3076+rt_fixed_cbd_bound+3076+rt_fixed_ntt_bound).
 + wp;call rt_fixed_ntt_bound_cost;auto=> />;smt().
 seq 3:(0<=work<=4416+579+rt_kernel_tail_bound+3076+rt_fixed_cbd_bound+3076+rt_fixed_ntt_bound+9225+rt_fixed_gprepare_bound).
 + wp;call rt_fixed_gprepare_bound_cost;auto=> />;smt().
 seq 3:(0<=work<=4416+579+rt_kernel_tail_bound+3076+rt_fixed_cbd_bound+3076+rt_fixed_ntt_bound+9225+rt_fixed_gprepare_bound+3459+rt_kernel_peel_bound).
 + wp;ecall(rt_kernel_peel_spec input);auto=> />;smt().
 seq 4:(0<=work-backend<=4416+579+rt_kernel_tail_bound+3076+rt_fixed_cbd_bound+3076+rt_fixed_ntt_bound+9225+rt_fixed_gprepare_bound+3459+rt_kernel_peel_bound+579).
 + wp;call(_:true ==>true);first by trivial.
   auto=> />;smt().
 seq 3:(0<=work-backend<=4416+579+rt_kernel_tail_bound+3076+rt_fixed_cbd_bound+3076+rt_fixed_ntt_bound+9225+rt_fixed_gprepare_bound+3459+rt_kernel_peel_bound+579+3077+rt_fixed_sotpencode_bound).
 + wp;call rt_fixed_sotpencode_bound_cost;auto=> />;smt().
 wp;call rt_kernel_pkeenc_cost;auto=> />;rewrite /rt_kernel_sim_encrypt_bound;smt().
qed.
lemma rt_kernel_sim_encrypt_backend_cost (G<:RTKernelCostGPort) Cg :
 hoare[G.get:true ==>0<=res.`2<=Cg]=>
 hoare[RTKernelSimEncrypt(G).run:true ==>0<=res.`3<=Cg].
proof.
 move=>hG;proc;wp;call(_:true ==>true);first by trivial.
 wp;call(_:true ==>true);first by trivial.
 wp;call hG;wp;
 call(_:true ==>true);first by trivial.
 wp;call(_:true ==>true);first by trivial.
 wp;call(_:true ==>true);first by trivial.
 wp;call(_:true ==>true);first by trivial.
 wp;call(_:true ==>true);first by trivial.
 auto.
qed.
lemma rt_kernel_sim_encrypt_total_cost (G<:RTKernelCostGPort) Cg :
 hoare[G.get:true ==>0<=res.`2<=Cg]=>
 hoare[RTKernelSimEncrypt(G).run:true ==>
 0<=res.`2<=rt_kernel_sim_encrypt_bound+Cg].
proof.
 move=>hG;conseq(rt_kernel_sim_encrypt_local_cost G)(rt_kernel_sim_encrypt_backend_cost G Cg hG);smt().
qed.
lemma rt_kernel_sim_encrypt_cost_correct (G<:RTKernelCostGPort) Cg :
 islossless G.get=>hoare[G.get:true ==>0<=res.`2<=Cg]=>
 phoare[RTKernelSimEncrypt(G).run:true ==>
 0<=res.`2<=rt_kernel_sim_encrypt_bound+Cg]=1%r.
proof.
 move=>hg hc;by conseq(rt_kernel_sim_encrypt_ll G hg)(rt_kernel_sim_encrypt_total_cost G Cg hc).
qed.
