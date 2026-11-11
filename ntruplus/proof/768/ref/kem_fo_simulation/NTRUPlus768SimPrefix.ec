require import AllCore Distr.
from Jasmin require import JWord.
require import Array32 Array96 Array768 Array1152 Array2336 Array13506.
require import NTRUPlus768SimModel NTRUPlus768SimSampling NTRUPlus768SimAnswer.
require import NTRUPlus768FOEagerG NTRUPlus768FOGAdapters NTRUPlus768FOProcedures.
require import NTRUPlus768PKEModel NTRUPlus768DecapCompleteSpec.
require import NTRUPlus768DecapR2CompCaller NTRUPlus768DecapMessageProof.
require import NTRUPlus768DecapMessageSpec NTRUPlus768EncapGuardSpec.
require import NTRUPlus768DecapHashHPrepareProof NTRUPlus768ROMDomains NTRUPlus768KEMPayloadSpec.
require import NTRUPlus768ROMPayloadHash.
require import NTRUPlus768CCAStatusAdapter NTRUPlus768DecapClearProof.

module SimPrefix(G:FOGPort) = {
 proc run(pk ct:W8.t Array1152.t,sk:W8.t Array2336.t) : sim_request option = {
  var rp,mp:pke_poly;var ss:W8.t Array32.t;var status:W32.t;
  var bs:W8.t Array1152.t;var msg:W8.t Array96.t;var request:sim_request option;
  (rp,mp,ss,status) <@ GuardedR2.run(witness,witness,witness,witness,witness,encap_zero_ss,ct,complete_sk_poly sk);
  request<-None;
  if(status=W32.zero){
   (bs,msg,status) <@ DecapMessage(FOGHash(G)).run(witness,witness,witness,rp,mp);
   request<-Some {|sr_pk=pk;sr_ct=ct;sr_code=mp;sr_msg=msg;sr_fail=status;sr_suffix=complete_sk_suffix sk|};
  }
  return request;
 }
}.
module SimCore(G:FOGPort,D:SimAnswer) = {
 proc run(pk ct:W8.t Array1152.t,sk:W8.t Array2336.t) : W8.t Array32.t option = {
  var request:sim_request option;var result:W8.t Array32.t option;
  request <@ SimPrefix(G).run(pk,ct,sk);
  result<-None;
  if(request<>None){result <@ D.answer(oget request);}
  return result;
 }
}.

lemma sim_prefix_ll (G<:FOGPort) : islossless G.get=>islossless SimPrefix(G).run.
proof.
 move=>hg;proc;seq 2:true;1,4,5:by auto.
 + wp;call guarded_r2_lossless;auto.
 if;last by auto.
 wp;call(decap_message_lossless (FOGHash(G)) _);first by proc;call hg;auto.
 auto.
qed.
lemma sim_core_ll (G<:FOGPort)(D<:SimAnswer) :
 islossless G.get=>islossless D.answer=>islossless SimCore(G,D).run.
proof.
 move=>hg hd;proc;seq 2:true;1,4,5:by auto.
 + wp;call(sim_prefix_ll G hg);auto.
 if;last by auto.
 call hd;auto.
qed.

lemma sim_prefix_fields (G<:FOGPort) pk0 ct0 sk0 :
 hoare[SimPrefix(G).run:pk=pk0 /\ ct=ct0 /\ sk=sk0 ==>
 res<>None=>let q=oget res in q.`sr_pk=pk0 /\ q.`sr_ct=ct0 /\ q.`sr_suffix=complete_sk_suffix sk0].
proof.
 proc;seq 2:(pk=pk0 /\ ct=ct0 /\ sk=sk0 /\ request=None).
 + wp;call(_:true ==>true);first by trivial. auto.
 if;last by auto.
 wp;call(_:true ==>true);first by trivial. auto.
qed.

lemma sim_tail_answer (G<:FOGPort)(H<:SimHPort {-G}) q0 :
 equiv[FOTail(FOGHash(G),SimHShake(H)).run ~ SimAnswerReal(G,H).answer:
 pk{1}=q0.`sr_pk /\ ct{1}=q0.`sr_ct /\ m1{1}=q0.`sr_code /\
 msg{1}=q0.`sr_msg /\ decode_fail{1}=q0.`sr_fail /\ suffix{1}=q0.`sr_suffix /\
 q{2}=q0 /\ ={glob G,glob H} ==>
 cca_status_result res{1}.`1 res{1}.`2=res{2} /\ ={glob G,glob H}].
proof.
 proc;call(_: ={arg,glob G} ==> ={res,glob G});first by sim.
 inline{1} SimHShake(H).shake;wp.
 call(_: ={arg,glob H} ==> ={res,glob H});first by sim.
 wp;ecall{1}(hash_h_prepare_correct witness q0.`sr_msg q0.`sr_suffix).
 auto=> />;rewrite /sim_h_input;rewrite payload_h_preparation peel_encode_h;done.
qed.

lemma sim_core_actual (G<:FOGPort)(H<:SimHPort {-G}) :
 equiv[FOCore(FOGHash(G),SimHShake(H)).run ~ SimCore(G,SimAnswerReal(G,H)).run:
 ={pk,ct,sk,glob G,glob H} ==>
 cca_status_result res{1}.`1 res{1}.`2=res{2} /\ ={glob G,glob H}].
proof.
 proc;inline{2} SimPrefix(G).run;sp 0 3.
 seq 1 2:(={pk,ct,sk,rp,mp,ss,status,glob G,glob H} /\
  pk0{2}=pk{1} /\ ct0{2}=ct{1} /\ sk0{2}=sk{1} /\ request0{2}=None).
 + wp;call(_: ={arg} ==> ={res});first by sim.
   auto.
 if;first by auto.
 + seq 1 2:(={pk,ct,sk,mp,msg,status,glob G,glob H} /\
    request0{2}=Some {|sr_pk=pk{1};sr_ct=ct{1};sr_code=mp{1};sr_msg=msg{1};
      sr_fail=status{1};sr_suffix=complete_sk_suffix sk{1}|}).
   - wp;call(_: ={arg,glob G} ==> ={res,glob G});first by sim.
     auto.
   rcondt{2} 3;first by auto.
   wp;ecall(sim_tail_answer G H {|sr_pk=pk{1};sr_ct=ct{1};sr_code=mp{1};sr_msg=msg{1};
     sr_fail=status{1};sr_suffix=complete_sk_suffix sk{1}|});auto.
 rcondf{2} 3;first by auto.
 auto=> />;rewrite /cca_status_result;smt().
qed.

lemma sim_decaps_actual (G<:FOGPort)(H<:SimHPort {-G}) :
 equiv[FODecaps(FOGHash(G),SimHShake(H)).run ~ SimCore(G,SimAnswerReal(G,H)).run:
 ={pk,ct,sk,glob G,glob H} ==>
 cca_status_result res{1}.`1 res{1}.`2=res{2} /\
 res{1}.`3=clear_zero_spec /\ ={glob G,glob H}].
proof.
 proc*;inline{1} FODecaps(FOGHash(G),SimHShake(H)).run;wp.
 ecall{1}(decap_clear_correct workspace{1}).
 call(sim_core_actual G H);auto.
qed.
