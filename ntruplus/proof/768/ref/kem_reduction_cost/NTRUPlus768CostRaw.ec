require import AllCore List Distr FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152.
require import NTRUPlus768ROMDomains NTRUPlus768ROMOracles.
require import NTRUPlus768RawXOFSampling NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
require import NTRUPlus768FOEagerG NTRUPlus768FOGAdapters.
require import NTRUPlus768FOModel NTRUPlus768SimModel NTRUPlus768SimSampling NTRUPlus768SimOracles.
require import NTRUPlus768SecGOracles.

(* These are payload sizes, not CPU costs or a claim about the number of
   bytes physically traversed by abstract list/map operations. Invalid
   output lengths do not pass their input to SimRaw.full. *)
op cost_raw_input_bytes (input:W8.t list) (outlen:int) =
 if 0<=outlen<=raw_xof_max_output then size input else 0.
op cost_raw_output_bytes (answer:W8.t list option) =
 if answer=None then 0 else size(oget answer).

module CostRawRunner(R:RawXOFPort) = {
 proc get(input:W8.t list,outlen:int) : W8.t list option * int * int = {
  var answer:W8.t list option;var input_bytes,output_bytes:int;
  input_bytes<-cost_raw_input_bytes input outlen;
  answer<@R.get(input,outlen);
  output_bytes<-cost_raw_output_bytes answer;
  return(answer,input_bytes,output_bytes);
 }
}.
module CostRaw(G:FOGPort,H:SimHPort) = CostRawRunner(SimRaw(G,H)).

lemma cost_raw_input_nonnegative input outlen : 0<=cost_raw_input_bytes input outlen.
proof. rewrite /cost_raw_input_bytes;case(0<=outlen<=raw_xof_max_output);smt(size_ge0). qed.
lemma cost_raw_output_nonnegative answer : 0<=cost_raw_output_bytes answer.
proof. rewrite /cost_raw_output_bytes;case(answer=None);smt(size_ge0). qed.

lemma cost_raw_ll (G<:FOGPort) (H<:SimHPort) :
 islossless G.get=>islossless H.get=>islossless CostRaw(G,H).get.
proof. move=>hg hh;proc;wp;call(sim_raw_get_ll G H hg hh);auto. qed.

lemma cost_raw_runner_projection (R<:RawXOFPort) :
 equiv[CostRawRunner(R).get ~ R.get:
 ={input,outlen,glob R} ==>res{1}.`1=res{2} /\ ={glob R}].
proof.
 proc*;inline{1} CostRawRunner(R).get;wp.
 call(_: ={arg,glob R} ==> ={res,glob R});first by proc true;auto.
 auto.
qed.

(* The only call is the unchanged original procedure. The resource
   annotations are local; they add no adversary-visible global state. *)
lemma cost_raw_projection :
 equiv[CostRaw(SimGActual,SimHActual).get ~ SimRaw(SimGActual,SimHActual).get:
 ={input,outlen,glob ROE,glob ROF,glob ROG,glob ROH,
   glob RawXOFStreams,glob SimHistory} ==>
 res{1}.`1=res{2} /\
 ={glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob SimHistory}].
proof.
 conseq(cost_raw_runner_projection (SimRaw(SimGActual,SimHActual)))=> /#.
qed.

lemma cost_raw_logged_projection :
 equiv[CostRaw(SecGLogged(FOGActual),SimHActual).get ~ SimRaw(SecGLogged(FOGActual),SimHActual).get:
 ={input,outlen,glob ROE,glob ROF,glob ROG,glob ROH,
   glob RawXOFStreams,glob SimHistory,glob SecGHistory} ==>
 res{1}.`1=res{2} /\
 ={glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob SimHistory,glob SecGHistory}].
proof.
 conseq(cost_raw_runner_projection (SimRaw(SecGLogged(FOGActual),SimHActual)))=> /#.
qed.

lemma cost_raw_annotations (G<:FOGPort) (H<:SimHPort) input0 outlen0 :
 hoare[CostRaw(G,H).get:input=input0 /\ outlen=outlen0 ==>
 res.`2=cost_raw_input_bytes input0 outlen0 /\
 res.`3=cost_raw_output_bytes res.`1].
proof.
 proc;wp;call(_:true ==>true);first by trivial.
 auto.
qed.

lemma cost_sim_raw_shape (G<:FOGPort) (H<:SimHPort) outlen0 :
 hoare[SimRaw(G,H).get:outlen=outlen0 ==>
 if 0<=outlen0<=raw_xof_max_output
 then res<>None /\ size(oget res)=outlen0 else res=None].
proof.
 proc;sp;if.
 + wp;call(_:true ==>true);first by trivial.
   auto=> />;smt(raw_xof_output_size).
 auto.
qed.

lemma cost_raw_bytes_exact (G<:FOGPort) (H<:SimHPort) input0 outlen0 :
 hoare[CostRaw(G,H).get:input=input0 /\ outlen=outlen0 ==>
 res.`2=cost_raw_input_bytes input0 outlen0 /\
 res.`3=(if 0<=outlen0<=raw_xof_max_output then outlen0 else 0) /\
 (res.`1=None <=> !(0<=outlen0<=raw_xof_max_output))].
proof.
 proc;wp;call(cost_sim_raw_shape G H outlen0);auto=> />.
 rewrite /cost_raw_output_bytes;case(0<=outlen0<=raw_xof_max_output);smt().
qed.

lemma cost_raw_byte_bounds (G<:FOGPort) (H<:SimHPort) input0 outlen0 :
 hoare[CostRaw(G,H).get:input=input0 /\ outlen=outlen0 ==>
 0<=res.`2<=size input0 /\ 0<=res.`3<=224].
proof.
 conseq(cost_raw_bytes_exact G H input0 outlen0)=> //.
 rewrite /cost_raw_input_bytes /raw_xof_max_output;smt(size_ge0).
qed.

lemma cost_raw_empty_prefix stream : raw_xof_output 0 stream=[].
proof. by rewrite /raw_xof_output take0. qed.

lemma cost_sim_raw_zero (G<:FOGPort) (H<:SimHPort) :
 hoare[SimRaw(G,H).get:outlen=0 ==>res=Some []].
proof.
 proc;rcondt 2;first by auto=> />;rewrite /raw_xof_max_output.
 wp;call(_:true ==>true);first by trivial.
 auto;smt(cost_raw_empty_prefix).
qed.

lemma cost_raw_zero (G<:FOGPort) (H<:SimHPort) input0 :
 hoare[CostRaw(G,H).get:input=input0 /\ outlen=0 ==>
 res=(Some [],size input0,0)].
proof.
 proc;wp;call(cost_sim_raw_zero G H);auto=> />.
qed.

lemma cost_raw_actual_ll : islossless CostRaw(SimGActual,SimHActual).get.
proof.
 apply(cost_raw_ll SimGActual SimHActual).
 + exact rog_get_ll.
 exact roh_get_ll.
qed.

lemma cost_raw_zero_input_bytes n : 0<=n=>
 phoare[CostRaw(SimGActual,SimHActual).get:
 input=nseq n W8.zero /\ outlen=0 ==>res=(Some [],n,0)]=1%r.
proof.
 move=>hn;conseq cost_raw_actual_ll (cost_raw_zero SimGActual SimHActual (nseq n W8.zero))=> //.
 by rewrite size_nseq;smt().
qed.

lemma cost_raw_one_call_exceeds B &m : 0<=B=>
 Pr[CostRaw(SimGActual,SimHActual).get(nseq (B+1) W8.zero,0)@&m:
 res.`1=Some [] /\ B<res.`2 /\ res.`3=0]=1%r.
proof.
 move=>hB;byphoare(_:input=nseq(B+1)W8.zero /\ outlen=0 ==>_)=> //.
 conseq cost_raw_actual_ll (cost_raw_zero SimGActual SimHActual (nseq (B+1) W8.zero))=> //.
 by rewrite size_nseq;smt().
qed.

(* Output length zero still executes SimRaw.full and records H. *)
lemma cost_raw_zero_h_record (G<:FOGPort) (H<:SimHPort {-SimHistory}) x0 log0 :
 hoare[CostRaw(G,H).get:
 input=raw_query(H x0) /\ outlen=0 /\ SimHistory.h=log0 ==>
 (exists hout,SimHistory.h=log0.[x0<-hout]) /\
 res.`1=Some [] /\ res.`2=size(raw_query(H x0)) /\ res.`3=0].
proof.
 proc;wp;call(sim_raw_zero_h_record G H x0 log0);auto=> />.
 smt().
qed.

lemma cost_raw_zero_h_inserts x0 :
 phoare[CostRaw(SimGActual,SimHActual).get:
 input=raw_query(H x0) /\ outlen=0 /\ SimHistory.h=empty ==>
 res.`1=Some [] /\ x0 \in SimHistory.h /\ res.`3=0]=1%r.
proof.
 conseq cost_raw_actual_ll (cost_raw_zero_h_record SimGActual SimHActual x0 empty)=> //.
 move=> &hr hpre result h;smt(mem_set).
qed.
