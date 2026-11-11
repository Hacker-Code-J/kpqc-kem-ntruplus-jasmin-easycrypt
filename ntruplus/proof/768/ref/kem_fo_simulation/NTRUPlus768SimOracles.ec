require import AllCore List Distr FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152.
require import NTRUPlus768ROMDomains NTRUPlus768ROMDistributions NTRUPlus768ROMOracles.
require import NTRUPlus768CCAQueryCodec NTRUPlus768CCAOraclePorts.
require import NTRUPlus768RawXOFSampling NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
require import NTRUPlus768FOEagerG NTRUPlus768FOGAdapters NTRUPlus768FOQueryBudget.
require import NTRUPlus768FOModel.
require import NTRUPlus768SimModel NTRUPlus768SimSampling.

(* Only public typed/raw H calls use this wrapper. A repeated query is
   recorded too; the underlying H backend controls response consistency. *)
module SimLoggedH(H:SimHPort) : SimHPort = {
 proc get(input:fo_h_input) : W8.t Array224.t = {
  var hout;
  hout <@ H.get(input);
  SimHistory.record(input,hout);
  return hout;
 }
}.
module SimRaw(G:FOGPort,H:SimHPort) = {
 proc full(input:W8.t list) : W8.t Array224.t = {
  var stream;
  match decode_typed input with
  | None => {stream <@ FOGRawStreams(G).untyped(input);}
  | Some query => {
   match query with
   | E seed => {stream <@ FOGRawStreams(G).e(seed);}
   | F pk => {stream <@ FOGRawStreams(G).f(pk);}
   | G serialized => {stream <@ FOGRawStreams(G).g(serialized);}
   | H payload => {stream <@ SimLoggedH(H).get(payload);}
   end;
  }
  end;
  return stream;
 }
 proc get(input:W8.t list,outlen:int) : W8.t list option = {
  var result,stream;
  result<-None;
  if(0<=outlen<=raw_xof_max_output){
   stream <@ full(input);
   result<-Some(raw_xof_output outlen stream);
  }
  return result;
 }
}.
module SimOracles(G:FOGPort,H:SimHPort) : CCAExtendedOraclePort = {
 proc e=SharedCCAOracles.e
 proc f=SharedCCAOracles.f
 proc g(input:W8.t Array1152.t) : W8.t Array192.t = {var y; y <@ G.get(input);return y;}
 proc h=SimLoggedH(H).get
 proc raw=SimRaw(G,H).get
}.

lemma sim_log_included_extends log table table' :
 sim_log_included log table=>cache_extends table table'=>sim_log_included log table'.
proof. rewrite /sim_log_included /cache_extends; smt(). qed.
lemma sim_log_set_included log table x y :
 sim_log_included log table=>table.[x]=Some y=>sim_log_included log.[x<-y] table.
proof.
 move=>hl hv; rewrite /sim_log_included=>z v.
 rewrite get_setE; case(z=x)=>hz.
 + rewrite hz /=; smt().
 exact(hl z v).
qed.

lemma sim_logged_h_ll (H<:SimHPort) : islossless H.get=>islossless SimLoggedH(H).get.
proof. move=>h;proc;call sim_history_record_ll;call h;auto. qed.
lemma sim_logged_h_projection (H<:SimHPort {-SimHistory}) :
 equiv[SimLoggedH(H).get ~ H.get : ={input,glob H} ==> ={res,glob H}].
proof.
 proc*;inline{1} SimLoggedH(H).get SimHistory.record;wp.
 call(_: ={arg,glob H} ==> ={res,glob H});first by proc true;auto.
 auto.
qed.
lemma sim_logged_h_record (H<:SimHPort {-SimHistory}) x0 log0 :
 hoare[SimLoggedH(H).get:input=x0 /\ SimHistory.h=log0 ==>SimHistory.h=log0.[x0<-res]].
proof.
 proc;inline SimHistory.record;wp;call(_:true ==>true);first by trivial. auto.
qed.
lemma sim_logged_h_lookup (H<:SimHPort {-SimHistory}) x0 :
 hoare[SimLoggedH(H).get:input=x0 ==>SimHistory.h.[x0]=Some res].
proof.
 proc;inline SimHistory.record;wp;call(_:true ==>true);first by trivial.
 auto; smt(get_set_sameE).
qed.
lemma sim_logged_h_frame (H<:SimHPort {-SimPublic,-SimBad}) p0 b0 :
 hoare[SimLoggedH(H).get:glob SimPublic=p0 /\ glob SimBad=b0 ==>
 glob SimPublic=p0 /\ glob SimBad=b0].
proof. proc;inline SimHistory.record;wp;call(_:true ==>true);first by trivial. auto. qed.

lemma sim_logged_h_actual_included log0 table0 x0 :
 hoare[SimLoggedH(SimHActual).get:
 input=x0 /\ SimHistory.h=log0 /\ ROH.m=table0 /\ sim_log_included log0 table0 ==>
 sim_log_included SimHistory.h ROH.m /\ SimHistory.h.[x0]=Some res].
proof.
 proc;inline SimHistory.record;wp;call(roh_get_value table0 x0).
 auto; smt(sim_log_set_included sim_log_included_extends get_set_sameE).
qed.
lemma sim_logged_h_actual_invariant :
 hoare[SimLoggedH(SimHActual).get:sim_log_included SimHistory.h ROH.m ==>
 sim_log_included SimHistory.h ROH.m].
proof.
 proc*;exists* SimHistory.h,ROH.m,input;elim*=>log0 table0 x0.
 call(sim_logged_h_actual_included log0 table0 x0);auto.
qed.

lemma sim_raw_e_ll (G<:FOGPort) : islossless FOGRawStreams(G).e.
proof. proc;seq 1:true;1,4,5:by auto. by call roe_get_ll;auto. if;auto=> /> &hr _;exact uniform32_ll. qed.
lemma sim_raw_f_ll (G<:FOGPort) : islossless FOGRawStreams(G).f.
proof. proc;seq 1:true;1,4,5:by auto. by call rof_get_ll;auto. if;auto=> /> &hr _;exact uniform192_ll. qed.
lemma sim_raw_g_ll (G<:FOGPort) : islossless G.get=>islossless FOGRawStreams(G).g.
proof. move=>h;proc;seq 1:true;1,4,5:by auto. by call h;auto. if;auto=> /> &hr _;exact uniform32_ll. qed.
lemma sim_raw_untyped_ll (G<:FOGPort) : islossless FOGRawStreams(G).untyped.
proof. proc;if;auto=> /> &hr _;exact uniform224_ll. qed.
lemma sim_raw_full_ll (G<:FOGPort) (H<:SimHPort) :
 islossless G.get=>islossless H.get=>islossless SimRaw(G,H).full.
proof.
 move=>hg hh;proc;match.
 + call(sim_raw_untyped_ll G);auto.
 match.
 + call(sim_raw_e_ll G);auto.
 + call(sim_raw_f_ll G);auto.
 + call(sim_raw_g_ll G hg);auto.
 call(sim_logged_h_ll H hh);auto.
qed.
lemma sim_raw_get_ll (G<:FOGPort) (H<:SimHPort) :
 islossless G.get=>islossless H.get=>islossless SimRaw(G,H).get.
proof. move=>hg hh;proc;sp;if;last by auto. wp;call(sim_raw_full_ll G H hg hh);auto. qed.

lemma sim_raw_full_non_h_history (G<:FOGPort {-SimHistory}) (H<:SimHPort) log0 :
 hoare[SimRaw(G,H).full:SimHistory.h=log0 /\
 (forall x,decode_typed input<>Some(H x)) ==>SimHistory.h=log0].
proof.
 proc;match.
 + call(_:true ==>true);first by trivial. auto.
 match.
 + call(_:true ==>true);first by trivial. auto.
 + call(_:true ==>true);first by trivial. auto.
 + call(_:true ==>true);first by trivial. auto.
 conseq [-frame](_:false ==>_)=> //;smt().
qed.
lemma sim_raw_non_h_history (G<:FOGPort {-SimHistory}) (H<:SimHPort) log0 :
 hoare[SimRaw(G,H).get:SimHistory.h=log0 /\ !fo_raw_h input outlen ==>SimHistory.h=log0].
proof.
 proc;sp 1;if;last by auto.
 wp;call(sim_raw_full_non_h_history G H log0);auto=> />;smt(fo_raw_h_classification).
qed.
lemma sim_raw_invalid (G<:FOGPort) (H<:SimHPort) n0 log0 :
 !(0<=n0<=raw_xof_max_output)=>hoare[SimRaw(G,H).get:
 outlen=n0 /\ SimHistory.h=log0 ==>res=None /\ SimHistory.h=log0].
proof. move=>hn;proc;rcondf 2;auto. qed.

lemma sim_raw_full_h_record (G<:FOGPort) (H<:SimHPort {-SimHistory}) x0 log0 :
 hoare[SimRaw(G,H).full:decode_typed input=Some(H x0) /\ SimHistory.h=log0 ==>
 SimHistory.h=log0.[x0<-res]].
proof.
 proc;match.
 + conseq [-frame](_:false ==>_)=> //;smt().
 match.
 + conseq [-frame](_:false ==>_)=> //;smt().
 + conseq [-frame](_:false ==>_)=> //;smt().
 + conseq [-frame](_:false ==>_)=> //;smt().
 call(sim_logged_h_record H x0 log0);auto;smt().
qed.
lemma sim_raw_h_record (G<:FOGPort) (H<:SimHPort {-SimHistory}) x0 log0 n0 :
 0<=n0<=raw_xof_max_output=>hoare[SimRaw(G,H).get:
 decode_typed input=Some(H x0) /\ outlen=n0 /\ SimHistory.h=log0 ==>
 exists hout,SimHistory.h=log0.[x0<-hout] /\ res=Some(raw_xof_output n0 hout)].
proof.
 move=>hn;proc;rcondt 2;first by auto.
 wp;call(sim_raw_full_h_record G H x0 log0);auto=> />.
 move=> &hr _ hout;exists hout;done.
qed.
lemma sim_raw_zero_h_record (G<:FOGPort) (H<:SimHPort {-SimHistory}) x0 log0 :
 hoare[SimRaw(G,H).get:
 input=raw_query(H x0) /\ outlen=0 /\ SimHistory.h=log0 ==>
 exists hout,SimHistory.h=log0.[x0<-hout] /\ res=Some []].
proof.
 have h0:0<=0<=raw_xof_max_output by rewrite /raw_xof_max_output.
 conseq [-frame](sim_raw_h_record G H x0 log0 0 h0).
 + smt(decode_typed_encode).
 move=> &hr [hout [hh ->]];exists hout;by rewrite /raw_xof_output take0.
qed.

lemma sim_raw_full_frame (G<:FOGPort {-SimPublic,-SimBad})
 (H<:SimHPort {-SimPublic,-SimBad}) p0 b0 :
 hoare[SimRaw(G,H).full:glob SimPublic=p0 /\ glob SimBad=b0 ==>
 glob SimPublic=p0 /\ glob SimBad=b0].
proof.
 proc;match.
 + call(_:true ==>true);first by trivial. auto.
 match.
 + call(_:true ==>true);first by trivial. auto.
 + call(_:true ==>true);first by trivial. auto.
 + call(_:true ==>true);first by trivial. auto.
 call(sim_logged_h_frame H p0 b0);auto.
qed.
lemma sim_raw_get_frame (G<:FOGPort {-SimPublic,-SimBad})
 (H<:SimHPort {-SimPublic,-SimBad}) p0 b0 :
 hoare[SimRaw(G,H).get:glob SimPublic=p0 /\ glob SimBad=b0 ==>
 glob SimPublic=p0 /\ glob SimBad=b0].
proof.
 proc;sp 1;if;last by auto. wp;call(sim_raw_full_frame G H p0 b0);auto.
qed.

(* Exact physical-table projection. The private public-query history is
   not exposed through these response types. All raw suffix caches remain. *)
lemma sim_oracle_e_actual :
 equiv[SimOracles(SimGActual,SimHActual).e ~ SharedCCAExtendedOracles.e:
 ={arg,glob ROE} ==> ={res,glob ROE}].
proof. by sim. qed.
lemma sim_oracle_f_actual :
 equiv[SimOracles(SimGActual,SimHActual).f ~ SharedCCAExtendedOracles.f:
 ={arg,glob ROF} ==> ={res,glob ROF}].
proof. by sim. qed.
lemma sim_oracle_g_actual :
 equiv[SimOracles(SimGActual,SimHActual).g ~ SharedCCAExtendedOracles.g:
 ={arg,glob ROG} ==> ={res,glob ROG}].
proof. by sim. qed.
lemma sim_oracle_h_actual :
 equiv[SimOracles(SimGActual,SimHActual).h ~ SharedCCAExtendedOracles.h:
 ={arg,glob ROH} ==> ={res,glob ROH}].
proof.
 proc;inline SimHistory.record;wp.
 call(_: ={arg,glob ROH} ==> ={res,glob ROH});first by sim. auto.
qed.
lemma sim_raw_actual :
 equiv[SimRaw(SimGActual,SimHActual).get ~ RawXOF.get:
 ={arg,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams} ==>
 ={res,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams}].
proof.
 proc;inline SimRaw(SimGActual,SimHActual).full RawXOF.full
 FOGRawStreams(SimGActual).e FOGRawStreams(SimGActual).f FOGRawStreams(SimGActual).g FOGRawStreams(SimGActual).untyped
 SimLoggedH(SimHActual).get SimHistory.record
 RawXOFStreams.e RawXOFStreams.f RawXOFStreams.g RawXOFStreams.h RawXOFStreams.untyped
 SharedCCAOracles.e SharedCCAOracles.f SharedCCAOracles.g SharedCCAOracles.h;sim.
qed.

lemma sim_raw_full_actual_invariant :
 hoare[SimRaw(SimGActual,SimHActual).full:sim_log_included SimHistory.h ROH.m ==>
 sim_log_included SimHistory.h ROH.m].
proof.
 proc;match.
 + call(_:true ==>true);first by trivial. auto.
 match.
 + call(_:true ==>true);first by trivial. auto.
 + call(_:true ==>true);first by trivial. auto.
 + call(_:true ==>true);first by trivial. auto.
 call sim_logged_h_actual_invariant;auto.
qed.
lemma sim_raw_actual_invariant :
 hoare[SimRaw(SimGActual,SimHActual).get:sim_log_included SimHistory.h ROH.m ==>
 sim_log_included SimHistory.h ROH.m].
proof.
 proc;sp 1;if;last by auto. wp;call sim_raw_full_actual_invariant;auto.
qed.
