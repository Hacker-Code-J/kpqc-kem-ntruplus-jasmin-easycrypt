require import AllCore Distr List FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152 Array2336.
require import NTRUPlus768SimModel NTRUPlus768SimSampling NTRUPlus768SimAnswer NTRUPlus768SimPrefix NTRUPlus768SimOracles.
require import NTRUPlus768ROMOracles.
require import NTRUPlus768RawXOF NTRUPlus768FOSetupDistribution.
require import NTRUPlus768FOModel NTRUPlus768FOEagerG NTRUPlus768FOGAdapters.
require import NTRUPlus768CCAGame NTRUPlus768CCAStatusAdapter NTRUPlus768CCADecapOracle NTRUPlus768CCAOraclePorts.

(* The hybrid counts only unknown-answer calls. All shared-state callbacks
   go through the leak port, as required by Hybrid's module restrictions. *)
type sim_leak_input = [
 SimLeakE of W8.t Array32.t
 | SimLeakF of W8.t Array1152.t
 | SimLeakG of W8.t Array1152.t
 | SimLeakH of fo_h_input
 | SimLeakRaw of (W8.t list * int)
 | SimLeakDecap of W8.t Array1152.t
].
type sim_leak_output = [
 SimOut192 of W8.t Array192.t
 | SimOut32 of W8.t Array32.t
 | SimOut224 of W8.t Array224.t
 | SimOutRaw of W8.t list option
 | SimOutDecap of (sim_request option * cca_reply)
].
op sim_out192 (x:sim_leak_output) = with x=SimOut192 y=>y with x=SimOut32 _=>witness with x=SimOut224 _=>witness with x=SimOutRaw _=>witness with x=SimOutDecap _=>witness.
op sim_out32 (x:sim_leak_output) = with x=SimOut32 y=>y with x=SimOut192 _=>witness with x=SimOut224 _=>witness with x=SimOutRaw _=>witness with x=SimOutDecap _=>witness.
op sim_out224 (x:sim_leak_output) = with x=SimOut224 y=>y with x=SimOut192 _=>witness with x=SimOut32 _=>witness with x=SimOutRaw _=>witness with x=SimOutDecap _=>witness.
op sim_out_raw (x:sim_leak_output) = with x=SimOutRaw y=>y with x=SimOut192 _=>None with x=SimOut32 _=>None with x=SimOut224 _=>None with x=SimOutDecap _=>None.
op sim_out_decap (x:sim_leak_output) = with x=SimOutDecap y=>y with x=SimOut192 _=>(None,None) with x=SimOut32 _=>(None,None) with x=SimOut224 _=>(None,None) with x=SimOutRaw _=>(None,None).

module type SimLeaks = {proc leaks(x:sim_leak_input):sim_leak_output}.

module SimPrepare(G:FOGPort,H:SimHPort) = {
 proc run(ct:W8.t Array1152.t) : sim_request option * cca_reply = {
  var request:sim_request option;var result:cca_reply;var q:sim_request;
  SimPublic.count<-SimPublic.count+1;
  request<-None;result<-None;
  if(SimPublic.cstar<>Some ct){
   request<@SimPrefix(G).run(SimPublic.pk,ct,CCADecapOracle.sk);
   if(request<>None){
    q<-oget request;
    if(sim_h_input q \in SimHistory.h \/ Some(sim_h_input q)=FOContext.challenge_h){
     result<@SimAnswerReal(G,H).answer(q);
     request<-None;
    }
   }
  }
  return(request,result);
 }
}.
module SimLeaksBackend(G:FOGPort,H:SimHPort) : SimLeaks = {
 proc leaks(x:sim_leak_input) : sim_leak_output = {
  var out:sim_leak_output;var y192:W8.t Array192.t;var y32:W8.t Array32.t;
  var y224:W8.t Array224.t;var yr:W8.t list option;var yd:sim_request option * cca_reply;
  match x with
  | SimLeakE input=>{y192<@SimOracles(G,H).e(input);out<-SimOut192 y192;}
  | SimLeakF input=>{y32<@SimOracles(G,H).f(input);out<-SimOut32 y32;}
  | SimLeakG input=>{y192<@SimOracles(G,H).g(input);out<-SimOut192 y192;}
  | SimLeakH input=>{y224<@SimOracles(G,H).h(input);out<-SimOut224 y224;}
  | SimLeakRaw input=>{yr<@SimOracles(G,H).raw(input.`1,input.`2);out<-SimOutRaw yr;}
  | SimLeakDecap input=>{yd<@SimPrepare(G,H).run(input);out<-SimOutDecap yd;}
  end;
  return out;
 }
}.
module SimLeakHashes(B:SimLeaks) : CCAExtendedOraclePort = {
 proc e(input:W8.t Array32.t):W8.t Array192.t={var r;r<@B.leaks(SimLeakE input);return sim_out192 r;}
 proc f(input:W8.t Array1152.t):W8.t Array32.t={var r;r<@B.leaks(SimLeakF input);return sim_out32 r;}
 proc g(input:W8.t Array1152.t):W8.t Array192.t={var r;r<@B.leaks(SimLeakG input);return sim_out192 r;}
 proc h(input:fo_h_input):W8.t Array224.t={var r;r<@B.leaks(SimLeakH input);return sim_out224 r;}
 proc raw(input:W8.t list,outlen:int):W8.t list option={var r;r<@B.leaks(SimLeakRaw(input,outlen));return sim_out_raw r;}
}.
module SimLeakDecaps(B:SimLeaks,U:SimAnswer) : CCADecapPort = {
 proc decap(ct:W8.t Array1152.t) : cca_reply = {
  var out:sim_leak_output;var request:sim_request option;var reply:cca_reply;
  out<@B.leaks(SimLeakDecap ct);
  (request,reply)<-sim_out_decap out;
  if(request<>None){reply<@U.answer(oget request);}
  return reply;
 }
}.

module SimPhaseInput = {
 var pk,ct:W8.t Array1152.t
 var key:W8.t Array32.t
 var bit:bool
 proc init(pk0 ct0:W8.t Array1152.t,key0:W8.t Array32.t,bit0:bool)={pk<-pk0;ct<-ct0;key<-key0;bit<-bit0;}
}.
module SimAdaptive(A:CCAExtendedAdversary,B:SimLeaks,U:SimAnswer) = {
 proc distinguish(s:fo_setup_observation) : bool = {
  var guess:bool;
  guess<@A(SimLeakHashes(B),SimLeakDecaps(B,U)).guess(SimPhaseInput.pk,SimPhaseInput.ct,SimPhaseInput.key);
  return guess=SimPhaseInput.bit;
 }
}.

lemma sim_phase_input_ll : islossless SimPhaseInput.init.
proof. proc;auto. qed.
lemma sim_leak_e_ll (B<:SimLeaks) : islossless B.leaks=>islossless SimLeakHashes(B).e.
proof. move=>h;proc;call h;auto. qed.
lemma sim_leak_f_ll (B<:SimLeaks) : islossless B.leaks=>islossless SimLeakHashes(B).f.
proof. move=>h;proc;call h;auto. qed.
lemma sim_leak_g_ll (B<:SimLeaks) : islossless B.leaks=>islossless SimLeakHashes(B).g.
proof. move=>h;proc;call h;auto. qed.
lemma sim_leak_h_ll (B<:SimLeaks) : islossless B.leaks=>islossless SimLeakHashes(B).h.
proof. move=>h;proc;call h;auto. qed.
lemma sim_leak_raw_ll (B<:SimLeaks) : islossless B.leaks=>islossless SimLeakHashes(B).raw.
proof. move=>h;proc;call h;auto. qed.
lemma sim_leak_decap_ll (B<:SimLeaks)(U<:SimAnswer):
 islossless B.leaks=>islossless U.answer=>islossless SimLeakDecaps(B,U).decap.
proof. move=>hb hu;proc;seq 2:true;1,4,5:by auto. by wp;call hb;auto. if;auto;call hu;auto. qed.

lemma sim_prepare_ll (G<:FOGPort)(H<:SimHPort) :
 islossless G.get=>islossless H.get=>islossless SimPrepare(G,H).run.
proof.
 move=>hg hh;proc;sp;if;last by auto.
 seq 1:true;1,4,5:by auto. by call(sim_prefix_ll G hg);auto.
 if;last by auto. sp;if;last by auto.
 wp;call(sim_answer_real_ll G H hg hh);auto.
qed.
lemma sim_leaks_backend_ll (G<:FOGPort)(H<:SimHPort) :
 islossless G.get=>islossless H.get=>islossless SimLeaksBackend(G,H).leaks.
proof.
 move=>hg hh;proc;match.
 + inline SimOracles(G,H).e;wp;call roe_get_ll;auto.
 + inline SimOracles(G,H).f;wp;call rof_get_ll;auto.
 + inline SimOracles(G,H).g;wp;call hg;auto.
 + wp;call(sim_logged_h_ll H hh);auto.
 + wp;call(sim_raw_get_ll G H hg hh);auto.
 wp;call(sim_prepare_ll G H hg hh);auto.
qed.
lemma sim_adaptive_ll (A<:CCAExtendedAdversary) (B<:SimLeaks {-A})(U<:SimAnswer {-A}) :
 islossless B.leaks=>islossless U.answer=>
 (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
 islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
 islossless D.decap=>islossless A(H,D).guess)=>
 islossless SimAdaptive(A,B,U).distinguish.
proof.
 move=>hb hu ha;proc;call(ha (SimLeakHashes(B)) (SimLeakDecaps(B,U))
 (sim_leak_e_ll B hb)(sim_leak_f_ll B hb)(sim_leak_g_ll B hb)
 (sim_leak_h_ll B hb)(sim_leak_raw_ll B hb)(sim_leak_decap_ll B U hb hu));auto.
qed.
