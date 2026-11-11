require import AllCore List Distr FMap IntDiv.
from Jasmin require import JWord.
require import Array32 Array96 Array129 Array192 Array224 Array1152.
require import NTRUPlus768CCAQueryCodec NTRUPlus768ROMDomains.
require import NTRUPlus768RawXOFSampling NTRUPlus768RawXOF NTRUPlus768CCAGame.
require import NTRUPlus768CCADecapOracle NTRUPlus768CCAStatusAdapter.
require import NTRUPlus768FOModel.

op fo_raw_h (input:W8.t list) (outlen:int) =
 0<=outlen<=raw_xof_max_output /\ size input=129 /\ nth W8.zero input 0=W8.of_int 2.
op fo_query_count (nh nd:int) = nh+nd.
op fo_query_charge (nh nd lim:int) = min (nh+nd) lim.
op fo_budget_range (nh nd lim:int) = 0<=nh /\ 0<=nd /\ 0<=lim.

(* Attempts include repeated requests, raw zero-length requests, and every
   Decaps request. A denied request still increments the public attempt count.
   The clipped charge counts the first limit admitted requests. *)
module FOQueryRequest = {
 proc h() : bool = {
  var allowed:bool;
  allowed <- FOBudgetState.nH+FOBudgetState.nD<FOBudgetState.limit;
  FOBudgetState.nH <- FOBudgetState.nH+1;
  FOBudgetState.overflow <- FOBudgetState.overflow \/ !allowed;
  return allowed;
 }
 proc d() : bool = {
  var allowed:bool;
  allowed <- FOBudgetState.nH+FOBudgetState.nD<FOBudgetState.limit;
  FOBudgetState.nD <- FOBudgetState.nD+1;
  FOBudgetState.overflow <- FOBudgetState.overflow \/ !allowed;
  return allowed;
 }
}.
module FOCountHPort(H:CCAExtendedOraclePort) : CCAExtendedOraclePort = {
 proc e=H.e
 proc f=H.f
 proc g=H.g
 proc h(input:fo_h_input) : W8.t Array224.t = {
  var allowed:bool; var result:W8.t Array224.t;
  allowed <@ FOQueryRequest.h();
  result <@ H.h(input); return result;
 }
 proc raw(input:W8.t list,outlen:int) : W8.t list option = {
  var allowed:bool; var result:W8.t list option;
  if(fo_raw_h input outlen){allowed <@ FOQueryRequest.h();}
  result <@ H.raw(input,outlen); return result;
 }
}.
(* Identity counter assignments expose each public callback as a concrete
   FEL boundary even for an abstract backend. They change no counter value;
   the non-H projection lemmas below make that equality explicit. *)
module FOCapHPort(H:CCAExtendedOraclePort) : CCAExtendedOraclePort = {
 proc e(input:W8.t Array32.t) : W8.t Array192.t = {
  var r:W8.t Array192.t; r<@H.e(input);
  FOBudgetState.nH<-FOBudgetState.nH; return r;
 }
 proc f(input:W8.t Array1152.t) : W8.t Array32.t = {
  var r:W8.t Array32.t; r<@H.f(input);
  FOBudgetState.nH<-FOBudgetState.nH; return r;
 }
 proc g(input:W8.t Array1152.t) : W8.t Array192.t = {
  var r:W8.t Array192.t; r<@H.g(input);
  FOBudgetState.nH<-FOBudgetState.nH; return r;
 }
 proc h(input:fo_h_input) : W8.t Array224.t = {
  var allowed:bool; var result:W8.t Array224.t;
  allowed <@ FOQueryRequest.h(); result <- witness;
  if(allowed){result <@ H.h(input);}
  FOBudgetState.nH<-FOBudgetState.nH;
  return result;
 }
 proc raw(input:W8.t list,outlen:int) : W8.t list option = {
  var allowed:bool; var result:W8.t list option;
  allowed <- true;
  if(fo_raw_h input outlen){allowed <@ FOQueryRequest.h();}
  result <- None;
  if(allowed){result <@ H.raw(input,outlen);}
  FOBudgetState.nH<-FOBudgetState.nH;
  return result;
 }
}.
module FOCountDPort(D:CCADecapPort) : CCADecapPort = {
 proc decap(ct:W8.t Array1152.t) : cca_reply = {
  var allowed:bool; var result:cca_reply;
  allowed <@ FOQueryRequest.d();
  result <@ D.decap(ct); return result;
 }
}.
module FOCapDPort(D:CCADecapPort) : CCADecapPort = {
 proc decap(ct:W8.t Array1152.t) : cca_reply = {
  var allowed:bool; var result:cca_reply;
  allowed <@ FOQueryRequest.d(); result <- None;
  if(allowed){result <@ D.decap(ct);}
  FOBudgetState.nD<-FOBudgetState.nD;
  return result;
 }
}.
module FOCountedA(A:CCAExtendedAdversary,H:CCAExtendedOraclePort,D:CCADecapPort) = {
 proc guess=A(FOCountHPort(H),FOCountDPort(D)).guess
}.
module FOCappedA(A:CCAExtendedAdversary,H:CCAExtendedOraclePort,D:CCADecapPort) = {
 proc guess=A(FOCapHPort(H),FOCapDPort(D)).guess
}.

lemma fo_raw_h_encoded x n :
 fo_raw_h (raw_query(H x)) n=(0<=n<=raw_xof_max_output).
proof.
 rewrite /fo_raw_h /= Array129.size_to_list list129_head encode_h_tag /=.
 done.
qed.
lemma fo_raw_h_zero x : fo_raw_h(raw_query(H x))0.
proof. rewrite fo_raw_h_encoded /raw_xof_max_output; done. qed.
lemma fo_raw_h_invalid input n : !(0<=n<=raw_xof_max_output)=>!fo_raw_h input n.
proof. rewrite /fo_raw_h; smt(). qed.
lemma fo_raw_h_classification input n :
 fo_raw_h input n <=>
 0<=n<=raw_xof_max_output /\ exists x,decode_typed input=Some(H x).
proof.
 rewrite /fo_raw_h /decode_typed.
 case(size input=32); case(size input=1153); case(size input=129);
 case(nth W8.zero input 0=W8.of_int 2); smt().
qed.

lemma fo_request_h_ll : islossless FOQueryRequest.h.
proof. proc; auto. qed.
lemma fo_request_d_ll : islossless FOQueryRequest.d.
proof. proc; auto. qed.
lemma fo_count_h_ll (H<:CCAExtendedOraclePort) : islossless H.h=>islossless FOCountHPort(H).h.
proof. move=>h; proc; call h; call fo_request_h_ll; auto. qed.
lemma fo_count_raw_ll (H<:CCAExtendedOraclePort) : islossless H.raw=>islossless FOCountHPort(H).raw.
proof. move=>h; proc; call h; if; auto; call fo_request_h_ll; auto. qed.
lemma fo_cap_h_ll (H<:CCAExtendedOraclePort) : islossless H.h=>islossless FOCapHPort(H).h.
proof. move=>h; proc; seq 2:true; 1,4,5:by auto. by wp; call fo_request_h_ll; auto. if; auto; call h; auto. qed.
lemma fo_cap_e_ll (H<:CCAExtendedOraclePort) : islossless H.e=>islossless FOCapHPort(H).e.
proof. move=>h; proc; wp; call h; auto. qed.
lemma fo_cap_f_ll (H<:CCAExtendedOraclePort) : islossless H.f=>islossless FOCapHPort(H).f.
proof. move=>h; proc; wp; call h; auto. qed.
lemma fo_cap_g_ll (H<:CCAExtendedOraclePort) : islossless H.g=>islossless FOCapHPort(H).g.
proof. move=>h; proc; wp; call h; auto. qed.
lemma fo_cap_raw_ll (H<:CCAExtendedOraclePort) : islossless H.raw=>islossless FOCapHPort(H).raw.
proof. move=>h; proc; seq 3:true; 1,4,5:by auto. wp; sp 1; if; auto; call fo_request_h_ll; auto. if; auto; call h; auto. qed.
lemma fo_count_d_ll (D<:CCADecapPort) : islossless D.decap=>islossless FOCountDPort(D).decap.
proof. move=>h; proc; call h; call fo_request_d_ll; auto. qed.
lemma fo_cap_d_ll (D<:CCADecapPort) : islossless D.decap=>islossless FOCapDPort(D).decap.
proof. move=>h; proc; seq 2:true; 1,4,5:by auto. by wp; call fo_request_d_ll; auto. if; auto; call h; auto. qed.

lemma fo_request_h_state nh nd lim over : hoare[FOQueryRequest.h:
 FOBudgetState.nH=nh /\ FOBudgetState.nD=nd /\ FOBudgetState.limit=lim /\ FOBudgetState.overflow=over ==>
 FOBudgetState.nH=nh+1 /\ FOBudgetState.nD=nd /\ FOBudgetState.limit=lim /\
 res=(nh+nd<lim) /\ FOBudgetState.overflow=(over \/ !(nh+nd<lim))].
proof. proc; auto. qed.
lemma fo_request_d_state nh nd lim over : hoare[FOQueryRequest.d:
 FOBudgetState.nH=nh /\ FOBudgetState.nD=nd /\ FOBudgetState.limit=lim /\ FOBudgetState.overflow=over ==>
 FOBudgetState.nH=nh /\ FOBudgetState.nD=nd+1 /\ FOBudgetState.limit=lim /\
 res=(nh+nd<lim) /\ FOBudgetState.overflow=(over \/ !(nh+nd<lim))].
proof. proc; auto. qed.

lemma fo_count_h_projection (H<:CCAExtendedOraclePort {-FOBudgetState}) :
 equiv[FOCountHPort(H).h ~ H.h : ={input,glob H} ==> ={res,glob H}].
proof. proc*; inline FOCountHPort(H).h FOQueryRequest.h; sim. qed.
lemma fo_count_raw_projection (H<:CCAExtendedOraclePort {-FOBudgetState}) :
 equiv[FOCountHPort(H).raw ~ H.raw : ={input,outlen,glob H} ==> ={res,glob H}].
proof.
 proc*; inline{1} FOCountHPort(H).raw.
 wp; call(_: ={arg,glob H} ==> ={res,glob H}); first by proc true; auto.
 inline FOQueryRequest.h; auto.
qed.
lemma fo_count_d_projection (D<:CCADecapPort {-FOBudgetState}) :
 equiv[FOCountDPort(D).decap ~ D.decap : ={ct,glob D} ==> ={res,glob D}].
proof. proc*; inline FOCountDPort(D).decap FOQueryRequest.d; sim. qed.

lemma fo_cap_e_projection (H<:CCAExtendedOraclePort {-FOBudgetState}) :
 equiv[FOCapHPort(H).e ~ H.e:
 ={input,glob H,glob FOBudgetState} ==> ={res,glob H,glob FOBudgetState}].
proof.
 proc*; inline{1} FOCapHPort(H).e; wp.
 call(_: ={arg,glob H} ==> ={res,glob H}); first by proc true; auto.
 auto.
qed.
lemma fo_cap_f_projection (H<:CCAExtendedOraclePort {-FOBudgetState}) :
 equiv[FOCapHPort(H).f ~ H.f:
 ={input,glob H,glob FOBudgetState} ==> ={res,glob H,glob FOBudgetState}].
proof.
 proc*; inline{1} FOCapHPort(H).f; wp.
 call(_: ={arg,glob H} ==> ={res,glob H}); first by proc true; auto.
 auto.
qed.
lemma fo_cap_g_projection (H<:CCAExtendedOraclePort {-FOBudgetState}) :
 equiv[FOCapHPort(H).g ~ H.g:
 ={input,glob H,glob FOBudgetState} ==> ={res,glob H,glob FOBudgetState}].
proof.
 proc*; inline{1} FOCapHPort(H).g; wp.
 call(_: ={arg,glob H} ==> ={res,glob H}); first by proc true; auto.
 auto.
qed.

lemma fo_charge_bounds nh nd lim : fo_budget_range nh nd lim=>0<=fo_query_charge nh nd lim<=lim.
proof. rewrite /fo_budget_range /fo_query_charge; smt(). qed.
lemma fo_charge_h_step nh nd lim :
 fo_query_charge (nh+1) nd lim=fo_query_charge nh nd lim+b2i(nh+nd<lim).
proof. rewrite /fo_query_charge; smt(). qed.
lemma fo_charge_d_step nh nd lim :
 fo_query_charge nh (nd+1) lim=fo_query_charge nh nd lim+b2i(nh+nd<lim).
proof. rewrite /fo_query_charge; smt(). qed.
lemma fo_budget_configured q : hoare[FOBudgetState.configure:arg=q ==>
 FOBudgetState.nH=0 /\ FOBudgetState.nD=0 /\ FOBudgetState.limit=max 0 q /\
 !FOBudgetState.overflow /\ fo_query_charge FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit=0 /\
 fo_budget_range FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit].
proof. proc; auto; rewrite /fo_query_charge /fo_budget_range; smt(). qed.

lemma fo_count_h_count (H<:CCAExtendedOraclePort {-FOBudgetState}) nh nd lim :
 hoare[FOCountHPort(H).h:FOBudgetState.nH=nh /\ FOBudgetState.nD=nd /\ FOBudgetState.limit=lim ==>
 FOBudgetState.nH=nh+1 /\ FOBudgetState.nD=nd /\ FOBudgetState.limit=lim].
proof. proc; call(_:true ==>true); first by trivial. inline FOQueryRequest.h; auto. qed.
lemma fo_cap_h_count (H<:CCAExtendedOraclePort {-FOBudgetState}) nh nd lim :
 hoare[FOCapHPort(H).h:FOBudgetState.nH=nh /\ FOBudgetState.nD=nd /\ FOBudgetState.limit=lim ==>
 FOBudgetState.nH=nh+1 /\ FOBudgetState.nD=nd /\ FOBudgetState.limit=lim].
proof. proc; inline FOQueryRequest.h; sp; if; auto; call(_:true ==>true); first by trivial. auto. qed.
lemma fo_count_raw_count (H<:CCAExtendedOraclePort {-FOBudgetState}) nh nd lim x n :
 hoare[FOCountHPort(H).raw:input=x /\ outlen=n /\ FOBudgetState.nH=nh /\ FOBudgetState.nD=nd /\ FOBudgetState.limit=lim ==>
 FOBudgetState.nH=nh+b2i(fo_raw_h x n) /\ FOBudgetState.nD=nd /\ FOBudgetState.limit=lim].
proof. proc; call(_:true ==>true); first by trivial. inline FOQueryRequest.h; if; auto; smt(). qed.
lemma fo_cap_raw_count (H<:CCAExtendedOraclePort {-FOBudgetState}) nh nd lim x n :
 hoare[FOCapHPort(H).raw:input=x /\ outlen=n /\ FOBudgetState.nH=nh /\ FOBudgetState.nD=nd /\ FOBudgetState.limit=lim ==>
 FOBudgetState.nH=nh+b2i(fo_raw_h x n) /\ FOBudgetState.nD=nd /\ FOBudgetState.limit=lim].
proof.
 proc; seq 3 : (FOBudgetState.nH=nh+b2i(fo_raw_h x n) /\ FOBudgetState.nD=nd /\ FOBudgetState.limit=lim).
 + inline FOQueryRequest.h; sp 1; if; auto; smt().
 if; last by auto.
 wp; call(_:true ==>true); first by trivial. auto.
qed.
lemma fo_count_d_count (D<:CCADecapPort {-FOBudgetState}) nh nd lim :
 hoare[FOCountDPort(D).decap:FOBudgetState.nH=nh /\ FOBudgetState.nD=nd /\ FOBudgetState.limit=lim ==>
 FOBudgetState.nH=nh /\ FOBudgetState.nD=nd+1 /\ FOBudgetState.limit=lim].
proof. proc; call(_:true ==>true); first by trivial. inline FOQueryRequest.d; auto. qed.
lemma fo_cap_d_count (D<:CCADecapPort {-FOBudgetState}) nh nd lim :
 hoare[FOCapDPort(D).decap:FOBudgetState.nH=nh /\ FOBudgetState.nD=nd /\ FOBudgetState.limit=lim ==>
 FOBudgetState.nH=nh /\ FOBudgetState.nD=nd+1 /\ FOBudgetState.limit=lim].
proof. proc; inline FOQueryRequest.d; sp; if; auto; call(_:true ==>true); first by trivial. auto. qed.

lemma fo_cap_h_range (H<:CCAExtendedOraclePort {-FOBudgetState}) q0 :
 hoare[FOCapHPort(H).h:
 fo_budget_range FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit /\ FOBudgetState.limit=q0 ==>
 fo_budget_range FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit /\ FOBudgetState.limit=q0].
proof.
 proc; seq 2 : (fo_budget_range FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit /\ FOBudgetState.limit=q0).
 + inline FOQueryRequest.h; auto; rewrite /fo_budget_range; smt().
 if; last by auto.
 wp; call(_:true ==>true); first by trivial. auto.
qed.
lemma fo_cap_raw_range (H<:CCAExtendedOraclePort {-FOBudgetState}) q0 :
 hoare[FOCapHPort(H).raw:
 fo_budget_range FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit /\ FOBudgetState.limit=q0 ==>
 fo_budget_range FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit /\ FOBudgetState.limit=q0].
proof.
 proc; seq 3 : (fo_budget_range FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit /\ FOBudgetState.limit=q0).
 + inline FOQueryRequest.h; sp 1; if; auto; rewrite /fo_budget_range; smt().
 if; last by auto.
 wp; call(_:true ==>true); first by trivial. auto.
qed.
lemma fo_cap_d_range (D<:CCADecapPort {-FOBudgetState}) q0 :
 hoare[FOCapDPort(D).decap:
 fo_budget_range FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit /\ FOBudgetState.limit=q0 ==>
 fo_budget_range FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit /\ FOBudgetState.limit=q0].
proof.
 proc; seq 2 : (fo_budget_range FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit /\ FOBudgetState.limit=q0).
 + inline FOQueryRequest.d; auto; rewrite /fo_budget_range; smt().
 if; last by auto.
 wp; call(_:true ==>true); first by trivial. auto.
qed.
lemma fo_cap_adversary_range
 (A<:CCAExtendedAdversary {-FOBudgetState})
 (H<:CCAExtendedOraclePort {-A,-FOBudgetState}) (D<:CCADecapPort {-A,-FOBudgetState}) q0 :
 hoare[FOCappedA(A,H,D).guess:
 fo_budget_range FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit /\ FOBudgetState.limit=q0 ==>
 fo_budget_range FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit /\ FOBudgetState.limit=q0].
proof.
 proc(fo_budget_range FOBudgetState.nH FOBudgetState.nD FOBudgetState.limit /\ FOBudgetState.limit=q0); 1,2:by auto.
 + proc*; inline FOCapHPort(H).e; wp; call(_:true ==>true); first by trivial. auto.
 + proc*; inline FOCapHPort(H).f; wp; call(_:true ==>true); first by trivial. auto.
 + proc*; inline FOCapHPort(H).g; wp; call(_:true ==>true); first by trivial. auto.
 + exact(fo_cap_h_range H q0).
 + exact(fo_cap_raw_range H q0).
 exact(fo_cap_d_range D q0).
qed.

(* One aggregate backend keeps shared H/G state explicit. The two concrete
   instances may share ROH between the public H port and Decaps. No disjoint
   H/D-state hypothesis is built into this interface. *)
module type FOBackend = {
 proc e(input:W8.t Array32.t) : W8.t Array192.t
 proc f(input:W8.t Array1152.t) : W8.t Array32.t
 proc g(input:W8.t Array1152.t) : W8.t Array192.t
 proc h(input:fo_h_input) : W8.t Array224.t
 proc raw(input:W8.t list,outlen:int) : W8.t list option
 proc decap(ct:W8.t Array1152.t) : cca_reply
}.
module FOBackendPair(H:CCAExtendedOraclePort,D:CCADecapPort) : FOBackend = {
 proc e=H.e
 proc f=H.f
 proc g=H.g
 proc h=H.h
 proc raw=H.raw
 proc decap=D.decap
}.
module FOHashView(B:FOBackend) : CCAExtendedOraclePort = {
 proc e=B.e
 proc f=B.f
 proc g=B.g
 proc h=B.h
 proc raw=B.raw
}.
module FODecapView(B:FOBackend) : CCADecapPort = { proc decap=B.decap }.
