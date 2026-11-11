require import AllCore List FMap Distr.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152.
require import NTRUPlus768ROMDomains NTRUPlus768ROMOracles.
require import NTRUPlus768CCAQueryCodec NTRUPlus768CCAOraclePorts.
require import NTRUPlus768RawXOFSampling NTRUPlus768RawXOFStreams.

module type RawXOFPort = {
 proc get(input:W8.t list,outlen:int) : W8.t list option
}.

(* All byte-list inputs are covered. Invalid output lengths are rejected
   without changing any cache. A malformed input uses its entire byte list
   as an untyped cache key, never the old unconditional peeling adapters. *)
module RawXOF = {
 proc full(input:W8.t list) : W8.t Array224.t = {
  var stream;
  match decode_typed input with
  | None => { stream <@ RawXOFStreams.untyped(input); }
  | Some query => {
   match query with
   | E seed => { stream <@ RawXOFStreams.e(seed); }
   | F pk => { stream <@ RawXOFStreams.f(pk); }
   | G serialized => { stream <@ RawXOFStreams.g(serialized); }
   | H payload => { stream <@ RawXOFStreams.h(payload); }
   end;
  }
  end;
  return stream;
 }
 proc get(input:W8.t list,outlen:int) : W8.t list option = {
  var result,stream;
  result <- None;
  if(0<=outlen<=raw_xof_max_output){
   stream <@ full(input);
   result <- Some(raw_xof_output outlen stream);
  }
  return result;
 }
}.

module type CCAExtendedOraclePort = {
 proc e(input:W8.t Array32.t) : W8.t Array192.t
 proc f(input:W8.t Array1152.t) : W8.t Array32.t
 proc g(input:W8.t Array1152.t) : W8.t Array192.t
 proc h(input:W8.t Array96.t*W8.t Array32.t) : W8.t Array224.t
 proc raw(input:W8.t list,outlen:int) : W8.t list option
}.
module SharedCCAExtendedOracles : CCAExtendedOraclePort = {
 proc e=SharedCCAOracles.e
 proc f=SharedCCAOracles.f
 proc g=SharedCCAOracles.g
 proc h=SharedCCAOracles.h
 proc raw=RawXOF.get
}.

lemma raw_xof_full_ll : islossless RawXOF.full.
proof.
 proc; match.
 + by call raw_stream_untyped_ll; auto.
 match.
 + by call raw_stream_e_ll; auto.
 + by call raw_stream_f_ll; auto.
 + by call raw_stream_g_ll; auto.
 by call raw_stream_h_ll; auto.
qed.
lemma raw_xof_get_ll : islossless RawXOF.get.
proof. proc; sp; if; last by auto. wp; call raw_xof_full_ll; auto. qed.
lemma cca_extended_e_ll : islossless SharedCCAExtendedOracles.e.
proof. exact cca_e_ll. qed.
lemma cca_extended_f_ll : islossless SharedCCAExtendedOracles.f.
proof. exact cca_f_ll. qed.
lemma cca_extended_g_ll : islossless SharedCCAExtendedOracles.g.
proof. exact cca_g_ll. qed.
lemma cca_extended_h_ll : islossless SharedCCAExtendedOracles.h.
proof. exact cca_h_ll. qed.
lemma cca_extended_raw_ll : islossless SharedCCAExtendedOracles.raw.
proof. exact raw_xof_get_ll. qed.

lemma raw_xof_invalid_output n0 e0 f0 g0 h0 s0 :
 !(0<=n0<=raw_xof_max_output) => hoare[RawXOF.get :
 outlen=n0 /\ ROE.m=e0 /\ ROF.m=f0 /\ ROG.m=g0 /\ ROH.m=h0 /\
 glob RawXOFStreams=s0 ==>
 res=None /\ ROE.m=e0 /\ ROF.m=f0 /\ ROG.m=g0 /\ ROH.m=h0 /\
 glob RawXOFStreams=s0].
proof. move=>hn; proc; rcondf 2; auto. qed.
lemma raw_xof_output_length n0 : 0<=n0<=raw_xof_max_output =>
 hoare[RawXOF.get : outlen=n0 ==> res<>None /\ size(oget res)=n0].
proof.
 move=>hn; proc; rcondt 2; first by auto.
 wp; call (_:true ==> true); first by proc; match; [call (_:true ==>true)|match; call (_:true ==>true)]; auto.
 auto=> />.
 move=> result0; exact(raw_xof_output_size n0 result0 hn).
qed.

(* Optional resource policy. Every request, including repeats and rejected
   requests, consumes one position in the request budget. The separate
   forwarded counter counts actual calls to the shared raw oracle. *)
module BudgetRawXOF = {
 var attempts : int
 var forwarded : int
 var limit : int
 var max_input : int
 proc configure(q:int,maxinput:int) = {
  attempts<-0; forwarded<-0; limit<-max 0 q; max_input<-max 0 maxinput;
 }
 proc get(input:W8.t list,outlen:int) : W8.t list option = {
  var result,allowed;
  result<-None;
  allowed<-attempts<limit /\ size input<=max_input /\ 0<=outlen<=raw_xof_max_output;
  attempts<-attempts+1;
  if(allowed){
   forwarded<-forwarded+1;
   result<@RawXOF.get(input,outlen);
  }
  return result;
 }
}.
lemma budget_raw_configure_ll : islossless BudgetRawXOF.configure.
proof. by proc; auto. qed.
lemma budget_raw_get_ll : islossless BudgetRawXOF.get.
proof. proc; sp; if; last by auto. call raw_xof_get_ll; auto. qed.
lemma budget_raw_attempts c0 : hoare[BudgetRawXOF.get :
 BudgetRawXOF.attempts=c0 ==> BudgetRawXOF.attempts=c0+1].
proof.
 proc; sp; if; last by auto.
 call (_:true ==>true); first by conseq raw_xof_get_ll.
 auto.
qed.
lemma budget_raw_rejected c0 f0 e0 fm0 g0 h0 s0 :
 hoare[BudgetRawXOF.get :
 BudgetRawXOF.attempts=c0 /\ BudgetRawXOF.forwarded=f0 /\
 !(c0<BudgetRawXOF.limit /\ size input<=BudgetRawXOF.max_input /\
   0<=outlen<=raw_xof_max_output) /\
 ROE.m=e0 /\ ROF.m=fm0 /\ ROG.m=g0 /\ ROH.m=h0 /\ glob RawXOFStreams=s0 ==>
 res=None /\ BudgetRawXOF.attempts=c0+1 /\ BudgetRawXOF.forwarded=f0 /\
 ROE.m=e0 /\ ROF.m=fm0 /\ ROG.m=g0 /\ ROH.m=h0 /\ glob RawXOFStreams=s0].
proof. proc; sp; rcondf 1; auto. qed.
lemma budget_raw_forwarded_bound : hoare[BudgetRawXOF.get :
 0<=BudgetRawXOF.forwarded<=BudgetRawXOF.attempts /\
 BudgetRawXOF.forwarded<=BudgetRawXOF.limit ==>
 0<=BudgetRawXOF.forwarded<=BudgetRawXOF.attempts /\
 BudgetRawXOF.forwarded<=BudgetRawXOF.limit].
proof.
 proc; sp; if; last by auto; smt().
 call (_:true ==>true); first by conseq raw_xof_get_ll.
 auto; smt().
qed.
