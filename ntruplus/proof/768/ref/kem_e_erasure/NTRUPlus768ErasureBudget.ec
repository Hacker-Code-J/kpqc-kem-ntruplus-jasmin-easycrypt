require import AllCore List Distr FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152.
require import NTRUPlus768ROMDomains NTRUPlus768ROMOracles.
require import NTRUPlus768CCAQueryCodec NTRUPlus768CCAOraclePorts.
require import NTRUPlus768RawXOFSampling NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
require import NTRUPlus768CCADecapOracle NTRUPlus768CCAGame.
require import NTRUPlus768ErasureModel.

(* Only effective adversarial E requests pass through this monitor.
   Setup's physical E calls use ExpandROM directly and are not counted here. *)
module ErasureBudgetMonitor = {
 proc request(seed:erasure_seed) : bool = {
  var allowed:bool;
  allowed <- EBudgetState.requests<EBudgetState.limit;
  EBudgetState.requests <- EBudgetState.requests+1;
  EBudgetState.overflow <- EBudgetState.overflow \/ !allowed;
  return allowed;
 }
 proc forward(seed:erasure_seed) : unit = {
  EBudgetState.forwarded <- EBudgetState.forwarded+1;
  EBudgetState.queries <- seed::EBudgetState.queries;
  ErasureHit.mark(seed);
 }
}.

(* This port is observational: it forwards every original request, including
   E requests exceeding the analysis limit. The overflow latch is private. *)
module CountEPort(H:CCAExtendedOraclePort) : CCAExtendedOraclePort = {
 proc e(input:erasure_seed) : W8.t Array192.t = {
  var allowed:bool; var result:W8.t Array192.t;
  allowed <@ ErasureBudgetMonitor.request(input);
  ErasureBudgetMonitor.forward(input);
  result <@ H.e(input);
  return result;
 }
 proc f=H.f
 proc g=H.g
 proc h=H.h
 proc raw(input:W8.t list,outlen:int) : W8.t list option = {
  var seed:erasure_seed option; var allowed:bool; var result:W8.t list option;
  seed <- erasure_raw_seed input outlen;
  if(seed<>None){
   allowed <@ ErasureBudgetMonitor.request(oget seed);
   ErasureBudgetMonitor.forward(oget seed);
  }
  result <@ H.raw(input,outlen);
  return result;
 }
}.

(* This is an explicit restricted game policy. Over-budget typed E returns
   witness, over-budget raw E returns None, and no backend cache is touched.
   Every non-E request keeps the original backend behavior. *)
module CapEPort(H:CCAExtendedOraclePort) : CCAExtendedOraclePort = {
 proc e(input:erasure_seed) : W8.t Array192.t = {
  var allowed:bool; var result:W8.t Array192.t;
  allowed <@ ErasureBudgetMonitor.request(input);
  result <- witness;
  if(allowed){
   ErasureBudgetMonitor.forward(input);
   result <@ H.e(input);
  }
  return result;
 }
 proc f=H.f
 proc g=H.g
 proc h=H.h
 proc raw(input:W8.t list,outlen:int) : W8.t list option = {
  var seed:erasure_seed option; var allowed:bool; var result:W8.t list option;
  seed <- erasure_raw_seed input outlen;
  allowed <- true;
  if(seed<>None){allowed <@ ErasureBudgetMonitor.request(oget seed);}
  result <- None;
  if(allowed){
   if(seed<>None){ErasureBudgetMonitor.forward(oget seed);}
   result <@ H.raw(input,outlen);
  }
  return result;
 }
}.

module CountedA(A:CCAExtendedAdversary,H:CCAExtendedOraclePort,D:CCADecapPort) = {
 proc guess=A(CountEPort(H),D).guess
}.
module CappedA(A:CCAExtendedAdversary,H:CCAExtendedOraclePort,D:CCADecapPort) = {
 proc guess=A(CapEPort(H),D).guess
}.

lemma erasure_request_ll : islossless ErasureBudgetMonitor.request.
proof. proc; auto. qed.
lemma erasure_forward_ll : islossless ErasureBudgetMonitor.forward.
proof. proc; call erasure_hit_mark_ll; auto. qed.

lemma erasure_raw_seed_e seed outlen : 0<=outlen<=raw_xof_max_output =>
 erasure_raw_seed(raw_query(E seed))outlen=Some seed.
proof.
 move=>hn; rewrite /erasure_raw_seed; smt(Array32.size_to_list Array32.to_listK).
qed.
lemma erasure_raw_seed_some input outlen seed :
 erasure_raw_seed input outlen=Some seed <=>
 0<=outlen<=raw_xof_max_output /\ input=raw_query(E seed).
proof.
 split.
 + rewrite /erasure_raw_seed.
   case(0<=outlen<=raw_xof_max_output /\ size input=32)=>hc /=; last smt().
   move=>he; have hs:Array32.of_list W8.zero input=seed by smt().
   split; first smt().
   rewrite -hs; apply/eq_sym; apply Array32.of_listK; smt().
 move=>[hn ->]; exact(erasure_raw_seed_e seed outlen hn).
qed.
lemma erasure_raw_seed_invalid input outlen :
 !(0<=outlen<=raw_xof_max_output) => erasure_raw_seed input outlen=None.
proof. move=>hn; by rewrite /erasure_raw_seed hn. qed.
lemma erasure_raw_seed_zero seed : erasure_raw_seed(raw_query(E seed))0=Some seed.
proof. apply erasure_raw_seed_e; rewrite /raw_xof_max_output; smt(). qed.

lemma count_e_ll (H<:CCAExtendedOraclePort) :
 islossless H.e => islossless CountEPort(H).e.
proof. move=>hl; proc; call hl; call erasure_forward_ll; call erasure_request_ll; auto. qed.
lemma count_raw_ll (H<:CCAExtendedOraclePort) :
 islossless H.raw => islossless CountEPort(H).raw.
proof.
 move=>hl; proc; call hl; sp; if; last by auto.
 call erasure_forward_ll; call erasure_request_ll; auto.
qed.
lemma cap_e_ll (H<:CCAExtendedOraclePort) :
 islossless H.e => islossless CapEPort(H).e.
proof.
 move=>hl; proc; seq 2:true; 1,4,5:by auto.
 + wp; call erasure_request_ll; auto.
 if; last by auto.
 call hl; call erasure_forward_ll; auto.
qed.
lemma cap_raw_ll (H<:CCAExtendedOraclePort) :
 islossless H.raw => islossless CapEPort(H).raw.
proof.
 move=>hl; proc; seq 4:true; 1,4,5:by auto.
 + wp; sp; if; last by auto. call erasure_request_ll; auto.
 if; last by auto.
 call hl; if; last by auto.
 call erasure_forward_ll; auto.
qed.

lemma erasure_request_state n0 q0 over0 :
 hoare[ErasureBudgetMonitor.request:
 EBudgetState.requests=n0 /\ EBudgetState.limit=q0 /\ EBudgetState.overflow=over0 ==>
 res=(n0<q0) /\ EBudgetState.requests=n0+1 /\ EBudgetState.limit=q0 /\
 EBudgetState.overflow=(over0 \/ !(n0<q0))].
proof. proc; auto. qed.
lemma erasure_forward_state n0 xs bad0 used0 seed0 :
 hoare[ErasureBudgetMonitor.forward:
 EBudgetState.forwarded=n0 /\ EBudgetState.queries=xs /\ ErasureHit.bad=bad0 /\
 ErasureSeedLog.used=used0 /\ seed=seed0 ==>
 EBudgetState.forwarded=n0+1 /\ EBudgetState.queries=seed0::xs /\
 ErasureHit.bad=(bad0 \/ seed0 \in used0) /\ ErasureSeedLog.used=used0].
proof. proc; inline ErasureHit.mark; auto. qed.

lemma count_e_requests (H<:CCAExtendedOraclePort {-EBudgetState,-ErasureHit,-ErasureSeedLog}) n0 :
 hoare[CountEPort(H).e:EBudgetState.requests=n0 ==> EBudgetState.requests=n0+1].
proof. proc; call(_:true ==>true); first by trivial.
 inline ErasureBudgetMonitor.forward ErasureHit.mark ErasureBudgetMonitor.request; auto.
qed.
lemma count_raw_requests (H<:CCAExtendedOraclePort {-EBudgetState,-ErasureHit,-ErasureSeedLog}) n0 x0 len0 :
 hoare[CountEPort(H).raw:
 EBudgetState.requests=n0 /\ input=x0 /\ outlen=len0 ==>
 EBudgetState.requests=n0+b2i(erasure_raw_seed x0 len0<>None)].
proof.
 proc; call(_:true ==>true); first by trivial.
 inline ErasureBudgetMonitor.forward ErasureHit.mark ErasureBudgetMonitor.request.
 auto=> />; smt().
qed.
lemma cap_e_requests (H<:CCAExtendedOraclePort {-EBudgetState,-ErasureHit,-ErasureSeedLog}) n0 :
 hoare[CapEPort(H).e:EBudgetState.requests=n0 ==> EBudgetState.requests=n0+1].
proof.
 proc; inline ErasureBudgetMonitor.request; sp.
 if; last by auto.
 call(_:true ==>true); first by trivial.
 inline ErasureBudgetMonitor.forward ErasureHit.mark; auto.
qed.
lemma cap_raw_requests (H<:CCAExtendedOraclePort {-EBudgetState,-ErasureHit,-ErasureSeedLog}) n0 x0 len0 :
 hoare[CapEPort(H).raw:
 EBudgetState.requests=n0 /\ input=x0 /\ outlen=len0 ==>
 EBudgetState.requests=n0+b2i(erasure_raw_seed x0 len0<>None)].
proof.
 proc; inline ErasureBudgetMonitor.request.
 seq 4:(EBudgetState.requests=n0+b2i(erasure_raw_seed x0 len0<>None)); first by auto=> />; smt().
 if; last by auto.
 call(_:true ==>true); first by trivial.
 if; last by auto.
 inline ErasureBudgetMonitor.forward ErasureHit.mark; auto.
qed.

op erasure_cap_invariant (n f q:int) (xs:erasure_seed list) =
 0<=f<=n /\ f<=q /\ 0<=q /\ size xs=f.

lemma erasure_configure_invariant q0 : hoare[EBudgetState.configure:q=q0 ==>
 erasure_cap_invariant EBudgetState.requests EBudgetState.forwarded EBudgetState.limit EBudgetState.queries /\
 EBudgetState.limit=max 0 q0 /\ !EBudgetState.overflow].
proof. proc; auto; rewrite /erasure_cap_invariant; smt(). qed.

lemma cap_e_invariant (H<:CCAExtendedOraclePort {-EBudgetState,-ErasureHit,-ErasureSeedLog}) :
 hoare[CapEPort(H).e:
 erasure_cap_invariant EBudgetState.requests EBudgetState.forwarded EBudgetState.limit EBudgetState.queries ==>
 erasure_cap_invariant EBudgetState.requests EBudgetState.forwarded EBudgetState.limit EBudgetState.queries].
proof.
 proc; inline ErasureBudgetMonitor.request; sp; if.
 + call(_:true ==>true); first by trivial.
   inline ErasureBudgetMonitor.forward ErasureHit.mark; auto.
   rewrite /erasure_cap_invariant /=; smt().
 auto; rewrite /erasure_cap_invariant; smt().
qed.
lemma cap_raw_invariant (H<:CCAExtendedOraclePort {-EBudgetState,-ErasureHit,-ErasureSeedLog}) :
 hoare[CapEPort(H).raw:
 erasure_cap_invariant EBudgetState.requests EBudgetState.forwarded EBudgetState.limit EBudgetState.queries ==>
 erasure_cap_invariant EBudgetState.requests EBudgetState.forwarded EBudgetState.limit EBudgetState.queries].
proof.
 proc; inline ErasureBudgetMonitor.request.
 seq 4:(erasure_cap_invariant EBudgetState.requests EBudgetState.forwarded EBudgetState.limit EBudgetState.queries /\
  (seed<>None /\ allowed => EBudgetState.forwarded<EBudgetState.limit /\
   EBudgetState.forwarded<EBudgetState.requests)).
 + auto; rewrite /erasure_cap_invariant; smt().
 if; last by auto.
 call(_:true ==>true); first by trivial.
 if; last by auto.
 inline ErasureBudgetMonitor.forward ErasureHit.mark; auto.
 rewrite /erasure_cap_invariant /=; smt().
qed.

lemma count_e_backend (H<:CCAExtendedOraclePort {-EBudgetState,-ErasureHit,-ErasureSeedLog}) :
 equiv[CountEPort(H).e ~ H.e: ={input,glob H} ==> ={res,glob H}].
proof.
 proc*; inline{1} CountEPort(H).e.
 wp; call(_: ={arg,glob H} ==> ={res,glob H}); first by proc true; auto.
 inline ErasureBudgetMonitor.request ErasureBudgetMonitor.forward ErasureHit.mark; auto.
qed.
lemma count_raw_backend (H<:CCAExtendedOraclePort {-EBudgetState,-ErasureHit,-ErasureSeedLog}) :
 equiv[CountEPort(H).raw ~ H.raw: ={input,outlen,glob H} ==> ={res,glob H}].
proof.
 proc*; inline{1} CountEPort(H).raw.
 wp; call(_: ={arg,glob H} ==> ={res,glob H}); first by proc true; auto.
 inline ErasureBudgetMonitor.request ErasureBudgetMonitor.forward ErasureHit.mark.
 auto.
qed.

lemma cap_e_backend (H<:CCAExtendedOraclePort {-EBudgetState,-ErasureHit,-ErasureSeedLog}) :
 equiv[CapEPort(H).e ~ H.e:
 ={input,glob H} /\ EBudgetState.requests{1}<EBudgetState.limit{1} ==> ={res,glob H}].
proof.
 proc*; inline{1} CapEPort(H).e ErasureBudgetMonitor.request; sp.
 rcondt{1} 1; first by auto.
 wp; call(_: ={arg,glob H} ==> ={res,glob H}); first by proc true; auto.
 inline ErasureBudgetMonitor.forward ErasureHit.mark; auto.
qed.
lemma cap_raw_backend (H<:CCAExtendedOraclePort {-EBudgetState,-ErasureHit,-ErasureSeedLog}) :
 equiv[CapEPort(H).raw ~ H.raw:
 ={input,outlen,glob H} /\
 (erasure_raw_seed input{1} outlen{1}=None \/ EBudgetState.requests{1}<EBudgetState.limit{1}) ==>
 ={res,glob H}].
proof.
 proc*; inline{1} CapEPort(H).raw ErasureBudgetMonitor.request; sp.
 rcondt{1} 1; first by auto; smt().
 wp; call(_: ={arg,glob H} ==> ={res,glob H}); first by proc true; auto.
 inline ErasureBudgetMonitor.forward ErasureHit.mark; auto=> />; smt().
qed.

(* The concrete shared backend satisfies the ghost-state restrictions. *)
lemma count_shared_e_backend :
 equiv[CountEPort(SharedCCAExtendedOracles).e ~ SharedCCAExtendedOracles.e:
 ={input,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams} ==>
 ={res,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams}].
proof. conseq(count_e_backend SharedCCAExtendedOracles); smt(). qed.
lemma count_shared_raw_backend :
 equiv[CountEPort(SharedCCAExtendedOracles).raw ~ SharedCCAExtendedOracles.raw:
 ={input,outlen,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams} ==>
 ={res,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams}].
proof. conseq(count_raw_backend SharedCCAExtendedOracles); smt(). qed.
lemma cap_shared_e_ll : islossless CapEPort(SharedCCAExtendedOracles).e.
proof. exact(cap_e_ll SharedCCAExtendedOracles cca_extended_e_ll). qed.
lemma cap_shared_raw_ll : islossless CapEPort(SharedCCAExtendedOracles).raw.
proof. exact(cap_raw_ll SharedCCAExtendedOracles cca_extended_raw_ll). qed.

lemma cap_adversary_invariant
 (A<:CCAExtendedAdversary {-EBudgetState,-ErasureHit,-ErasureSeedLog,-ErasureSeedPool})
 (H<:CCAExtendedOraclePort {-A,-EBudgetState,-ErasureHit,-ErasureSeedLog})
 (D<:CCADecapPort {-A,-EBudgetState,-ErasureHit,-ErasureSeedLog}) :
 hoare[CappedA(A,H,D).guess:
 erasure_cap_invariant EBudgetState.requests EBudgetState.forwarded EBudgetState.limit EBudgetState.queries ==>
 erasure_cap_invariant EBudgetState.requests EBudgetState.forwarded EBudgetState.limit EBudgetState.queries].
proof.
 proc(erasure_cap_invariant EBudgetState.requests EBudgetState.forwarded EBudgetState.limit EBudgetState.queries); 1,2:by auto.
 + exact(cap_e_invariant H).
 + proc*; call(_:true ==>true); first by trivial. auto.
 + proc*; call(_:true ==>true); first by trivial. auto.
 + proc*; call(_:true ==>true); first by trivial. auto.
 + exact(cap_raw_invariant H).
 proc*; call(_:true ==>true); first by trivial. auto.
qed.

lemma cap_adversary_limit
 (A<:CCAExtendedAdversary {-EBudgetState,-ErasureHit,-ErasureSeedLog,-ErasureSeedPool})
 (H<:CCAExtendedOraclePort {-A,-EBudgetState,-ErasureHit,-ErasureSeedLog})
 (D<:CCADecapPort {-A,-EBudgetState,-ErasureHit,-ErasureSeedLog}) q0 :
 hoare[CappedA(A,H,D).guess:EBudgetState.limit=q0 ==> EBudgetState.limit=q0].
proof.
 proc*; call(_:true ==>true); first by trivial.
 auto.
qed.

op erasure_trace_hit (used queries:erasure_seed list) = List.has (List.mem used) queries.

lemma erasure_forward_hit :
 hoare[ErasureBudgetMonitor.forward:
 ErasureHit.bad=erasure_trace_hit ErasureSeedLog.used EBudgetState.queries ==>
 ErasureHit.bad=erasure_trace_hit ErasureSeedLog.used EBudgetState.queries].
proof.
 proc; inline ErasureHit.mark; auto; rewrite /erasure_trace_hit /=; smt().
qed.
lemma cap_e_hit_invariant (H<:CCAExtendedOraclePort {-EBudgetState,-ErasureHit,-ErasureSeedLog}) :
 hoare[CapEPort(H).e:
 ErasureHit.bad=erasure_trace_hit ErasureSeedLog.used EBudgetState.queries ==>
 ErasureHit.bad=erasure_trace_hit ErasureSeedLog.used EBudgetState.queries].
proof.
 proc; inline ErasureBudgetMonitor.request; sp; if; last by auto.
 call(_:true ==>true); first by trivial.
 call erasure_forward_hit; auto.
qed.
lemma cap_raw_hit_invariant (H<:CCAExtendedOraclePort {-EBudgetState,-ErasureHit,-ErasureSeedLog}) :
 hoare[CapEPort(H).raw:
 ErasureHit.bad=erasure_trace_hit ErasureSeedLog.used EBudgetState.queries ==>
 ErasureHit.bad=erasure_trace_hit ErasureSeedLog.used EBudgetState.queries].
proof.
 proc; seq 4:(ErasureHit.bad=erasure_trace_hit ErasureSeedLog.used EBudgetState.queries).
 + inline ErasureBudgetMonitor.request; auto.
 if; last by auto.
 call(_:true ==>true); first by trivial.
 if; last by auto.
 call erasure_forward_hit; auto.
qed.

(* Hidden setup seeds and the hit latch cannot affect the response, control
   flow, request budget, forwarded query log, or backend state. *)
lemma cap_e_ghost_independent
 (H<:CCAExtendedOraclePort {-EBudgetState,-ErasureHit,-ErasureSeedLog}) :
 equiv[CapEPort(H).e ~ CapEPort(H).e:
 ={input,glob EBudgetState,glob H} ==> ={res,glob EBudgetState,glob H}].
proof.
 proc; inline ErasureBudgetMonitor.request ErasureBudgetMonitor.forward ErasureHit.mark.
 sim (: ={glob EBudgetState,glob H}).
qed.
lemma cap_raw_ghost_independent
 (H<:CCAExtendedOraclePort {-EBudgetState,-ErasureHit,-ErasureSeedLog}) :
 equiv[CapEPort(H).raw ~ CapEPort(H).raw:
 ={input,outlen,glob EBudgetState,glob H} ==> ={res,glob EBudgetState,glob H}].
proof.
 proc; inline ErasureBudgetMonitor.request ErasureBudgetMonitor.forward ErasureHit.mark.
 sim (: ={glob EBudgetState,glob H}).
qed.

lemma cap_adversary_hit_invariant
 (A<:CCAExtendedAdversary {-EBudgetState,-ErasureHit,-ErasureSeedLog,-ErasureSeedPool})
 (H<:CCAExtendedOraclePort {-A,-EBudgetState,-ErasureHit,-ErasureSeedLog})
 (D<:CCADecapPort {-A,-EBudgetState,-ErasureHit,-ErasureSeedLog}) :
 hoare[CappedA(A,H,D).guess:
 ErasureHit.bad=erasure_trace_hit ErasureSeedLog.used EBudgetState.queries ==>
 ErasureHit.bad=erasure_trace_hit ErasureSeedLog.used EBudgetState.queries].
proof.
 proc(ErasureHit.bad=erasure_trace_hit ErasureSeedLog.used EBudgetState.queries); 1,2:by auto.
 + exact(cap_e_hit_invariant H).
 + proc*; call(_:true ==>true); first by trivial. auto.
 + proc*; call(_:true ==>true); first by trivial. auto.
 + proc*; call(_:true ==>true); first by trivial. auto.
 + exact(cap_raw_hit_invariant H).
 proc*; call(_:true ==>true); first by trivial. auto.
qed.

(* There is no freshness premise: zero-length and repeated raw E requests
   each consume one request position, just like the typed interface. *)
lemma cap_raw_e_requests
 (H<:CCAExtendedOraclePort {-EBudgetState,-ErasureHit,-ErasureSeedLog}) n0 seed0 len0 :
 0<=len0<=raw_xof_max_output =>
 hoare[CapEPort(H).raw:
 EBudgetState.requests=n0 /\ input=raw_query(E seed0) /\ outlen=len0 ==>
 EBudgetState.requests=n0+1].
proof.
 move=>hn; conseq(cap_raw_requests H n0 (raw_query(E seed0)) len0)=> />.
 move=> &hr _ ->; by rewrite(erasure_raw_seed_e seed0 len0 hn).
qed.
lemma count_raw_e_requests
 (H<:CCAExtendedOraclePort {-EBudgetState,-ErasureHit,-ErasureSeedLog}) n0 seed0 len0 :
 0<=len0<=raw_xof_max_output =>
 hoare[CountEPort(H).raw:
 EBudgetState.requests=n0 /\ input=raw_query(E seed0) /\ outlen=len0 ==>
 EBudgetState.requests=n0+1].
proof.
 move=>hn; conseq(count_raw_requests H n0 (raw_query(E seed0)) len0)=> />.
 move=> &hr _ ->; by rewrite(erasure_raw_seed_e seed0 len0 hn).
qed.

lemma cap_raw_non_e_frame
 (H<:CCAExtendedOraclePort {-EBudgetState,-ErasureHit,-ErasureSeedLog}) x0 len0 budget0 bad0 used0 :
 erasure_raw_seed x0 len0=None =>
 hoare[CapEPort(H).raw:
 input=x0 /\ outlen=len0 /\ glob EBudgetState=budget0 /\ ErasureHit.bad=bad0 /\ ErasureSeedLog.used=used0 ==>
 glob EBudgetState=budget0 /\ ErasureHit.bad=bad0 /\ ErasureSeedLog.used=used0].
proof.
 move=>hn; proc; rcondf 3; first by auto.
 rcondt 4; first by auto.
 rcondf 4; first by auto.
 call(_:true ==>true); first by trivial.
 auto.
qed.
lemma count_raw_non_e_frame
 (H<:CCAExtendedOraclePort {-EBudgetState,-ErasureHit,-ErasureSeedLog}) x0 len0 budget0 bad0 used0 :
 erasure_raw_seed x0 len0=None =>
 hoare[CountEPort(H).raw:
 input=x0 /\ outlen=len0 /\ glob EBudgetState=budget0 /\ ErasureHit.bad=bad0 /\ ErasureSeedLog.used=used0 ==>
 glob EBudgetState=budget0 /\ ErasureHit.bad=bad0 /\ ErasureSeedLog.used=used0].
proof.
 move=>hn; proc; rcondf 2; first by auto.
 call(_:true ==>true); first by trivial.
 auto.
qed.

lemma cap_adversary_queries_bound
 (A<:CCAExtendedAdversary {-EBudgetState,-ErasureHit,-ErasureSeedLog,-ErasureSeedPool})
 (H<:CCAExtendedOraclePort {-A,-EBudgetState,-ErasureHit,-ErasureSeedLog})
 (D<:CCADecapPort {-A,-EBudgetState,-ErasureHit,-ErasureSeedLog}) q0 :
 hoare[CappedA(A,H,D).guess:
 erasure_cap_invariant EBudgetState.requests EBudgetState.forwarded EBudgetState.limit EBudgetState.queries /\
 EBudgetState.limit=q0 ==> size EBudgetState.queries<=q0].
proof.
 proc*; call(cap_adversary_invariant A H D).
 auto; rewrite /erasure_cap_invariant; smt().
qed.
