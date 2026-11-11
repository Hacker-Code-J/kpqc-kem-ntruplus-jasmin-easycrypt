require import AllCore List Distr FMap.
from Jasmin require import JWord.
require import Array32 Array192.
require import NTRUPlus768FreshRetryLaw NTRUPlus768ROMOracles.
require import NTRUPlus768ROMDistributions NTRUPlus768CCASetupState.
require import NTRUPlus768CCAQueryCodec NTRUPlus768RawXOFSampling.

type erasure_seed = W8.t Array32.t.

(* Private analysis state. Every attempted seed is retained, including
   rejected proposals and duplicates. The adversary cannot read this state. *)
module ErasureSeedLog = {
 var used : erasure_seed list
 proc init() = { used <- []; }
}.
module ErasureHit = {
 var bad : bool
 proc init() = { bad <- false; }
 proc mark(seed:erasure_seed) = {
  bad <- bad \/ seed \in ErasureSeedLog.used;
 }
}.
module LoggedProgrammedExpand = {
 proc shake(seed:erasure_seed) : W8.t Array192.t = {
  var y:W8.t Array192.t;
  ErasureSeedLog.used <- seed::ErasureSeedLog.used;
  y <@ ProgrammedFreshExpand.shake(seed);
  return y;
 }
}.
module LoggedErasedExpand = {
 proc shake(seed:erasure_seed) : W8.t Array192.t = {
  var y:W8.t Array192.t;
  ErasureSeedLog.used <- seed::ErasureSeedLog.used;
  y <@ FreshExpand.shake(seed);
  return y;
 }
}.

module ErasureSeedPool = {
 var seeds : erasure_seed list
 var cursor : int
 proc init(xs:erasure_seed list) = { seeds <- xs; cursor <- 0; }
 proc sample() : erasure_seed = {
  var x:erasure_seed;
  x <- nth witness seeds cursor;
  cursor <- cursor+1;
  return x;
 }
}.

(* The cap is a separate analysis policy, not a property of the original
   game. Requests count all effective E requests; queries records only
   forwarded ones, in reverse order. Over-budget responses are specified
   by the separate port wrappers. *)
module EBudgetState = {
 var requests,forwarded,limit : int
 var overflow : bool
 var queries : erasure_seed list
 proc configure(q:int) = {
  requests <- 0; forwarded <- 0; limit <- max 0 q;
  overflow <- false; queries <- [];
 }
}.

(* The existing decoder classifies exactly 32-byte inputs as E; the
   separate codec lemmas connect this test to Some(E seed). *)
op erasure_raw_seed (input:W8.t list) (outlen:int) : erasure_seed option =
 if 0<=outlen<=raw_xof_max_output /\ size input=32 then
  Some(Array32.of_list W8.zero input)
 else None.

op erasure_tables_agree (s:erasure_seed list)
 (m1 m2:(erasure_seed,W8.t Array192.t) fmap) =
 forall x,!(List.mem s x) => m1.[x]=m2.[x].

lemma erasure_log_init_ll : islossless ErasureSeedLog.init.
proof. proc; auto. qed.
lemma erasure_hit_init_ll : islossless ErasureHit.init.
proof. proc; auto. qed.
lemma erasure_hit_mark_ll : islossless ErasureHit.mark.
proof. proc; auto. qed.
lemma erasure_pool_sample_ll : islossless ErasureSeedPool.sample.
proof. proc; auto. qed.
lemma erasure_budget_configure_ll : islossless EBudgetState.configure.
proof. proc; auto. qed.
lemma logged_programmed_expand_ll : islossless LoggedProgrammedExpand.shake.
proof. proc; call programmed_fresh_expand_ll; auto. qed.
lemma logged_erased_expand_ll : islossless LoggedErasedExpand.shake.
proof. proc; call fresh_expand_ll; auto. qed.
