require import AllCore Distr.
from Jasmin require import JWord.
require import Array32 Array192 Array768 Array1152 Array2336 Array14466.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteAttempt.
require import NTRUPlus768KeygenCompleteRetry NTRUPlus768KeygenCompleteFinish NTRUPlus768KeygenCompleteProof.
require import NTRUPlus768KeygenClear NTRUPlus768KeygenClearProof.
require import NTRUPlus768EncapCompleteHash NTRUPlus768ROMOracles.

type retry_state = {
 rs_buf : W8.t Array192.t;
 rs_ntt : W16.t Array768.t;
 rs_inv : W16.t Array768.t;
 rs_ok : bool;
 rs_count : int;
}.
op [opaque] retry_initial : retry_state =
 {|rs_buf=witness;rs_ntt=witness;rs_inv=witness;rs_ok=false;rs_count=0|}.
type keygen_output = keygen_witness * W8.t Array14466.t.
type counted_output = keygen_output * int * int.
type stopped_output = keygen_output option * int * int.

op [opaque] stopped_success (r:stopped_output) = r.`1 <> None.
op [opaque] stopped_event (event:keygen_output -> bool) (r:stopped_output) =
 r.`1 <> None /\ event (oget r.`1).
op [opaque] counted_within (qf qg:int) (r:counted_output) =
 r.`2 <= max 0 qf /\ r.`3 <= max 0 qg.

module BoundedRetry(R:KeygenSeedRNG,E:KeygenExpand) = {
 proc f_from(start:retry_state,limit:int) : retry_state = {
  var seed:W8.t Array32.t; var buf:W8.t Array192.t;
  var ntt,inverse:W16.t Array768.t; var status:W64.t; var count:int;
  buf <- start.`rs_buf; ntt <- start.`rs_ntt; inverse <- start.`rs_inv;
  status <- if start.`rs_ok then W64.zero else W64.one; count <- start.`rs_count;
  while (status <> W64.zero /\ count < max 0 limit) {
   seed <@ R.sample();
   (buf,ntt,inverse,status) <@ KeygenAttempt(E).f(seed);
   count <- count+1;
  }
  return {|rs_buf=buf;rs_ntt=ntt;rs_inv=inverse;rs_ok=status=W64.zero;rs_count=count|};
 }
 proc f(limit:int) : retry_state = { var result; result <@ f_from(retry_initial,limit); return result; }
 proc g_from(start:retry_state,limit:int) : retry_state = {
  var seed:W8.t Array32.t; var buf:W8.t Array192.t;
  var ntt,inverse:W16.t Array768.t; var status:W64.t; var count:int;
  buf <- start.`rs_buf; ntt <- start.`rs_ntt; inverse <- start.`rs_inv;
  status <- if start.`rs_ok then W64.zero else W64.one; count <- start.`rs_count;
  while (status <> W64.zero /\ count < max 0 limit) {
   seed <@ R.sample();
   (buf,ntt,inverse,status) <@ KeygenAttempt(E).g(seed);
   count <- count+1;
  }
  return {|rs_buf=buf;rs_ntt=ntt;rs_inv=inverse;rs_ok=status=W64.zero;rs_count=count|};
 }
 proc g(limit:int) : retry_state = { var result; result <@ g_from(retry_initial,limit); return result; }
}.

module CountedRetry(R:KeygenSeedRNG,E:KeygenExpand) = {
 proc f_from(start:retry_state) : retry_state = {
  var seed:W8.t Array32.t; var buf:W8.t Array192.t;
  var ntt,inverse:W16.t Array768.t; var status:W64.t; var count:int;
  buf <- start.`rs_buf; ntt <- start.`rs_ntt; inverse <- start.`rs_inv;
  status <- if start.`rs_ok then W64.zero else W64.one; count <- start.`rs_count;
  while (status <> W64.zero) {
   seed <@ R.sample();
   (buf,ntt,inverse,status) <@ KeygenAttempt(E).f(seed);
   count <- count+1;
  }
  return {|rs_buf=buf;rs_ntt=ntt;rs_inv=inverse;rs_ok=status=W64.zero;rs_count=count|};
 }
 proc f() : retry_state = { var result; result <@ f_from(retry_initial); return result; }
 proc g_from(start:retry_state) : retry_state = {
  var seed:W8.t Array32.t; var buf:W8.t Array192.t;
  var ntt,inverse:W16.t Array768.t; var status:W64.t; var count:int;
  buf <- start.`rs_buf; ntt <- start.`rs_ntt; inverse <- start.`rs_inv;
  status <- if start.`rs_ok then W64.zero else W64.one; count <- start.`rs_count;
  while (status <> W64.zero) {
   seed <@ R.sample();
   (buf,ntt,inverse,status) <@ KeygenAttempt(E).g(seed);
   count <- count+1;
  }
  return {|rs_buf=buf;rs_ntt=ntt;rs_inv=inverse;rs_ok=status=W64.zero;rs_count=count|};
 }
 proc g() : retry_state = { var result; result <@ g_from(retry_initial); return result; }
}.

(* Finish and clear are the exact old calls. The seed/attempt loops above
   differ only by private counts and, for the analysis model, a finite guard. *)
module ObservedFinish = {
 proc run(fv:retry_state,gv:retry_state,workspace:W8.t Array14466.t) : keygen_output = {
  var pk:W8.t Array1152.t; var sk:W8.t Array2336.t;
  var h,hinv:W16.t Array768.t;
  (pk,sk,h,hinv) <@ KeygenFinish(SHAKEFROM).run(fv.`rs_ntt,fv.`rs_inv,gv.`rs_ntt,gv.`rs_inv);
  workspace <@ NTRUPlus768KeygenClear.M.jade_ntruplus_ntruplus768_amd64_ref_keygen_clear(workspace);
  return ({|kg_pk=pk;kg_sk=sk;kg_fbuf=fv.`rs_buf;kg_gbuf=gv.`rs_buf;
    kg_finv=fv.`rs_inv;kg_ginv=gv.`rs_inv;kg_h=h;kg_hinv=hinv|},workspace);
 }
}.
module StoppedKeygen(R:KeygenSeedRNG,E:KeygenExpand) = {
 proc run(qf:int,qg:int,workspace:W8.t Array14466.t) : stopped_output = {
  var fv,gv:retry_state; var result:keygen_output option; var out:keygen_output;
  result <- None; gv <- retry_initial;
  fv <@ BoundedRetry(R,E).f(qf);
  if (fv.`rs_ok) {
   gv <@ BoundedRetry(R,E).g(qg);
   if (gv.`rs_ok) {
    out <@ ObservedFinish.run(fv,gv,workspace); result <- Some out;
   }
  }
  return(result,fv.`rs_count,gv.`rs_count);
 }
}.
module CountedKeygen(R:KeygenSeedRNG,E:KeygenExpand) = {
 proc run(workspace:W8.t Array14466.t) : counted_output = {
  var fv,gv:retry_state; var out:keygen_output;
  fv <@ CountedRetry(R,E).f();
  gv <@ CountedRetry(R,E).g();
  out <@ ObservedFinish.run(fv,gv,workspace);
  return(out,fv.`rs_count,gv.`rs_count);
 }
}.

(* Splitting a real retry loop does not assume that its suffix terminates. *)
module SplitRetry(R:KeygenSeedRNG,E:KeygenExpand) = {
 proc f(limit:int) : retry_state = {
  var v:retry_state;
  v <@ BoundedRetry(R,E).f(limit);
  v <@ CountedRetry(R,E).f_from(v);
  return v;
 }
 proc g(limit:int) : retry_state = {
  var v:retry_state;
  v <@ BoundedRetry(R,E).g(limit);
  v <@ CountedRetry(R,E).g_from(v);
  return v;
 }
}.
module PrefixBad = { var bad:bool }.
module SplitKeygen(R:KeygenSeedRNG,E:KeygenExpand) = {
 proc run(qf:int,qg:int,workspace:W8.t Array14466.t) : counted_output = {
  var fv,gv:retry_state; var out:keygen_output;
  fv <@ SplitRetry(R,E).f(qf);
  gv <@ SplitRetry(R,E).g(qg);
  out <@ ObservedFinish.run(fv,gv,workspace);
  return(out,fv.`rs_count,gv.`rs_count);
 }
}.
module ResumedKeygen(R:KeygenSeedRNG,E:KeygenExpand) = {
 proc run(qf:int,qg:int,workspace:W8.t Array14466.t) : counted_output = {
  var fv,gv:retry_state; var out:keygen_output;
  PrefixBad.bad <- false;
  fv <@ BoundedRetry(R,E).f(qf);
  if (!fv.`rs_ok) { PrefixBad.bad <- true; fv <@ CountedRetry(R,E).f_from(fv); }
  gv <@ BoundedRetry(R,E).g(qg);
  if (!gv.`rs_ok) { PrefixBad.bad <- true; gv <@ CountedRetry(R,E).g_from(gv); }
  out <@ ObservedFinish.run(fv,gv,workspace);
  return(out,fv.`rs_count,gv.`rs_count);
 }
}.
module PrefixOnlyKeygen(R:KeygenSeedRNG,E:KeygenExpand) = {
 proc run(qf:int,qg:int,workspace:W8.t Array14466.t) : counted_output = {
  var fv,gv:retry_state; var out:keygen_output;
  PrefixBad.bad <- false;
  fv <@ BoundedRetry(R,E).f(qf);
  if (!fv.`rs_ok) { PrefixBad.bad <- true; }
  gv <@ BoundedRetry(R,E).g(qg);
  if (!gv.`rs_ok) { PrefixBad.bad <- true; }
  out <@ ObservedFinish.run(fv,gv,workspace);
  return(out,fv.`rs_count,gv.`rs_count);
 }
}.

lemma stopped_event_some (event:keygen_output -> bool) out nf ng :
 stopped_event event (Some out,nf,ng) = event out.
proof. by rewrite /stopped_event /=. qed.
lemma stopped_event_none (event:keygen_output -> bool) nf ng :
 stopped_event event (None,nf,ng) = false.
proof. by rewrite /stopped_event /=. qed.
