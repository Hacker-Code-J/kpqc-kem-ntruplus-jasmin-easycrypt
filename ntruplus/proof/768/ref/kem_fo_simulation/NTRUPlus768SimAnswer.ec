require import AllCore Distr.
from Jasmin require import JWord.
require import Array32 Array224.
require import NTRUPlus768SimModel NTRUPlus768SimSampling.
require import NTRUPlus768FOGAdapters NTRUPlus768FOEagerG NTRUPlus768FOProcedures.
require import NTRUPlus768CCAStatusAdapter.

(* The private prefix supplies a request before this H response is read.
   This tail itself uses the public key and recovered data, not a secret key. *)
module SimAnswerReal(G:FOGPort,H:SimHPort) : SimAnswer = {
 proc answer(q:sim_request) : W8.t Array32.t option = {
  var hout:W8.t Array224.t;var result:W8.t Array32.t*W32.t;
  hout <@ H.get(sim_h_input q);
  result <@ FORegenerateFinish(FOGHash(G)).run(q.`sr_pk,q.`sr_ct,q.`sr_code,q.`sr_msg,hout,q.`sr_fail);
  return cca_status_result result.`1 result.`2;
 }
}.
(* Only a selected hybrid query uses this diagnostic wrapper. Its bad
   value is retained for the probability bound and erased only in the
   separate winning-event projection. *)
module SimAnswerRejectGet(G:FOGPort,H:SimHPort) : SimAnswer = {
 proc answer(q:sim_request) : W8.t Array32.t option = {
  var result:W8.t Array32.t option;
  result <@ SimAnswerReal(G,H).answer(q);
  SimBad.hidden<-SimBad.hidden \/ result<>None;
  SimBad.selected_calls<-SimBad.selected_calls+1;
  return None;
 }
}.
module SimAnswerSample(H:SimHRO.RO) : SimAnswer = {
 proc answer(q:sim_request) : W8.t Array32.t option = {
  H.sample(sim_h_input q);
  return None;
 }
}.
module SimAnswerNever : SimAnswer = {
 proc answer(q:sim_request) : W8.t Array32.t option = {return None;}
}.

lemma sim_answer_real_ll (G<:FOGPort)(H<:SimHPort) :
 islossless G.get=>islossless H.get=>islossless SimAnswerReal(G,H).answer.
proof.
 move=>hg hh;proc;call(fo_regenerate_finish_lossless (FOGHash(G)) _).
 + proc;call hg;auto.
 call hh;auto.
qed.
lemma sim_answer_reject_ll (G<:FOGPort)(H<:SimHPort) :
 islossless G.get=>islossless H.get=>islossless SimAnswerRejectGet(G,H).answer.
proof. move=>hg hh;proc;wp;call(sim_answer_real_ll G H hg hh);auto. qed.
lemma sim_answer_sample_ll (H<:SimHRO.RO) :
 islossless H.sample=>islossless SimAnswerSample(H).answer.
proof. move=>h;proc;call h;auto. qed.
lemma sim_answer_never_ll : islossless SimAnswerNever.answer.
proof. proc;auto. qed.
