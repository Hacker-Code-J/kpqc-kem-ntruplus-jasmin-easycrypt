require import AllCore Distr.
from Jasmin require import JWord.
require import Array32 Array192.

module type ProposalPort = {
 proc draw() : W8.t Array32.t * W8.t Array192.t
}.

(* This shared adapter is used only in the actual sample/attempt pairing.
   The expansion call is the first effect of KeygenAttempt. *)
module PairPorts(P:ProposalPort) = {
 var pending : W8.t Array192.t
 proc sample() : W8.t Array32.t = {
  var v:W8.t Array32.t * W8.t Array192.t;
  v <@ P.draw(); pending <- v.`2; return v.`1;
 }
 proc shake(seed:W8.t Array32.t) : W8.t Array192.t = {
  return pending;
 }
}.

lemma pair_ports_sample_lossless (P<:ProposalPort) :
 islossless P.draw => islossless PairPorts(P).sample.
proof. move=> pl; proc; wp; call pl; auto. qed.

lemma pair_ports_shake_lossless (P<:ProposalPort) : islossless PairPorts(P).shake.
proof. proc; auto. qed.

lemma pair_ports_shake_value (P<:ProposalPort) :
 hoare[PairPorts(P).shake : true ==> res=PairPorts.pending].
proof. proc; auto. qed.
