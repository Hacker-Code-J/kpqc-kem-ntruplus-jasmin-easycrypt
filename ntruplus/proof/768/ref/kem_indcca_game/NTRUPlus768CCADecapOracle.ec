require import AllCore Distr FMap.
from Jasmin require import JWord.
require import Array32 Array1152 Array2336.
require import NTRUPlus768CCAStatusAdapter NTRUPlus768ROMOracles.
require import NTRUPlus768EncapGuardSpec NTRUPlus768DecapCompleteProof.

(* This is the complete adversary-facing capability.  Reset, key/challenge
   installation, and the implementation globals are excluded from it. *)
module type CCADecapPort = {
 proc decap(ct:W8.t Array1152.t) : cca_reply
}.

module CCADecapOracle = {
 var sk:W8.t Array2336.t
 var cstar:W8.t Array1152.t option
 var count:int

 proc reset() : unit = {
  sk <- witness; cstar <- None; count <- 0;
 }
 proc init(sk0:W8.t Array2336.t,cstar0:W8.t Array1152.t) : unit = {
  sk <- sk0; cstar <- Some cstar0; count <- 0;
 }
 proc decap(ct:W8.t Array1152.t) : cca_reply = {
  var answer:cca_reply;
  count <- count+1;
  if (cstar=Some ct) {
   answer <- None;
  } else {
   answer <@ CCAStatusAdapter.run(ct,sk);
  }
  return answer;
 }
}.

lemma cca_decap_reset_lossless : islossless CCADecapOracle.reset.
proof. proc; auto. qed.
lemma cca_decap_init_lossless : islossless CCADecapOracle.init.
proof. proc; auto. qed.
lemma cca_decap_reset_state : hoare[CCADecapOracle.reset : true ==>
 CCADecapOracle.sk=witness /\ CCADecapOracle.cstar=None /\ CCADecapOracle.count=0].
proof. proc; auto. qed.
lemma cca_decap_init_state sk0 c0 :
 hoare[CCADecapOracle.init : arg=(sk0,c0) ==>
 CCADecapOracle.sk=sk0 /\ CCADecapOracle.cstar=Some c0 /\ CCADecapOracle.count=0].
proof. proc; auto. qed.

lemma cca_decap_lossless : islossless CCADecapOracle.decap.
proof.
 proc; sp 1; if; first by auto.
 call cca_status_adapter_lossless; auto.
qed.
lemma cca_decap_count n0 :
 hoare[CCADecapOracle.decap : CCADecapOracle.count=n0 ==>
 CCADecapOracle.count=n0+1].
proof.
 proc; sp 1; if; first by auto.
 call (_:true ==> true); first by trivial.
 auto.
qed.
lemma cca_decap_private_state sk0 c0 :
 hoare[CCADecapOracle.decap : CCADecapOracle.sk=sk0 /\ CCADecapOracle.cstar=c0 ==>
 CCADecapOracle.sk=sk0 /\ CCADecapOracle.cstar=c0].
proof.
 proc; sp 1; if; first by auto.
 call (_:true ==> true); first by trivial.
 auto.
qed.

(* Equality compares all 1152 bytes before the only actual-Decaps call.
   The blocked request still increments the request counter. *)
lemma cca_decap_challenge_no_effects c0 sk0 n0 &m :
 phoare[CCADecapOracle.decap : ct=c0 /\ CCADecapOracle.cstar=Some c0 /\
 CCADecapOracle.sk=sk0 /\ CCADecapOracle.count=n0 /\
 (glob ROE)=(glob ROE){m} /\ (glob ROF)=(glob ROF){m} /\
 (glob ROG)=(glob ROG){m} /\ (glob ROH)=(glob ROH){m} ==>
 res=None /\ CCADecapOracle.cstar=Some c0 /\ CCADecapOracle.sk=sk0 /\
 CCADecapOracle.count=n0+1 /\
 (glob ROE)=(glob ROE){m} /\ (glob ROF)=(glob ROF){m} /\
 (glob ROG)=(glob ROG){m} /\ (glob ROH)=(glob ROH){m}]=1%r.
proof. proc; rcondt 2; auto. qed.

(* Every other fixed-length ciphertext, including invalid encodings, is
   passed to the original Decaps guard through the status adapter. *)
lemma cca_decap_forward_projection n0 :
 equiv[CCADecapOracle.decap ~ CCAStatusAdapter.run :
 ={ct,glob ROG,glob ROH} /\ CCADecapOracle.sk{1}=sk{2} /\
 CCADecapOracle.cstar{1}<>Some ct{1} /\ CCADecapOracle.count{1}=n0 ==>
 ={res,glob ROG,glob ROH} /\ CCADecapOracle.count{1}=n0+1].
proof.
 proc; rcondf{1} 2; first by auto.
 inline{1} CCAStatusAdapter.run; wp.
 call (_: ={ct,sk,workspace,glob ROG,glob ROH} ==> ={res,glob ROG,glob ROH}); first by sim.
 auto.
qed.

lemma cca_decap_actual_projection n0 :
 equiv[CCADecapOracle.decap ~ CompleteDecaps(SHAKEGROM,SHAKEHROM).run :
 ={ct,glob ROG,glob ROH} /\ CCADecapOracle.sk{1}=sk{2} /\
 workspace{2}=witness /\ CCADecapOracle.cstar{1}<>Some ct{1} /\
 CCADecapOracle.count{1}=n0 ==>
 res{1}=cca_status_result res.`1{2} res.`2{2} /\
 ={glob ROG,glob ROH} /\ CCADecapOracle.count{1}=n0+1].
proof.
 transitivity CCAStatusAdapter.run
  (={ct,glob ROG,glob ROH} /\ CCADecapOracle.sk{1}=sk{2} /\
   CCADecapOracle.cstar{1}<>Some ct{1} /\ CCADecapOracle.count{1}=n0 ==>
   ={res,glob ROG,glob ROH} /\ CCADecapOracle.count{1}=n0+1)
  (={ct,sk,glob ROG,glob ROH} /\ workspace{2}=witness ==>
   res{1}=cca_status_result res.`1{2} res.`2{2} /\ ={glob ROG,glob ROH}) => //.
 + smt().
 + exact(cca_decap_forward_projection n0).
 + exact cca_status_adapter_projection.
qed.

lemma cca_decap_noncanonical ct0 sk0 c0 n0 &m : !encap_key_canonical ct0 =>
 phoare[CCADecapOracle.decap : ct=ct0 /\ CCADecapOracle.sk=sk0 /\
 CCADecapOracle.cstar=c0 /\ CCADecapOracle.count=n0 /\
 ROG.m=ROG.m{m} /\ ROH.m=ROH.m{m} ==>
 res=None /\ CCADecapOracle.count=n0+1 /\
 CCADecapOracle.sk=sk0 /\ CCADecapOracle.cstar=c0 /\
 ROG.m=ROG.m{m} /\ ROH.m=ROH.m{m}]=1%r.
proof.
 move=> hc; proc; sp 1; if; first by auto.
 call(cca_status_adapter_noncanonical ct0 sk0 &m hc); auto.
qed.
