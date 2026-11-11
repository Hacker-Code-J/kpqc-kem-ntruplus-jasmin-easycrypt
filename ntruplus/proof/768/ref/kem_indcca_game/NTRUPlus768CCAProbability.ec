require import AllCore Distr DBool StdOrder.
import RealOrder RField.

module type CCABoolBody = {
 proc run() : bool
}.
module type PartialCCABody = {
 proc run(qf:int,qg:int) : bool option
}.

(* None is a returned setup-abort result. A diverging body is still
   nonreturning: the completion does not assign an outcome to divergence. *)
op cca_complete_value (outcome:bool option) (fallback:bool) =
 if outcome=None then fallback else oget outcome.

module CompleteFallback(B:PartialCCABody) = {
 proc sample(qf:int,qg:int) : bool option * bool = {
  var outcome:bool option; var fallback:bool;
  outcome <@ B.run(qf,qg);
  fallback <$ dbool;
  return(outcome,fallback);
 }
 proc run(qf:int,qg:int) : bool = {
  var pair:bool option * bool;
  pair <@ sample(qf,qg);
  return cca_complete_value pair.`1 pair.`2;
 }
}.

lemma cca_complete_valueE outcome fallback :
 cca_complete_value outcome fallback =
 (outcome=Some true \/ (outcome=None /\ fallback)).
proof. case:outcome=>[|b]; rewrite /cca_complete_value /=; smt(). qed.

lemma cca_partial_win_return (B<:CCABoolBody) &m :
 Pr[B.run() @ &m:res]+Pr[B.run() @ &m:!res]=Pr[B.run() @ &m:true].
proof. rewrite Pr[mu_not]; ring. qed.

lemma cca_partial_signed_identity (B<:CCABoolBody) &m :
 Pr[B.run() @ &m:res]-1%r/2%r =
  (Pr[B.run() @ &m:res]-Pr[B.run() @ &m:!res])/2%r -
  (1%r-Pr[B.run() @ &m:true])/2%r.
proof. have h:=cca_partial_win_return B &m; smt(). qed.

lemma cca_partial_event_spec (B<:PartialCCABody) &m qf0 qg0
 (p:bool option -> bool) :
 phoare[B.run : qf=qf0 /\ qg=qg0 /\ (glob B)=(glob B){m} ==> p res] =
 (Pr[B.run(qf0,qg0) @ &m:p res]).
proof.
 bypr=> &n [-> [-> hg]].
 byequiv (_: ={qf,qg,glob B} ==> ={res}) => //.
 by sim.
qed.

lemma cca_fallback_sample_projection (B<:PartialCCABody) &m qf0 qg0
 (p:bool option -> bool) :
 Pr[CompleteFallback(B).sample(qf0,qg0) @ &m:p res.`1]=
 Pr[B.run(qf0,qg0) @ &m:p res].
proof.
 byequiv (_: ={qf,qg,glob B} ==> res.`1{1}=res{2}) => //.
 proc*; inline{1} CompleteFallback(B).sample; wp; rnd{1}.
 call (_: ={qf,qg,glob B} ==> ={res,glob B}); first by sim.
 auto.
qed.

lemma cca_fallback_sample_bit (B<:PartialCCABody) &m qf0 qg0
 (p:bool option -> bool) b :
 Pr[CompleteFallback(B).sample(qf0,qg0) @ &m:p res.`1 /\ res.`2=b]=
 Pr[B.run(qf0,qg0) @ &m:p res]/2%r.
proof.
 byphoare (_:qf=qf0 /\ qg=qg0 /\ (glob B)=(glob B){m} ==>
   p res.`1 /\ res.`2=b) => //.
 proc; seq 1 : (p outcome) (Pr[B.run(qf0,qg0) @ &m:p res]) (1%r/2%r)
   (Pr[B.run(qf0,qg0) @ &m:!p res]) 0%r true => //.
 + call (cca_partial_event_spec B &m qf0 qg0 p); auto.
 + rnd; auto=> />; by rewrite dbool1E.
 + hoare; rnd; auto; smt().
qed.

lemma cca_fallback_run_sample (B<:PartialCCABody) :
 equiv[CompleteFallback(B).run ~ CompleteFallback(B).sample :
  ={qf,qg,glob B} ==>
  res{1}=cca_complete_value res.`1{2} res.`2{2} /\ ={glob B}].
proof.
 proc*; inline{1} CompleteFallback(B).run; wp.
 call (_: ={qf,qg,glob B} ==> ={res,glob B}); first by sim.
 auto.
qed.

lemma cca_fallback_win (B<:PartialCCABody) &m qf0 qg0 :
 Pr[CompleteFallback(B).run(qf0,qg0) @ &m:res]=
 Pr[B.run(qf0,qg0) @ &m:res=Some true]+
 Pr[B.run(qf0,qg0) @ &m:res=None]/2%r.
proof.
 have he:Pr[CompleteFallback(B).run(qf0,qg0) @ &m:res]=
   Pr[CompleteFallback(B).sample(qf0,qg0) @ &m:
    res.`1=Some true \/ (res.`1=None /\ res.`2=true)].
 + byequiv (cca_fallback_run_sample B) => //.
   move=> &1 &2 [-> _]; rewrite cca_complete_valueE; smt().
 rewrite he Pr[mu_or].
 have hz:Pr[CompleteFallback(B).sample(qf0,qg0) @ &m:
   res.`1=Some true /\ (res.`1=None /\ res.`2=true)]=0%r.
 + have he0:Pr[CompleteFallback(B).sample(qf0,qg0) @ &m:
     res.`1=Some true /\ (res.`1=None /\ res.`2=true)]=
     Pr[CompleteFallback(B).sample(qf0,qg0) @ &m:false]
     by rewrite Pr[mu_eq]; smt().
   by rewrite he0 Pr[mu_false].
 by rewrite hz (cca_fallback_sample_projection B &m qf0 qg0 (fun x=>x=Some true))
  (cca_fallback_sample_bit B &m qf0 qg0 (fun x=>x=None) true) /=.
qed.

lemma cca_fallback_exhaustion_win (B<:PartialCCABody) &m qf0 qg0 :
 Pr[CompleteFallback(B).sample(qf0,qg0) @ &m:res.`1=None /\ res.`2=true]=
 Pr[B.run(qf0,qg0) @ &m:res=None]/2%r.
proof. exact(cca_fallback_sample_bit B &m qf0 qg0 (fun x=>x=None) true). qed.

lemma cca_fallback_return (B<:PartialCCABody) &m qf0 qg0 :
 Pr[CompleteFallback(B).run(qf0,qg0) @ &m:true]=
 Pr[B.run(qf0,qg0) @ &m:true].
proof.
 have he:Pr[CompleteFallback(B).run(qf0,qg0) @ &m:true]=
   Pr[CompleteFallback(B).sample(qf0,qg0) @ &m:true].
 + by byequiv (cca_fallback_run_sample B).
 rewrite he; exact(cca_fallback_sample_projection B &m qf0 qg0 predT).
qed.

lemma cca_fallback_lossless (B<:PartialCCABody) :
 islossless B.run => islossless CompleteFallback(B).run.
proof.
 move=>hB; proc; inline CompleteFallback(B).sample.
 wp; rnd; call hB; auto=> />; exact dbool_ll.
qed.

lemma cca_option_partition (B<:PartialCCABody) &m qf0 qg0 :
 Pr[B.run(qf0,qg0) @ &m:res=Some true]+
 Pr[B.run(qf0,qg0) @ &m:res=Some false]+
 Pr[B.run(qf0,qg0) @ &m:res=None]=Pr[B.run(qf0,qg0) @ &m:true].
proof.
 have he:Pr[B.run(qf0,qg0) @ &m:res<>None]=
   Pr[B.run(qf0,qg0) @ &m:res=Some true \/ res=Some false].
 + rewrite Pr[mu_eq]; smt().
 move:he; rewrite Pr[mu_not] Pr[mu_or]=>he.
 have hz:Pr[B.run(qf0,qg0) @ &m:res=Some true /\ res=Some false]=0%r.
 + have he0:Pr[B.run(qf0,qg0) @ &m:res=Some true /\ res=Some false]=
     Pr[B.run(qf0,qg0) @ &m:false] by rewrite Pr[mu_eq]; smt().
   by rewrite he0 Pr[mu_false].
 smt().
qed.

lemma cca_fallback_always_none (B<:PartialCCABody) &m qf0 qg0 :
 Pr[B.run(qf0,qg0) @ &m:res=None]=1%r =>
 Pr[CompleteFallback(B).run(qf0,qg0) @ &m:res]=1%r/2%r.
proof.
 move=>hn; have hp:=cca_option_partition B &m qf0 qg0.
 have hr:Pr[B.run(qf0,qg0) @ &m:true]<=1%r by smt(mu_bounded).
 have hl:0%r<=Pr[B.run(qf0,qg0) @ &m:res=Some false] by smt(mu_bounded).
 have ht:0%r<=Pr[B.run(qf0,qg0) @ &m:res=Some true] by smt(mu_bounded).
 rewrite (cca_fallback_win B &m qf0 qg0); smt().
qed.

lemma cca_fallback_centered_return (B<:PartialCCABody) &m qf0 qg0 :
 Pr[CompleteFallback(B).run(qf0,qg0) @ &m:res]-
   Pr[B.run(qf0,qg0) @ &m:true]/2%r =
 (Pr[B.run(qf0,qg0) @ &m:res=Some true]-
  Pr[B.run(qf0,qg0) @ &m:res=Some false])/2%r.
proof.
 have hm:=cca_fallback_win B &m qf0 qg0.
 have hp:=cca_option_partition B &m qf0 qg0; smt().
qed.

lemma cca_fallback_centered_lossless (B<:PartialCCABody) &m qf0 qg0 :
 islossless B.run =>
 Pr[CompleteFallback(B).run(qf0,qg0) @ &m:res]-1%r/2%r =
 (Pr[B.run(qf0,qg0) @ &m:res=Some true]-
  Pr[B.run(qf0,qg0) @ &m:res=Some false])/2%r.
proof.
 move=>hB; have hm:=cca_fallback_centered_return B &m qf0 qg0.
 have ht:Pr[B.run(qf0,qg0) @ &m:true]=1%r by byphoare hB.
 by move:hm; rewrite ht.
qed.
