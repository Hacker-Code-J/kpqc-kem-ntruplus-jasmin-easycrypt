require import AllCore Distr.
from Jasmin require import JWord.
require import NTRUPlus768KEMFailureModel NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteProof.
require import NTRUPlus768KeygenCompleteAgreement NTRUPlus768KEMAgreementContext NTRUPlus768KEMAgreementSpec.
require import NTRUPlus768EncapCompleteRNG NTRUPlus768EncapCompleteSpec NTRUPlus768EncapCompleteProof NTRUPlus768EncapCompleteHash.
require import NTRUPlus768DecapMessageSpec NTRUPlus768DecapCompleteHash NTRUPlus768DecapCompleteProof NTRUPlus768DecapCompleteSpec.
require import NTRUPlus768EncapClearProof NTRUPlus768EncapClearCoinsProof NTRUPlus768DecapClearProof.

require import NTRUPlus768KEMFailureSpec.

lemma encap_instrumented_functional (F<:EncapSHAKEF) (G<:MessageSHAKE) (H<:CompleteSHAKEH) (Q<:EncapRNG) pk0 :
  (forall x,hoare[F.shake:input=x ==> res=encap_shake_f_spec x]) =>
  (forall x,hoare[G.shake:input=x ==> res=message_shake_spec x]) =>
  (forall x,hoare[H.shake:input=x ==> res=complete_shake_h_spec x]) =>
  hoare[EncapRandomInstrumented(F,G,H,Q).run:pk=pk0 ==>
    (res.`1.`1,res.`1.`2,res.`1.`3)=encap_derand_spec pk0 res.`2 /\
    res.`1.`4=encap_clear_zero_spec /\ res.`1.`5=encap_clear_coins_zero_spec].
proof.
  move=> hf hg hh; proc.
  ecall(encap_clear_coins_functional coins).
  ecall(encap_derand_functional F G H pk0 coins workspace hf hg hh).
  wp; call (_:true); auto => />; smt().
qed.

(* Pure coupling of identical Encaps calls under the displayed state
   separation. Neither the law nor termination of Q is constrained. *)
lemma encap_instrumented_projection (Q<:EncapRNG) (F<:EncapSHAKEF {-Q})
    (G<:MessageSHAKE {-Q,-F}) (H<:CompleteSHAKEH {-Q,-F,-G}) :
  equiv[EncapRandom(F,G,H,Q).run ~ EncapRandomInstrumented(F,G,H,Q).run:
    ={pk,workspace,glob F,glob G,glob H,glob Q} ==>
    res{1}=res{2}.`1 /\ ={glob F,glob G,glob H,glob Q}].
proof.
  proc.
  conseq (_:_ ==> ={ct,ss,status,workspace,coins,glob F,glob G,glob H,glob Q}) => //.
  sim.
qed.

lemma correctness_independent_public_projection (R<:KeygenSeedRNG) (Q<:EncapRNG {-R}) (E<:KeygenExpand {-R,-Q})
    (F<:EncapSHAKEF {-R,-Q,-E}) (G<:MessageSHAKE {-R,-Q,-E,-F}) (H<:CompleteSHAKEH {-R,-Q,-E,-F,-G}) :
  equiv[KEMCorrectness(R,E,F,G,H,Q).run ~ KEMCorrectnessInstrumented(R,E,F,G,H,Q).run:
    ={glob R,glob E,glob F,glob G,glob H,glob Q} ==>
    res{1}=res{2}.`1 /\ ={glob R,glob E,glob F,glob G,glob H,glob Q}].
proof.
  proc; inline{1} Keygen(R,E,F).run.
  seq 2 1 : (pk{1}=w{2}.`kg_pk /\ sk{1}=w{2}.`kg_sk /\
    ={glob R,glob E,glob F,glob G,glob H,glob Q}).
  + wp; call (_: ={glob R,glob E,glob F}); first by sim.
    by auto.
  call (_: ={glob G,glob H}); first by sim.
  call(encap_instrumented_projection Q F G H).
  by auto => />.
qed.

lemma correctness_failure_implies_bad (R<:KeygenSeedRNG) (E<:KeygenExpand) (F<:EncapSHAKEF)
    (G<:MessageSHAKE) (H<:CompleteSHAKEH) (Q<:EncapRNG) :
  (forall x,hoare[F.shake:input=x ==> res=encap_shake_f_spec x]) =>
  (forall x,hoare[G.shake:input=x ==> res=message_shake_spec x]) =>
  (forall x,hoare[H.shake:input=x ==> res=complete_shake_h_spec x]) =>
  hoare[KEMCorrectnessInstrumented(R,E,F,G,H,Q).run:true ==> res.`1 => res.`2].
proof.
  move=> hf hg hh; proc.
  ecall(complete_functional G H er.`1 w.`kg_sk witness hg hh).
  ecall(encap_instrumented_functional F G H Q w.`kg_pk hf hg hh).
  call(keygen_instrumented_functional R E F hf).
  auto => />; smt(generated_key_failure_implies_bad).
qed.

lemma correctness_independent_failure_probability (R<:KeygenSeedRNG) (Q<:EncapRNG {-R}) (E<:KeygenExpand {-R,-Q})
    (F<:EncapSHAKEF {-R,-Q,-E}) (G<:MessageSHAKE {-R,-Q,-E,-F}) (H<:CompleteSHAKEH {-R,-Q,-E,-F,-G}) &m :
  Pr[KEMCorrectness(R,E,F,G,H,Q).run() @ &m:res] =
  Pr[KEMCorrectnessInstrumented(R,E,F,G,H,Q).run() @ &m:res.`1].
proof. by byequiv(correctness_independent_public_projection R Q E F G H). qed.

lemma correctness_independent_failure_bound (R<:KeygenSeedRNG) (Q<:EncapRNG {-R}) (E<:KeygenExpand {-R,-Q})
    (F<:EncapSHAKEF {-R,-Q,-E}) (G<:MessageSHAKE {-R,-Q,-E,-F}) (H<:CompleteSHAKEH {-R,-Q,-E,-F,-G}) &m :
  (forall x,hoare[F.shake:input=x ==> res=encap_shake_f_spec x]) =>
  (forall x,hoare[G.shake:input=x ==> res=message_shake_spec x]) =>
  (forall x,hoare[H.shake:input=x ==> res=complete_shake_h_spec x]) =>
  Pr[KEMCorrectness(R,E,F,G,H,Q).run() @ &m:res] <=
  Pr[KEMCorrectnessInstrumented(R,E,F,G,H,Q).run() @ &m:res.`2].
proof.
  move=> hf hg hh; rewrite(correctness_independent_failure_probability R Q E F G H &m).
  have hz:Pr[KEMCorrectnessInstrumented(R,E,F,G,H,Q).run() @ &m:res.`1 /\ !res.`2]=0%r.
  + byphoare (_:true ==> res.`1 /\ !res.`2) => //; hoare.
    conseq(correctness_failure_implies_bad R E F G H Q hf hg hh) => />; smt().
  rewrite Pr[mu_split res.`2] hz /=.
  by byequiv (_: ={glob R,glob Q,glob E,glob F,glob G,glob H} ==> ={res}) => //; sim.
qed.


(* The common-source theorem allows both random-byte calls to use one
   mutable RNG state. Hash modules are separated from that state and from
   one another; no law or termination premise is used for this coupling. *)
lemma correctness_public_projection (B<:KEMRNG) (E<:KeygenExpand {-B})
    (F<:EncapSHAKEF {-B,-E}) (G<:MessageSHAKE {-B,-E,-F}) (H<:CompleteSHAKEH {-B,-E,-F,-G}) :
  equiv[KEMCorrectness(KeygenRNGPort(B),E,F,G,H,EncapRNGPort(B)).run ~
    KEMCorrectnessInstrumented(KeygenRNGPort(B),E,F,G,H,EncapRNGPort(B)).run:
    ={glob B,glob E,glob F,glob G,glob H} ==>
    res{1}=res{2}.`1 /\ ={glob B,glob E,glob F,glob G,glob H}].
proof.
  proc; inline{1} Keygen(KeygenRNGPort(B),E,F).run.
  seq 2 1 : (pk{1}=w{2}.`kg_pk /\ sk{1}=w{2}.`kg_sk /\
    ={glob B,glob E,glob F,glob G,glob H}).
  + wp; call (_: ={glob B,glob E,glob F}); first by sim.
    by auto.
  call (_: ={glob G,glob H}); first by sim.
  call(encap_instrumented_projection (EncapRNGPort(B)) F G H).
  by auto => />.
qed.

lemma correctness_public_failure_probability (B<:KEMRNG) (E<:KeygenExpand {-B})
    (F<:EncapSHAKEF {-B,-E}) (G<:MessageSHAKE {-B,-E,-F}) (H<:CompleteSHAKEH {-B,-E,-F,-G}) &m :
  Pr[KEMCorrectness(KeygenRNGPort(B),E,F,G,H,EncapRNGPort(B)).run() @ &m:res] =
  Pr[KEMCorrectnessInstrumented(KeygenRNGPort(B),E,F,G,H,EncapRNGPort(B)).run() @ &m:res.`1].
proof. by byequiv(correctness_public_projection B E F G H). qed.

lemma correctness_failure_bound (B<:KEMRNG) (E<:KeygenExpand {-B})
    (F<:EncapSHAKEF {-B,-E}) (G<:MessageSHAKE {-B,-E,-F}) (H<:CompleteSHAKEH {-B,-E,-F,-G}) &m :
  (forall x,hoare[F.shake:input=x ==> res=encap_shake_f_spec x]) =>
  (forall x,hoare[G.shake:input=x ==> res=message_shake_spec x]) =>
  (forall x,hoare[H.shake:input=x ==> res=complete_shake_h_spec x]) =>
  Pr[KEMCorrectness(KeygenRNGPort(B),E,F,G,H,EncapRNGPort(B)).run() @ &m:res] <=
  Pr[KEMCorrectnessInstrumented(KeygenRNGPort(B),E,F,G,H,EncapRNGPort(B)).run() @ &m:res.`2].
proof.
  move=> hf hg hh; rewrite(correctness_public_failure_probability B E F G H &m).
  have hz:Pr[KEMCorrectnessInstrumented(KeygenRNGPort(B),E,F,G,H,EncapRNGPort(B)).run() @ &m:res.`1 /\ !res.`2]=0%r.
  + byphoare (_:true ==> res.`1 /\ !res.`2) => //; hoare.
    conseq(correctness_failure_implies_bad (KeygenRNGPort(B)) E F G H (EncapRNGPort(B)) hf hg hh) => />; smt().
  rewrite Pr[mu_split res.`2] hz /=.
  by byequiv (_: ={glob B,glob E,glob F,glob G,glob H} ==> ={res}) => //; sim.
qed.
