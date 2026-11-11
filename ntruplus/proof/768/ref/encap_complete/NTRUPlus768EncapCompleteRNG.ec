require import AllCore Distr.
from Jasmin require import JWord.
require import Array1152 Array96 Array32 Array13634.
require import NTRUPlus768EncapCompleteSpec NTRUPlus768EncapCompleteHash NTRUPlus768EncapCompleteProof.
require import NTRUPlus768DecapMessageSpec NTRUPlus768DecapCompleteHash.
require import NTRUPlus768EncapClearProof NTRUPlus768EncapClearCoins NTRUPlus768EncapClearCoinsProof.

module type EncapRNG = { proc sample() : W8.t Array96.t }.
op encap_random_result pk coins =
  let v=encap_derand_spec pk coins in
    (v.`1,v.`2,v.`3,encap_clear_zero_spec,encap_clear_coins_zero_spec).

(* Sample before inspecting the public key, including on rejected keys.
   The final array exposes erasure of the local coin buffer only. *)
module EncapRandom(F:EncapSHAKEF,G:MessageSHAKE,H:CompleteSHAKEH,R:EncapRNG) = {
  proc run(pk:W8.t Array1152.t,workspace:W8.t Array13634.t) :
    W8.t Array1152.t * W8.t Array32.t * W32.t * W8.t Array13634.t * W8.t Array96.t = {
    var coins:W8.t Array96.t; var ct:W8.t Array1152.t; var ss:W8.t Array32.t; var status:W32.t;
    coins <@ R.sample();
    (ct,ss,status,workspace) <@ EncapDerand(F,G,H).run(pk,coins,workspace);
    coins <@ NTRUPlus768EncapClearCoins.M.jade_ntruplus_ntruplus768_amd64_ref_encap_clear_coins(coins);
    return(ct,ss,status,workspace,coins);
  }
}.
module EncapRandomSpec(R:EncapRNG) = {
  proc run(pk:W8.t Array1152.t,workspace:W8.t Array13634.t) :
    W8.t Array1152.t * W8.t Array32.t * W32.t * W8.t Array13634.t * W8.t Array96.t = {
    var coins:W8.t Array96.t;
    coins <@ R.sample();
    return encap_random_result pk coins;
  }
}.

(* Hash procedures are required not to modify the RNG's state. No law,
   uniformity, independence between draws, or termination of R is assumed
   by this distribution-preserving equivalence. *)
lemma encap_random_equiv (R<:EncapRNG) (F<:EncapSHAKEF {-R}) (G<:MessageSHAKE {-R}) (H<:CompleteSHAKEH {-R}) :
  (forall x, hoare [F.shake : input=x ==> res=encap_shake_f_spec x]) =>
  (forall x, hoare [G.shake : input=x ==> res=message_shake_spec x]) =>
  (forall x, hoare [H.shake : input=x ==> res=complete_shake_h_spec x]) =>
  islossless F.shake => islossless G.shake => islossless H.shake =>
  equiv [EncapRandom(F,G,H,R).run ~ EncapRandomSpec(R).run : ={pk,workspace,glob R} ==> ={res,glob R}].
proof.
  move=> hf hg hh fl gl hl; proc.
  seq 1 1 : (={pk,workspace,coins,glob R}).
  + call (_:true); by auto.
  ecall{1}(encap_clear_coins_correct coins{1}).
  ecall{1}(encap_derand_correct F G H pk{1} coins{1} workspace{1} hf hg hh fl gl hl).
  auto => />; rewrite /encap_random_result /=; smt().
qed.
lemma encap_random_lossless (R<:EncapRNG) (F<:EncapSHAKEF) (G<:MessageSHAKE) (H<:CompleteSHAKEH) :
  islossless R.sample => islossless F.shake => islossless G.shake => islossless H.shake =>
  islossless EncapRandom(F,G,H,R).run.
proof.
  move=> rl fl gl hl; proc; call encap_clear_coins_lossless; call(encap_derand_lossless F G H fl gl hl);
    call rl; by auto.
qed.
lemma encap_random_math_equiv (R<:EncapRNG) :
  equiv [EncapRandom(MathematicalSHAKEF,MathematicalSHAKE,MathematicalSHAKEH,R).run ~ EncapRandomSpec(R).run :
    ={pk,workspace,glob R} ==> ={res,glob R}].
proof.
  exact(encap_random_equiv R MathematicalSHAKEF MathematicalSHAKE MathematicalSHAKEH
    encap_mathematical_f_functional mathematical_shake_functional complete_mathematical_h_functional
    encap_mathematical_f_lossless mathematical_shake_lossless complete_mathematical_h_lossless).
qed.

(* Arbitrary distribution supplied as RNG state. Uniform 96-byte coins are
   one possible instantiation, not an implicit assumption of this model. *)
module DistributionRNG = {
  var law : W8.t Array96.t distr
  proc sample() : W8.t Array96.t = {
    var coins; coins <$ law; return coins;
  }
}.
lemma encap_distribution_spec (d:W8.t Array96.t distr) pk0 ws0
    (p:(W8.t Array1152.t * W8.t Array32.t * W32.t * W8.t Array13634.t * W8.t Array96.t) -> bool) :
  phoare [EncapRandomSpec(DistributionRNG).run : pk=pk0 /\ workspace=ws0 /\ DistributionRNG.law=d ==>
    p res] = (mu d (fun coins => p(encap_random_result pk0 coins))).
proof.
  proc; inline DistributionRNG.sample; wp; rnd; skip; by auto => />.
qed.

lemma encap_distribution_correct (d:W8.t Array96.t distr) pk0 ws0
    (p:(W8.t Array1152.t * W8.t Array32.t * W32.t * W8.t Array13634.t * W8.t Array96.t) -> bool) :
  phoare [EncapRandom(MathematicalSHAKEF,MathematicalSHAKE,MathematicalSHAKEH,DistributionRNG).run :
    pk=pk0 /\ workspace=ws0 /\ DistributionRNG.law=d ==> p res] =
    (mu d (fun coins => p(encap_random_result pk0 coins))).
proof.
  conseq (encap_random_math_equiv DistributionRNG) (encap_distribution_spec d pk0 ws0 p); smt().
qed.
