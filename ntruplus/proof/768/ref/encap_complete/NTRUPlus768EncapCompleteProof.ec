require import AllCore Distr.
from Jasmin require import JWord.
require import Array768 Array1152 Array96 Array32 Array224 Array13634.
require import NTRUPlus768EncapCompleteSpec NTRUPlus768EncapCompleteHash NTRUPlus768EncapCompleteBody.
require import NTRUPlus768DecapMessageSpec NTRUPlus768DecapCompleteHash.
require import NTRUPlus768EncapGuard NTRUPlus768EncapGuardSpec NTRUPlus768EncapGuardProof NTRUPlus768CanonicalDecoder.
require import NTRUPlus768PolyToBytesProof NTRUPlus768EncapClear NTRUPlus768EncapClearProof.

lemma encap_tuple3_eta (x:'a * 'b * 'c) : (x.`1,x.`2,x.`3)=x.
proof. by case:x. qed.
module EncapCore(F:EncapSHAKEF,G:MessageSHAKE,H:CompleteSHAKEH) = {
  proc run(pk:W8.t Array1152.t, coins:W8.t Array96.t) : W8.t Array1152.t * W8.t Array32.t * W32.t = {
    var hp:W16.t Array768.t; var ct:W8.t Array1152.t; var ss:W8.t Array32.t; var status:W32.t;
    var hashout:W8.t Array224.t;
    (hp,ct,ss,status) <@ NTRUPlus768EncapGuard.M.jade_ntruplus_ntruplus768_amd64_ref_encap_guard(witness,encap_zero_ct,encap_zero_ss,pk);
    if(status=W32.zero) {
      hashout <@ EncapSeed(F,H).run(pk,coins);
      (ct,ss) <@ EncapBody(G).run(hp,coins,hashout);
    }
    return(ct,ss,status);
  }
}.
lemma encap_core_functional (F<:EncapSHAKEF) (G<:MessageSHAKE) (H<:CompleteSHAKEH) pk0 coins0 :
  (forall x, hoare [F.shake : input=x ==> res=encap_shake_f_spec x]) =>
  (forall x, hoare [G.shake : input=x ==> res=message_shake_spec x]) =>
  (forall x, hoare [H.shake : input=x ==> res=complete_shake_h_spec x]) =>
  hoare [EncapCore(F,G,H).run : pk=pk0 /\ coins=coins0 ==> res=encap_derand_spec pk0 coins0].
proof.
  move=> hf hg hh; case(encap_key_canonical pk0) => hk.
  + proc; rcondt 2.
    - call(encap_guard_canonical_functional witness encap_zero_ct encap_zero_ss pk0 hk); by auto.
    call(encap_body_functional G pk0 coins0 hg hk).
    call(encap_seed_functional F H pk0 coins0 hf hh).
    call(encap_guard_canonical_functional witness encap_zero_ct encap_zero_ss pk0 hk).
    auto => />; by rewrite /encap_derand_spec hk.
  proc; rcondf 2.
  + call(encap_guard_reject_functional witness encap_zero_ct encap_zero_ss pk0 hk);
      auto => />; smt(W32.to_uint0 W32.to_uint1).
  call(encap_guard_reject_functional witness encap_zero_ct encap_zero_ss pk0 hk).
  auto => />; by rewrite /encap_derand_spec hk.
qed.
lemma encap_core_lossless (F<:EncapSHAKEF) (G<:MessageSHAKE) (H<:CompleteSHAKEH) :
  islossless F.shake => islossless G.shake => islossless H.shake => islossless EncapCore(F,G,H).run.
proof.
  move=> fl gl hl; proc; seq 1:true.
  + ecall(encap_guard_functional witness encap_zero_ct encap_zero_ss pk); auto.
  + call encap_guard_lossless; auto.
  + if; [call(encap_body_lossless G gl); call(encap_seed_lossless F H fl hl)|]; auto.
  + hoare; ecall(encap_guard_functional witness encap_zero_ct encap_zero_ss pk); auto.
  auto.
qed.
(* Separate array-value call composition. The cleared workspace argument is
   not a formal embedding of native C fields, stack spills, or registers. *)
module EncapDerand(F:EncapSHAKEF,G:MessageSHAKE,H:CompleteSHAKEH) = {
  proc run(pk:W8.t Array1152.t, coins:W8.t Array96.t,workspace:W8.t Array13634.t) :
      W8.t Array1152.t * W8.t Array32.t * W32.t * W8.t Array13634.t = {
    var ct:W8.t Array1152.t; var ss:W8.t Array32.t; var status:W32.t;
    (ct,ss,status) <@ EncapCore(F,G,H).run(pk,coins);
    workspace <@ NTRUPlus768EncapClear.M.jade_ntruplus_ntruplus768_amd64_ref_encap_clear(workspace);
    return(ct,ss,status,workspace);
  }
}.
lemma encap_derand_functional (F<:EncapSHAKEF) (G<:MessageSHAKE) (H<:CompleteSHAKEH) pk0 coins0 ws0 :
  (forall x, hoare [F.shake : input=x ==> res=encap_shake_f_spec x]) =>
  (forall x, hoare [G.shake : input=x ==> res=message_shake_spec x]) =>
  (forall x, hoare [H.shake : input=x ==> res=complete_shake_h_spec x]) =>
  hoare [EncapDerand(F,G,H).run : pk=pk0 /\ coins=coins0 /\ workspace=ws0 ==>
    (res.`1,res.`2,res.`3)=encap_derand_spec pk0 coins0 /\ res.`4=encap_clear_zero_spec].
proof.
  move=> hf hg hh; proc; call(encap_clear_functional ws0); call(encap_core_functional F G H pk0 coins0 hf hg hh);
    auto => />; by rewrite encap_tuple3_eta.
qed.
lemma encap_derand_lossless (F<:EncapSHAKEF) (G<:MessageSHAKE) (H<:CompleteSHAKEH) :
  islossless F.shake => islossless G.shake => islossless H.shake => islossless EncapDerand(F,G,H).run.
proof. move=> fl gl hl; proc; call encap_clear_lossless; call(encap_core_lossless F G H fl gl hl); by auto. qed.
lemma encap_derand_correct (F<:EncapSHAKEF) (G<:MessageSHAKE) (H<:CompleteSHAKEH) pk0 coins0 ws0 :
  (forall x, hoare [F.shake : input=x ==> res=encap_shake_f_spec x]) =>
  (forall x, hoare [G.shake : input=x ==> res=message_shake_spec x]) =>
  (forall x, hoare [H.shake : input=x ==> res=complete_shake_h_spec x]) =>
  islossless F.shake => islossless G.shake => islossless H.shake =>
  phoare [EncapDerand(F,G,H).run : pk=pk0 /\ coins=coins0 /\ workspace=ws0 ==>
    (res.`1,res.`2,res.`3)=encap_derand_spec pk0 coins0 /\ res.`4=encap_clear_zero_spec]=1%r.
proof.
  move=> hf hg hh fl gl hl; by conseq(encap_derand_lossless F G H fl gl hl)
    (encap_derand_functional F G H pk0 coins0 ws0 hf hg hh).
qed.
lemma encap_derand_math_correct pk0 coins0 ws0 :
  phoare [EncapDerand(MathematicalSHAKEF,MathematicalSHAKE,MathematicalSHAKEH).run :
    pk=pk0 /\ coins=coins0 /\ workspace=ws0 ==>
    (res.`1,res.`2,res.`3)=encap_derand_spec pk0 coins0 /\ res.`4=encap_clear_zero_spec]=1%r.
proof.
  exact(encap_derand_correct MathematicalSHAKEF MathematicalSHAKE MathematicalSHAKEH pk0 coins0 ws0
    encap_mathematical_f_functional mathematical_shake_functional complete_mathematical_h_functional
    encap_mathematical_f_lossless mathematical_shake_lossless complete_mathematical_h_lossless).
qed.
lemma encap_derand_reject_no_hash (F<:EncapSHAKEF) (G<:MessageSHAKE) (H<:CompleteSHAKEH) pk0 coins0 ws0 &m :
  !encap_key_canonical pk0 =>
  phoare [EncapDerand(F,G,H).run : pk=pk0 /\ coins=coins0 /\ workspace=ws0 /\
    (glob F)=(glob F){m} /\ (glob G)=(glob G){m} /\ (glob H)=(glob H){m} ==>
    res=(encap_zero_ct,encap_zero_ss,W32.one,encap_clear_zero_spec) /\
    (glob F)=(glob F){m} /\ (glob G)=(glob G){m} /\ (glob H)=(glob H){m}]=1%r.
proof.
  move=> hk; proc; inline EncapCore(F,G,H).run.
  rcondf 4.
  + call(encap_guard_reject_functional witness encap_zero_ct encap_zero_ss pk0 hk);
      auto => />; smt(W32.to_uint0 W32.to_uint1).
  call(encap_clear_correct ws0); wp.
  call(encap_guard_noncanonical_reject witness encap_zero_ct encap_zero_ss pk0 hk); by auto.
qed.
