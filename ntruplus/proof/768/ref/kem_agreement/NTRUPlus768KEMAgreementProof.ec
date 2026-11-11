require import AllCore Distr.
from Jasmin require import JWord.
require import Array32 Array96 Array1152 Array13506 Array13634 Array2336.
require import NTRUPlus768KEMAgreementContext NTRUPlus768KEMAgreementSpec.
require import NTRUPlus768EncapCompleteSpec NTRUPlus768EncapCompleteProof NTRUPlus768EncapCompleteHash.
require import NTRUPlus768DecapCompleteSpec NTRUPlus768DecapCompleteProof NTRUPlus768DecapCompleteHash.
require import NTRUPlus768DecapMessageSpec NTRUPlus768EncapGuardSpec.
require import NTRUPlus768EncapClearProof NTRUPlus768DecapClearProof NTRUPlus768PolyToBytesProof.

(* This procedure connects the actual extracted component callers. Hash
   contracts remain explicit for the native external hash implementations;
   this is an array model, not a formal C heap/ABI or erasure theorem. *)
module KEMRoundTrip(F : EncapSHAKEF, G : MessageSHAKE, H : CompleteSHAKEH) = {
  proc run(pk : W8.t Array1152.t, sk : W8.t Array2336.t, coins : W8.t Array96.t,
      eworkspace : W8.t Array13634.t, dworkspace : W8.t Array13506.t) :
      W8.t Array32.t * W8.t Array32.t * W32.t * W32.t * W8.t Array13634.t * W8.t Array13506.t = {
    var ct : W8.t Array1152.t;
    var ek,dk : W8.t Array32.t;
    var es,ds : W32.t;
    (ct,ek,es,eworkspace) <@ EncapDerand(F,G,H).run(pk,coins,eworkspace);
    (dk,ds,dworkspace) <@ CompleteDecaps(G,H).run(ct,sk,dworkspace);
    return (ek,dk,es,ds,eworkspace,dworkspace);
  }
}.

lemma agreement_roundtrip_functional (F <: EncapSHAKEF) (G <: MessageSHAKE) (H <: CompleteSHAKEH)
    fbuf gbuf finv ginv h hinv pk0 sk0 coins0 ews0 dws0 :
  (forall x, hoare [F.shake : input=x ==> res=encap_shake_f_spec x]) =>
  (forall x, hoare [G.shake : input=x ==> res=message_shake_spec x]) =>
  (forall x, hoare [H.shake : input=x ==> res=complete_shake_h_spec x]) =>
  agreement_key_relation fbuf gbuf finv ginv h hinv pk0 sk0 =>
  agreement_no_wrap fbuf gbuf pk0 coins0 =>
  hoare [KEMRoundTrip(F,G,H).run : pk=pk0 /\ sk=sk0 /\ coins=coins0 /\
    eworkspace=ews0 /\ dworkspace=dws0 ==>
    res=(encap_full_key pk0 coins0,encap_full_key pk0 coins0,W32.zero,W32.zero,
      encap_clear_zero_spec,clear_zero_spec)].
proof.
  move=> hf hg hh hk hn.
  have [hpk _] := agreement_key_canonical fbuf gbuf finv ginv h hinv pk0 sk0 hk.
  have hkey := agreement_spec_key fbuf gbuf finv ginv h hinv pk0 sk0 coins0 hk hn.
  clear hk hn.
  proc.
  seq 1 : (ct=poly_tobytes_spec(encap_full_cipher pk0 coins0) /\
    ek=encap_full_key pk0 coins0 /\ es=W32.zero /\ eworkspace=encap_clear_zero_spec /\
    sk=sk0 /\ dworkspace=dws0).
  + call (encap_derand_functional F G H pk0 coins0 ews0 hf hg hh).
    auto => />; rewrite (encap_derand_accept pk0 coins0 hpk); smt().
  call (complete_functional G H (poly_tobytes_spec(encap_full_cipher pk0 coins0)) sk0 dws0 hg hh).
  auto => />; rewrite hkey; smt().
qed.

lemma agreement_roundtrip_lossless (F <: EncapSHAKEF) (G <: MessageSHAKE) (H <: CompleteSHAKEH) :
  islossless F.shake => islossless G.shake => islossless H.shake =>
  islossless KEMRoundTrip(F,G,H).run.
proof.
  move=> fl gl hl; proc; call (complete_lossless G H gl hl);
    call (encap_derand_lossless F G H fl gl hl); by auto.
qed.

lemma agreement_roundtrip_correct (F <: EncapSHAKEF) (G <: MessageSHAKE) (H <: CompleteSHAKEH)
    fbuf gbuf finv ginv h hinv pk0 sk0 coins0 ews0 dws0 :
  (forall x, hoare [F.shake : input=x ==> res=encap_shake_f_spec x]) =>
  (forall x, hoare [G.shake : input=x ==> res=message_shake_spec x]) =>
  (forall x, hoare [H.shake : input=x ==> res=complete_shake_h_spec x]) =>
  islossless F.shake => islossless G.shake => islossless H.shake =>
  agreement_key_relation fbuf gbuf finv ginv h hinv pk0 sk0 =>
  agreement_no_wrap fbuf gbuf pk0 coins0 =>
  phoare [KEMRoundTrip(F,G,H).run : pk=pk0 /\ sk=sk0 /\ coins=coins0 /\
    eworkspace=ews0 /\ dworkspace=dws0 ==>
    res=(encap_full_key pk0 coins0,encap_full_key pk0 coins0,W32.zero,W32.zero,
      encap_clear_zero_spec,clear_zero_spec)]=1%r.
proof.
  move=> hf hg hh fl gl hl hk hn.
  by conseq (agreement_roundtrip_lossless F G H fl gl hl)
    (agreement_roundtrip_functional F G H fbuf gbuf finv ginv h hinv pk0 sk0 coins0 ews0 dws0 hf hg hh hk hn).
qed.

lemma agreement_roundtrip_math_correct fbuf gbuf finv ginv h hinv pk0 sk0 coins0 ews0 dws0 :
  agreement_key_relation fbuf gbuf finv ginv h hinv pk0 sk0 =>
  agreement_no_wrap fbuf gbuf pk0 coins0 =>
  phoare [KEMRoundTrip(MathematicalSHAKEF,MathematicalSHAKE,MathematicalSHAKEH).run :
    pk=pk0 /\ sk=sk0 /\ coins=coins0 /\ eworkspace=ews0 /\ dworkspace=dws0 ==>
    res=(encap_full_key pk0 coins0,encap_full_key pk0 coins0,W32.zero,W32.zero,
      encap_clear_zero_spec,clear_zero_spec)]=1%r.
proof.
  move=> hk hn.
  exact (agreement_roundtrip_correct MathematicalSHAKEF MathematicalSHAKE MathematicalSHAKEH
    fbuf gbuf finv ginv h hinv pk0 sk0 coins0 ews0 dws0
    encap_mathematical_f_functional mathematical_shake_functional complete_mathematical_h_functional
    encap_mathematical_f_lossless mathematical_shake_lossless complete_mathematical_h_lossless hk hn).
qed.
