require import AllCore Distr.
from Jasmin require import JWord.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteProof.
require import NTRUPlus768KeygenCompleteAgreement NTRUPlus768KeygenRetryLaw NTRUPlus768KeygenIIDProof.
require import NTRUPlus768KEMAgreementProof NTRUPlus768KeygenClearProof.
require import NTRUPlus768EncapCompleteHash NTRUPlus768DecapMessageSpec NTRUPlus768DecapCompleteHash.

lemma keygen_iid_kem_terminates
    (E<:KeygenExpand {-IIDSeedRNG}) (F<:EncapSHAKEF {-IIDSeedRNG})
    (G<:MessageSHAKE) (H<:CompleteSHAKEH) d expand0 :
  (forall x, hoare [E.shake:seed=x ==> res=expand0 x]) =>
  islossless E.shake => islossless F.shake => islossless G.shake => islossless H.shake =>
  is_lossless d => 0%r < mu d (keygen_f_seed_accept expand0) =>
  0%r < mu d (keygen_g_seed_accept expand0) =>
  phoare [KeygenKEMInstrumented(IIDSeedRNG,E,F,G,H).run : IIDSeedRNG.law=d ==> true]=1%r.
proof.
  move=> he el fl gl hl dll pf pg; proc.
  call(agreement_roundtrip_lossless F G H fl gl hl).
  call(keygen_iid_instrumented_terminates E F d expand0 he el fl dll pf pg).
  by auto.
qed.

(* Key-related premises come from actual KeyGen. The sufficient integer
   no-wrap condition remains explicit; this implication is not a zero
   decryption-failure bound and is not an IND-CCA theorem. *)
lemma keygen_iid_kem_correct
    (E<:KeygenExpand {-IIDSeedRNG}) (F<:EncapSHAKEF {-IIDSeedRNG})
    (G<:MessageSHAKE) (H<:CompleteSHAKEH) d expand0 coins0 :
  (forall x, hoare [E.shake:seed=x ==> res=expand0 x]) =>
  (forall x, hoare [F.shake:input=x ==> res=encap_shake_f_spec x]) =>
  (forall x, hoare [G.shake:input=x ==> res=message_shake_spec x]) =>
  (forall x, hoare [H.shake:input=x ==> res=complete_shake_h_spec x]) =>
  islossless E.shake => islossless F.shake => islossless G.shake => islossless H.shake =>
  is_lossless d => 0%r < mu d (keygen_f_seed_accept expand0) =>
  0%r < mu d (keygen_g_seed_accept expand0) =>
  phoare [KeygenKEMInstrumented(IIDSeedRNG,E,F,G,H).run : IIDSeedRNG.law=d /\ coins=coins0 ==>
    keygen_witness_valid res.`1 /\ res.`3=keygen_clear_zero_spec /\
    (keygen_coins_no_wrap res.`1 coins0 => res.`2=keygen_roundtrip_value res.`1.`kg_pk coins0)]=1%r.
proof.
  move=> he hf hg hh el fl gl hl dll pf pg.
  by conseq (keygen_iid_kem_terminates E F G H d expand0 he el fl gl hl dll pf pg)
    (keygen_kem_functional IIDSeedRNG E F G H coins0 hf hg hh).
qed.

lemma keygen_mathematical_iid_kem_correct d coins0 :
  is_lossless d =>
  0%r < mu d (keygen_f_seed_accept keygen_seed_expansion) =>
  0%r < mu d (keygen_g_seed_accept keygen_seed_expansion) =>
  phoare [KeygenKEMInstrumented(IIDSeedRNG,MathematicalKeygenExpand,MathematicalSHAKEF,MathematicalSHAKE,MathematicalSHAKEH).run :
    IIDSeedRNG.law=d /\ coins=coins0 ==>
    keygen_witness_valid res.`1 /\ res.`3=keygen_clear_zero_spec /\
    (keygen_coins_no_wrap res.`1 coins0 => res.`2=keygen_roundtrip_value res.`1.`kg_pk coins0)]=1%r.
proof.
  move=> dll pf pg.
  exact(keygen_iid_kem_correct MathematicalKeygenExpand MathematicalSHAKEF MathematicalSHAKE MathematicalSHAKEH
    d keygen_seed_expansion coins0 mathematical_keygen_expand_functional encap_mathematical_f_functional
    mathematical_shake_functional complete_mathematical_h_functional mathematical_keygen_expand_lossless
    encap_mathematical_f_lossless mathematical_shake_lossless complete_mathematical_h_lossless dll pf pg).
qed.
