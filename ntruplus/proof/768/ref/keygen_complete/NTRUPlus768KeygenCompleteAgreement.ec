require import AllCore Distr.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array768 Array1152 Array2336 Array14466 Array13634 Array13506.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteRetry NTRUPlus768KeygenCompleteProof.
require import NTRUPlus768KEMAgreementContext NTRUPlus768KEMAgreementSpec NTRUPlus768KEMAgreementProof.
require import NTRUPlus768EncapCompleteHash NTRUPlus768EncapCompleteSpec NTRUPlus768DecapMessageSpec NTRUPlus768DecapCompleteHash.
require import NTRUPlus768EncapClearProof NTRUPlus768DecapClearProof NTRUPlus768KeygenClearProof.

op [opaque] keygen_coins_no_wrap (w:keygen_witness) coins =
 agreement_no_wrap w.`kg_fbuf w.`kg_gbuf w.`kg_pk coins.
op keygen_roundtrip_value pk coins =
 (encap_full_key pk coins,encap_full_key pk coins,W32.zero,W32.zero,encap_clear_zero_spec,clear_zero_spec).

lemma keygen_roundtrip_conditional (F<:EncapSHAKEF) (G<:MessageSHAKE) (H<:CompleteSHAKEH)
 (w:keygen_witness) coins0 ews0 dws0 :
 (forall x,hoare[F.shake:input=x ==> res=encap_shake_f_spec x]) =>
 (forall x,hoare[G.shake:input=x ==> res=message_shake_spec x]) =>
 (forall x,hoare[H.shake:input=x ==> res=complete_shake_h_spec x]) =>
 hoare[KEMRoundTrip(F,G,H).run : keygen_witness_valid w /\ pk=w.`kg_pk /\ sk=w.`kg_sk /\ coins=coins0 /\
 eworkspace=ews0 /\ dworkspace=dws0 ==>
 keygen_coins_no_wrap w coins0 => res=keygen_roundtrip_value w.`kg_pk coins0].
proof.
 move=> hf hg hh; case(keygen_witness_valid w) => hk.
 + rewrite /keygen_witness_valid in hk.
   case(keygen_coins_no_wrap w coins0) => hn.
   - rewrite /keygen_coins_no_wrap in hn.
   conseq(agreement_roundtrip_functional F G H
 w.`kg_fbuf w.`kg_gbuf w.`kg_finv w.`kg_ginv w.`kg_h w.`kg_hinv w.`kg_pk w.`kg_sk coins0 ews0 dws0
 hf hg hh hk hn) => />.
   conseq (_:true ==> true) => //; smt().
 conseq (_:false ==> true) => //; smt().
qed.

(* This is proof instrumentation of KeyGen followed by the existing actual
   Encaps/Decaps callers; private witnesses make the sufficient no-wrap event
   observable to the theorem, not to a public KEM API or an adversary. *)
module KeygenKEMInstrumented(R:KeygenSeedRNG,E:KeygenExpand,F:EncapSHAKEF,G:MessageSHAKE,H:CompleteSHAKEH) = {
 proc run(coins:W8.t Array96.t,workspace:W8.t Array14466.t,eworkspace:W8.t Array13634.t,dworkspace:W8.t Array13506.t) :
 keygen_witness * (W8.t Array32.t * W8.t Array32.t * W32.t * W32.t * W8.t Array13634.t * W8.t Array13506.t) * W8.t Array14466.t = {
  var w:keygen_witness;
  var result:W8.t Array32.t * W8.t Array32.t * W32.t * W32.t * W8.t Array13634.t * W8.t Array13506.t;
  (w,workspace) <@ KeygenInstrumented(R,E,F).run(workspace);
  result <@ KEMRoundTrip(F,G,H).run(w.`kg_pk,w.`kg_sk,coins,eworkspace,dworkspace);
  return(w,result,workspace);
 }
}.
lemma keygen_kem_functional (R<:KeygenSeedRNG) (E<:KeygenExpand) (F<:EncapSHAKEF) (G<:MessageSHAKE) (H<:CompleteSHAKEH) coins0 :
 (forall x,hoare[F.shake:input=x ==> res=encap_shake_f_spec x]) =>
 (forall x,hoare[G.shake:input=x ==> res=message_shake_spec x]) =>
 (forall x,hoare[H.shake:input=x ==> res=complete_shake_h_spec x]) =>
 hoare[KeygenKEMInstrumented(R,E,F,G,H).run : coins=coins0 ==>
 keygen_witness_valid res.`1 /\ res.`3=keygen_clear_zero_spec /\
 (keygen_coins_no_wrap res.`1 coins0 => res.`2=keygen_roundtrip_value res.`1.`kg_pk coins0)].
proof.
 move=> hf hg hh; proc.
 ecall(keygen_roundtrip_conditional F G H w coins0 eworkspace dworkspace hf hg hh).
 call(keygen_instrumented_functional R E F hf).
 auto => />; smt().
qed.
lemma keygen_kem_lossless (R<:KeygenSeedRNG) (E<:KeygenExpand) (F<:EncapSHAKEF) (G<:MessageSHAKE) (H<:CompleteSHAKEH) :
 islossless KeygenRetry(R,E).f => islossless KeygenRetry(R,E).g =>
 islossless F.shake => islossless G.shake => islossless H.shake =>
 islossless KeygenKEMInstrumented(R,E,F,G,H).run.
proof.
 move=> fl gl hf hg hh; proc; call(agreement_roundtrip_lossless F G H hf hg hh);
 call(keygen_instrumented_lossless R E F fl gl hf); auto.
qed.
lemma keygen_kem_correct (R<:KeygenSeedRNG) (E<:KeygenExpand) (F<:EncapSHAKEF) (G<:MessageSHAKE) (H<:CompleteSHAKEH) coins0 :
 (forall x,hoare[F.shake:input=x ==> res=encap_shake_f_spec x]) =>
 (forall x,hoare[G.shake:input=x ==> res=message_shake_spec x]) =>
 (forall x,hoare[H.shake:input=x ==> res=complete_shake_h_spec x]) =>
 islossless KeygenRetry(R,E).f => islossless KeygenRetry(R,E).g =>
 islossless F.shake => islossless G.shake => islossless H.shake =>
 phoare[KeygenKEMInstrumented(R,E,F,G,H).run : coins=coins0 ==>
 keygen_witness_valid res.`1 /\ res.`3=keygen_clear_zero_spec /\
 (keygen_coins_no_wrap res.`1 coins0 => res.`2=keygen_roundtrip_value res.`1.`kg_pk coins0)]=1%r.
proof.
 move=> hf hg hh fl gl hfl hgl hhl.
 by conseq(keygen_kem_lossless R E F G H fl gl hfl hgl hhl)(keygen_kem_functional R E F G H coins0 hf hg hh).
qed.
