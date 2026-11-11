require import AllCore Distr.
from Jasmin require import JWord.
require import Array768 Array1152.
require import NTRUPlus768CanonicalDecoder NTRUPlus768EncapGuardSpec.
require import NTRUPlus768DecapR2CompSpec NTRUPlus768InvNTTProof.
require import NTRUPlus768BasemulAlgebra NTRUPlus768PolyBasemulAlgebra.
require import NTRUPlus768DecapCandidateAlgebra NTRUPlus768EncapCompleteAlgebra.
require import NTRUPlus768PKEModel NTRUPlus768PKEProcedures NTRUPlus768PKECallProof.
require import NTRUPlus768RRecWordChecks NTRUPlus768RRecPublicInverse NTRUPlus768RRecProcedures.

require import NTRUPlus768RRecModel.

lemma rrec_finish_functional cp0 m0 inverse0 :
 hoare[RRecFinish.run : cp=cp0 /\ m=m0 /\ inverse=inverse0 ==>
 res=rrec_finish_spec cp0 m0 inverse0].
proof.
 proc; seq 4 : (candidate=rrec_candidate cp0 m0 inverse0 /\
 valid=pke_domain(rrec_candidate cp0 m0 inverse0) /\ result=None).
 + call(rrec_trit_functional (rrec_candidate cp0 m0 inverse0)).
   call(rrec_normalize_functional (invntt_spec(decap_r2_spec cp0 m0 inverse0))).
   call(rrec_core_functional cp0 m0 inverse0).
   wp; skip; rewrite rrec_candidateE; auto.
 if; auto=> />; rewrite /rrec_finish_spec; smt().
qed.
lemma rrec_verify_functional pk0 m0 ct0 candidate0 :
 pke_domain m0 => (candidate0<>None => pke_domain(oget candidate0)) =>
 hoare[RRecVerify.run : pk=pk0 /\ m=m0 /\ ct=ct0 /\ candidate=candidate0 ==>
 res=rrec_verify_spec pk0 m0 ct0 candidate0].
proof.
 move=>hm hd; case(candidate0=None)=>hn.
 + proc; rcondf 2; auto=> />; by rewrite /rrec_verify_spec hn.
 proc; rcondt 2; first by auto.
 seq 2 : (checked=pke_enc_spec pk0 m0 (oget candidate0) /\
 candidate=candidate0 /\ ct=ct0 /\ result=None).
 + call(pke_enc_functional pk0 m0 (oget candidate0) hm (hd hn)); auto.
 if; auto=> />; rewrite /rrec_verify_spec hn; smt().
qed.
lemma rrec_using_inverse_functional pk0 m0 ct0 inverse0 :
 hoare[RRecUsingInverse.run : pk=pk0 /\ m=m0 /\ ct=ct0 /\ inverse=inverse0 ==>
 res=rrec_using_inverse_spec pk0 m0 ct0 inverse0].
proof.
 case(encap_key_canonical ct0)=>hc; last first.
 + proc; rcondf 3.
   - call(pke_decoder_functional witness ct0); auto=> />; rewrite /encap_status hc; smt(W32.to_uint0 W32.to_uint1).
   call(pke_decoder_functional witness ct0); auto=> />; by rewrite /rrec_using_inverse_spec hc.
 case(pke_domain m0)=>hm; proc; rcondt 3.
 + call(pke_decoder_functional witness ct0); auto=> />; by rewrite /encap_status hc.
 + rcondt 4.
   - call(rrec_trit_functional m0); call(pke_decoder_functional witness ct0); auto.
   call(rrec_verify_functional pk0 m0 ct0 (rrec_finish_spec (decoded_poly ct0) m0 inverse0)
     hm (rrec_finish_domain (decoded_poly ct0) m0 inverse0)).
   call(rrec_finish_functional (decoded_poly ct0) m0 inverse0).
   call(rrec_trit_functional m0); call(pke_decoder_functional witness ct0).
   auto=> />; by rewrite /rrec_using_inverse_spec hc hm.
 + call(pke_decoder_functional witness ct0); auto=> />; by rewrite /encap_status hc.
 rcondf 4.
 + call(rrec_trit_functional m0); call(pke_decoder_functional witness ct0); auto.
 call(rrec_trit_functional m0); call(pke_decoder_functional witness ct0).
 auto=> />; by rewrite /rrec_using_inverse_spec hc hm.
qed.

lemma rrec_functional pk0 m0 ct0 :
 hoare[RRec.run : pk=pk0 /\ m=m0 /\ ct=ct0 ==> res=rrec_spec pk0 m0 ct0].
proof.
 case(encap_key_canonical pk0)=>hk; last first.
 + proc; rcondf 3.
   - call(pke_decoder_functional witness pk0); auto=> />; rewrite /encap_status hk; smt(W32.to_uint0 W32.to_uint1).
   call(pke_decoder_functional witness pk0); auto=> />; by rewrite /rrec_spec hk.
 have hq:in_qrange768(decoded_poly pk0).
 + exact(encap_pointwise_blocks _ (candidate_canonical_decoder_qrange pk0 hk)).
 proc; rcondt 3.
 + call(pke_decoder_functional witness pk0); auto=> />; by rewrite /encap_status hk.
 seq 3 : (pk=pk0 /\ m=m0 /\ ct=ct0 /\ result=None /\
 inverse=rrec_public_inverse(decoded_poly pk0)).
 + call(rrec_public_inverse_functional (decoded_poly pk0) hq).
   call(pke_decoder_functional witness pk0); auto.
 if.
 + call(rrec_using_inverse_functional pk0 m0 ct0 (oget(rrec_public_inverse(decoded_poly pk0)))).
   auto=> />; rewrite /rrec_spec hk; smt().
 auto=> />; rewrite /rrec_spec hk; smt().
qed.
lemma rrec_correct pk0 m0 ct0 :
 phoare[RRec.run : pk=pk0 /\ m=m0 /\ ct=ct0 ==> res=rrec_spec pk0 m0 ct0]=1%r.
proof. by conseq rrec_lossless (rrec_functional pk0 m0 ct0). qed.

(* This is the arbitrary-ciphertext direction. It assumes neither an
   honest encryption nor a valid generated key nor a no-wrap event. *)
lemma rrec_sound pk0 m0 ct0 :
 hoare[RRec.run : pk=pk0 /\ m=m0 /\ ct=ct0 ==>
 forall r, res=Some r => pke_domain m0 /\ pke_domain r /\ pke_enc_spec pk0 m0 r=Some ct0].
proof.
 conseq(rrec_functional pk0 m0 ct0)=> /> &hr r hs.
 exact(rrec_spec_sound _ _ _ _ hs).
qed.
lemma rrec_sound_correct pk0 m0 ct0 :
 phoare[RRec.run : pk=pk0 /\ m=m0 /\ ct=ct0 ==>
 forall r, res=Some r => pke_domain m0 /\ pke_domain r /\ pke_enc_spec pk0 m0 r=Some ct0]=1%r.
proof. by conseq rrec_lossless (rrec_sound pk0 m0 ct0). qed.
lemma rrec_reencrypt_correct pk0 m0 ct0 r0 : rrec_spec pk0 m0 ct0=Some r0 =>
 phoare[PKEEnc.run : pk=pk0 /\ m=m0 /\ r=r0 ==>res=Some ct0]=1%r.
proof.
 move=>hs; have [hm [hr he]]:=rrec_spec_sound pk0 m0 ct0 r0 hs.
 rewrite -he; exact(pke_enc_correct pk0 m0 r0 hm hr).
qed.
lemma rrec_reject_key pk0 m0 ct0 : !encap_key_canonical pk0 =>
 phoare[RRec.run : pk=pk0 /\ m=m0 /\ ct=ct0 ==>res=None]=1%r.
proof.
 move=>hk; rewrite -(rrec_spec_reject_key pk0 m0 ct0 hk).
 exact(rrec_correct pk0 m0 ct0).
qed.
lemma rrec_reject_cipher pk0 m0 ct0 : !encap_key_canonical ct0 =>
 phoare[RRec.run : pk=pk0 /\ m=m0 /\ ct=ct0 ==>res=None]=1%r.
proof.
 move=>hc; rewrite -(rrec_spec_reject_cipher pk0 m0 ct0 hc).
 exact(rrec_correct pk0 m0 ct0).
qed.
lemma rrec_reject_message pk0 m0 ct0 : !pke_domain m0 =>
 phoare[RRec.run : pk=pk0 /\ m=m0 /\ ct=ct0 ==>res=None]=1%r.
proof.
 move=>hm.
 have he:rrec_spec pk0 m0 ct0=None.
 + rewrite /rrec_spec /=; case(encap_key_canonical pk0)=>hk //=.
   case(rrec_public_inverse(decoded_poly pk0)=None)=>hi //=.
   by rewrite /rrec_using_inverse_spec hm.
 rewrite -he; exact(rrec_correct pk0 m0 ct0).
qed.
lemma rrec_finish_reject cp0 m0 inverse0 : !pke_domain(rrec_candidate cp0 m0 inverse0) =>
 phoare[RRecFinish.run : cp=cp0 /\ m=m0 /\ inverse=inverse0 ==>res=None]=1%r.
proof.
 move=>hn.
 have he:rrec_finish_spec cp0 m0 inverse0=None by rewrite /rrec_finish_spec hn.
 rewrite -he; by conseq rrec_finish_lossless (rrec_finish_functional cp0 m0 inverse0).
qed.

require import NTRUPlus768KeygenCompleteProof NTRUPlus768RRecAlgebra.

(* Forward randomness recovery does not use the secret-product no-wrap
   event. Both m and r range over the full ternary polynomial domain. *)
lemma rrec_public_forward_correct pk0 m0 r0 :
 encap_key_canonical pk0 => rrec_public_inverse(decoded_poly pk0)<>None =>
 pke_domain m0 => pke_domain r0 =>
 phoare[RRec.run : pk=pk0 /\ m=m0 /\ ct=pke_ciphertext pk0 m0 r0 ==>
 res=Some r0]=1%r.
proof.
 move=>hk hi hm hr.
 have he:=rrec_public_forward pk0 m0 r0 hk hi hm hr.
 rewrite -he; exact(rrec_correct pk0 m0 (pke_ciphertext pk0 m0 r0)).
qed.
lemma rrec_keyed_forward_correct w m0 r0 :
 pke_key_relation w => pke_domain m0 => pke_domain r0 =>
 phoare[RRec.run : pk=w.`kg_pk /\ m=m0 /\ ct=pke_ciphertext w.`kg_pk m0 r0 ==>
 res=Some r0]=1%r.
proof.
 move=>hk hm hr.
 have he:=rrec_keyed_forward w m0 r0 hk hm hr.
 rewrite -he; exact(rrec_correct w.`kg_pk m0 (pke_ciphertext w.`kg_pk m0 r0)).
qed.
