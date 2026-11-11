require import AllCore Distr.
from Jasmin require import JWord.
require import Array768 Array1152.
require import NTRUPlus768CanonicalDecoder NTRUPlus768EncapGuardSpec.
require import NTRUPlus768BasemulAlgebra NTRUPlus768PolyBasemulAlgebra.
require import NTRUPlus768DecapCandidateAlgebra NTRUPlus768EncapCompleteAlgebra.
require import NTRUPlus768PKEModel NTRUPlus768PKECallProof NTRUPlus768KeygenCompleteProof.
require import NTRUPlus768RRecWordChecks NTRUPlus768RRecPublicInverse.
require import NTRUPlus768RRecModel NTRUPlus768RRecAlgebra NTRUPlus768RRecProcedures NTRUPlus768RRecCallProof.
require import NTRUPlus768RRecLinearModel NTRUPlus768RRecLinearProcedures.

lemma linear_rrec_using_inverse_functional pk0 m0 ct0 inverse0 :
 hoare[LinearRRecUsingInverse.run:pk=pk0 /\ m=m0 /\ ct=ct0 /\ inverse=inverse0 ==>
 res=rrec_linear_using_inverse_spec pk0 m0 ct0 inverse0].
proof.
 case(encap_key_canonical ct0)=>hc; last first.
 + proc; rcondf 3.
   - call(pke_decoder_functional witness ct0); auto=> />; rewrite /encap_status hc; smt(W32.to_uint0 W32.to_uint1).
   call(pke_decoder_functional witness ct0); auto=> />; by rewrite /rrec_linear_using_inverse_spec hc.
 case(pke_domain m0)=>hm; proc; rcondt 3.
 + call(pke_decoder_functional witness ct0); auto=> />; by rewrite /encap_status hc.
 + rcondt 4.
   - call(rrec_trit_functional m0); call(pke_decoder_functional witness ct0); auto.
   call(rrec_finish_functional (decoded_poly ct0) m0 inverse0).
   call(rrec_trit_functional m0); call(pke_decoder_functional witness ct0).
   auto=> />; by rewrite /rrec_linear_using_inverse_spec hc hm.
 + call(pke_decoder_functional witness ct0); auto=> />; by rewrite /encap_status hc.
 rcondf 4.
 + call(rrec_trit_functional m0); call(pke_decoder_functional witness ct0); auto.
 call(rrec_trit_functional m0); call(pke_decoder_functional witness ct0).
 auto=> />; by rewrite /rrec_linear_using_inverse_spec hc hm.
qed.
lemma linear_rrec_functional pk0 m0 ct0 :
 hoare[LinearRRec.run:pk=pk0 /\ m=m0 /\ ct=ct0 ==>res=rrec_linear_spec pk0 m0 ct0].
proof.
 case(encap_key_canonical pk0)=>hk; last first.
 + proc; rcondf 3.
   - call(pke_decoder_functional witness pk0); auto=> />; rewrite /encap_status hk; smt(W32.to_uint0 W32.to_uint1).
   call(pke_decoder_functional witness pk0); auto=> />; by rewrite /rrec_linear_spec hk.
 have hq:in_qrange768(decoded_poly pk0).
 + exact(encap_pointwise_blocks _ (candidate_canonical_decoder_qrange pk0 hk)).
 proc; rcondt 3.
 + call(pke_decoder_functional witness pk0); auto=> />; by rewrite /encap_status hk.
 seq 3:(pk=pk0 /\ m=m0 /\ ct=ct0 /\ result=None /\ inverse=rrec_public_inverse(decoded_poly pk0)).
 + call(rrec_public_inverse_functional (decoded_poly pk0) hq).
   call(pke_decoder_functional witness pk0); auto.
 if.
 + call(linear_rrec_using_inverse_functional pk0 m0 ct0 (oget(rrec_public_inverse(decoded_poly pk0)))).
   auto=> />; rewrite /rrec_linear_spec hk; smt().
 auto=> />; rewrite /rrec_linear_spec hk; smt().
qed.
lemma linear_rrec_correct pk0 m0 ct0 :
 phoare[LinearRRec.run:pk=pk0 /\ m=m0 /\ ct=ct0 ==>res=rrec_linear_spec pk0 m0 ct0]=1%r.
proof. by conseq linear_rrec_lossless (linear_rrec_functional pk0 m0 ct0). qed.
lemma linear_rrec_invalid_key pk0 m0 ct0 : !encap_key_canonical pk0 =>
 phoare[LinearRRec.run:pk=pk0 /\ m=m0 /\ ct=ct0 ==>res=None]=1%r.
proof.
 move=>h; rewrite -(rrec_linear_reject_key pk0 m0 ct0 h); exact(linear_rrec_correct pk0 m0 ct0).
qed.
lemma linear_rrec_invalid_cipher pk0 m0 ct0 : !encap_key_canonical ct0 =>
 phoare[LinearRRec.run:pk=pk0 /\ m=m0 /\ ct=ct0 ==>res=None]=1%r.
proof.
 move=>h; rewrite -(rrec_linear_reject_cipher pk0 m0 ct0 h); exact(linear_rrec_correct pk0 m0 ct0).
qed.
lemma linear_rrec_invalid_message pk0 m0 ct0 : !pke_domain m0 =>
 phoare[LinearRRec.run:pk=pk0 /\ m=m0 /\ ct=ct0 ==>res=None]=1%r.
proof.
 move=>h; rewrite -(rrec_linear_reject_message pk0 m0 ct0 h); exact(linear_rrec_correct pk0 m0 ct0).
qed.
lemma linear_rrec_missing_inverse pk0 m0 ct0 : rrec_public_inverse(decoded_poly pk0)=None =>
 phoare[LinearRRec.run:pk=pk0 /\ m=m0 /\ ct=ct0 ==>res=None]=1%r.
proof.
 move=>h; rewrite -(rrec_linear_reject_inverse pk0 m0 ct0 h); exact(linear_rrec_correct pk0 m0 ct0).
qed.

lemma linear_rrec_keyed_forward w m0 r0 : pke_key_relation w =>pke_domain m0 =>pke_domain r0 =>
 phoare[LinearRRec.run:pk=w.`kg_pk /\ m=m0 /\ ct=pke_ciphertext w.`kg_pk m0 r0 ==>res=Some r0]=1%r.
proof.
 move=>hk hm hr.
 have he:=rrec_linear_from_checked _ _ _ _ (rrec_keyed_forward w m0 r0 hk hm hr).
 rewrite -he; exact(linear_rrec_correct w.`kg_pk m0 (pke_ciphertext w.`kg_pk m0 r0)).
qed.

require import NTRUPlus768RRecLinearAlgebra.

(* Positive guards make the public inverse a unit. Every trit candidate
   then passes re-encryption algebraically; negative guards return None
   on both sides. No honest-ciphertext or no-wrap premise is used. *)
lemma rrec_linear_checked_equivalence pk m ct : rrec_linear_spec pk m ct=rrec_spec pk m ct.
proof.
 rewrite /rrec_linear_spec /rrec_spec /=; case(encap_key_canonical pk)=>hp //=.
 case(rrec_public_inverse(decoded_poly pk)=None)=>hi //=.
 rewrite /rrec_linear_using_inverse_spec /rrec_using_inverse_spec.
 case(encap_key_canonical ct /\ pke_domain m)=>hc //=.
 move:hc=>[hct hm].
 case(pke_domain(rrec_candidate (decoded_poly ct) m (oget(rrec_public_inverse(decoded_poly pk)))))=>hr.
 + have he:=rrec_linear_candidate_reencrypt pk m ct hp hi hct hm hr.
   by rewrite /rrec_finish_spec hr /rrec_verify_spec /= he.
 by rewrite /rrec_finish_spec hr /rrec_verify_spec.
qed.
lemma linear_rrec_checked_correct pk0 m0 ct0 :
 phoare[LinearRRec.run:pk=pk0 /\ m=m0 /\ ct=ct0 ==>res=rrec_spec pk0 m0 ct0]=1%r.
proof.
 rewrite -(rrec_linear_checked_equivalence pk0 m0 ct0).
 exact(linear_rrec_correct pk0 m0 ct0).
qed.
lemma linear_rrec_actual_equiv :
 equiv[LinearRRec.run ~ RRec.run: ={pk,m,ct} ==> ={res}].
proof.
 proc*; ecall{1}(linear_rrec_checked_correct pk{1} m{1} ct{1}).
 ecall{2}(rrec_correct pk{2} m{2} ct{2}); auto.
qed.
lemma linear_rrec_event_probability &mem pk0 m0 ct0 (event:pke_poly option->bool) :
 Pr[LinearRRec.run(pk0,m0,ct0) @ &mem:event res]=
 Pr[RRec.run(pk0,m0,ct0) @ &mem:event res].
proof. byequiv linear_rrec_actual_equiv=> //. qed.
lemma linear_rrec_sound pk0 m0 ct0 :
 hoare[LinearRRec.run:pk=pk0 /\ m=m0 /\ ct=ct0 ==>
 forall r,res=Some r =>pke_domain m0 /\ pke_domain r /\ pke_enc_spec pk0 m0 r=Some ct0].
proof.
 conseq(linear_rrec_functional pk0 m0 ct0)=> /> &hr r hs.
 rewrite rrec_linear_checked_equivalence in hs.
 exact(rrec_spec_sound _ _ _ _ hs).
qed.

(* Requested generated-key specialization. Ciphertext and message are
   arbitrary here; guards are part of both public procedures. *)
lemma linear_rrec_generated_equiv w : pke_key_relation w =>
 equiv[LinearRRec.run ~ RRec.run:
 pk{1}=w.`kg_pk /\ pk{2}=w.`kg_pk /\ ={m,ct} ==> ={res}].
proof. move=>hk; conseq linear_rrec_actual_equiv=> />; smt(). qed.
