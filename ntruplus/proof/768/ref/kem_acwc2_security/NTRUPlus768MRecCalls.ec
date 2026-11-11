require import AllCore Distr.
from Jasmin require import JWord.
require import Array768 Array1152.
require import NTRUPlus768MRecModel NTRUPlus768MRecProof NTRUPlus768PKEModel NTRUPlus768PKECallProof.
require import NTRUPlus768RRecWordChecks NTRUPlus768CanonicalDecoder NTRUPlus768EncapGuardSpec.
require import NTRUPlus768NTTProof NTRUPlus768InvNTTProof NTRUPlus768PolySubProof.
require import NTRUPlus768PolyBasemulProof NTRUPlus768EncapCompleteBody NTRUPlus768DecapCandidateSpec.
require import NTRUPlus768PolyFromBytesCheckedProof.

lemma mrec_candidate_lossless : islossless MRecCandidate.run.
proof.
 proc;call rrec_normalize_lossless;call invntt_lossless;call rrec_normalize_lossless;
 call poly_sub_lossless;call poly_basemul_lossless;call ntt_lossless;auto.
qed.
lemma mrec_candidate_functional pk0 r0 ct0 :
 hoare[MRecCandidate.run:hp=decoded_poly pk0 /\ cp=decoded_poly ct0 /\ r=r0 ==>
 res=mrec_candidate pk0 r0 ct0].
proof.
 proc;call(rrec_normalize_functional(invntt_spec(mrec_difference pk0 r0 ct0))).
 call(invntt_functional witness(mrec_difference pk0 r0 ct0)).
 call(rrec_normalize_functional(poly_sub_spec(decoded_poly ct0)(pke_product pk0 r0))).
 call(poly_sub_functional witness(decoded_poly ct0)(pke_product pk0 r0)).
 call(encap_product_functional witness(decoded_poly pk0)(pke_rhat r0)).
 call(ntt_functional witness r0).
 skip;rewrite pke_rhatE pke_productE /mrec_candidate /mrec_difference;auto.
qed.
lemma mrec_candidate_correct pk0 r0 ct0 :
 phoare[MRecCandidate.run:hp=decoded_poly pk0 /\ cp=decoded_poly ct0 /\ r=r0 ==>
 res=mrec_candidate pk0 r0 ct0]=1%r.
proof. by conseq mrec_candidate_lossless (mrec_candidate_functional pk0 r0 ct0). qed.
lemma mrec_lossless : islossless MRec.run.
proof.
 proc;seq 4:true;1,4,5:by auto.
 + call rrec_trit_lossless;call poly_frombytes_checked_lossless;call poly_frombytes_checked_lossless;auto.
 if;last by auto.
 seq 2:true;1,4,5:by auto.
 + call rrec_trit_lossless;call mrec_candidate_lossless;auto.
 if;auto.
qed.
lemma mrec_status_zero pk : (encap_status pk=W32.zero)=encap_key_canonical pk.
proof.
 rewrite /encap_status;case(encap_key_canonical pk)=>hc //;smt(W32.to_uint0 W32.to_uint1).
qed.
lemma mrec_functional pk0 r0 ct0 :
 hoare[MRec.run:pk=pk0 /\ r=r0 /\ ct=ct0 ==>res=mrec_spec pk0 r0 ct0].
proof.
 proc;seq 4:(pk=pk0 /\ r=r0 /\ ct=ct0 /\ hp=decoded_poly pk0 /\ cp=decoded_poly ct0 /\
 hs=encap_status pk0 /\ cs=encap_status ct0 /\ valid=pke_domain r0 /\ result=None).
 + call(rrec_trit_functional r0);call(pke_decoder_functional witness ct0);
   call(pke_decoder_functional witness pk0);auto.
 if.
 + seq 2:(pk=pk0 /\ r=r0 /\ ct=ct0 /\ encap_key_canonical pk0 /\ encap_key_canonical ct0 /\
   pke_domain r0 /\ m=mrec_candidate pk0 r0 ct0 /\ valid=pke_domain(mrec_candidate pk0 r0 ct0) /\ result=None).
   - call(rrec_trit_functional(mrec_candidate pk0 r0 ct0));call(mrec_candidate_functional pk0 r0 ct0);
     auto=> />;smt(mrec_status_zero).
   if;auto=> />;rewrite /mrec_spec;smt().
 auto=> />;rewrite /mrec_spec;smt(mrec_status_zero).
qed.
lemma mrec_correct pk0 r0 ct0 :
 phoare[MRec.run:pk=pk0 /\ r=r0 /\ ct=ct0 ==>res=mrec_spec pk0 r0 ct0]=1%r.
proof. by conseq mrec_lossless (mrec_functional pk0 r0 ct0). qed.
lemma mrec_call_vcmr pk0 m0 r0 ct0 : encap_key_canonical pk0=>pke_domain m0=>pke_domain r0=>
 pke_enc_spec pk0 m0 r0=Some ct0=>
 phoare[MRec.run:pk=pk0 /\ r=r0 /\ ct=ct0 ==>res=Some m0]=1%r.
proof.
 move=>hp hm hr he;rewrite -(mrec_vcmr pk0 m0 r0 ct0 hp hm hr he).
 exact(mrec_correct pk0 r0 ct0).
qed.
