require import AllCore Distr.
from Jasmin require import JWord.
require import Array768 Array1152.
require import NTRUPlus768MRecModel NTRUPlus768MRecProof NTRUPlus768PKEModel.
require import NTRUPlus768RRecWordChecks NTRUPlus768RRecCodec NTRUPlus768RRecTransform NTRUPlus768RRecSerialization.
require import NTRUPlus768CanonicalDecoder NTRUPlus768EncapGuardSpec NTRUPlus768InvNTTProof NTRUPlus768InvNTTAlgebra.
require import NTRUPlus768KeygenSecretFBridge NTRUPlus768KeygenPublicKeyBridge NTRUPlus768R2Serialization.
require import NTRUPlus768KEMPayloadSpec NTRUPlus768RRecAlgebra NTRUPlus768PolyToBytesAlgebra.
require import NTRUPlus768ValidKeyR2Recovery NTRUPlus768PolyFromBytesChecked NTRUPlus768InvNTT.
require import NTRUPlus768PolyFromBytesCheckedProof NTRUPlus768PKECallProof.

(* A G input is decoded by the inverse transform, not by enumeration of
   the ternary image. Canonical bytes and a ternary result are sufficient
   for exact re-encoding; the theorem below proves that fact. *)
op [opaque] mrec_randomness_candidate (query:W8.t Array1152.t) : pke_poly =
 rrec_normalize(invntt_spec(rrec_normalize(decoded_poly query))).
op [opaque] mrec_decode_randomness (query:W8.t Array1152.t) : pke_poly option =
 if encap_key_canonical query then
 let r=mrec_randomness_candidate query in if pke_domain r then Some r else None
 else None.

lemma mrec_randomness_reencode query : encap_key_canonical query=>pke_domain(mrec_randomness_candidate query)=>
 rr_G_input(mrec_randomness_candidate query)=query.
proof.
 move=>hc hr.
 have he:rrec_normalize(inverse_invntt_spec(rrec_normalize(decoded_poly query)))=mrec_randomness_candidate query
 by rewrite /mrec_randomness_candidate invntt_specE.
 have hf:=rrec_inverse_forward_trit _ _ (mrec_normalize_shape _) hr he.
 have hm:poly_coeff_eq_mod_q(pke_rhat(mrec_randomness_candidate query))(decoded_poly query).
 + move=>j hj;by rewrite(hf j hj)(rrec_normalize_mod _ j hj).
 have hs:=rr_G_input_serializer _ hr.
 have hd:=in_qrange768_poly_tobytes_input_qrange _ (rrec_public_key_range query hc).
 have hb:=poly_tobytes_mod_q_congr _ _ hs hd hm.
 by rewrite /rr_G_input hb (rrec_canonical_reencode query hc).
qed.
lemma mrec_decode_randomness_sound query r : mrec_decode_randomness query=Some r=>
 pke_domain r /\ query=rr_G_input r.
proof.
 rewrite /mrec_decode_randomness;case(encap_key_canonical query)=>hc //;rewrite /=.
 case(pke_domain(mrec_randomness_candidate query))=>hr //.
 move=>/someI he;subst r;split;first exact hr.
 apply/eq_sym;exact(mrec_randomness_reencode query hc hr).
qed.
lemma mrec_randomness_forward r : pke_domain r=>mrec_randomness_candidate(rr_G_input r)=r.
proof.
 move=>hr;rewrite /mrec_randomness_candidate invntt_specE.
 apply(rrec_normalized_inverse_recovers _ r (mrec_normalize_shape _) hr).
 have hd:poly_coeff_eq_mod_q(decoded_poly(rr_G_input r))(pke_rhat r).
 + rewrite /rr_G_input;exact(r2_serialized_decode_mod_q _ (rr_G_input_serializer r hr)).
 move=>j hj;by rewrite(rrec_normalize_mod _ j hj)(hd j hj).
qed.
lemma mrec_decode_randomness_forward r : pke_domain r=>mrec_decode_randomness(rr_G_input r)=Some r.
proof.
 move=>hr;have hc:encap_key_canonical(rr_G_input r).
 + rewrite /rr_G_input;exact(payload_serialized_canonical _ (rr_G_input_serializer r hr)).
 by rewrite /mrec_decode_randomness hc /= (mrec_randomness_forward r hr) hr.
qed.
lemma mrec_decode_randomness_iff query r :
 mrec_decode_randomness query=Some r <=> pke_domain r /\ query=rr_G_input r.
proof.
 split;first exact(mrec_decode_randomness_sound query r).
 move=>[hr ->];exact(mrec_decode_randomness_forward r hr).
qed.

module MRecDecodeCandidate = {
 proc run(cp:pke_poly) : pke_poly = {
  var centered,inverse,r:pke_poly;
  centered<@RRecNormalize.run(cp);
  inverse<@NTRUPlus768InvNTT.M.jade_ntruplus_ntruplus768_amd64_ref_invntt(witness,centered);
  r<@RRecNormalize.run(inverse);return r;
 }
}.
module MRecDecode = {
 proc run(query:W8.t Array1152.t) : pke_poly option = {
  var cp,r:pke_poly;var status:W32.t;var valid:bool;var result:pke_poly option;
  result<-None;
  (cp,status)<@NTRUPlus768PolyFromBytesChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes(witness,query);
  if(status=W32.zero){
   r<@MRecDecodeCandidate.run(cp);valid<@RRecTrit.check(r);
   if(valid){result<-Some r;}
  }
  return result;
 }
}.
lemma mrec_decode_candidate_ll : islossless MRecDecodeCandidate.run.
proof. proc;call rrec_normalize_lossless;call invntt_lossless;call rrec_normalize_lossless;auto. qed.
lemma mrec_decode_candidate_functional query0 :
 hoare[MRecDecodeCandidate.run:cp=decoded_poly query0 ==>res=mrec_randomness_candidate query0].
proof.
 proc;call(rrec_normalize_functional(invntt_spec(rrec_normalize(decoded_poly query0)))).
 call(invntt_functional witness(rrec_normalize(decoded_poly query0))).
 call(rrec_normalize_functional(decoded_poly query0)).
 auto=> />;by rewrite /mrec_randomness_candidate.
qed.
lemma mrec_decode_ll : islossless MRecDecode.run.
proof.
 proc;seq 2:true;1,4,5:by auto.
 + call poly_frombytes_checked_lossless;auto.
 if;last by auto.
 seq 2:true;1,4,5:by auto.
 + call rrec_trit_lossless;call mrec_decode_candidate_ll;auto.
 if;auto.
qed.
lemma mrec_decode_functional query0 :
 hoare[MRecDecode.run:query=query0 ==>res=mrec_decode_randomness query0].
proof.
 case(encap_key_canonical query0)=>hc;last first.
 + proc;rcondf 3.
   - call(pke_decoder_functional witness query0);auto=> />;rewrite /encap_status hc;smt(W32.to_uint0 W32.to_uint1).
   call(pke_decoder_functional witness query0);auto=> />;by rewrite /mrec_decode_randomness hc.
 proc;rcondt 3.
 + call(pke_decoder_functional witness query0);auto=> />;by rewrite /encap_status hc.
 seq 4:(query=query0 /\ r=mrec_randomness_candidate query0 /\
 valid=pke_domain(mrec_randomness_candidate query0) /\ result=None).
 + call(rrec_trit_functional(mrec_randomness_candidate query0));call(mrec_decode_candidate_functional query0);
   call(pke_decoder_functional witness query0);auto.
 if;auto=> />;rewrite /mrec_decode_randomness hc /=;smt().
qed.
lemma mrec_decode_correct query0 :
 phoare[MRecDecode.run:query=query0 ==>res=mrec_decode_randomness query0]=1%r.
proof. by conseq mrec_decode_ll (mrec_decode_functional query0). qed.
