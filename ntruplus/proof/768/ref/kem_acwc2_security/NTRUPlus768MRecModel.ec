require import AllCore Distr.
from Jasmin require import JWord.
require import Array768 Array1152.
require import NTRUPlus768PKEModel NTRUPlus768CanonicalDecoder NTRUPlus768EncapGuardSpec.
require import NTRUPlus768RRecWordChecks NTRUPlus768PolySubProof NTRUPlus768InvNTTProof.
require import NTRUPlus768NTTProof NTRUPlus768DecapCandidateSpec.
require import NTRUPlus768PolyFromBytesChecked NTRUPlus768NTT NTRUPlus768PolyBasemul NTRUPlus768PolySub NTRUPlus768InvNTT.

(* Public message recovery computes c-h*r in the serialized NTT domain,
   normalizes its coefficients before inverse NTT, then accepts only a
   ternary result. No secret key, search, or re-encryption test is used. *)
op [opaque] mrec_difference (pk:W8.t Array1152.t) (r:pke_poly) (ct:W8.t Array1152.t) : pke_poly =
 rrec_normalize(poly_sub_spec (decoded_poly ct) (pke_product pk r)).
op [opaque] mrec_candidate pk r ct : pke_poly =
 rrec_normalize(invntt_spec(mrec_difference pk r ct)).
op [opaque] mrec_spec (pk:W8.t Array1152.t) (r:pke_poly) (ct:W8.t Array1152.t) : pke_poly option =
 if encap_key_canonical pk /\ encap_key_canonical ct /\ pke_domain r then
 let m=mrec_candidate pk r ct in if pke_domain m then Some m else None
 else None.

(* Fixed-size array composition of existing extracted kernels and the
   already verified centering/trit-check loops; no new native exported API
   is claimed by this public reduction procedure. *)
module MRecCandidate = {
 proc run(hp cp r:pke_poly) : pke_poly = {
  var rh,product,difference,centered,inverse,result:pke_poly;
  rh<@NTRUPlus768NTT.M.jade_ntruplus_ntruplus768_amd64_ref_ntt(witness,r);
  product<@NTRUPlus768PolyBasemul.M.jade_ntruplus_ntruplus768_amd64_ref_poly_basemul(witness,hp,rh);
  difference<@NTRUPlus768PolySub.M.jade_ntruplus_ntruplus768_amd64_ref_poly_sub(witness,cp,product);
  centered<@RRecNormalize.run(difference);
  inverse<@NTRUPlus768InvNTT.M.jade_ntruplus_ntruplus768_amd64_ref_invntt(witness,centered);
  result<@RRecNormalize.run(inverse);
  return result;
 }
}.
module MRec = {
 proc run(pk:W8.t Array1152.t,r:pke_poly,ct:W8.t Array1152.t) : pke_poly option = {
  var hp,cp,m:pke_poly;var hs,cs:W32.t;var valid:bool;var result:pke_poly option;
  result<-None;
  (hp,hs)<@NTRUPlus768PolyFromBytesChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes(witness,pk);
  (cp,cs)<@NTRUPlus768PolyFromBytesChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes(witness,ct);
  valid<@RRecTrit.check(r);
  if(hs=W32.zero /\ cs=W32.zero /\ valid){
   m<@MRecCandidate.run(hp,cp,r);
   valid<@RRecTrit.check(m);
   if(valid){result<-Some m;}
  }
  return result;
 }
}.

lemma mrec_spec_some pk r ct m : mrec_spec pk r ct=Some m=>
 encap_key_canonical pk /\ encap_key_canonical ct /\ pke_domain r /\
 pke_domain m /\ m=mrec_candidate pk r ct.
proof.
 rewrite /mrec_spec;case(encap_key_canonical pk /\ encap_key_canonical ct /\ pke_domain r)=>h //.
 case(pke_domain(mrec_candidate pk r ct))=>hm //;smt().
qed.
lemma mrec_spec_accept pk r ct : encap_key_canonical pk=>encap_key_canonical ct=>pke_domain r=>
 pke_domain(mrec_candidate pk r ct)=>mrec_spec pk r ct=Some(mrec_candidate pk r ct).
proof. move=>hp hc hr hm;by rewrite /mrec_spec hp hc hr /= hm. qed.
lemma mrec_spec_reject_key pk r ct : !encap_key_canonical pk=>mrec_spec pk r ct=None.
proof. move=>hp;by rewrite /mrec_spec hp. qed.
lemma mrec_spec_reject_cipher pk r ct : !encap_key_canonical ct=>mrec_spec pk r ct=None.
proof. move=>hc;by rewrite /mrec_spec hc /=. qed.
lemma mrec_spec_reject_randomness pk r ct : !pke_domain r=>mrec_spec pk r ct=None.
proof. move=>hr;by rewrite /mrec_spec hr /=. qed.
