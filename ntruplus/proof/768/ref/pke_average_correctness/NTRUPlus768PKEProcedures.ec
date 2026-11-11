require import AllCore Distr.
from Jasmin require import JWord.
require import Array768 Array1152.
require import NTRUPlus768NTT NTRUPlus768NTTProof.
require import NTRUPlus768PolyBasemul NTRUPlus768PolyBasemulProof.
require import NTRUPlus768PolyCenteredAdd NTRUPlus768PolyCenteredAddCorrectness.
require import NTRUPlus768PolyToBytes NTRUPlus768PolyToBytesProof.
require import NTRUPlus768PolyFromBytesChecked NTRUPlus768PolyFromBytesCheckedProof.
require import NTRUPlus768DecapCandidate NTRUPlus768DecapCandidateProof.

(* Array-value compositions of existing extracted kernels, not new native
   exported procedures. Scratch destinations are explicit witness arrays;
   the existing kernel contracts establish their fully written outputs.
   This boundary makes no additional native-storage or erasure claim. *)
module PKEEncBody = {
 proc run(hp:W16.t Array768.t,m:W16.t Array768.t,r:W16.t Array768.t) : W8.t Array1152.t = {
  var rhat,mhat,product,cipher:W16.t Array768.t;
  var ct:W8.t Array1152.t;
  rhat <@ NTRUPlus768NTT.M.jade_ntruplus_ntruplus768_amd64_ref_ntt(witness,r);
  mhat <@ NTRUPlus768NTT.M.jade_ntruplus_ntruplus768_amd64_ref_ntt(witness,m);
  product <@ NTRUPlus768PolyBasemul.M.jade_ntruplus_ntruplus768_amd64_ref_poly_basemul(witness,hp,rhat);
  cipher <@ NTRUPlus768PolyCenteredAdd.M.jade_ntruplus_ntruplus768_amd64_ref_poly_centered_add(witness,product,mhat);
  ct <@ NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes(witness,cipher);
  return ct;
 }
}.
module PKEEnc = {
 proc run(pk:W8.t Array1152.t,m:W16.t Array768.t,r:W16.t Array768.t) : W8.t Array1152.t option = {
  var hp:W16.t Array768.t; var status:W32.t;
  var ct:W8.t Array1152.t; var result:W8.t Array1152.t option;
  result <- None;
  (hp,status) <@ NTRUPlus768PolyFromBytesChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes(witness,pk);
  if(status=W32.zero){
   ct <@ PKEEncBody.run(hp,m,r);
   result <- Some ct;
  }
  return result;
 }
}.

(* The underlying PKE needs only the serialized f component of the secret
   key. Both byte arrays pass the actual checked decoder before candidate
   multiplication, inverse NTT, and centered reduction modulo three. *)
module PKEDec = {
 proc run(ct:W8.t Array1152.t,fbytes:W8.t Array1152.t) : W16.t Array768.t option = {
  var cp,fp,recovered:W16.t Array768.t; var status:W32.t;
  var result:W16.t Array768.t option;
  result <- None;
  (cp,status) <@ NTRUPlus768PolyFromBytesChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes(witness,ct);
  if(status=W32.zero){
   (fp,status) <@ NTRUPlus768PolyFromBytesChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes(witness,fbytes);
   if(status=W32.zero){
    recovered <@ NTRUPlus768DecapCandidate.M.jade_ntruplus_ntruplus768_amd64_ref_decap_candidate(witness,cp,fp);
    result <- Some recovered;
   }
  }
  return result;
 }
}.

lemma pke_enc_body_lossless : islossless PKEEncBody.run.
proof.
 proc; call poly_tobytes_lossless; call poly_centered_add_lossless;
 call poly_basemul_lossless; call ntt_lossless; call ntt_lossless; auto.
qed.
lemma pke_enc_lossless : islossless PKEEnc.run.
proof.
 proc; seq 2:true; 1,4,5:by auto.
 + call poly_frombytes_checked_lossless; auto.
 if; last by auto.
 wp; call pke_enc_body_lossless; auto.
qed.
lemma pke_dec_lossless : islossless PKEDec.run.
proof.
 proc; seq 2:true; 1,4,5:by auto.
 + call poly_frombytes_checked_lossless; auto.
 if; last by auto.
 seq 1:true; 1,4,5:by auto.
 + call poly_frombytes_checked_lossless; auto.
 if; last by auto.
 wp; call decap_candidate_lossless; auto.
qed.
