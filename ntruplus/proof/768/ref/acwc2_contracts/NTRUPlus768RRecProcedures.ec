require import AllCore Distr.
from Jasmin require import JWord.
require import Array768 Array1152.
require import NTRUPlus768DecapR2Comp NTRUPlus768DecapR2CompSpec NTRUPlus768DecapR2CompProof.
require import NTRUPlus768InvNTT NTRUPlus768InvNTTProof.

(* An internal arithmetic composition. Its inverse argument is derived
   from the public key by the public caller below, never supplied as a
   recovery witness. No new native export or memory-layout claim is made. *)
module RRecCore = {
 proc run(cp:W16.t Array768.t,m:W16.t Array768.t,inverse:W16.t Array768.t) : W16.t Array768.t = {
  var rhat,raw:W16.t Array768.t;
  rhat <@ NTRUPlus768DecapR2Comp.M.jade_ntruplus_ntruplus768_amd64_ref_decap_r2(witness,cp,m,inverse);
  raw <@ NTRUPlus768InvNTT.M.jade_ntruplus_ntruplus768_amd64_ref_invntt(witness,rhat);
  return raw;
 }
}.
lemma rrec_core_lossless : islossless RRecCore.run.
proof. proc; call invntt_lossless; call decap_r2_lossless; auto. qed.
lemma rrec_core_functional cp0 m0 inverse0 :
 hoare[RRecCore.run : cp=cp0 /\ m=m0 /\ inverse=inverse0 ==>
 res=invntt_spec(decap_r2_spec cp0 m0 inverse0)].
proof.
 proc; call(invntt_functional witness (decap_r2_spec cp0 m0 inverse0)).
 call(decap_r2_functional witness cp0 m0 inverse0); auto.
qed.

require import NTRUPlus768PolyFromBytesChecked NTRUPlus768PolyFromBytesCheckedProof.
require import NTRUPlus768RRecPublicInverse NTRUPlus768RRecWordChecks.
require import NTRUPlus768PKEProcedures.

module RRecFinish = {
 proc run(cp:W16.t Array768.t,m:W16.t Array768.t,inverse:W16.t Array768.t) : W16.t Array768.t option = {
  var raw,candidate:W16.t Array768.t; var valid:bool;
  var result:W16.t Array768.t option;
  result <- None;
  raw <@ RRecCore.run(cp,m,inverse);
  candidate <@ RRecNormalize.run(raw);
  valid <@ RRecTrit.check(candidate);
  if(valid){ result <- Some candidate; }
  return result;
 }
}.

(* A single public consistency check, with no enumeration of randomness. *)
module RRecVerify = {
 proc run(pk:W8.t Array1152.t,m:W16.t Array768.t,ct:W8.t Array1152.t,
          candidate:W16.t Array768.t option) : W16.t Array768.t option = {
  var result:W16.t Array768.t option; var checked:W8.t Array1152.t option;
  result <- None;
  if(candidate<>None){
   checked <@ PKEEnc.run(pk,m,oget candidate);
   if(checked=Some ct){result<-candidate;}
  }
  return result;
 }
}.

module RRecUsingInverse = {
 proc run(pk:W8.t Array1152.t,m:W16.t Array768.t,ct:W8.t Array1152.t,
          inverse:W16.t Array768.t) : W16.t Array768.t option = {
  var cp:W16.t Array768.t; var status:W32.t; var valid_message:bool;
  var result:W16.t Array768.t option;
  result <- None;
  (cp,status) <@ NTRUPlus768PolyFromBytesChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes(witness,ct);
  if(status=W32.zero){
   valid_message <@ RRecTrit.check(m);
   if(valid_message){
    result <@ RRecFinish.run(cp,m,inverse);
    result <@ RRecVerify.run(pk,m,ct,result);
   }
  }
  return result;
 }
}.

(* Public randomness recovery has exactly the three public inputs below.
   The inverse is computed from the checked public key and canonicalized
   inside RRecPublicInverse. Neither a secret key nor a supplied inverse
   or an honest-encryption witness is an input to this procedure. *)
module RRec = {
 proc run(pk:W8.t Array1152.t,m:W16.t Array768.t,ct:W8.t Array1152.t) : W16.t Array768.t option = {
  var hp:W16.t Array768.t; var status:W32.t;
  var inverse,result:W16.t Array768.t option;
  result <- None;
  (hp,status) <@ NTRUPlus768PolyFromBytesChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes(witness,pk);
  if(status=W32.zero){
   inverse <@ RRecPublicInverse.run(hp);
   if(inverse<>None){
    result <@ RRecUsingInverse.run(pk,m,ct,oget inverse);
   }
  }
  return result;
 }
}.

lemma rrec_finish_lossless : islossless RRecFinish.run.
proof.
 proc; seq 4:true; 1,4,5:by auto.
 + call rrec_trit_lossless; call rrec_normalize_lossless; call rrec_core_lossless; auto.
 if; auto.
qed.
lemma rrec_verify_lossless : islossless RRecVerify.run.
proof.
 proc; sp; if; last by auto.
 seq 1:true; 1,4,5:by auto.
 + call pke_enc_lossless; auto.
 if; auto.
qed.
lemma rrec_using_inverse_lossless : islossless RRecUsingInverse.run.
proof.
 proc; seq 2:true; 1,4,5:by auto.
 + call poly_frombytes_checked_lossless; auto.
 if; last by auto.
 seq 1:true; 1,4,5:by auto.
 + call rrec_trit_lossless; auto.
 if; last by auto.
 call rrec_verify_lossless; call rrec_finish_lossless; auto.
qed.
lemma rrec_lossless : islossless RRec.run.
proof.
 proc; seq 2:true; 1,4,5:by auto.
 + call poly_frombytes_checked_lossless; auto.
 if; last by auto.
 seq 1:true; 1,4,5:by auto.
 + call rrec_public_inverse_lossless; auto.
 if; last by auto.
 call rrec_using_inverse_lossless; auto.
qed.
