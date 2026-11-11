require import AllCore Distr.
from Jasmin require import JWord.
require import Array768 Array1152.
require import NTRUPlus768PolyFromBytesChecked NTRUPlus768PolyFromBytesCheckedProof.
require import NTRUPlus768RRecPublicInverse NTRUPlus768RRecWordChecks NTRUPlus768RRecProcedures.

(* Internal helper: its inverse is computed from the public key by the
   caller below. RRecFinish retains actual DecapR2, inverse NTT, centering,
   and the trit check. No PKE re-encryption call occurs here. *)
module LinearRRecUsingInverse = {
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
   }
  }
  return result;
 }
}.

(* Public input is exactly (pk,m,ct). This is an array-level composition
   of existing kernels and model glue, not a new native exported API or
   a claim that the original Decaps caller executes this whole procedure. *)
module LinearRRec = {
 proc run(pk:W8.t Array1152.t,m:W16.t Array768.t,ct:W8.t Array1152.t) : W16.t Array768.t option = {
  var hp:W16.t Array768.t; var status:W32.t;
  var inverse,result:W16.t Array768.t option;
  result <- None;
  (hp,status) <@ NTRUPlus768PolyFromBytesChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes(witness,pk);
  if(status=W32.zero){
   inverse <@ RRecPublicInverse.run(hp);
   if(inverse<>None){
    result <@ LinearRRecUsingInverse.run(pk,m,ct,oget inverse);
   }
  }
  return result;
 }
}.
lemma linear_rrec_using_inverse_lossless : islossless LinearRRecUsingInverse.run.
proof.
 proc; seq 2:true; 1,4,5:by auto.
 + call poly_frombytes_checked_lossless; auto.
 if; last by auto.
 seq 1:true; 1,4,5:by auto.
 + call rrec_trit_lossless; auto.
 if; last by auto.
 call rrec_finish_lossless; auto.
qed.
lemma linear_rrec_lossless : islossless LinearRRec.run.
proof.
 proc; seq 2:true; 1,4,5:by auto.
 + call poly_frombytes_checked_lossless; auto.
 if; last by auto.
 seq 1:true; 1,4,5:by auto.
 + call rrec_public_inverse_lossless; auto.
 if; last by auto.
 call linear_rrec_using_inverse_lossless; auto.
qed.
