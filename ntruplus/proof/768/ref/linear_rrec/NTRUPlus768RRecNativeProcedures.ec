require import AllCore Distr.
from Jasmin require import JWord.
require import Array32 Array96 Array129 Array192 Array224 Array768 Array1152 Array2336 Array13506.
require import NTRUPlus768PKEModel NTRUPlus768PKEProcedures.
require import NTRUPlus768DecapCompleteSpec NTRUPlus768DecapCompleteHash NTRUPlus768DecapCompleteTailProof.
require import NTRUPlus768DecapCompleteProof NTRUPlus768DecapMessageSpec NTRUPlus768DecapMessageProof NTRUPlus768DecapR2CompCaller.
require import NTRUPlus768DecapHashHPrepare NTRUPlus768DecapHashHPrepareProof.
require import NTRUPlus768PolyCBD1Checked NTRUPlus768PolyCBD1CheckedProof.
require import NTRUPlus768NTT NTRUPlus768NTTProof NTRUPlus768PolyToBytes NTRUPlus768PolyToBytesProof.
require import NTRUPlus768DecapFinish NTRUPlus768DecapFinishCorrectness.
require import NTRUPlus768DecapClear NTRUPlus768DecapClearProof NTRUPlus768EncapGuardSpec.

(* Proof-facing array compositions of existing kernels. The outlined old
   body is connected to CompleteTail; it is not a replacement native export. *)
module NativeRegenerateFinish = {
 proc run(recovered:W8.t Array1152.t,hashout:W8.t Array224.t,decode_fail:W32.t)
   : W8.t Array32.t * W32.t = {
  var r1,r1ntt:pke_poly; var regenerated:W8.t Array1152.t;
  var ss:W8.t Array32.t; var status:W32.t;
  r1 <@ NTRUPlus768PolyCBD1Checked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(witness,complete_hash_tail hashout);
  r1ntt <@ NTRUPlus768NTT.M.jade_ntruplus_ntruplus768_amd64_ref_ntt(witness,r1);
  regenerated <@ NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes(witness,r1ntt);
  (ss,status) <@ NTRUPlus768DecapFinish.M.jade_ntruplus_ntruplus768_amd64_ref_decap_finish(witness,hashout,recovered,regenerated,decode_fail);
  return(ss,status);
 }
}.
module NativeTailOutlined(H:CompleteSHAKEH) = {
 proc run(recovered:W8.t Array1152.t,msg:W8.t Array96.t,
   decode_fail:W32.t,suffix:W8.t Array32.t) : W8.t Array32.t * W32.t = {
  var input:W8.t Array129.t; var hashout:W8.t Array224.t;
  var result:W8.t Array32.t * W32.t;
  input <@ NTRUPlus768DecapHashHPrepare.M.jade_ntruplus_ntruplus768_amd64_ref_decap_hash_h_prepare(witness,msg,suffix);
  hashout <@ H.shake(input);
  result <@ NativeRegenerateFinish.run(recovered,hashout,decode_fail);
  return result;
 }
}.
module ReencryptFinish = {
 proc run(pk ct:W8.t Array1152.t,m1:pke_poly,hashout:W8.t Array224.t,decode_fail:W32.t)
   : W8.t Array32.t * W32.t = {
  var r1:pke_poly; var ct2:W8.t Array1152.t option;
  var ss:W8.t Array32.t; var status:W32.t;
  r1 <@ NTRUPlus768PolyCBD1Checked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(witness,complete_hash_tail hashout);
  ct2 <@ PKEEnc.run(pk,m1,r1);
  ss <- encap_zero_ss; status <- W32.one;
  if(ct2<>None){
   (ss,status) <@ NTRUPlus768DecapFinish.M.jade_ntruplus_ntruplus768_amd64_ref_decap_finish(witness,hashout,ct,oget ct2,decode_fail);
  }
  return(ss,status);
 }
}.
module ReencryptTail(H:CompleteSHAKEH) = {
 proc run(pk ct:W8.t Array1152.t,m1:pke_poly,msg:W8.t Array96.t,
   decode_fail:W32.t,suffix:W8.t Array32.t) : W8.t Array32.t * W32.t = {
  var input:W8.t Array129.t; var hashout:W8.t Array224.t;
  var result:W8.t Array32.t * W32.t;
  input <@ NTRUPlus768DecapHashHPrepare.M.jade_ntruplus_ntruplus768_amd64_ref_decap_hash_h_prepare(witness,msg,suffix);
  hashout <@ H.shake(input);
  result <@ ReencryptFinish.run(pk,ct,m1,hashout,decode_fail);
  return result;
 }
}.
module ReencryptCore(G:MessageSHAKE,H:CompleteSHAKEH) = {
 proc run(pk ct:W8.t Array1152.t,sk:W8.t Array2336.t) : W8.t Array32.t * W32.t = {
  var rp,mp:pke_poly; var ss:W8.t Array32.t; var status:W32.t;
  var bs:W8.t Array1152.t; var msg:W8.t Array96.t;
  (rp,mp,ss,status) <@ GuardedR2.run(witness,witness,witness,witness,witness,encap_zero_ss,ct,complete_sk_poly sk);
  if(status=W32.zero){
   (bs,msg,status) <@ DecapMessage(G).run(witness,witness,witness,rp,mp);
   (ss,status) <@ ReencryptTail(H).run(pk,ct,mp,msg,status,complete_sk_suffix sk);
  }
  return(ss,status);
 }
}.
module ReencryptDecaps(G:MessageSHAKE,H:CompleteSHAKEH) = {
 proc run(pk ct:W8.t Array1152.t,sk:W8.t Array2336.t,workspace:W8.t Array13506.t)
   : W8.t Array32.t * W32.t * W8.t Array13506.t = {
  var ss:W8.t Array32.t; var status:W32.t;
  (ss,status) <@ ReencryptCore(G,H).run(pk,ct,sk);
  workspace <@ NTRUPlus768DecapClear.M.jade_ntruplus_ntruplus768_amd64_ref_decap_clear(workspace);
  return(ss,status,workspace);
 }
}.

lemma native_regenerate_finish_lossless : islossless NativeRegenerateFinish.run.
proof. proc; call finish_ll; call poly_tobytes_lossless; call ntt_lossless; call poly_cbd1_lossless; auto. qed.
lemma native_tail_outlined_lossless (H<:CompleteSHAKEH) :
 islossless H.shake => islossless NativeTailOutlined(H).run.
proof. move=>hH; proc; call native_regenerate_finish_lossless; call hH; call hash_h_prepare_lossless; auto. qed.
lemma reencrypt_finish_lossless : islossless ReencryptFinish.run.
proof.
 proc; seq 4:true; 1,4,5:by auto.
 + wp; call pke_enc_lossless; call poly_cbd1_lossless; auto.
 if; last by auto.
 call finish_ll; auto.
qed.
lemma reencrypt_tail_lossless (H<:CompleteSHAKEH) :
 islossless H.shake => islossless ReencryptTail(H).run.
proof. move=>hH; proc; call reencrypt_finish_lossless; call hH; call hash_h_prepare_lossless; auto. qed.
lemma reencrypt_core_lossless (G<:MessageSHAKE) (H<:CompleteSHAKEH) :
 islossless G.shake => islossless H.shake => islossless ReencryptCore(G,H).run.
proof.
 move=>hG hH; proc; seq 1:true; 1,4,5:by auto.
 + call guarded_r2_lossless; auto.
 if; last by auto.
 call(reencrypt_tail_lossless H hH); call(decap_message_lossless G hG); auto.
qed.
lemma reencrypt_decaps_lossless (G<:MessageSHAKE) (H<:CompleteSHAKEH) :
 islossless G.shake => islossless H.shake => islossless ReencryptDecaps(G,H).run.
proof.
 move=>hG hH; proc; call decap_clear_lossless; call(reencrypt_core_lossless G H hG hH); auto.
qed.
