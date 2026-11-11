require import AllCore Distr.
from Jasmin require import JWord.
require import Array32 Array96 Array129 Array192 Array224 Array768 Array1152 Array1153 Array2336 Array13506.
require import NTRUPlus768PKEModel NTRUPlus768PKEProcedures NTRUPlus768SOTPContracts.
require import NTRUPlus768RRecLinearProcedures NTRUPlus768ACWC2HashG.
require import NTRUPlus768DecapCompleteSpec NTRUPlus768DecapCompleteHash.
require import NTRUPlus768DecapMessageSpec NTRUPlus768DecapMessageProof NTRUPlus768DecapR2CompCaller.
require import NTRUPlus768DecapHashHPrepare NTRUPlus768DecapHashHPrepareProof.
require import NTRUPlus768PolyCBD1Checked NTRUPlus768PolyCBD1CheckedProof.
require import NTRUPlus768DecapFinish NTRUPlus768DecapFinishCorrectness.
require import NTRUPlus768DecapClear NTRUPlus768DecapClearProof NTRUPlus768EncapGuardSpec.

(* The same existing NTT/serialization/tag kernels prepare G's input for
   any query-only backend. No procedure below directly reads a ROM table. *)
module FOHashG(G:MessageSHAKE) = {
 proc run(r:pke_poly) : W8.t Array192.t = {
  var serialized:W8.t Array1152.t; var input:W8.t Array1153.t; var pad:W8.t Array192.t;
  (serialized,input) <@ ACWC2GPrepare.run(r);
  pad <@ G.shake(input);
  return pad;
 }
}.

(* This performs full modified-FO regeneration, not same-m1 re-encryption.
   Both option checks are explicit. Checks are deferred until after the
   existing H call, preserving the native decode-failure hash side effect. *)
module FORegenerateFinish(G:MessageSHAKE) = {
 proc run(pk ct:W8.t Array1152.t,m1:pke_poly,msg:W8.t Array96.t,
   hashout:W8.t Array224.t,decode_fail:W32.t) : W8.t Array32.t * W32.t = {
  var recovered:pke_poly option; var decoded:W8.t Array96.t option;
  var r1,code:pke_poly; var pad:W8.t Array192.t; var ct2:W8.t Array1152.t option;
  var ss:W8.t Array32.t; var status,failed:W32.t;
  recovered <@ LinearRRec.run(pk,m1,ct);
  decoded <- if decode_fail=W32.zero then Some msg else None;
  r1 <@ NTRUPlus768PolyCBD1Checked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(witness,complete_hash_tail hashout);
  pad <@ FOHashG(G).run(r1);
  code <@ SOTPEncode.run(msg,pad);
  ct2 <@ PKEEnc.run(pk,code,r1);
  failed <- W32.of_int(b2i(decoded=None \/ recovered=None));
  ss <- encap_zero_ss; status <- W32.one;
  if(ct2<>None){
   (ss,status) <@ NTRUPlus768DecapFinish.M.jade_ntruplus_ntruplus768_amd64_ref_decap_finish(witness,hashout,ct,oget ct2,failed);
  }
  return(ss,status);
 }
}.
module FOTail(G:MessageSHAKE,H:CompleteSHAKEH) = {
 proc run(pk ct:W8.t Array1152.t,m1:pke_poly,msg:W8.t Array96.t,
   decode_fail:W32.t,suffix:W8.t Array32.t) : W8.t Array32.t * W32.t = {
  var input:W8.t Array129.t; var hashout:W8.t Array224.t;
  var result:W8.t Array32.t * W32.t;
  input <@ NTRUPlus768DecapHashHPrepare.M.jade_ntruplus_ntruplus768_amd64_ref_decap_hash_h_prepare(witness,msg,suffix);
  hashout <@ H.shake(input);
  result <@ FORegenerateFinish(G).run(pk,ct,m1,msg,hashout,decode_fail);
  return result;
 }
}.
module FOCore(G:MessageSHAKE,H:CompleteSHAKEH) = {
 proc run(pk ct:W8.t Array1152.t,sk:W8.t Array2336.t) : W8.t Array32.t * W32.t = {
  var rp,mp:pke_poly; var ss:W8.t Array32.t; var status:W32.t;
  var bs:W8.t Array1152.t; var msg:W8.t Array96.t;
  (rp,mp,ss,status) <@ GuardedR2.run(witness,witness,witness,witness,witness,encap_zero_ss,ct,complete_sk_poly sk);
  if(status=W32.zero){
   (bs,msg,status) <@ DecapMessage(G).run(witness,witness,witness,rp,mp);
   (ss,status) <@ FOTail(G,H).run(pk,ct,mp,msg,status,complete_sk_suffix sk);
  }
  return(ss,status);
 }
}.
module FODecaps(G:MessageSHAKE,H:CompleteSHAKEH) = {
 proc run(pk ct:W8.t Array1152.t,sk:W8.t Array2336.t,workspace:W8.t Array13506.t)
   : W8.t Array32.t * W32.t * W8.t Array13506.t = {
  var ss:W8.t Array32.t; var status:W32.t;
  (ss,status) <@ FOCore(G,H).run(pk,ct,sk);
  workspace <@ NTRUPlus768DecapClear.M.jade_ntruplus_ntruplus768_amd64_ref_decap_clear(workspace);
  return(ss,status,workspace);
 }
}.

lemma fo_hash_g_lossless (G<:MessageSHAKE) :
 islossless G.shake =>islossless FOHashG(G).run.
proof. move=>hG; proc; call hG; call acwc2_g_prepare_lossless; auto. qed.
lemma fo_regenerate_finish_lossless (G<:MessageSHAKE) :
 islossless G.shake =>islossless FORegenerateFinish(G).run.
proof.
 move=>hG; proc; seq 9:true; 1,4,5:by auto.
 + wp; call pke_enc_lossless; call sotp_encode_lossless;
   call(fo_hash_g_lossless G hG); call poly_cbd1_lossless; wp; call linear_rrec_lossless; auto.
 if; last by auto.
 call finish_ll; auto.
qed.
lemma fo_tail_lossless (G<:MessageSHAKE) (H<:CompleteSHAKEH) :
 islossless G.shake =>islossless H.shake =>islossless FOTail(G,H).run.
proof.
 move=>hG hH; proc; call(fo_regenerate_finish_lossless G hG); call hH; call hash_h_prepare_lossless; auto.
qed.
lemma fo_core_lossless (G<:MessageSHAKE) (H<:CompleteSHAKEH) :
 islossless G.shake =>islossless H.shake =>islossless FOCore(G,H).run.
proof.
 move=>hG hH; proc; seq 1:true; 1,4,5:by auto.
 + call guarded_r2_lossless; auto.
 if; last by auto.
 call(fo_tail_lossless G H hG hH); call(decap_message_lossless G hG); auto.
qed.
lemma fo_decaps_lossless (G<:MessageSHAKE) (H<:CompleteSHAKEH) :
 islossless G.shake =>islossless H.shake =>islossless FODecaps(G,H).run.
proof.
 move=>hG hH; proc; call decap_clear_lossless; call(fo_core_lossless G H hG hH); auto.
qed.
