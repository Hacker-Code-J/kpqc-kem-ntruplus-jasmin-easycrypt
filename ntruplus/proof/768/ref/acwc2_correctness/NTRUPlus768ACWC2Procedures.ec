require import AllCore Distr.
from Jasmin require import JWord.
require import Array96 Array192 Array768 Array1152 Array2336.
require import NTRUPlus768PKEModel NTRUPlus768PKEProcedures.
require import NTRUPlus768SOTPContracts NTRUPlus768RRecProcedures.
require import NTRUPlus768ACWC2HashG NTRUPlus768ACWC2Model.

module type ACWC2GPort = {
 proc run(r:pke_poly) : W8.t Array192.t
}.

(* A reference for a previously chosen full function. Its initialization
   is separate from query access; repeated queries read the same value. *)
module ACWC2FullG = {
 var table:acwc2_g_map
 proc init(g:acwc2_g_map) : unit = {table<-g;}
 proc run(r:pke_poly) : W8.t Array192.t = {return table r;}
}.

(* Array-level composition of the existing PKE, SOTP, and public RRec
   procedures. These definitions do not introduce native exported APIs. *)
module ACWC2Enc(G:ACWC2GPort) = {
 proc run(pk:W8.t Array1152.t,msg:W8.t Array96.t,r:pke_poly) : W8.t Array1152.t option = {
  var pad:W8.t Array192.t; var code:pke_poly; var ct:W8.t Array1152.t option;
  pad <@ G.run(r);
  code <@ SOTPEncode.run(msg,pad);
  ct <@ PKEEnc.run(pk,code,r);
  return ct;
 }
}.
module ACWC2Dec(G:ACWC2GPort) = {
 proc run(pk:W8.t Array1152.t,sk:W8.t Array2336.t,ct:W8.t Array1152.t) : W8.t Array96.t option = {
  var code,recovered:pke_poly option; var pad:W8.t Array192.t;
  var msg:W8.t Array96.t option;
  code <@ PKEDec.run(ct,acwc2_secret_bytes sk);
  msg <- None;
  if(code<>None){
   recovered <@ RRec.run(pk,oget code,ct);
   if(recovered<>None){
    pad <@ G.run(oget recovered);
    msg <@ SOTPDecode.run(oget code,pad);
   }
  }
  return msg;
 }
}.
module ACWC2RoundTrip(G:ACWC2GPort) = {
 proc run(pk:W8.t Array1152.t,sk:W8.t Array2336.t,msg:W8.t Array96.t,r:pke_poly) : bool = {
  var ct:W8.t Array1152.t option; var decoded:W8.t Array96.t option;
  var failed:bool;
  ct <@ ACWC2Enc(G).run(pk,msg,r);
  failed <- true;
  if(ct<>None){
   decoded <@ ACWC2Dec(G).run(pk,sk,oget ct);
   failed <- decoded<>Some msg;
  }
  return failed;
 }
}.
module ACWC2ROMEnc = ACWC2Enc(ACWC2HashG).
module ACWC2ROMDec = ACWC2Dec(ACWC2HashG).
module ACWC2ROMRoundTrip = ACWC2RoundTrip(ACWC2HashG).

lemma acwc2_full_g_lossless : islossless ACWC2FullG.run.
proof. proc; auto. qed.
lemma acwc2_enc_lossless (G<:ACWC2GPort) : islossless G.run => islossless ACWC2Enc(G).run.
proof. move=>hG; proc; call pke_enc_lossless; call sotp_encode_lossless; call hG; auto. qed.
lemma acwc2_dec_lossless (G<:ACWC2GPort) : islossless G.run => islossless ACWC2Dec(G).run.
proof.
 move=>hG; proc; seq 2:true; 1,4,5:by auto.
 + wp; call pke_dec_lossless; auto.
 if; last by auto.
 seq 1:true; 1,4,5:by auto.
 + call rrec_lossless; auto.
 if; last by auto.
 call sotp_decode_lossless; call hG; auto.
qed.
lemma acwc2_roundtrip_lossless (G<:ACWC2GPort) : islossless G.run => islossless ACWC2RoundTrip(G).run.
proof.
 move=>hG; proc; seq 2:true; 1,4,5:by auto.
 + wp; call(acwc2_enc_lossless G hG); auto.
 if; last by auto.
 wp; call(acwc2_dec_lossless G hG); auto.
qed.
lemma acwc2_rom_roundtrip_lossless : islossless ACWC2ROMRoundTrip.run.
proof. exact(acwc2_roundtrip_lossless ACWC2HashG acwc2_hash_g_lossless). qed.
