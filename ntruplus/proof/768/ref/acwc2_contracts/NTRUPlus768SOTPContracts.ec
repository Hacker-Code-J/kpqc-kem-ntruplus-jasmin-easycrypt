require import AllCore Distr.
from Jasmin require import JWord.
require import Array96 Array192 Array768.
require import NTRUPlus768PKEModel NTRUPlus768PKEKeyDistribution.
require import NTRUPlus768ROMDistributions NTRUPlus768ROMSOTPMaskLaw.
require import NTRUPlus768PolySOTPEncodeCheckedProof NTRUPlus768PolySOTPEncodeCheckedRoundTrip.
require import NTRUPlus768PolySOTPDecodeCheckedProof NTRUPlus768PolySOTPDecodeCheckedLossless.
require import NTRUPlus768RRecWordChecks NTRUPlus768SOTPRigidity.
require import NTRUPlus768PolySOTPDecodeAlgebra NTRUPlus768PolySOTPEncodeAlgebra.
require import NTRUPlus768PolySOTPRoundTrip NTRUPlus768PolyCBD1Algebra.

op [opaque] sotp_decode_option (code:W16.t Array768.t) (pad:W8.t Array192.t) =
 if pke_domain code /\ !poly_sotp_decode_fail_spec code pad then
 Some(poly_sotp_decode_msg_spec code pad) else None.

(* These wrappers call the extracted SOTP kernels. Decode additionally
   calls an explicit trit-domain check; this guard is array-model glue,
   not a claim that the original raw native decoder contains that check.
   Success is the zero STATUS, including a successfully decoded zero message. *)
module SOTPEncode = {
 proc run(msg:W8.t Array96.t,pad:W8.t Array192.t) : W16.t Array768.t = {
  var code:W16.t Array768.t;
  code <@ NTRUPlus768PolySOTPEncodeChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_encode(witness,msg,pad);
  return code;
 }
}.
module SOTPDecode = {
 proc run(code:W16.t Array768.t,pad:W8.t Array192.t) : W8.t Array96.t option = {
  var valid:bool; var msg:W8.t Array96.t; var status:W32.t;
  var output:W8.t Array96.t option;
  valid <@ RRecTrit.check(code);
  output <- None;
  if(valid){
   (msg,status) <@ NTRUPlus768PolySOTPDecodeChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_decode(witness,code,pad);
   if(status=W32.zero){output <- Some msg;}
  }
  return output;
 }
}.
module SOTPRoundTrip = {
 proc run(msg:W8.t Array96.t,pad:W8.t Array192.t) : W8.t Array96.t option = {
  var code:W16.t Array768.t; var output:W8.t Array96.t option;
  code <@ SOTPEncode.run(msg,pad);
  output <@ SOTPDecode.run(code,pad);
  return output;
 }
}.
module SOTPReencode = {
 proc run(code:W16.t Array768.t,pad:W8.t Array192.t) : W16.t Array768.t option = {
  var msg:W8.t Array96.t option; var rebuilt:W16.t Array768.t;
  var output:W16.t Array768.t option;
  msg <@ SOTPDecode.run(code,pad);
  output <- None;
  if(msg<>None){
   rebuilt <@ SOTPEncode.run(oget msg,pad);
   output <- Some rebuilt;
  }
  return output;
 }
}.
module SOTPUniformEncode = {
 proc run(msg:W8.t Array96.t) : W16.t Array768.t = {
  var pad:W8.t Array192.t; var code:W16.t Array768.t;
  pad <$ uniform192;
  code <@ SOTPEncode.run(msg,pad);
  return code;
 }
}.

(* Sampling reference used only to state the exact distribution coupling. *)
module SOTPUniformValue = {
 proc run(msg:W8.t Array96.t) : W16.t Array768.t = {
  var pad:W8.t Array192.t;
  pad <$ uniform192;
  return poly_sotp_encode_spec msg pad;
 }
}.

lemma sotp_domainE code : pke_domain code=poly_sotp_trit_input code.
proof. by rewrite /pke_domain /poly_cbd1_trit_output /poly_sotp_trit_input. qed.
lemma sotp_decode_option_success code pad msg :
 sotp_decode_option code pad=Some msg =>
 pke_domain code /\ !poly_sotp_decode_fail_spec code pad /\
 msg=poly_sotp_decode_msg_spec code pad.
proof. rewrite /sotp_decode_option; case(pke_domain code /\ !poly_sotp_decode_fail_spec code pad); smt(). qed.
lemma sotp_encode_decode_option msg pad :
 sotp_decode_option (poly_sotp_encode_spec msg pad) pad=Some msg.
proof.
 have ht:=poly_sotp_encode_spec_trit_input msg pad.
 rewrite /sotp_decode_option sotp_domainE ht poly_sotp_encode_fail_spec_false /=
 poly_sotp_encode_decode_msg.
 done.
qed.
lemma sotp_decode_option_rigidity code pad msg :
 sotp_decode_option code pad=Some msg => poly_sotp_encode_spec msg pad=code.
proof.
 move=>hs; have [_ [hf hm]]:=sotp_decode_option_success code pad msg hs.
 rewrite hm; exact(sotp_decode_encode_rigidity code pad hf).
qed.

lemma sotp_encode_lossless : islossless SOTPEncode.run.
proof. proc; call poly_sotp_encode_lossless; auto. qed.
lemma sotp_decode_lossless : islossless SOTPDecode.run.
proof.
 proc; seq 2:true; 1,4,5:by auto.
 + wp; call rrec_trit_lossless; auto.
 if; last by auto.
 seq 1:true; 1,4,5:by auto.
 + call poly_sotp_decode_lossless; auto.
 if; auto.
qed.
lemma sotp_roundtrip_lossless : islossless SOTPRoundTrip.run.
proof. proc; call sotp_decode_lossless; call sotp_encode_lossless; auto. qed.
lemma sotp_reencode_lossless : islossless SOTPReencode.run.
proof.
 proc; seq 2:true; 1,4,5:by auto.
 + wp; call sotp_decode_lossless; auto.
 if; last by auto.
 wp; call sotp_encode_lossless; auto.
qed.
lemma sotp_uniform_encode_lossless : islossless SOTPUniformEncode.run.
proof. proc; call sotp_encode_lossless; rnd; auto=> />.
 exact uniform192_ll. qed.

lemma sotp_encode_functional msg0 pad0 :
 hoare[SOTPEncode.run:msg=msg0 /\ pad=pad0 ==> res=poly_sotp_encode_spec msg0 pad0].
proof. proc; call(poly_sotp_encode_functional witness msg0 pad0); auto. qed.
lemma sotp_decode_functional code0 pad0 :
 hoare[SOTPDecode.run:code=code0 /\ pad=pad0 ==> res=sotp_decode_option code0 pad0].
proof.
 case(pke_domain code0)=>ht; proc.
 + rcondt 3.
   - wp; call(rrec_trit_functional code0); auto=> />; exact ht.
   have htrit:poly_sotp_trit_input code0 by rewrite -sotp_domainE.
   seq 3:(code=code0 /\ pad=pad0 /\ output=None /\
     msg=poly_sotp_decode_msg_spec code0 pad0 /\
     status=W32.of_int(b2i(poly_sotp_decode_fail_spec code0 pad0))).
   - call(poly_sotp_decode_functional witness code0 pad0).
     wp; call(rrec_trit_functional code0); auto=> />.
   if; auto=> />; rewrite /sotp_decode_option ht /=;
    case(poly_sotp_decode_fail_spec code0 pad0); smt(W32.to_uint0 W32.to_uint1).
 rcondf 3.
 + wp; call(rrec_trit_functional code0); auto=> />; exact ht.
 wp; call(rrec_trit_functional code0); auto=> />; by rewrite /sotp_decode_option ht.
qed.
lemma sotp_encode_correct msg0 pad0 :
 phoare[SOTPEncode.run:msg=msg0 /\ pad=pad0 ==> res=poly_sotp_encode_spec msg0 pad0]=1%r.
proof. by conseq sotp_encode_lossless (sotp_encode_functional msg0 pad0). qed.
lemma sotp_decode_correct code0 pad0 :
 phoare[SOTPDecode.run:code=code0 /\ pad=pad0 ==> res=sotp_decode_option code0 pad0]=1%r.
proof. by conseq sotp_decode_lossless (sotp_decode_functional code0 pad0). qed.
lemma sotp_decode_success_domain code0 pad0 :
 hoare[SOTPDecode.run:code=code0 /\ pad=pad0 ==>
 res<>None => pke_domain code0 /\ poly_sotp_trit_input code0].
proof.
 conseq(sotp_decode_functional code0 pad0)=> />.
 rewrite /sotp_decode_option; smt(sotp_domainE).
qed.
lemma sotp_decode_actual_rigidity code0 pad0 :
 hoare[SOTPDecode.run:code=code0 /\ pad=pad0 ==>
 res<>None => poly_sotp_encode_spec (oget res) pad0=code0].
proof.
 conseq(sotp_decode_functional code0 pad0)=> />.
 move=> &hr.
 rewrite /sotp_decode_option; case(pke_domain code{hr} /\ !poly_sotp_decode_fail_spec code{hr} pad{hr})=>h /=;
 smt(sotp_decode_encode_rigidity).
qed.
lemma sotp_roundtrip_correct msg0 pad0 :
 phoare[SOTPRoundTrip.run:msg=msg0 /\ pad=pad0 ==> res=Some msg0]=1%r.
proof.
 conseq sotp_roundtrip_lossless (_:msg=msg0 /\ pad=pad0 ==> res=Some msg0)=> //.
 proc; call(sotp_decode_functional (poly_sotp_encode_spec msg0 pad0) pad0).
 call(sotp_encode_functional msg0 pad0); auto=> />; exact(sotp_encode_decode_option msg0 pad0).
qed.
lemma sotp_reencode_rigidity code0 pad0 :
 hoare[SOTPReencode.run:code=code0 /\ pad=pad0 ==> res=None \/ res=Some code0].
proof.
 proc; seq 2:(code=code0 /\ pad=pad0 /\ msg=sotp_decode_option code0 pad0 /\ output=None).
 + wp; call(sotp_decode_functional code0 pad0); auto.
 if.
 + wp; ecall(sotp_encode_functional (oget msg) pad); auto=> />.
   rewrite /sotp_decode_option; case(pke_domain code0 /\ !poly_sotp_decode_fail_spec code0 pad0)=>h /=;
   smt(sotp_decode_encode_rigidity).
 auto.
qed.

(* Fixed-message hiding: only the independent 192-byte pad is random. *)
lemma sotp_encode_psi1 msg :
 dmap uniform192 (poly_sotp_encode_spec msg)=pke_psi1.
proof. by rewrite sotp_encode_uniform_law /cbd1_uniform pke_cbd1_uniform. qed.
lemma sotp_uniform_encode_equiv :
 equiv[SOTPUniformEncode.run ~ SOTPUniformValue.run : ={msg} ==> ={res}].
proof.
 proc; seq 1 1:(={msg,pad}); first by rnd; auto.
 wp; ecall{1}(sotp_encode_correct msg{2} pad{2}); auto.
qed.
lemma sotp_uniform_encode_law &m msg0 event :
 Pr[SOTPUniformEncode.run(msg0) @ &m:event res]=mu pke_psi1 event.
proof.
 have he:Pr[SOTPUniformEncode.run(msg0) @ &m:event res]=
   Pr[SOTPUniformValue.run(msg0) @ &m:event res]
   by byequiv sotp_uniform_encode_equiv.
 rewrite he -(sotp_encode_psi1 msg0) dmapE /(\o).
 byphoare (_:msg=msg0 ==> event res)=> //.
 proc; rnd; auto.
qed.
