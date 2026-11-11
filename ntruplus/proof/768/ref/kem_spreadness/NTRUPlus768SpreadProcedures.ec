require import AllCore Distr.
from Jasmin require import JWord.
require import Array96 Array192 Array768 Array1152.
require import NTRUPlus768PKEModel NTRUPlus768PKEProcedures NTRUPlus768PKECallProof.
require import NTRUPlus768PKEKeyDistribution NTRUPlus768ROMDistributions.
require import NTRUPlus768PolyCBD1Checked NTRUPlus768PolyCBD1CheckedProof.
require import NTRUPlus768PolyCBD1Algebra NTRUPlus768SOTPContracts.
require import NTRUPlus768ACWC2HashG.

module SpreadSample = {
 proc run() : pke_poly = {
  var buf:W8.t Array192.t;var r:pke_poly;
  buf <$ uniform192;
  r <@ NTRUPlus768PolyCBD1Checked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(witness,buf);
  return r;
 }
}.
module SpreadSampleValue = {
 proc run() : pke_poly = {var r:pke_poly;r <$ pke_psi1;return r;}
}.
module SpreadSampleBuffer = {
 proc run() : pke_poly = {var buf:W8.t Array192.t;buf <$ uniform192;return poly_cbd1_spec buf;}
}.

(* One independent 192-byte encryption-randomness buffer is processed by
   the actual CBD and PKE array kernels. The message is already fixed. *)
module SpreadPKE = {
 proc run(pk:W8.t Array1152.t,m:pke_poly) : W8.t Array1152.t option = {
  var r:pke_poly; var ct:W8.t Array1152.t option;
  r <@ SpreadSample.run();
  ct <@ PKEEnc.run(pk,m,r);
  return ct;
 }
}.
module SpreadPKEValue = {
 proc run(pk:W8.t Array1152.t,m:pke_poly) : W8.t Array1152.t option = {
  var r:pke_poly;
  r <@ SpreadSampleValue.run();
  return pke_enc_spec pk m r;
 }
}.

(* This uses the current G table. It neither clears that table nor
   silently replaces a cached answer with an independent pad. *)
module SpreadEncoded = {
 proc run(pk:W8.t Array1152.t,msg:W8.t Array96.t) : W8.t Array1152.t option = {
  var pad:W8.t Array192.t;var r,code:pke_poly;
  var ct:W8.t Array1152.t option;
  r <@ SpreadSample.run();
  pad <@ ACWC2HashG.run(r);
  code <@ SOTPEncode.run(msg,pad);
  ct <@ PKEEnc.run(pk,code,r);
  return ct;
 }
}.

lemma spread_sample_lossless : islossless SpreadSample.run.
proof. proc;call poly_cbd1_lossless;rnd;auto=> />;exact uniform192_ll. qed.
lemma spread_sample_value_lossless : islossless SpreadSampleValue.run.
proof. proc;rnd;auto=> />;exact pke_psi1_lossless. qed.
lemma spread_sample_buffer_equiv : equiv[SpreadSample.run ~ SpreadSampleBuffer.run:true ==> ={res}].
proof.
 proc;seq 1 1:(={buf});first by rnd;auto.
 ecall{1}(poly_cbd1_correct witness buf{2});auto.
qed.
lemma spread_sample_law &m event : Pr[SpreadSample.run() @ &m:event res]=mu pke_psi1 event.
proof.
 have he:Pr[SpreadSample.run() @ &m:event res]=Pr[SpreadSampleBuffer.run() @ &m:event res]
  by byequiv spread_sample_buffer_equiv.
 rewrite he.
 rewrite -pke_cbd1_uniform dmapE /(\o).
 byphoare(_:true ==>event res)=> //;proc;rnd;auto.
qed.
lemma spread_sample_value_law &m event : Pr[SpreadSampleValue.run() @ &m:event res]=mu pke_psi1 event.
proof. byphoare(_:true ==>event res)=> //;proc;rnd;auto. qed.
lemma spread_sample_domain : hoare[SpreadSample.run:true ==>pke_domain res].
proof. proc;ecall(poly_cbd1_functional witness buf);auto=> />;smt(pke_domain_cbd). qed.
lemma spread_sample_equiv : equiv[SpreadSample.run ~ SpreadSampleValue.run:true ==> ={res} /\ pke_domain res{1}].
proof.
 conseq(_:true ==> ={res}) spread_sample_domain _=> //.
 bypr(res{1})(res{2})=> // &1 &2 r.
 by rewrite(spread_sample_law &1 (pred1 r)) (spread_sample_value_law &2 (pred1 r)).
qed.
lemma spread_pke_lossless : islossless SpreadPKE.run.
proof. proc;call pke_enc_lossless;call spread_sample_lossless;auto. qed.
lemma spread_pke_value_lossless : islossless SpreadPKEValue.run.
proof. proc;call spread_sample_value_lossless;auto. qed.
lemma spread_encoded_lossless : islossless SpreadEncoded.run.
proof.
 proc;call pke_enc_lossless;call sotp_encode_lossless;call acwc2_hash_g_lossless;
 call spread_sample_lossless;auto.
qed.

lemma spread_enc_correct pk0 m0 r0 :
 phoare[PKEEnc.run:pk=pk0 /\ m=m0 /\ r=r0 /\ pke_domain m0 /\ pke_domain r0 ==>
 res=pke_enc_spec pk0 m0 r0]=1%r.
proof.
 bypr=> &mem [hp [hm [hr [hdm hdr]]]].
 byphoare(pke_enc_correct pk0 m0 r0 hdm hdr)=> //.
qed.

lemma spread_pke_equiv : equiv[SpreadPKE.run ~ SpreadPKEValue.run:
 ={pk,m} /\ pke_domain m{1} ==> ={res}].
proof.
 proc;seq 1 1:(={pk,m,r} /\ pke_domain m{1} /\ pke_domain r{1}).
 + call spread_sample_equiv;auto.
 ecall{1}(spread_enc_correct pk{1} m{1} r{1});auto.
qed.

lemma spread_pke_value_probability pk0 m0 event &m :
 Pr[SpreadPKEValue.run(pk0,m0) @ &m:event res]=
 mu pke_psi1(fun r=>event(pke_enc_spec pk0 m0 r)).
proof. byphoare(_:pk=pk0 /\ m=m0 ==>event res)=> //;proc;inline SpreadSampleValue.run;wp;rnd;auto. qed.
lemma spread_pke_probability pk0 m0 event &m : pke_domain m0=>
 Pr[SpreadPKE.run(pk0,m0) @ &m:event res]=
 mu pke_psi1(fun r=>event(pke_enc_spec pk0 m0 r)).
proof.
 move=>hm;rewrite -(spread_pke_value_probability pk0 m0 event &m).
 byequiv spread_pke_equiv=> //;smt().
qed.
