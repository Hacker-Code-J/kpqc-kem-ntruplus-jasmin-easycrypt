require import AllCore IntDiv.
from Jasmin require import JWord.
require import Array768 Array1152.
require import NTRUPlus768PKEModel NTRUPlus768PKEProcedures.
require import NTRUPlus768RRecPublicInverse NTRUPlus768RRecProcedures NTRUPlus768RRecLinearProcedures.
require import NTRUPlus768MRecModel NTRUPlus768MRecDecode NTRUPlus768SecExtract.
require import NTRUPlus768RTWordCodec.
require import NTRUPlus768RTFixedNTT NTRUPlus768RTFixedInvNTT NTRUPlus768RTFixedBasemul NTRUPlus768RTFixedBaseinv NTRUPlus768RTFixedToBytes NTRUPlus768RTFixedFromBytes NTRUPlus768RTFixedCenteredAdd NTRUPlus768RTFixedPolySub NTRUPlus768RTFixedDecapR2 NTRUPlus768RTFixedWordChecks.

(* Fixed finite-word implementations with local proof-observation charges.
   Array arguments, results, bindings and Some constructions reserve 3N
   owned-cell copy operations. Calls pay 2+arity, scratch allocation,
   actual selector operations and the callee measured work. The counters
   are erased and are not global state. No mathematical polynomial
   operation is executed or assigned a unit price by these wrappers. *)

op rt_kernel_encode_bound:int = 2304+(3076+rt_fixed_ntt_bound+4612+rt_fixed_tobytes_bound)+3457.
module RTKernelEncode = {
 proc run(a:W16.t Array768.t):(W8.t Array1152.t)*int = {
  var h:W16.t Array768.t;var bytes:W8.t Array1152.t;
  var rt_work:int;
  var rt_call_0:(W16.t Array768.t)*int;
  var rt_call_1:(W8.t Array1152.t)*int;
  rt_work<-2304;
  rt_call_0<@RTFixedNTT.jade_ntruplus_ntruplus768_amd64_ref_ntt(witness,a);
  h<-rt_call_0.`1;
  rt_work<-rt_work+rt_call_0.`2+3076;
  rt_call_1<@RTFixedToBytes.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes(witness,h);
  bytes<-rt_call_1.`1;
  rt_work<-rt_work+rt_call_1.`2+4612;
  rt_work<-rt_work+3457;
  return(bytes,rt_work);
 }
}.

lemma rt_kernel_encode_projection :
 equiv[RTKernelEncode.run ~ RTWordEncode.run: ={a} ==>res{1}.`1=res{2}].
proof.
 proc;sp 1 0;
 seq 3 1:(={a,h}).
 + by wp;call rt_fixed_ntt_jade_ntruplus_ntruplus768_amd64_ref_ntt_projection;auto.
 seq 3 1:(={a,bytes,h}).
 + by wp;call rt_fixed_tobytes_jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes_projection;auto.
 auto.
qed.
lemma rt_kernel_encode_cost :
 hoare[RTKernelEncode.run:true ==>0<=res.`2<=rt_kernel_encode_bound].
proof.
 proc;seq 1:(rt_work=2304);first by auto.
 seq 3:(0<=rt_work<=(2304+(3076+rt_fixed_ntt_bound))).
 + wp;call rt_fixed_ntt_bound_cost;auto=> />;smt().
 seq 3:(0<=rt_work<=((2304+(3076+rt_fixed_ntt_bound))+(4612+rt_fixed_tobytes_bound))).
 + wp;call rt_fixed_tobytes_bound_cost;auto=> />;smt().
 auto=> />;smt().
qed.

op rt_kernel_publicinverse_bound:int = 2304+(1+3076+rt_fixed_baseinv_bound+2+(4612+rt_fixed_tobytes_bound+3076+rt_fixed_frombytes_bound+2+(2306)))+2305.
module RTKernelPublicInverse = {
 proc run(hp:W16.t Array768.t):(W16.t Array768.t option)*int = {
  var raw,canonical:W16.t Array768.t;var status:W64.t;var decoded_status:W32.t;var bytes:W8.t Array1152.t;var result:W16.t Array768.t option;
  var rt_work:int;
  var rt_call_1:(W16.t Array768.t*W64.t)*int;
  var rt_call_3:(W8.t Array1152.t)*int;
  var rt_call_4:(W16.t Array768.t*W32.t)*int;
  rt_work<-2304;
  result<-None;rt_work<-rt_work+1;
  rt_call_1<@RTFixedBaseinv.__poly_baseinv_core(witness,hp);
  (raw,status)<-rt_call_1.`1;
  rt_work<-rt_work+rt_call_1.`2+3076;
  rt_work<-rt_work+2;
  if(status=W64.zero){
   rt_call_3<@RTFixedToBytes.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes(witness,raw);
   bytes<-rt_call_3.`1;
   rt_work<-rt_work+rt_call_3.`2+4612;
   rt_call_4<@RTFixedFromBytes.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes(witness,bytes);
   (canonical,decoded_status)<-rt_call_4.`1;
   rt_work<-rt_work+rt_call_4.`2+3076;
   rt_work<-rt_work+2;
   if(decoded_status=W32.zero){
    result<-Some canonical;rt_work<-rt_work+2306;
   }
  }
  rt_work<-rt_work+2305;
  return(result,rt_work);
 }
}.

lemma rt_kernel_publicinverse_projection :
 equiv[RTKernelPublicInverse.run ~ RRecPublicInverse.run: ={hp} ==>res{1}.`1=res{2}].
proof.
 proc;sp 1 0;
 seq 2 1:(={hp,result}).
 + by auto.
 seq 3 1:(={hp,raw,result,status}).
 + by wp;call rt_fixed_baseinv___poly_baseinv_core_projection;auto.
 seq 2 1:(={hp,raw,result,status}).
 + sp 1 0;if;first by auto.
   - seq 3 1:(={bytes,hp,raw,result,status}).
     + by wp;call rt_fixed_tobytes_jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes_projection;auto.
     seq 3 1:(={bytes,canonical,decoded_status,hp,raw,result,status}).
     + by wp;call rt_fixed_frombytes_jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes_projection;auto.
     seq 2 1:(={bytes,canonical,decoded_status,hp,raw,result,status}).
     + sp 1 0;if;first by auto.
       - seq 2 1:(={bytes,canonical,decoded_status,hp,raw,result,status}).
         + by auto.
         auto.
       auto.
     auto.
   auto.
 auto.
qed.
lemma rt_kernel_publicinverse_cost :
 hoare[RTKernelPublicInverse.run:true ==>0<=res.`2<=rt_kernel_publicinverse_bound].
proof.
 proc;seq 1:(rt_work=2304);first by auto.
 seq 2:(0<=rt_work<=(2304+1)).
 + auto=> />;smt().
 seq 3:(0<=rt_work<=((2304+1)+(3076+rt_fixed_baseinv_bound))).
 + wp;call rt_fixed_baseinv_bound_cost;auto=> />;smt().
 seq 2:(0<=rt_work<=(((2304+1)+(3076+rt_fixed_baseinv_bound))+(2+(4612+rt_fixed_tobytes_bound+3076+rt_fixed_frombytes_bound+2+(2306))))).
 + sp 1;if.
   - seq 3:(0<=rt_work<=((((2304+1)+(3076+rt_fixed_baseinv_bound))+2)+(4612+rt_fixed_tobytes_bound))).
     + wp;call rt_fixed_tobytes_bound_cost;auto=> />;smt().
     seq 3:(0<=rt_work<=(((((2304+1)+(3076+rt_fixed_baseinv_bound))+2)+(4612+rt_fixed_tobytes_bound))+(3076+rt_fixed_frombytes_bound))).
     + wp;call rt_fixed_frombytes_bound_cost;auto=> />;smt().
     seq 2:(0<=rt_work<=((((((2304+1)+(3076+rt_fixed_baseinv_bound))+2)+(4612+rt_fixed_tobytes_bound))+(3076+rt_fixed_frombytes_bound))+(2+(2306)))).
     + sp 1;if.
       - seq 2:(0<=rt_work<=(((((((2304+1)+(3076+rt_fixed_baseinv_bound))+2)+(4612+rt_fixed_tobytes_bound))+(3076+rt_fixed_frombytes_bound))+2)+2306)).
         + auto=> />;smt().
         auto=> />;smt().
       auto=> />;smt().
     auto=> />;smt().
   auto=> />;smt().
 auto=> />;smt().
qed.

op rt_kernel_pkeencbody_bound:int = 6912+(3076+rt_fixed_ntt_bound+3076+rt_fixed_ntt_bound+3077+rt_fixed_basemul_bound+3077+rt_fixed_centeredadd_bound+4612+rt_fixed_tobytes_bound)+3457.
module RTKernelPKEEncBody = {
 proc run(hp m r:W16.t Array768.t):(W8.t Array1152.t)*int = {
  var rhat,mhat,product,cipher:W16.t Array768.t;var ct:W8.t Array1152.t;
  var rt_work:int;
  var rt_call_0:(W16.t Array768.t)*int;
  var rt_call_1:(W16.t Array768.t)*int;
  var rt_call_2:(W16.t Array768.t)*int;
  var rt_call_3:(W16.t Array768.t)*int;
  var rt_call_4:(W8.t Array1152.t)*int;
  rt_work<-6912;
  rt_call_0<@RTFixedNTT.jade_ntruplus_ntruplus768_amd64_ref_ntt(witness,r);
  rhat<-rt_call_0.`1;
  rt_work<-rt_work+rt_call_0.`2+3076;
  rt_call_1<@RTFixedNTT.jade_ntruplus_ntruplus768_amd64_ref_ntt(witness,m);
  mhat<-rt_call_1.`1;
  rt_work<-rt_work+rt_call_1.`2+3076;
  rt_call_2<@RTFixedBasemul.jade_ntruplus_ntruplus768_amd64_ref_poly_basemul(witness,hp,rhat);
  product<-rt_call_2.`1;
  rt_work<-rt_work+rt_call_2.`2+3077;
  rt_call_3<@RTFixedCenteredAdd.jade_ntruplus_ntruplus768_amd64_ref_poly_centered_add(witness,product,mhat);
  cipher<-rt_call_3.`1;
  rt_work<-rt_work+rt_call_3.`2+3077;
  rt_call_4<@RTFixedToBytes.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes(witness,cipher);
  ct<-rt_call_4.`1;
  rt_work<-rt_work+rt_call_4.`2+4612;
  rt_work<-rt_work+3457;
  return(ct,rt_work);
 }
}.

lemma rt_kernel_pkeencbody_projection :
 equiv[RTKernelPKEEncBody.run ~ PKEEncBody.run: ={hp,m,r} ==>res{1}.`1=res{2}].
proof.
 proc;sp 1 0;
 seq 3 1:(={hp,m,r,rhat}).
 + by wp;call rt_fixed_ntt_jade_ntruplus_ntruplus768_amd64_ref_ntt_projection;auto.
 seq 3 1:(={hp,m,mhat,r,rhat}).
 + by wp;call rt_fixed_ntt_jade_ntruplus_ntruplus768_amd64_ref_ntt_projection;auto.
 seq 3 1:(={hp,m,mhat,product,r,rhat}).
 + by wp;call rt_fixed_basemul_jade_ntruplus_ntruplus768_amd64_ref_poly_basemul_projection;auto.
 seq 3 1:(={cipher,hp,m,mhat,product,r,rhat}).
 + by wp;call rt_fixed_centeredadd_jade_ntruplus_ntruplus768_amd64_ref_poly_centered_add_projection;auto.
 seq 3 1:(={cipher,ct,hp,m,mhat,product,r,rhat}).
 + by wp;call rt_fixed_tobytes_jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes_projection;auto.
 auto.
qed.
lemma rt_kernel_pkeencbody_cost :
 hoare[RTKernelPKEEncBody.run:true ==>0<=res.`2<=rt_kernel_pkeencbody_bound].
proof.
 proc;seq 1:(rt_work=6912);first by auto.
 seq 3:(0<=rt_work<=(6912+(3076+rt_fixed_ntt_bound))).
 + wp;call rt_fixed_ntt_bound_cost;auto=> />;smt().
 seq 3:(0<=rt_work<=((6912+(3076+rt_fixed_ntt_bound))+(3076+rt_fixed_ntt_bound))).
 + wp;call rt_fixed_ntt_bound_cost;auto=> />;smt().
 seq 3:(0<=rt_work<=(((6912+(3076+rt_fixed_ntt_bound))+(3076+rt_fixed_ntt_bound))+(3077+rt_fixed_basemul_bound))).
 + wp;call rt_fixed_basemul_bound_cost;auto=> />;smt().
 seq 3:(0<=rt_work<=((((6912+(3076+rt_fixed_ntt_bound))+(3076+rt_fixed_ntt_bound))+(3077+rt_fixed_basemul_bound))+(3077+rt_fixed_centeredadd_bound))).
 + wp;call rt_fixed_centeredadd_bound_cost;auto=> />;smt().
 seq 3:(0<=rt_work<=(((((6912+(3076+rt_fixed_ntt_bound))+(3076+rt_fixed_ntt_bound))+(3077+rt_fixed_basemul_bound))+(3077+rt_fixed_centeredadd_bound))+(4612+rt_fixed_tobytes_bound))).
 + wp;call rt_fixed_tobytes_bound_cost;auto=> />;smt().
 auto=> />;smt().
qed.

op rt_kernel_pkeenc_bound:int = 8064+(1+3076+rt_fixed_frombytes_bound+2+(3461+rt_kernel_pkeencbody_bound+3458))+3457.
module RTKernelPKEEnc = {
 proc run(pk:W8.t Array1152.t,m r:W16.t Array768.t):(W8.t Array1152.t option)*int = {
  var hp:W16.t Array768.t;var status:W32.t;var ct:W8.t Array1152.t;var result:W8.t Array1152.t option;
  var rt_work:int;
  var rt_call_1:(W16.t Array768.t*W32.t)*int;
  var rt_call_3:(W8.t Array1152.t)*int;
  rt_work<-8064;
  result<-None;rt_work<-rt_work+1;
  rt_call_1<@RTFixedFromBytes.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes(witness,pk);
  (hp,status)<-rt_call_1.`1;
  rt_work<-rt_work+rt_call_1.`2+3076;
  rt_work<-rt_work+2;
  if(status=W32.zero){
   rt_call_3<@RTKernelPKEEncBody.run(hp,m,r);
   ct<-rt_call_3.`1;
   rt_work<-rt_work+rt_call_3.`2+3461;
   result<-Some ct;rt_work<-rt_work+3458;
  }
  rt_work<-rt_work+3457;
  return(result,rt_work);
 }
}.

lemma rt_kernel_pkeenc_projection :
 equiv[RTKernelPKEEnc.run ~ PKEEnc.run: ={m,pk,r} ==>res{1}.`1=res{2}].
proof.
 proc;sp 1 0;
 seq 2 1:(={m,pk,r,result}).
 + by auto.
 seq 3 1:(={hp,m,pk,r,result,status}).
 + by wp;call rt_fixed_frombytes_jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes_projection;auto.
 seq 2 1:(={hp,m,pk,r,result,status}).
 + sp 1 0;if;first by auto.
   - seq 3 1:(={ct,hp,m,pk,r,result,status}).
     + by wp;call rt_kernel_pkeencbody_projection;auto.
     seq 2 1:(={ct,hp,m,pk,r,result,status}).
     + by auto.
     auto.
   auto.
 auto.
qed.
lemma rt_kernel_pkeenc_cost :
 hoare[RTKernelPKEEnc.run:true ==>0<=res.`2<=rt_kernel_pkeenc_bound].
proof.
 proc;seq 1:(rt_work=8064);first by auto.
 seq 2:(0<=rt_work<=(8064+1)).
 + auto=> />;smt().
 seq 3:(0<=rt_work<=((8064+1)+(3076+rt_fixed_frombytes_bound))).
 + wp;call rt_fixed_frombytes_bound_cost;auto=> />;smt().
 seq 2:(0<=rt_work<=(((8064+1)+(3076+rt_fixed_frombytes_bound))+(2+(3461+rt_kernel_pkeencbody_bound+3458)))).
 + sp 1;if.
   - seq 3:(0<=rt_work<=((((8064+1)+(3076+rt_fixed_frombytes_bound))+2)+(3461+rt_kernel_pkeencbody_bound))).
     + wp;call rt_kernel_pkeencbody_cost;auto=> />;smt().
     seq 2:(0<=rt_work<=(((((8064+1)+(3076+rt_fixed_frombytes_bound))+2)+(3461+rt_kernel_pkeencbody_bound))+3458)).
     + auto=> />;smt().
     auto=> />;smt().
   auto=> />;smt().
 auto=> />;smt().
qed.

op rt_kernel_rreccore_bound:int = 6912+(3078+rt_fixed_decapr2_bound+3076+rt_fixed_invntt_bound)+2305.
module RTKernelRRecCore = {
 proc run(cp m inverse:W16.t Array768.t):(W16.t Array768.t)*int = {
  var rhat,raw:W16.t Array768.t;
  var rt_work:int;
  var rt_call_0:(W16.t Array768.t)*int;
  var rt_call_1:(W16.t Array768.t)*int;
  rt_work<-6912;
  rt_call_0<@RTFixedDecapR2.jade_ntruplus_ntruplus768_amd64_ref_decap_r2(witness,cp,m,inverse);
  rhat<-rt_call_0.`1;
  rt_work<-rt_work+rt_call_0.`2+3078;
  rt_call_1<@RTFixedInvNTT.jade_ntruplus_ntruplus768_amd64_ref_invntt(witness,rhat);
  raw<-rt_call_1.`1;
  rt_work<-rt_work+rt_call_1.`2+3076;
  rt_work<-rt_work+2305;
  return(raw,rt_work);
 }
}.

lemma rt_kernel_rreccore_projection :
 equiv[RTKernelRRecCore.run ~ RRecCore.run: ={cp,inverse,m} ==>res{1}.`1=res{2}].
proof.
 proc;sp 1 0;
 seq 3 1:(={cp,inverse,m,rhat}).
 + by wp;call rt_fixed_decapr2_jade_ntruplus_ntruplus768_amd64_ref_decap_r2_projection;auto.
 seq 3 1:(={cp,inverse,m,raw,rhat}).
 + by wp;call rt_fixed_invntt_jade_ntruplus_ntruplus768_amd64_ref_invntt_projection;auto.
 auto.
qed.
lemma rt_kernel_rreccore_cost :
 hoare[RTKernelRRecCore.run:true ==>0<=res.`2<=rt_kernel_rreccore_bound].
proof.
 proc;seq 1:(rt_work=6912);first by auto.
 seq 3:(0<=rt_work<=(6912+(3078+rt_fixed_decapr2_bound))).
 + wp;call rt_fixed_decapr2_bound_cost;auto=> />;smt().
 seq 3:(0<=rt_work<=((6912+(3078+rt_fixed_decapr2_bound))+(3076+rt_fixed_invntt_bound))).
 + wp;call rt_fixed_invntt_bound_cost;auto=> />;smt().
 auto=> />;smt().
qed.

op rt_kernel_rrecfinish_bound:int = 6912+(1+2309+rt_kernel_rreccore_bound+2307+rt_fixed_normalize_bound+3+rt_fixed_trit_bound+1+(2306))+2305.
module RTKernelRRecFinish = {
 proc run(cp m inverse:W16.t Array768.t):(W16.t Array768.t option)*int = {
  var raw,candidate:W16.t Array768.t;var valid:bool;var result:W16.t Array768.t option;
  var rt_work:int;
  var rt_call_1:(W16.t Array768.t)*int;
  var rt_call_2:(W16.t Array768.t)*int;
  var rt_call_3:(bool)*int;
  rt_work<-6912;
  result<-None;rt_work<-rt_work+1;
  rt_call_1<@RTKernelRRecCore.run(cp,m,inverse);
  raw<-rt_call_1.`1;
  rt_work<-rt_work+rt_call_1.`2+2309;
  rt_call_2<@RTFixedWordChecks.normalize(raw);
  candidate<-rt_call_2.`1;
  rt_work<-rt_work+rt_call_2.`2+2307;
  rt_call_3<@RTFixedWordChecks.trit(candidate);
  valid<-rt_call_3.`1;
  rt_work<-rt_work+rt_call_3.`2+3;
  rt_work<-rt_work+1;
  if(valid){
   result<-Some candidate;rt_work<-rt_work+2306;
  }
  rt_work<-rt_work+2305;
  return(result,rt_work);
 }
}.

lemma rt_kernel_rrecfinish_projection :
 equiv[RTKernelRRecFinish.run ~ RRecFinish.run: ={cp,inverse,m} ==>res{1}.`1=res{2}].
proof.
 proc;sp 1 0;
 seq 2 1:(={cp,inverse,m,result}).
 + by auto.
 seq 3 1:(={cp,inverse,m,raw,result}).
 + by wp;call rt_kernel_rreccore_projection;auto.
 seq 3 1:(={candidate,cp,inverse,m,raw,result}).
 + by wp;call rt_fixed_normalize_projection;auto.
 seq 3 1:(={candidate,cp,inverse,m,raw,result,valid}).
 + by wp;call rt_fixed_trit_projection;auto.
 seq 2 1:(={candidate,cp,inverse,m,raw,result,valid}).
 + sp 1 0;if;first by auto.
   - seq 2 1:(={candidate,cp,inverse,m,raw,result,valid}).
     + by auto.
     auto.
   auto.
 auto.
qed.
lemma rt_kernel_rrecfinish_cost :
 hoare[RTKernelRRecFinish.run:true ==>0<=res.`2<=rt_kernel_rrecfinish_bound].
proof.
 proc;seq 1:(rt_work=6912);first by auto.
 seq 2:(0<=rt_work<=(6912+1)).
 + auto=> />;smt().
 seq 3:(0<=rt_work<=((6912+1)+(2309+rt_kernel_rreccore_bound))).
 + wp;call rt_kernel_rreccore_cost;auto=> />;smt().
 seq 3:(0<=rt_work<=(((6912+1)+(2309+rt_kernel_rreccore_bound))+(2307+rt_fixed_normalize_bound))).
 + wp;call rt_fixed_normalize_bound_cost;auto=> />;smt().
 seq 3:(0<=rt_work<=((((6912+1)+(2309+rt_kernel_rreccore_bound))+(2307+rt_fixed_normalize_bound))+(3+rt_fixed_trit_bound))).
 + wp;call rt_fixed_trit_bound_cost;auto=> />;smt().
 seq 2:(0<=rt_work<=(((((6912+1)+(2309+rt_kernel_rreccore_bound))+(2307+rt_fixed_normalize_bound))+(3+rt_fixed_trit_bound))+(1+(2306)))).
 + sp 1;if.
   - seq 2:(0<=rt_work<=((((((6912+1)+(2309+rt_kernel_rreccore_bound))+(2307+rt_fixed_normalize_bound))+(3+rt_fixed_trit_bound))+1)+2306)).
     + auto=> />;smt().
     auto=> />;smt().
   auto=> />;smt().
 auto=> />;smt().
qed.

op rt_kernel_linearusinginverse_bound:int = 11520+(1+3076+rt_fixed_frombytes_bound+2+(3+rt_fixed_trit_bound+1+(2309+rt_kernel_rrecfinish_bound)))+2305.
module RTKernelLinearUsingInverse = {
 proc run(pk:W8.t Array1152.t,m:W16.t Array768.t,ct:W8.t Array1152.t,inverse:W16.t Array768.t):(W16.t Array768.t option)*int = {
  var cp:W16.t Array768.t;var status:W32.t;var valid_message:bool;var result:W16.t Array768.t option;
  var rt_work:int;
  var rt_call_1:(W16.t Array768.t*W32.t)*int;
  var rt_call_3:(bool)*int;
  var rt_call_5:(W16.t Array768.t option)*int;
  rt_work<-11520;
  result<-None;rt_work<-rt_work+1;
  rt_call_1<@RTFixedFromBytes.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes(witness,ct);
  (cp,status)<-rt_call_1.`1;
  rt_work<-rt_work+rt_call_1.`2+3076;
  rt_work<-rt_work+2;
  if(status=W32.zero){
   rt_call_3<@RTFixedWordChecks.trit(m);
   valid_message<-rt_call_3.`1;
   rt_work<-rt_work+rt_call_3.`2+3;
   rt_work<-rt_work+1;
   if(valid_message){
    rt_call_5<@RTKernelRRecFinish.run(cp,m,inverse);
    result<-rt_call_5.`1;
    rt_work<-rt_work+rt_call_5.`2+2309;
   }
  }
  rt_work<-rt_work+2305;
  return(result,rt_work);
 }
}.

lemma rt_kernel_linearusinginverse_projection :
 equiv[RTKernelLinearUsingInverse.run ~ LinearRRecUsingInverse.run: ={ct,inverse,m,pk} ==>res{1}.`1=res{2}].
proof.
 proc;sp 1 0;
 seq 2 1:(={ct,inverse,m,pk,result}).
 + by auto.
 seq 3 1:(={cp,ct,inverse,m,pk,result,status}).
 + by wp;call rt_fixed_frombytes_jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes_projection;auto.
 seq 2 1:(={cp,ct,inverse,m,pk,result,status}).
 + sp 1 0;if;first by auto.
   - seq 3 1:(={cp,ct,inverse,m,pk,result,status,valid_message}).
     + by wp;call rt_fixed_trit_projection;auto.
     seq 2 1:(={cp,ct,inverse,m,pk,result,status,valid_message}).
     + sp 1 0;if;first by auto.
       - seq 3 1:(={cp,ct,inverse,m,pk,result,status,valid_message}).
         + by wp;call rt_kernel_rrecfinish_projection;auto.
         auto.
       auto.
     auto.
   auto.
 auto.
qed.
lemma rt_kernel_linearusinginverse_cost :
 hoare[RTKernelLinearUsingInverse.run:true ==>0<=res.`2<=rt_kernel_linearusinginverse_bound].
proof.
 proc;seq 1:(rt_work=11520);first by auto.
 seq 2:(0<=rt_work<=(11520+1)).
 + auto=> />;smt().
 seq 3:(0<=rt_work<=((11520+1)+(3076+rt_fixed_frombytes_bound))).
 + wp;call rt_fixed_frombytes_bound_cost;auto=> />;smt().
 seq 2:(0<=rt_work<=(((11520+1)+(3076+rt_fixed_frombytes_bound))+(2+(3+rt_fixed_trit_bound+1+(2309+rt_kernel_rrecfinish_bound))))).
 + sp 1;if.
   - seq 3:(0<=rt_work<=((((11520+1)+(3076+rt_fixed_frombytes_bound))+2)+(3+rt_fixed_trit_bound))).
     + wp;call rt_fixed_trit_bound_cost;auto=> />;smt().
     seq 2:(0<=rt_work<=(((((11520+1)+(3076+rt_fixed_frombytes_bound))+2)+(3+rt_fixed_trit_bound))+(1+(2309+rt_kernel_rrecfinish_bound)))).
     + sp 1;if.
       - seq 3:(0<=rt_work<=((((((11520+1)+(3076+rt_fixed_frombytes_bound))+2)+(3+rt_fixed_trit_bound))+1)+(2309+rt_kernel_rrecfinish_bound))).
         + wp;call rt_kernel_rrecfinish_cost;auto=> />;smt().
         auto=> />;smt().
       auto=> />;smt().
     auto=> />;smt().
   auto=> />;smt().
 auto=> />;smt().
qed.

op rt_kernel_linearrrec_bound:int = 9216+(1+3076+rt_fixed_frombytes_bound+2+(2307+rt_kernel_publicinverse_bound+2+(2311+rt_kernel_linearusinginverse_bound)))+2305.
module RTKernelLinearRRec = {
 proc run(pk:W8.t Array1152.t,m:W16.t Array768.t,ct:W8.t Array1152.t):(W16.t Array768.t option)*int = {
  var hp:W16.t Array768.t;var status:W32.t;var inverse,result:W16.t Array768.t option;
  var rt_work:int;
  var rt_call_1:(W16.t Array768.t*W32.t)*int;
  var rt_call_3:(W16.t Array768.t option)*int;
  var rt_call_5:(W16.t Array768.t option)*int;
  rt_work<-9216;
  result<-None;rt_work<-rt_work+1;
  rt_call_1<@RTFixedFromBytes.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes(witness,pk);
  (hp,status)<-rt_call_1.`1;
  rt_work<-rt_work+rt_call_1.`2+3076;
  rt_work<-rt_work+2;
  if(status=W32.zero){
   rt_call_3<@RTKernelPublicInverse.run(hp);
   inverse<-rt_call_3.`1;
   rt_work<-rt_work+rt_call_3.`2+2307;
   rt_work<-rt_work+2;
   if(inverse<>None){
    rt_call_5<@RTKernelLinearUsingInverse.run(pk,m,ct,oget inverse);
    result<-rt_call_5.`1;
    rt_work<-rt_work+rt_call_5.`2+2311;
   }
  }
  rt_work<-rt_work+2305;
  return(result,rt_work);
 }
}.

lemma rt_kernel_linearrrec_projection :
 equiv[RTKernelLinearRRec.run ~ LinearRRec.run: ={ct,m,pk} ==>res{1}.`1=res{2}].
proof.
 proc;sp 1 0;
 seq 2 1:(={ct,m,pk,result}).
 + by auto.
 seq 3 1:(={ct,hp,m,pk,result,status}).
 + by wp;call rt_fixed_frombytes_jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes_projection;auto.
 seq 2 1:(={ct,hp,m,pk,result,status}).
 + sp 1 0;if;first by auto.
   - seq 3 1:(={ct,hp,inverse,m,pk,result,status}).
     + by wp;call rt_kernel_publicinverse_projection;auto.
     seq 2 1:(={ct,hp,inverse,m,pk,result,status}).
     + sp 1 0;if;first by auto.
       - seq 3 1:(={ct,hp,inverse,m,pk,result,status}).
         + by wp;call rt_kernel_linearusinginverse_projection;auto.
         auto.
       auto.
     auto.
   auto.
 auto.
qed.
lemma rt_kernel_linearrrec_cost :
 hoare[RTKernelLinearRRec.run:true ==>0<=res.`2<=rt_kernel_linearrrec_bound].
proof.
 proc;seq 1:(rt_work=9216);first by auto.
 seq 2:(0<=rt_work<=(9216+1)).
 + auto=> />;smt().
 seq 3:(0<=rt_work<=((9216+1)+(3076+rt_fixed_frombytes_bound))).
 + wp;call rt_fixed_frombytes_bound_cost;auto=> />;smt().
 seq 2:(0<=rt_work<=(((9216+1)+(3076+rt_fixed_frombytes_bound))+(2+(2307+rt_kernel_publicinverse_bound+2+(2311+rt_kernel_linearusinginverse_bound))))).
 + sp 1;if.
   - seq 3:(0<=rt_work<=((((9216+1)+(3076+rt_fixed_frombytes_bound))+2)+(2307+rt_kernel_publicinverse_bound))).
     + wp;call rt_kernel_publicinverse_cost;auto=> />;smt().
     seq 2:(0<=rt_work<=(((((9216+1)+(3076+rt_fixed_frombytes_bound))+2)+(2307+rt_kernel_publicinverse_bound))+(2+(2311+rt_kernel_linearusinginverse_bound)))).
     + sp 1;if.
       - seq 3:(0<=rt_work<=((((((9216+1)+(3076+rt_fixed_frombytes_bound))+2)+(2307+rt_kernel_publicinverse_bound))+2)+(2311+rt_kernel_linearusinginverse_bound))).
         + wp;call rt_kernel_linearusinginverse_cost;auto=> />;smt().
         auto=> />;smt().
       auto=> />;smt().
     auto=> />;smt().
   auto=> />;smt().
 auto=> />;smt().
qed.

op rt_kernel_unit_bound:int = 2304+(3459+rt_kernel_encode_bound+3076+rt_fixed_frombytes_bound+2307+rt_kernel_publicinverse_bound)+2.
module RTKernelUnit = {
 proc run(a:W16.t Array768.t):(bool)*int = {
  var pk:W8.t Array1152.t;var hp:W16.t Array768.t;var status:W32.t;var inverse:W16.t Array768.t option;
  var rt_work:int;
  var rt_call_0:(W8.t Array1152.t)*int;
  var rt_call_1:(W16.t Array768.t*W32.t)*int;
  var rt_call_2:(W16.t Array768.t option)*int;
  rt_work<-2304;
  rt_call_0<@RTKernelEncode.run(a);
  pk<-rt_call_0.`1;
  rt_work<-rt_work+rt_call_0.`2+3459;
  rt_call_1<@RTFixedFromBytes.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes(witness,pk);
  (hp,status)<-rt_call_1.`1;
  rt_work<-rt_work+rt_call_1.`2+3076;
  rt_call_2<@RTKernelPublicInverse.run(hp);
  inverse<-rt_call_2.`1;
  rt_work<-rt_work+rt_call_2.`2+2307;
  rt_work<-rt_work+2;
  return(inverse<>None,rt_work);
 }
}.

lemma rt_kernel_unit_projection :
 equiv[RTKernelUnit.run ~ RTWordUnit.run: ={a} ==>res{1}.`1=res{2}].
proof.
 proc;sp 1 0;
 seq 3 1:(={a,pk}).
 + by wp;call rt_kernel_encode_projection;auto.
 seq 3 1:(={a,hp,pk,status}).
 + by wp;call rt_fixed_frombytes_jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes_projection;auto.
 seq 3 1:(={a,hp,inverse,pk,status}).
 + by wp;call rt_kernel_publicinverse_projection;auto.
 auto.
qed.
lemma rt_kernel_unit_cost :
 hoare[RTKernelUnit.run:true ==>0<=res.`2<=rt_kernel_unit_bound].
proof.
 proc;seq 1:(rt_work=2304);first by auto.
 seq 3:(0<=rt_work<=(2304+(3459+rt_kernel_encode_bound))).
 + wp;call rt_kernel_encode_cost;auto=> />;smt().
 seq 3:(0<=rt_work<=((2304+(3459+rt_kernel_encode_bound))+(3076+rt_fixed_frombytes_bound))).
 + wp;call rt_fixed_frombytes_bound_cost;auto=> />;smt().
 seq 3:(0<=rt_work<=(((2304+(3459+rt_kernel_encode_bound))+(3076+rt_fixed_frombytes_bound))+(2307+rt_kernel_publicinverse_bound))).
 + wp;call rt_kernel_publicinverse_cost;auto=> />;smt().
 auto=> />;smt().
qed.

op rt_kernel_recover_bound:int = 6912+(3459+rt_kernel_encode_bound+3459+rt_kernel_encode_bound+2309+rt_kernel_linearrrec_bound)+2305.
module RTKernelRecover = {
 proc run(a b code:W16.t Array768.t):(W16.t Array768.t option)*int = {
  var pk,ct:W8.t Array1152.t;var answer:W16.t Array768.t option;
  var rt_work:int;
  var rt_call_0:(W8.t Array1152.t)*int;
  var rt_call_1:(W8.t Array1152.t)*int;
  var rt_call_2:(W16.t Array768.t option)*int;
  rt_work<-6912;
  rt_call_0<@RTKernelEncode.run(a);
  pk<-rt_call_0.`1;
  rt_work<-rt_work+rt_call_0.`2+3459;
  rt_call_1<@RTKernelEncode.run(b);
  ct<-rt_call_1.`1;
  rt_work<-rt_work+rt_call_1.`2+3459;
  rt_call_2<@RTKernelLinearRRec.run(pk,code,ct);
  answer<-rt_call_2.`1;
  rt_work<-rt_work+rt_call_2.`2+2309;
  rt_work<-rt_work+2305;
  return(answer,rt_work);
 }
}.

lemma rt_kernel_recover_projection :
 equiv[RTKernelRecover.run ~ RTWordRecover.run: ={a,b,code} ==>res{1}.`1=res{2}].
proof.
 proc;sp 1 0;
 seq 3 1:(={a,b,code,pk}).
 + by wp;call rt_kernel_encode_projection;auto.
 seq 3 1:(={a,b,code,ct,pk}).
 + by wp;call rt_kernel_encode_projection;auto.
 seq 3 1:(={a,answer,b,code,ct,pk}).
 + by wp;call rt_kernel_linearrrec_projection;auto.
 auto.
qed.
lemma rt_kernel_recover_cost :
 hoare[RTKernelRecover.run:true ==>0<=res.`2<=rt_kernel_recover_bound].
proof.
 proc;seq 1:(rt_work=6912);first by auto.
 seq 3:(0<=rt_work<=(6912+(3459+rt_kernel_encode_bound))).
 + wp;call rt_kernel_encode_cost;auto=> />;smt().
 seq 3:(0<=rt_work<=((6912+(3459+rt_kernel_encode_bound))+(3459+rt_kernel_encode_bound))).
 + wp;call rt_kernel_encode_cost;auto=> />;smt().
 seq 3:(0<=rt_work<=(((6912+(3459+rt_kernel_encode_bound))+(3459+rt_kernel_encode_bound))+(2309+rt_kernel_linearrrec_bound))).
 + wp;call rt_kernel_linearrrec_cost;auto=> />;smt().
 auto=> />;smt().
qed.

op rt_kernel_mreccandidate_bound:int = 6912+(3076+rt_fixed_ntt_bound+3077+rt_fixed_basemul_bound+3077+rt_fixed_polysub_bound+2307+rt_fixed_normalize_bound+3076+rt_fixed_invntt_bound+2307+rt_fixed_normalize_bound)+2305.
module RTKernelMRecCandidate = {
 proc run(hp cp r:W16.t Array768.t):(W16.t Array768.t)*int = {
  var rh,product,difference,centered,inverse,result:W16.t Array768.t;
  var rt_work:int;
  var rt_call_0:(W16.t Array768.t)*int;
  var rt_call_1:(W16.t Array768.t)*int;
  var rt_call_2:(W16.t Array768.t)*int;
  var rt_call_3:(W16.t Array768.t)*int;
  var rt_call_4:(W16.t Array768.t)*int;
  var rt_call_5:(W16.t Array768.t)*int;
  rt_work<-6912;
  rt_call_0<@RTFixedNTT.jade_ntruplus_ntruplus768_amd64_ref_ntt(witness,r);
  rh<-rt_call_0.`1;
  rt_work<-rt_work+rt_call_0.`2+3076;
  rt_call_1<@RTFixedBasemul.jade_ntruplus_ntruplus768_amd64_ref_poly_basemul(witness,hp,rh);
  product<-rt_call_1.`1;
  rt_work<-rt_work+rt_call_1.`2+3077;
  rt_call_2<@RTFixedPolySub.jade_ntruplus_ntruplus768_amd64_ref_poly_sub(witness,cp,product);
  difference<-rt_call_2.`1;
  rt_work<-rt_work+rt_call_2.`2+3077;
  rt_call_3<@RTFixedWordChecks.normalize(difference);
  centered<-rt_call_3.`1;
  rt_work<-rt_work+rt_call_3.`2+2307;
  rt_call_4<@RTFixedInvNTT.jade_ntruplus_ntruplus768_amd64_ref_invntt(witness,centered);
  inverse<-rt_call_4.`1;
  rt_work<-rt_work+rt_call_4.`2+3076;
  rt_call_5<@RTFixedWordChecks.normalize(inverse);
  result<-rt_call_5.`1;
  rt_work<-rt_work+rt_call_5.`2+2307;
  rt_work<-rt_work+2305;
  return(result,rt_work);
 }
}.

lemma rt_kernel_mreccandidate_projection :
 equiv[RTKernelMRecCandidate.run ~ MRecCandidate.run: ={cp,hp,r} ==>res{1}.`1=res{2}].
proof.
 proc;sp 1 0;
 seq 3 1:(={cp,hp,r,rh}).
 + by wp;call rt_fixed_ntt_jade_ntruplus_ntruplus768_amd64_ref_ntt_projection;auto.
 seq 3 1:(={cp,hp,product,r,rh}).
 + by wp;call rt_fixed_basemul_jade_ntruplus_ntruplus768_amd64_ref_poly_basemul_projection;auto.
 seq 3 1:(={cp,difference,hp,product,r,rh}).
 + by wp;call rt_fixed_polysub_jade_ntruplus_ntruplus768_amd64_ref_poly_sub_projection;auto.
 seq 3 1:(={centered,cp,difference,hp,product,r,rh}).
 + by wp;call rt_fixed_normalize_projection;auto.
 seq 3 1:(={centered,cp,difference,hp,inverse,product,r,rh}).
 + by wp;call rt_fixed_invntt_jade_ntruplus_ntruplus768_amd64_ref_invntt_projection;auto.
 seq 3 1:(={centered,cp,difference,hp,inverse,product,r,result,rh}).
 + by wp;call rt_fixed_normalize_projection;auto.
 auto.
qed.
lemma rt_kernel_mreccandidate_cost :
 hoare[RTKernelMRecCandidate.run:true ==>0<=res.`2<=rt_kernel_mreccandidate_bound].
proof.
 proc;seq 1:(rt_work=6912);first by auto.
 seq 3:(0<=rt_work<=(6912+(3076+rt_fixed_ntt_bound))).
 + wp;call rt_fixed_ntt_bound_cost;auto=> />;smt().
 seq 3:(0<=rt_work<=((6912+(3076+rt_fixed_ntt_bound))+(3077+rt_fixed_basemul_bound))).
 + wp;call rt_fixed_basemul_bound_cost;auto=> />;smt().
 seq 3:(0<=rt_work<=(((6912+(3076+rt_fixed_ntt_bound))+(3077+rt_fixed_basemul_bound))+(3077+rt_fixed_polysub_bound))).
 + wp;call rt_fixed_polysub_bound_cost;auto=> />;smt().
 seq 3:(0<=rt_work<=((((6912+(3076+rt_fixed_ntt_bound))+(3077+rt_fixed_basemul_bound))+(3077+rt_fixed_polysub_bound))+(2307+rt_fixed_normalize_bound))).
 + wp;call rt_fixed_normalize_bound_cost;auto=> />;smt().
 seq 3:(0<=rt_work<=(((((6912+(3076+rt_fixed_ntt_bound))+(3077+rt_fixed_basemul_bound))+(3077+rt_fixed_polysub_bound))+(2307+rt_fixed_normalize_bound))+(3076+rt_fixed_invntt_bound))).
 + wp;call rt_fixed_invntt_bound_cost;auto=> />;smt().
 seq 3:(0<=rt_work<=((((((6912+(3076+rt_fixed_ntt_bound))+(3077+rt_fixed_basemul_bound))+(3077+rt_fixed_polysub_bound))+(2307+rt_fixed_normalize_bound))+(3076+rt_fixed_invntt_bound))+(2307+rt_fixed_normalize_bound))).
 + wp;call rt_fixed_normalize_bound_cost;auto=> />;smt().
 auto=> />;smt().
qed.

op rt_kernel_mrec_bound:int = 9216+(1+3076+rt_fixed_frombytes_bound+3076+rt_fixed_frombytes_bound+3+rt_fixed_trit_bound+5+(2309+rt_kernel_mreccandidate_bound+3+rt_fixed_trit_bound+1+(2306)))+2305.
module RTKernelMRec = {
 proc run(pk:W8.t Array1152.t,r:W16.t Array768.t,ct:W8.t Array1152.t):(W16.t Array768.t option)*int = {
  var hp,cp,m:W16.t Array768.t;var hs,cs:W32.t;var valid:bool;var result:W16.t Array768.t option;
  var rt_work:int;
  var rt_call_1:(W16.t Array768.t*W32.t)*int;
  var rt_call_2:(W16.t Array768.t*W32.t)*int;
  var rt_call_3:(bool)*int;
  var rt_call_5:(W16.t Array768.t)*int;
  var rt_call_6:(bool)*int;
  rt_work<-9216;
  result<-None;rt_work<-rt_work+1;
  rt_call_1<@RTFixedFromBytes.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes(witness,pk);
  (hp,hs)<-rt_call_1.`1;
  rt_work<-rt_work+rt_call_1.`2+3076;
  rt_call_2<@RTFixedFromBytes.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes(witness,ct);
  (cp,cs)<-rt_call_2.`1;
  rt_work<-rt_work+rt_call_2.`2+3076;
  rt_call_3<@RTFixedWordChecks.trit(r);
  valid<-rt_call_3.`1;
  rt_work<-rt_work+rt_call_3.`2+3;
  rt_work<-rt_work+5;
  if(hs=W32.zero /\ cs=W32.zero /\ valid){
   rt_call_5<@RTKernelMRecCandidate.run(hp,cp,r);
   m<-rt_call_5.`1;
   rt_work<-rt_work+rt_call_5.`2+2309;
   rt_call_6<@RTFixedWordChecks.trit(m);
   valid<-rt_call_6.`1;
   rt_work<-rt_work+rt_call_6.`2+3;
   rt_work<-rt_work+1;
   if(valid){
    result<-Some m;rt_work<-rt_work+2306;
   }
  }
  rt_work<-rt_work+2305;
  return(result,rt_work);
 }
}.

lemma rt_kernel_mrec_projection :
 equiv[RTKernelMRec.run ~ MRec.run: ={ct,pk,r} ==>res{1}.`1=res{2}].
proof.
 proc;sp 1 0;
 seq 2 1:(={ct,pk,r,result}).
 + by auto.
 seq 3 1:(={ct,hp,hs,pk,r,result}).
 + by wp;call rt_fixed_frombytes_jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes_projection;auto.
 seq 3 1:(={cp,cs,ct,hp,hs,pk,r,result}).
 + by wp;call rt_fixed_frombytes_jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes_projection;auto.
 seq 3 1:(={cp,cs,ct,hp,hs,pk,r,result,valid}).
 + by wp;call rt_fixed_trit_projection;auto.
 seq 2 1:(={cp,cs,ct,hp,hs,pk,r,result,valid}).
 + sp 1 0;if;first by auto.
   - seq 3 1:(={cp,cs,ct,hp,hs,m,pk,r,result,valid}).
     + by wp;call rt_kernel_mreccandidate_projection;auto.
     seq 3 1:(={cp,cs,ct,hp,hs,m,pk,r,result,valid}).
     + by wp;call rt_fixed_trit_projection;auto.
     seq 2 1:(={cp,cs,ct,hp,hs,m,pk,r,result,valid}).
     + sp 1 0;if;first by auto.
       - seq 2 1:(={cp,cs,ct,hp,hs,m,pk,r,result,valid}).
         + by auto.
         auto.
       auto.
     auto.
   auto.
 auto.
qed.
lemma rt_kernel_mrec_cost :
 hoare[RTKernelMRec.run:true ==>0<=res.`2<=rt_kernel_mrec_bound].
proof.
 proc;seq 1:(rt_work=9216);first by auto.
 seq 2:(0<=rt_work<=(9216+1)).
 + auto=> />;smt().
 seq 3:(0<=rt_work<=((9216+1)+(3076+rt_fixed_frombytes_bound))).
 + wp;call rt_fixed_frombytes_bound_cost;auto=> />;smt().
 seq 3:(0<=rt_work<=(((9216+1)+(3076+rt_fixed_frombytes_bound))+(3076+rt_fixed_frombytes_bound))).
 + wp;call rt_fixed_frombytes_bound_cost;auto=> />;smt().
 seq 3:(0<=rt_work<=((((9216+1)+(3076+rt_fixed_frombytes_bound))+(3076+rt_fixed_frombytes_bound))+(3+rt_fixed_trit_bound))).
 + wp;call rt_fixed_trit_bound_cost;auto=> />;smt().
 seq 2:(0<=rt_work<=(((((9216+1)+(3076+rt_fixed_frombytes_bound))+(3076+rt_fixed_frombytes_bound))+(3+rt_fixed_trit_bound))+(5+(2309+rt_kernel_mreccandidate_bound+3+rt_fixed_trit_bound+1+(2306))))).
 + sp 1;if.
   - seq 3:(0<=rt_work<=((((((9216+1)+(3076+rt_fixed_frombytes_bound))+(3076+rt_fixed_frombytes_bound))+(3+rt_fixed_trit_bound))+5)+(2309+rt_kernel_mreccandidate_bound))).
     + wp;call rt_kernel_mreccandidate_cost;auto=> />;smt().
     seq 3:(0<=rt_work<=(((((((9216+1)+(3076+rt_fixed_frombytes_bound))+(3076+rt_fixed_frombytes_bound))+(3+rt_fixed_trit_bound))+5)+(2309+rt_kernel_mreccandidate_bound))+(3+rt_fixed_trit_bound))).
     + wp;call rt_fixed_trit_bound_cost;auto=> />;smt().
     seq 2:(0<=rt_work<=((((((((9216+1)+(3076+rt_fixed_frombytes_bound))+(3076+rt_fixed_frombytes_bound))+(3+rt_fixed_trit_bound))+5)+(2309+rt_kernel_mreccandidate_bound))+(3+rt_fixed_trit_bound))+(1+(2306)))).
     + sp 1;if.
       - seq 2:(0<=rt_work<=(((((((((9216+1)+(3076+rt_fixed_frombytes_bound))+(3076+rt_fixed_frombytes_bound))+(3+rt_fixed_trit_bound))+5)+(2309+rt_kernel_mreccandidate_bound))+(3+rt_fixed_trit_bound))+1)+2306)).
         + auto=> />;smt().
         auto=> />;smt().
       auto=> />;smt().
     auto=> />;smt().
   auto=> />;smt().
 auto=> />;smt().
qed.

op rt_kernel_decodecandidate_bound:int = 2304+(2307+rt_fixed_normalize_bound+3076+rt_fixed_invntt_bound+2307+rt_fixed_normalize_bound)+2305.
module RTKernelDecodeCandidate = {
 proc run(cp:W16.t Array768.t):(W16.t Array768.t)*int = {
  var centered,inverse,r:W16.t Array768.t;
  var rt_work:int;
  var rt_call_0:(W16.t Array768.t)*int;
  var rt_call_1:(W16.t Array768.t)*int;
  var rt_call_2:(W16.t Array768.t)*int;
  rt_work<-2304;
  rt_call_0<@RTFixedWordChecks.normalize(cp);
  centered<-rt_call_0.`1;
  rt_work<-rt_work+rt_call_0.`2+2307;
  rt_call_1<@RTFixedInvNTT.jade_ntruplus_ntruplus768_amd64_ref_invntt(witness,centered);
  inverse<-rt_call_1.`1;
  rt_work<-rt_work+rt_call_1.`2+3076;
  rt_call_2<@RTFixedWordChecks.normalize(inverse);
  r<-rt_call_2.`1;
  rt_work<-rt_work+rt_call_2.`2+2307;
  rt_work<-rt_work+2305;
  return(r,rt_work);
 }
}.

lemma rt_kernel_decodecandidate_projection :
 equiv[RTKernelDecodeCandidate.run ~ MRecDecodeCandidate.run: ={cp} ==>res{1}.`1=res{2}].
proof.
 proc;sp 1 0;
 seq 3 1:(={centered,cp}).
 + by wp;call rt_fixed_normalize_projection;auto.
 seq 3 1:(={centered,cp,inverse}).
 + by wp;call rt_fixed_invntt_jade_ntruplus_ntruplus768_amd64_ref_invntt_projection;auto.
 seq 3 1:(={centered,cp,inverse,r}).
 + by wp;call rt_fixed_normalize_projection;auto.
 auto.
qed.
lemma rt_kernel_decodecandidate_cost :
 hoare[RTKernelDecodeCandidate.run:true ==>0<=res.`2<=rt_kernel_decodecandidate_bound].
proof.
 proc;seq 1:(rt_work=2304);first by auto.
 seq 3:(0<=rt_work<=(2304+(2307+rt_fixed_normalize_bound))).
 + wp;call rt_fixed_normalize_bound_cost;auto=> />;smt().
 seq 3:(0<=rt_work<=((2304+(2307+rt_fixed_normalize_bound))+(3076+rt_fixed_invntt_bound))).
 + wp;call rt_fixed_invntt_bound_cost;auto=> />;smt().
 seq 3:(0<=rt_work<=(((2304+(2307+rt_fixed_normalize_bound))+(3076+rt_fixed_invntt_bound))+(2307+rt_fixed_normalize_bound))).
 + wp;call rt_fixed_normalize_bound_cost;auto=> />;smt().
 auto=> />;smt().
qed.

op rt_kernel_decode_bound:int = 3456+(1+3076+rt_fixed_frombytes_bound+2+(2307+rt_kernel_decodecandidate_bound+3+rt_fixed_trit_bound+1+(2306)))+2305.
module RTKernelDecode = {
 proc run(query:W8.t Array1152.t):(W16.t Array768.t option)*int = {
  var cp,r:W16.t Array768.t;var status:W32.t;var valid:bool;var result:W16.t Array768.t option;
  var rt_work:int;
  var rt_call_1:(W16.t Array768.t*W32.t)*int;
  var rt_call_3:(W16.t Array768.t)*int;
  var rt_call_4:(bool)*int;
  rt_work<-3456;
  result<-None;rt_work<-rt_work+1;
  rt_call_1<@RTFixedFromBytes.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes(witness,query);
  (cp,status)<-rt_call_1.`1;
  rt_work<-rt_work+rt_call_1.`2+3076;
  rt_work<-rt_work+2;
  if(status=W32.zero){
   rt_call_3<@RTKernelDecodeCandidate.run(cp);
   r<-rt_call_3.`1;
   rt_work<-rt_work+rt_call_3.`2+2307;
   rt_call_4<@RTFixedWordChecks.trit(r);
   valid<-rt_call_4.`1;
   rt_work<-rt_work+rt_call_4.`2+3;
   rt_work<-rt_work+1;
   if(valid){
    result<-Some r;rt_work<-rt_work+2306;
   }
  }
  rt_work<-rt_work+2305;
  return(result,rt_work);
 }
}.

lemma rt_kernel_decode_projection :
 equiv[RTKernelDecode.run ~ MRecDecode.run: ={query} ==>res{1}.`1=res{2}].
proof.
 proc;sp 1 0;
 seq 2 1:(={query,result}).
 + by auto.
 seq 3 1:(={cp,query,result,status}).
 + by wp;call rt_fixed_frombytes_jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes_projection;auto.
 seq 2 1:(={cp,query,result,status}).
 + sp 1 0;if;first by auto.
   - seq 3 1:(={cp,query,r,result,status}).
     + by wp;call rt_kernel_decodecandidate_projection;auto.
     seq 3 1:(={cp,query,r,result,status,valid}).
     + by wp;call rt_fixed_trit_projection;auto.
     seq 2 1:(={cp,query,r,result,status,valid}).
     + sp 1 0;if;first by auto.
       - seq 2 1:(={cp,query,r,result,status,valid}).
         + by auto.
         auto.
       auto.
     auto.
   auto.
 auto.
qed.
lemma rt_kernel_decode_cost :
 hoare[RTKernelDecode.run:true ==>0<=res.`2<=rt_kernel_decode_bound].
proof.
 proc;seq 1:(rt_work=3456);first by auto.
 seq 2:(0<=rt_work<=(3456+1)).
 + auto=> />;smt().
 seq 3:(0<=rt_work<=((3456+1)+(3076+rt_fixed_frombytes_bound))).
 + wp;call rt_fixed_frombytes_bound_cost;auto=> />;smt().
 seq 2:(0<=rt_work<=(((3456+1)+(3076+rt_fixed_frombytes_bound))+(2+(2307+rt_kernel_decodecandidate_bound+3+rt_fixed_trit_bound+1+(2306))))).
 + sp 1;if.
   - seq 3:(0<=rt_work<=((((3456+1)+(3076+rt_fixed_frombytes_bound))+2)+(2307+rt_kernel_decodecandidate_bound))).
     + wp;call rt_kernel_decodecandidate_cost;auto=> />;smt().
     seq 3:(0<=rt_work<=(((((3456+1)+(3076+rt_fixed_frombytes_bound))+2)+(2307+rt_kernel_decodecandidate_bound))+(3+rt_fixed_trit_bound))).
     + wp;call rt_fixed_trit_bound_cost;auto=> />;smt().
     seq 2:(0<=rt_work<=((((((3456+1)+(3076+rt_fixed_frombytes_bound))+2)+(2307+rt_kernel_decodecandidate_bound))+(3+rt_fixed_trit_bound))+(1+(2306)))).
     + sp 1;if.
       - seq 2:(0<=rt_work<=(((((((3456+1)+(3076+rt_fixed_frombytes_bound))+2)+(2307+rt_kernel_decodecandidate_bound))+(3+rt_fixed_trit_bound))+1)+2306)).
         + auto=> />;smt().
         auto=> />;smt().
       auto=> />;smt().
     auto=> />;smt().
   auto=> />;smt().
 auto=> />;smt().
qed.

op rt_kernel_candidate_bound:int = 10368+(2307+rt_kernel_decode_bound+1+2+(2310+rt_kernel_mrec_bound+2+(4613)))+4609.
module RTKernelCandidate = {
 proc run(pk ct query:W8.t Array1152.t):((W16.t Array768.t*W16.t Array768.t) option)*int = {
  var ro,mo:W16.t Array768.t option;var result:(W16.t Array768.t*W16.t Array768.t) option;
  var rt_work:int;
  var rt_call_0:(W16.t Array768.t option)*int;
  var rt_call_3:(W16.t Array768.t option)*int;
  rt_work<-10368;
  rt_call_0<@RTKernelDecode.run(query);
  ro<-rt_call_0.`1;
  rt_work<-rt_work+rt_call_0.`2+2307;
  result<-None;rt_work<-rt_work+1;
  rt_work<-rt_work+2;
  if(ro<>None){
   rt_call_3<@RTKernelMRec.run(pk,oget ro,ct);
   mo<-rt_call_3.`1;
   rt_work<-rt_work+rt_call_3.`2+2310;
   rt_work<-rt_work+2;
   if(mo<>None){
    result<-Some(oget mo,oget ro);rt_work<-rt_work+4613;
   }
  }
  rt_work<-rt_work+4609;
  return(result,rt_work);
 }
}.

lemma rt_kernel_candidate_projection :
 equiv[RTKernelCandidate.run ~ SecCandidate.run: ={ct,pk,query} ==>res{1}.`1=res{2}].
proof.
 proc;sp 1 0;
 seq 3 1:(={ct,pk,query,ro}).
 + by wp;call rt_kernel_decode_projection;auto.
 seq 2 1:(={ct,pk,query,result,ro}).
 + by auto.
 seq 2 1:(={ct,pk,query,result,ro}).
 + sp 1 0;if;first by auto.
   - seq 3 1:(={ct,mo,pk,query,result,ro}).
     + by wp;call rt_kernel_mrec_projection;auto.
     seq 2 1:(={ct,mo,pk,query,result,ro}).
     + sp 1 0;if;first by auto.
       - seq 2 1:(={ct,mo,pk,query,result,ro}).
         + by auto.
         auto.
       auto.
     auto.
   auto.
 auto.
qed.
lemma rt_kernel_candidate_cost :
 hoare[RTKernelCandidate.run:true ==>0<=res.`2<=rt_kernel_candidate_bound].
proof.
 proc;seq 1:(rt_work=10368);first by auto.
 seq 3:(0<=rt_work<=(10368+(2307+rt_kernel_decode_bound))).
 + wp;call rt_kernel_decode_cost;auto=> />;smt().
 seq 2:(0<=rt_work<=((10368+(2307+rt_kernel_decode_bound))+1)).
 + auto=> />;smt().
 seq 2:(0<=rt_work<=(((10368+(2307+rt_kernel_decode_bound))+1)+(2+(2310+rt_kernel_mrec_bound+2+(4613))))).
 + sp 1;if.
   - seq 3:(0<=rt_work<=((((10368+(2307+rt_kernel_decode_bound))+1)+2)+(2310+rt_kernel_mrec_bound))).
     + wp;call rt_kernel_mrec_cost;auto=> />;smt().
     seq 2:(0<=rt_work<=(((((10368+(2307+rt_kernel_decode_bound))+1)+2)+(2310+rt_kernel_mrec_bound))+(2+(4613)))).
     + sp 1;if.
       - seq 2:(0<=rt_work<=((((((10368+(2307+rt_kernel_decode_bound))+1)+2)+(2310+rt_kernel_mrec_bound))+2)+4613)).
         + auto=> />;smt().
         auto=> />;smt().
       auto=> />;smt().
     auto=> />;smt().
   auto=> />;smt().
 auto=> />;smt().
qed.

