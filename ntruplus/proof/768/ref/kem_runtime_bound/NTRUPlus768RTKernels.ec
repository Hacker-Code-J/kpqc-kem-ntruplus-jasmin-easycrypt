require import AllCore List Distr StdOrder.
from Jasmin require import JWord.
require import Array32 Array768 Array1152.
require import NTRUPlus768PKEModel NTRUPlus768PKEKeyDistribution.
require import NTRUPlus768PKEProcedures NTRUPlus768PKECallProof.
require import NTRUPlus768RRecWordChecks NTRUPlus768HistKey.
require import NTRUPlus768SecModel NTRUPlus768SecBaseGames.
require import NTRUPlus768OWGames NTRUPlus768INJGames.
require import NTRUPlus768OWCodec NTRUPlus768OWCodecCalls NTRUPlus768OWCodecProof.
require import NTRUPlus768OWUniform NTRUPlus768CyclotomicFactorization.
require import NTRUPlus768EncapGuardSpec.
import IntOrder.

require import NTRUPlus768RTKernelTypes.

module RTPolyEqual = {
 proc run(x y:pke_poly):bool = {
  var same,word_equal:bool;var i:int;
  same<-true;i<-0;
  while(i<768){
   word_equal<-(x.[i]=y.[i]);same<-same /\ word_equal;i<-i+1;
  }
  return same;
 }
}.
lemma rt_poly_equal_ll : islossless RTPolyEqual.run.
proof. proc;while true(768-i);auto=> />;smt(). qed.
lemma rt_poly_equal_spec x0 y0 :
 hoare[RTPolyEqual.run:x=x0 /\ y=y0 ==>res=(x0=y0)].
proof.
 proc;while(x=x0 /\ y=y0 /\ 0<=i<=768 /\
 same=(forall j,0<=j<i=>x0.[j]=y0.[j])).
 + auto=> />;smt().
 auto=> />;smt(Array768.tP).
qed.
lemma rt_poly_equal_correct x0 y0 :
 phoare[RTPolyEqual.run:x=x0 /\ y=y0 ==>res=(x0=y0)]=1%r.
proof. by conseq rt_poly_equal_ll(rt_poly_equal_spec x0 y0). qed.

module RTINJCheck = {
 proc run(pk:W8.t Array1152.t,collision:sec_collision):bool*rt_kernel_profile = {
  var v0,v1,v2,v3,em,er,win:bool;
  var c0,c1:W8.t Array1152.t option;var cmp:bool*int;
  var trits,polys,encryptions,ciphers:int;
  win<-false;trits<-0;polys<-0;encryptions<-0;ciphers<-0;
  v0<@RRecTrit.check(collision.`1);trits<-trits+1;
  v1<@RRecTrit.check(collision.`2);trits<-trits+1;
  v2<@RRecTrit.check(collision.`3);trits<-trits+1;
  v3<@RRecTrit.check(collision.`4);trits<-trits+1;
  em<@RTPolyEqual.run(collision.`1,collision.`2);polys<-polys+1;
  er<@RTPolyEqual.run(collision.`3,collision.`4);polys<-polys+1;
  if(v0 /\ v1 /\ v2 /\ v3 /\ !(em /\ er)){
   c0<@PKEEnc.run(pk,collision.`1,collision.`3);encryptions<-encryptions+1;
   c1<@PKEEnc.run(pk,collision.`2,collision.`4);encryptions<-encryptions+1;
   match c0 with
   | None => {}
   | Some x => {
    match c1 with
    | None => {}
    | Some y => {cmp<@HistKey.cipher(x,y);ciphers<-ciphers+1;win<-cmp.`1;}
    end;
   }
   end;
  }
  return(win,rtk_profile 0 0 0 0 encryptions trits polys ciphers 0 0);
 }
}.

(* The caller's canonical-key/domain contract makes the None branch
   unreachable. Its explicit default keeps the procedure total. *)
module RTEncrypt = {
 proc run(pk:W8.t Array1152.t,m r:pke_poly):W8.t Array1152.t*rt_kernel_profile = {
  var out:W8.t Array1152.t option;var ct:W8.t Array1152.t;var calls:int;
  calls<-0;out<@PKEEnc.run(pk,m,r);calls<-calls+1;
  ct<-if out=None then Array1152.init(fun _=>W8.zero) else oget out;
  return(ct,rtk_profile 0 0 0 0 calls 0 0 0 0 0);
 }
}.
module RTOWKernel(B:SecOWAdversary) = {
 proc run(pk:W8.t Array1152.t):bool*rt_kernel_profile = {
  var code,r,answer:pke_poly;var out:W8.t Array1152.t*rt_kernel_profile;
  var win:bool;var draws,calls,comparisons:int;
  draws<-0;calls<-0;comparisons<-0;
  code<$pke_psi1;draws<-draws+1;
  r<$pke_psi1;draws<-draws+1;
  out<@RTEncrypt.run(pk,code,r);
  answer<@B.run(pk,out.`1);calls<-calls+1;
  win<@RTPolyEqual.run(answer,code);comparisons<-comparisons+1;
  return(win,rtk_add out.`2(rtk_profile 0 0 0 0 0 0 comparisons 0 draws calls));
 }
}.
module RTINJNTRUReduction(B:SecINJAdversary) = {
 proc run(h:NTRUPoly.poly):bool*rt_kernel_profile = {
  var a:NTRUPoly.poly;var pk:W8.t Array1152.t;var collision:sec_collision;
  var accept,win:bool;var checked:bool*rt_kernel_profile;
  var scales,units,encodes,calls:int;var profile:rt_kernel_profile;
  scales<-0;units<-0;encodes<-0;calls<-0;win<-false;
  profile<-rtk_profile 0 0 0 0 0 0 0 0 0 0;
  a<-ow_scale3 h;scales<-scales+1;
  accept<@OWUnitTest.run(a);units<-units+1;
  if(accept){
   pk<@OWEncode.run(a);encodes<-encodes+1;
   collision<@B.run(pk);calls<-calls+1;
   checked<@RTINJCheck.run(pk,collision);win<-checked.`1;profile<-checked.`2;
  }
  return(win,rtk_add profile(rtk_profile scales units encodes 0 0 0 0 0 0 calls));
 }
}.
module RTOWNTRUReduction(B:SecOWAdversary) = {
 proc run(h:NTRUPoly.poly):bool*rt_kernel_profile = {
  var a:NTRUPoly.poly;var pk:W8.t Array1152.t;
  var accept,win:bool;var checked:bool*rt_kernel_profile;
  var scales,units,encodes:int;var profile:rt_kernel_profile;
  scales<-0;units<-0;encodes<-0;win<-false;
  profile<-rtk_profile 0 0 0 0 0 0 0 0 0 0;
  a<-ow_scale3 h;scales<-scales+1;
  accept<@OWUnitTest.run(a);units<-units+1;
  if(accept){
   pk<@OWEncode.run(a);encodes<-encodes+1;
   checked<@RTOWKernel(B).run(pk);win<-checked.`1;profile<-checked.`2;
  }
  return(win,rtk_add profile(rtk_profile scales units encodes 0 0 0 0 0 0 0));
 }
}.
module RTOWRLWESolver(B:SecOWAdversary) = {
 proc run(a b:NTRUPoly.poly):NTRUPoly.poly*rt_kernel_profile = {
  var pk,ct:W8.t Array1152.t;var code:pke_poly;var answer:NTRUPoly.poly;var accept:bool;
  var units,encodes,recovers,calls:int;
  units<-0;encodes<-0;recovers<-0;calls<-0;answer<-NTRUPoly.poly0;
  accept<@OWUnitTest.run(a);units<-units+1;
  if(accept){
   pk<@OWEncode.run(a);encodes<-encodes+1;
   ct<@OWEncode.run(b);encodes<-encodes+1;
   code<@B.run(pk,ct);calls<-calls+1;
   answer<@OWRecover.run(a,b,code);recovers<-recovers+1;
  }
  return(answer,rtk_profile 0 units encodes recovers 0 0 0 0 0 calls);
 }
}.

lemma rt_pke_enc_spec pk0 m0 r0 :
 hoare[PKEEnc.run:pk=pk0 /\ m=m0 /\ r=r0 /\ pke_domain m0 /\ pke_domain r0 ==>
 res=pke_enc_spec pk0 m0 r0].
proof.
 case(pke_domain m0 /\ pke_domain r0)=>h.
 + have [hm hr]:=h;conseq(pke_enc_functional pk0 m0 r0 hm hr);smt().
 exfalso=> />;smt().
qed.
lemma rt_pke_enc_correct pk0 m0 r0 :
 phoare[PKEEnc.run:pk=pk0 /\ m=m0 /\ r=r0 /\ pke_domain m0 /\ pke_domain r0 ==>
 res=pke_enc_spec pk0 m0 r0]=1%r.
proof. by conseq pke_enc_lossless(rt_pke_enc_spec pk0 m0 r0). qed.

lemma rt_encrypt_ll : islossless RTEncrypt.run.
proof. proc;wp;call pke_enc_lossless;auto. qed.
lemma rt_encrypt_spec pk0 m0 r0 :
 hoare[RTEncrypt.run:pk=pk0 /\ m=m0 /\ r=r0 /\
 encap_key_canonical pk0 /\ pke_domain m0 /\ pke_domain r0 ==>
 res.`1=pke_ciphertext pk0 m0 r0 /\ res.`2=rtk_profile 0 0 0 0 1 0 0 0 0 0].
proof.
 proc;wp;call(rt_pke_enc_spec pk0 m0 r0);auto=> />.
 rewrite /pke_enc_spec;smt().
qed.
lemma rt_encrypt_correct pk0 m0 r0 :
 phoare[RTEncrypt.run:pk=pk0 /\ m=m0 /\ r=r0 /\
 encap_key_canonical pk0 /\ pke_domain m0 /\ pke_domain r0 ==>
 res.`1=pke_ciphertext pk0 m0 r0 /\ res.`2=rtk_profile 0 0 0 0 1 0 0 0 0 0]=1%r.
proof. by conseq rt_encrypt_ll(rt_encrypt_spec pk0 m0 r0). qed.
lemma rt_encrypt_profile :
 hoare[RTEncrypt.run:true ==>res.`2=rtk_profile 0 0 0 0 1 0 0 0 0 0].
proof. proc;wp;call(_:true ==>true);first by trivial. auto. qed.

lemma rt_inj_check_ll : islossless RTINJCheck.run.
proof.
 proc;seq 17:true;1,4,5:by auto.
 + wp;call rt_poly_equal_ll;wp;call rt_poly_equal_ll;
   wp;call rrec_trit_lossless;wp;call rrec_trit_lossless;
   wp;call rrec_trit_lossless;wp;call rrec_trit_lossless;auto.
 if;last by auto.
 seq 4:true;1,4,5:by auto.
 + wp;call pke_enc_lossless;wp;call pke_enc_lossless;auto.
 match;first by auto.
 match;first by auto.
 wp;call hist_cipher_lossless;auto.
qed.
lemma rt_inj_check_spec pk0 coll0 :
 hoare[RTINJCheck.run:pk=pk0 /\ collision=coll0 ==>res.`1=sec_inj_win pk0 coll0].
proof.
 proc;seq 17:(pk=pk0 /\ collision=coll0 /\ win=false /\
 v0=pke_domain coll0.`1 /\ v1=pke_domain coll0.`2 /\
 v2=pke_domain coll0.`3 /\ v3=pke_domain coll0.`4 /\
 em=(coll0.`1=coll0.`2) /\ er=(coll0.`3=coll0.`4)).
 + wp;call(rt_poly_equal_spec coll0.`3 coll0.`4);
   wp;call(rt_poly_equal_spec coll0.`1 coll0.`2);
   wp;call(rrec_trit_functional coll0.`4);wp;call(rrec_trit_functional coll0.`3);
   wp;call(rrec_trit_functional coll0.`2);wp;call(rrec_trit_functional coll0.`1);auto.
 if.
 + seq 4:(pk=pk0 /\ collision=coll0 /\ win=false /\
    pke_domain coll0.`1 /\ pke_domain coll0.`2 /\ pke_domain coll0.`3 /\ pke_domain coll0.`4 /\
    (coll0.`1,coll0.`3)<>(coll0.`2,coll0.`4) /\
    c0=pke_enc_spec pk0 coll0.`1 coll0.`3 /\ c1=pke_enc_spec pk0 coll0.`2 coll0.`4).
   - wp;call(rt_pke_enc_spec pk0 coll0.`2 coll0.`4);
     wp;call(rt_pke_enc_spec pk0 coll0.`1 coll0.`3);auto=> />;smt().
   match.
   - auto=> />;rewrite /sec_inj_win;smt().
   match.
   - auto=> />;rewrite /sec_inj_win;smt().
   wp;ecall(hist_cipher_spec x y);auto=> />;rewrite /sec_inj_win;smt().
 auto=> />;rewrite /sec_inj_win;smt().
qed.
lemma rt_inj_check_correct pk0 coll0 :
 phoare[RTINJCheck.run:pk=pk0 /\ collision=coll0 ==>res.`1=sec_inj_win pk0 coll0]=1%r.
proof. by conseq rt_inj_check_ll(rt_inj_check_spec pk0 coll0). qed.
lemma rt_inj_check_profile :
 hoare[RTINJCheck.run:true ==>rtk_le res.`2(rtk_profile 0 0 0 0 2 4 2 1 0 0)].
proof.
 proc;seq 17:(trits=4 /\ polys=2 /\ encryptions=0 /\ ciphers=0).
 + wp;call(_:true ==>true);first by trivial.
   wp;call(_:true ==>true);first by trivial.
   wp;call(_:true ==>true);first by trivial.
   wp;call(_:true ==>true);first by trivial.
   wp;call(_:true ==>true);first by trivial.
   wp;call(_:true ==>true);first by trivial.
   auto.
 if;last by auto=> />;rewrite /rtk_profile;smt().
 seq 4:(trits=4 /\ polys=2 /\ encryptions=2 /\ ciphers=0).
 + wp;call(_:true ==>true);first by trivial.
   wp;call(_:true ==>true);first by trivial.
   auto.
 match;first by auto=> />;rewrite /rtk_profile;smt().
 match;first by auto=> />;rewrite /rtk_profile;smt().
 wp;call(_:true ==>true);first by trivial.
 auto=> />;rewrite /rtk_profile;smt().
qed.

lemma rt_ow_kernel_ll(B<:SecOWAdversary) :
 islossless B.run=>islossless RTOWKernel(B).run.
proof.
 move=>hb;proc;wp;call rt_poly_equal_ll;wp;call hb;
 call rt_encrypt_ll;wp;rnd;wp;rnd;auto=> />;smt(pke_psi1_lossless).
qed.
lemma rt_ow_kernel_profile(B<:SecOWAdversary) :
 hoare[RTOWKernel(B).run:true ==>
 rtk_le res.`2(rtk_profile 0 0 0 0 1 0 1 0 2 1)].
proof.
 proc;wp;call(_:true ==>true);first by trivial.
 wp;call(_:true ==>true);first by trivial.
 call rt_encrypt_profile;wp;rnd;wp;rnd;auto=> />;
 rewrite /rtk_add /rtk_profile;smt().
qed.
lemma rt_ow_kernel_projection(B<:SecOWAdversary) :
 equiv[RTOWKernel(B).run ~ OWKernel(B).run:
 ={pk,glob B} /\ encap_key_canonical pk{1} ==>
 res{1}.`1=res{2} /\ ={glob B}].
proof.
 proc;wp;ecall{1}(rt_poly_equal_correct answer{1} code{1});wp.
 call(_: ={arg,glob B} ==> ={res,glob B});first by proc true;auto.
 wp;ecall{1}(rt_encrypt_correct pk{1} code{1} r{1}).
 wp;rnd;wp;rnd;auto=> />.
 move=> &2 hk code hc r hr;split.
 + rewrite /pke_domain;exact(pke_psi1_trits code hc).
 rewrite /pke_domain;exact(pke_psi1_trits r hr).
qed.

lemma rt_inj_ntru_projection(B<:SecINJAdversary) :
 equiv[RTINJNTRUReduction(B).run ~ INJNTRUReduction(B).run:
 ={arg,glob B} ==>res{1}.`1=res{2} /\ ={glob B}].
proof.
 proc;inline{2} INJFieldKernel(B).guess;wp.
 seq 10 2:(={h,glob B} /\ a{1}=ow_scale3 h{1} /\ a{2}=a{1} /\
 accept{1}=ow_unit_test a{1} /\ !win{1} /\ !win0{2}).
 + wp;ecall{1}(ow_unit_test_correct (ow_scale3 h{1}));auto.
 if;first by auto.
 + inline{2} INJKernel(B).run;wp.
   ecall{1}(rt_inj_check_correct pk{1} collision{1});wp.
   call(_: ={arg,glob B} ==> ={res,glob B});first by proc true;auto.
   wp;ecall{1}(ow_encode_correct a{1});auto.
 auto=> />;smt().
qed.
lemma rt_ow_ntru_projection(B<:SecOWAdversary) :
 equiv[RTOWNTRUReduction(B).run ~ OWNTRUReduction(B).run:
 ={arg,glob B} ==>res{1}.`1=res{2} /\ ={glob B}].
proof.
 proc;inline{2} OWFieldKernel(B).guess;wp.
 seq 9 2:(={h,glob B} /\ a{1}=ow_scale3 h{1} /\ a{2}=a{1} /\
 accept{1}=ow_unit_test a{1} /\ !win{1} /\ !win0{2}).
 + wp;ecall{1}(ow_unit_test_correct (ow_scale3 h{1}));auto.
 if;first by auto.
 + wp;call(rt_ow_kernel_projection B);wp.
   ecall{1}(ow_encode_correct a{1});auto=> />;smt(ow_encode_canonical).
 auto=> />;smt().
qed.
lemma rt_rlwe_projection(B<:SecOWAdversary) :
 equiv[RTOWRLWESolver(B).run ~ OWRLWESolver(B).run:
 ={arg,glob B} ==>res{1}.`1=res{2} /\ ={glob B}].
proof.
 proc;seq 7 1:(={a,b,glob B} /\ accept{1}=ow_unit_test a{1} /\
 answer{1}=NTRUPoly.poly0 /\ answer{2}=NTRUPoly.poly0).
 + wp;ecall{1}(ow_unit_test_correct a{1});auto.
 if;first by auto.
 + wp;ecall{1}(ow_recover_correct a{1} b{1} code{1});wp.
   call(_: ={arg,glob B} ==> ={res,glob B});first by proc true;auto.
   wp;ecall{1}(ow_encode_correct b{1});wp;ecall{1}(ow_encode_correct a{1});auto.
 auto.
qed.

lemma rt_inj_ntru_ll(B<:SecINJAdversary) :
 islossless B.run=>islossless RTINJNTRUReduction(B).run.
proof.
 move=>hb;proc;seq 10:true;1,4,5:by auto.
 + wp;call ow_unit_test_ll;auto.
 if;last by auto.
 wp;call rt_inj_check_ll;wp;call hb;wp;call ow_encode_ll;auto.
qed.
lemma rt_ow_ntru_ll(B<:SecOWAdversary) :
 islossless B.run=>islossless RTOWNTRUReduction(B).run.
proof.
 move=>hb;proc;seq 9:true;1,4,5:by auto.
 + wp;call ow_unit_test_ll;auto.
 if;last by auto.
 wp;call(rt_ow_kernel_ll B hb);wp;call ow_encode_ll;auto.
qed.
lemma rt_rlwe_ll(B<:SecOWAdversary) :
 islossless B.run=>islossless RTOWRLWESolver(B).run.
proof.
 move=>hb;proc;seq 7:true;1,4,5:by auto.
 + wp;call ow_unit_test_ll;auto.
 if;last by auto.
 wp;call ow_recover_ll;wp;call hb;
 wp;call ow_encode_ll;wp;call ow_encode_ll;auto.
qed.

lemma rt_inj_ntru_profile(B<:SecINJAdversary) :
 hoare[RTINJNTRUReduction(B).run:true ==>
 rtk_le res.`2(rtk_profile 1 1 1 0 2 4 2 1 0 1)].
proof.
 proc;seq 10:(scales=1 /\ units=1 /\ encodes=0 /\ calls=0 /\
 profile=rtk_profile 0 0 0 0 0 0 0 0 0 0).
 + wp;call(_:true ==>true);first by trivial. auto.
 if;last by auto=> />;rewrite /rtk_add /rtk_profile;smt().
 wp;call rt_inj_check_profile;wp.
 call(_:true ==>true);first by trivial.
 wp;call(_:true ==>true);first by trivial.
 auto=> />;rewrite /rtk_add /rtk_profile;smt().
qed.
lemma rt_ow_ntru_profile(B<:SecOWAdversary) :
 hoare[RTOWNTRUReduction(B).run:true ==>
 rtk_le res.`2(rtk_profile 1 1 1 0 1 0 1 0 2 1)].
proof.
 proc;seq 9:(scales=1 /\ units=1 /\ encodes=0 /\
 profile=rtk_profile 0 0 0 0 0 0 0 0 0 0).
 + wp;call(_:true ==>true);first by trivial. auto.
 if;last by auto=> />;rewrite /rtk_add /rtk_profile;smt().
 wp;call(rt_ow_kernel_profile B);wp.
 call(_:true ==>true);first by trivial.
 auto=> />;rewrite /rtk_add /rtk_profile;smt().
qed.
lemma rt_rlwe_profile(B<:SecOWAdversary) :
 hoare[RTOWRLWESolver(B).run:true ==>
 rtk_le res.`2(rtk_profile 0 1 2 1 0 0 0 0 0 1)].
proof.
 proc;seq 7:(units=1 /\ encodes=0 /\ recovers=0 /\ calls=0).
 + wp;call(_:true ==>true);first by trivial. auto.
 if;last by auto=> />;rewrite /rtk_profile;smt().
 wp;call(_:true ==>true);first by trivial.
 wp;call(_:true ==>true);first by trivial.
 wp;call(_:true ==>true);first by trivial.
 wp;call(_:true ==>true);first by trivial.
 auto=> />;rewrite /rtk_profile;smt().
qed.
