require import AllCore Distr IntDiv.
from Jasmin require import JWord.
require import Array768 Array1152.
require import NTRUPlus768OWCodec NTRUPlus768OWCodecProof NTRUPlus768OWCodecCalls.
require import NTRUPlus768OWUniform NTRUPlus768OWUniformScale.
require import NTRUPlus768PKEModel NTRUPlus768PKEKeyDistribution NTRUPlus768PKECallProof.
require import NTRUPlus768CanonicalDecoder NTRUPlus768EncapGuardSpec NTRUPlus768BasemulAlgebra.
require import NTRUPlus768NTTAlgebra NTRUPlus768NTTProof NTRUPlus768NTT.
require import NTRUPlus768PolyToBytesAlgebra NTRUPlus768PolyToBytesProof NTRUPlus768PolyToBytes.
require import NTRUPlus768PolyFromBytesChecked NTRUPlus768PolyFromBytesCheckedProof.
require import NTRUPlus768RRecCanonical NTRUPlus768RRecPublicInverse NTRUPlus768RRecAlgebra.
require import NTRUPlus768RRecLinearModel NTRUPlus768RRecLinearProcedures NTRUPlus768RRecLinearProof.
require import NTRUPlus768R2Serialization NTRUPlus768ValidKeyR2Recovery NTRUPlus768KeygenSecretFBridge.
require import NTRUPlus768GenKeyProjection NTRUPlus768CyclotomicFactorization NTRUPlus768EvaluationSemantics.
require import NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768TerminalRepresentation.
require import NTRUPlus768Crepmod3Algebra.

(* The executable interface consists of finite word arrays. Polynomial
   representatives occur only in logical statements and specifications. *)
module RTWordEncode = {
 proc run(a:pke_poly):W8.t Array1152.t = {
  var h:pke_poly;var bytes:W8.t Array1152.t;
  h<@NTRUPlus768NTT.M.jade_ntruplus_ntruplus768_amd64_ref_ntt(witness,a);
  bytes<@NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes(witness,h);
  return bytes;
 }
}.
module RTWordUnit = {
 proc run(a:pke_poly):bool = {
  var pk:W8.t Array1152.t;var hp:pke_poly;var status:W32.t;var inverse:pke_poly option;
  pk<@RTWordEncode.run(a);
  (hp,status)<@NTRUPlus768PolyFromBytesChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes(witness,pk);
  inverse<@RRecPublicInverse.run(hp);
  return inverse<>None;
 }
}.
module RTWordRecover = {
 proc run(a b code:pke_poly):pke_poly option = {
  var pk,ct:W8.t Array1152.t;var answer:pke_poly option;
  pk<@RTWordEncode.run(a);ct<@RTWordEncode.run(b);
  answer<@LinearRRec.run(pk,code,ct);
  return answer;
 }
}.
module RTWordScale3 = {
 proc run(a:pke_poly):pke_poly = {
  var i,x:int;
  i<-0;
  while(i<768) {
   x<-3*W16.to_uint a.[i];
   if(3457<=x) {x<-x-3457;}
   if(3457<=x) {x<-x-3457;}
   a.[i]<-W16.of_int x;
   i<-i+1;
  }
  return a;
 }
 (* Proof-observation counter for primitive operations. Entry and return
    each copy 768 owned cells at three operations per cell. Indexed
    accesses include address selection; scalar transfers and casts are
    conservatively charged. Counter maintenance itself is erased. *)
 proc measure(a:pke_poly):pke_poly*int = {
  var i,x,steps:int;
  steps<-0;
  steps<-steps+2304;
  i<-0;steps<-steps+1;
  steps<-steps+2;
  while(i<768) {
   x<-3*W16.to_uint a.[i];steps<-steps+4;
   steps<-steps+2;
   if(3457<=x) {x<-x-3457;steps<-steps+2;}
   steps<-steps+2;
   if(3457<=x) {x<-x-3457;steps<-steps+2;}
   a.[i]<-W16.of_int x;steps<-steps+3;
   i<-i+1;steps<-steps+2;
   steps<-steps+2;
  }
  steps<-steps+2304;
  steps<-steps+1;
  return(a,steps);
 }
}.

lemma rt_word_encode_ll : islossless RTWordEncode.run.
proof. proc;call poly_tobytes_lossless;call ntt_lossless;auto. qed.
lemma rt_word_unit_ll : islossless RTWordUnit.run.
proof. proc;call rrec_public_inverse_lossless;call poly_frombytes_checked_lossless;call rt_word_encode_ll;auto. qed.
lemma rt_word_recover_ll : islossless RTWordRecover.run.
proof. proc;call linear_rrec_lossless;call rt_word_encode_ll;call rt_word_encode_ll;auto. qed.
lemma rt_word_scale3_ll : islossless RTWordScale3.run.
proof.
 proc;while(0<=i<=768)(768-i).
 + move=>z;auto=> />;smt().
 auto=> />;smt().
qed.

lemma rt_word_encode_functional p0 :
 hoare[RTWordEncode.run:a=ow_coeff_words p0 ==>res=ow_encode p0].
proof.
 proc;call(rrec_tobytes_functional (ntt_spec(ow_coeff_words p0)) (ow_encode_ntt_serializer p0)).
 call(ntt_functional witness(ow_coeff_words p0));auto=> />.
 by rewrite(ow_encode_direct p0).
qed.
lemma rt_word_unit_functional p0 :
 hoare[RTWordUnit.run:a=ow_coeff_words p0 ==>res=ow_unit_test p0].
proof.
 proc;call(rrec_public_inverse_functional (decoded_poly(ow_encode p0))
  (rrec_public_key_range _ (ow_encode_canonical p0))).
 call(pke_decoder_functional witness(ow_encode p0));call(rt_word_encode_functional p0).
 auto=> />;by rewrite /ow_unit_test.
qed.
lemma rt_word_recover_functional a0 b0 code0 :
 hoare[RTWordRecover.run:a=ow_coeff_words a0 /\ b=ow_coeff_words b0 /\ code=code0 ==>
 res=rrec_linear_spec(ow_encode a0)code0(ow_encode b0)].
proof.
 proc;call(linear_rrec_functional (ow_encode a0) code0 (ow_encode b0)).
 call(rt_word_encode_functional b0);call(rt_word_encode_functional a0);auto.
qed.

lemma rt_word_encode_correct p0 :
 phoare[RTWordEncode.run:a=ow_coeff_words p0 ==>res=ow_encode p0]=1%r.
proof. by conseq rt_word_encode_ll(rt_word_encode_functional p0). qed.
lemma rt_word_unit_correct p0 :
 phoare[RTWordUnit.run:a=ow_coeff_words p0 ==>res=ow_unit_test p0]=1%r.
proof. by conseq rt_word_unit_ll(rt_word_unit_functional p0). qed.
lemma rt_word_recover_correct a0 b0 code0 :
 phoare[RTWordRecover.run:a=ow_coeff_words a0 /\ b=ow_coeff_words b0 /\ code=code0 ==>
 res=rrec_linear_spec(ow_encode a0)code0(ow_encode b0)]=1%r.
proof. by conseq rt_word_recover_ll(rt_word_recover_functional a0 b0 code0). qed.

lemma rt_word_canonical_roundtrip a : rrec_canonical_domain a=>
 ow_coeff_words(input_poly a)=a.
proof.
 move=>ha;apply rrec_canonical_domain_unique.
 + exact(ow_coeff_words_canonical _).
 + exact ha.
 rewrite(ow_coeff_words_poly _ (gen_input_poly_degree a)).
 exact(eqm_global_refl _).
qed.

lemma rt_word_encode_projection :
 equiv[RTWordEncode.run ~ OWEncode.run:a{1}=ow_coeff_words p{2} ==> ={res}].
proof.
 exists* p{2};elim*=>p0;proc*.
 ecall{1}(rt_word_encode_correct p0);ecall{2}(ow_encode_correct p0);auto.
qed.
lemma rt_word_unit_projection :
 equiv[RTWordUnit.run ~ OWUnitTest.run:a{1}=ow_coeff_words p{2} ==> ={res}].
proof.
 exists* p{2};elim*=>p0;proc*.
 ecall{1}(rt_word_unit_correct p0);ecall{2}(ow_unit_test_correct p0);auto.
qed.
lemma rt_word_recover_projection :
 equiv[RTWordRecover.run ~ OWRecover.run:
 a{1}=ow_coeff_words a{2} /\ b{1}=ow_coeff_words b{2} /\ ={code} ==>
 res{2}=(if res{1}=None then NTRUPoly.poly0 else input_poly(oget res{1}))].
proof.
 exists* a{2},b{2},code{2};elim*=>a0 b0 code0;proc*.
 ecall{1}(rt_word_recover_correct a0 b0 code0).
 ecall{2}(ow_recover_correct a0 b0 code0).
 auto=> />;by rewrite /ow_recover.
qed.

(* These are specifications of the finite arithmetic, not executable
   coefficient or polynomial accessors. *)
op rt_word_reduce3 (x:int) =
 let y=if 3457<=x then x-3457 else x in
 if 3457<=y then y-3457 else y.
op rt_word_scale3_spec (a:pke_poly) =
 Array768.init(fun i=>W16.of_int(rt_word_reduce3(3*W16.to_uint a.[i]))).

lemma rt_word_sub_q_mod x : (x-3457) %% 3457=x %% 3457.
proof.
 have he:x-3457=(-1)*3457+x by ring.
 by rewrite he modzMDl.
qed.
lemma rt_word_reduce3_range x : 0<=x<10371=>0<=rt_word_reduce3 x<3457.
proof. rewrite /rt_word_reduce3;case(3457<=x);case(3457<=x-3457);smt(). qed.
lemma rt_word_reduce3_mod x : 0<=x<10371=>rt_word_reduce3 x=x %% 3457.
proof.
 move=>hx;have hr:=rt_word_reduce3_range x hx.
 have he:(rt_word_reduce3 x) %% 3457=rt_word_reduce3 x by apply modz_small;smt().
 rewrite -he /rt_word_reduce3.
 case(3457<=x)=>h1 /=;last by rewrite ifF 1:/#.
 have htwo:(x-6914) %% 3457=x %% 3457.
 + have hd:x-6914=(-2)*3457+x by ring.
   by rewrite hd modzMDl.
 have hone:=rt_word_sub_q_mod x.
 case(3457<=x-3457)=>h2 /=;smt().
qed.
lemma rt_word_canonical_uint a i : rrec_canonical_domain a=>0<=i<768=>
 W16.to_uint a.[i]=coeff a.[i] /\ 0<=W16.to_uint a.[i]<3457.
proof.
 move=>ha hi;have hr:=ha i hi.
 have he:W16.to_uint a.[i]=coeff a.[i].
 + rewrite {1}(word_from_coeff a.[i]) W16.to_uint_small;move:hr;rewrite /q;smt().
 rewrite he;move:hr;rewrite /q;smt().
qed.
lemma rt_word_coeff_words_uint p i : 0<=i<768=>
 W16.to_uint(ow_coeff_words p).[i]=CycloFq.asint(NTRUPoly."_.[_]" p i).
proof.
 move=>hi;have [he _]:=rt_word_canonical_uint _ i (ow_coeff_words_canonical p) hi;rewrite he.
 exact(ow_coeff_words_coeff p i hi).
qed.
lemma rt_word_scale3_intermediates a i :
 rrec_canonical_domain a=>0<=i<768=>
 let x=3*W16.to_uint a.[i] in
 let y=if 3457<=x then x-3457 else x in
 0<=x<=10368 /\ 0<=y<=6911 /\ 0<=rt_word_reduce3 x<=3456.
proof.
 move=>ha hi;have [_ hu]:=rt_word_canonical_uint a i ha hi.
 have hr:=rt_word_reduce3_range (3*W16.to_uint a.[i]) _;first smt().
 smt().
qed.
lemma rt_word_scale3_spec_words p :
 rt_word_scale3_spec(ow_coeff_words p)=ow_coeff_words(ow_scale3 p).
proof.
 apply Array768.tP=>i hi.
 rewrite /rt_word_scale3_spec Array768.initiE 1:hi /= (rt_word_coeff_words_uint p i hi).
 have hr:=CycloFq.rg_asint(NTRUPoly."_.[_]" p i).
 have hb:0<=3*CycloFq.asint(NTRUPoly."_.[_]" p i)<10371.
 + move:hr;rewrite /q;smt().
 rewrite(rt_word_reduce3_mod _ hb) /ow_coeff_words Array768.initiE 1:hi /=
  ow_scale3E /ow_polyscale NTRUPoly.polyZE CycloFq.mulE.
 by rewrite /lift_int CycloFq.incyclocoeffK /=.
qed.

lemma rt_word_scale3_prefix_step (a0 aa:pke_poly) (ii:int) :
 0<=ii<768=>
 (forall j,0<=j<768=>aa.[j]=
  if j<ii then W16.of_int(rt_word_reduce3(3*W16.to_uint a0.[j])) else a0.[j])=>
 forall j,0<=j<768=>
 aa.[ii<-W16.of_int(rt_word_reduce3(3*W16.to_uint a0.[ii]))].[j]=
 if j<ii+1 then W16.of_int(rt_word_reduce3(3*W16.to_uint a0.[j])) else a0.[j].
proof.
 move=>hi hp j hj;rewrite Array768.get_setE 1:hi.
 case(j=ii)=>he.
 + by rewrite he ifT 1:/#.
 rewrite(hp j hj).
 have heq:(j<ii+1)=(j<ii) by smt().
 by rewrite heq.
qed.

lemma rt_word_scale3_spec_functional a0 :
 hoare[RTWordScale3.run:a=a0 ==>res=rt_word_scale3_spec a0].
proof.
 proc;while(0<=i<=768 /\
  forall j,0<=j<768=>a.[j]=
   if j<i then W16.of_int(rt_word_reduce3(3*W16.to_uint a0.[j])) else a0.[j]).
 + auto=> />;move=> &m h0 h1 hprefix hlt.
   have hi:0<=i{m}<768 by smt().
   have he:=hprefix i{m} hi.
   rewrite ifF 1:/# in he.
   have hs:=rt_word_scale3_prefix_step a0 a{m} i{m} hi hprefix.
   rewrite he;split.
   - move=>hb;split.
     * move=>hb2.
       have hv:rt_word_reduce3(3*W16.to_uint a0.[i{m}])=
        3*W16.to_uint a0.[i{m}]-6914.
       + rewrite /rt_word_reduce3;smt().
       split;first smt().
       move=>j hj0 hj1;rewrite -hv;apply(hs j);smt().
     move=>hb2.
     have hv:rt_word_reduce3(3*W16.to_uint a0.[i{m}])=
      3*W16.to_uint a0.[i{m}]-3457.
     * rewrite /rt_word_reduce3;smt().
     split;first smt().
     move=>j hj0 hj1;rewrite -hv;apply(hs j);smt().
   move=>hb.
   have hv:rt_word_reduce3(3*W16.to_uint a0.[i{m}])=
    3*W16.to_uint a0.[i{m}].
   - rewrite /rt_word_reduce3;smt().
   split;first smt().
   move=>j hj0 hj1;rewrite -hv;apply(hs j);smt().
 auto=> />;split;first smt().
 move=>aa ii hstop hi hbound hprefix;apply Array768.tP=>j hj.
 rewrite /rt_word_scale3_spec Array768.initiE 1:hj /= (hprefix j hj) ifT 1:/#;done.
qed.

lemma rt_word_scale3_functional p0 :
 hoare[RTWordScale3.run:a=ow_coeff_words p0 ==>res=ow_coeff_words(ow_scale3 p0)].
proof.
 conseq(rt_word_scale3_spec_functional (ow_coeff_words p0));
 smt(rt_word_scale3_spec_words).
qed.
lemma rt_word_scale3_correct p0 :
 phoare[RTWordScale3.run:a=ow_coeff_words p0 ==>res=ow_coeff_words(ow_scale3 p0)]=1%r.
proof. by conseq rt_word_scale3_ll(rt_word_scale3_functional p0). qed.

lemma rt_word_scale3_measure_projection :
 equiv[RTWordScale3.measure ~ RTWordScale3.run: ={a} ==>res{1}.`1=res{2}].
proof. proc;wp;while(={a,i});auto. qed.
lemma rt_word_scale3_measure_ll : islossless RTWordScale3.measure.
proof.
 proc;wp;while(0<=i<=768)(768-i).
 + move=>z;auto=> />;smt().
 auto=> />;smt().
qed.
lemma rt_word_scale3_measure_cost :
 hoare[RTWordScale3.measure:true ==>16132<=res.`2<=19204].
proof.
 proc;wp;while(0<=i<=768 /\ 2307+15*i<=steps<=2307+19*i).
 + auto=> />;smt().
 auto=> />;smt().
qed.
