require import AllCore List Distr FMap StdOrder.
from Jasmin require import JWord.
require import Array32 Array768 Array1152.
require import NTRUPlus768RTModel NTRUPlus768RTStore NTRUPlus768RTKernelTypes.
require import NTRUPlus768RTKernels NTRUPlus768RTProjection NTRUPlus768RTView NTRUPlus768RTAdaptive.
require import NTRUPlus768AHState NTRUPlus768AHActualReduction.
require import NTRUPlus768SecModel NTRUPlus768EncapGuardSpec NTRUPlus768SecBaseGames NTRUPlus768SecGOracles.
require import NTRUPlus768OWGames NTRUPlus768INJGames NTRUPlus768OWCodec NTRUPlus768OWCodecCalls NTRUPlus768OWUniform.
require import NTRUPlus768PKEKeyDistribution NTRUPlus768OWCodecProof.
require import NTRUPlus768CyclotomicFactorization NTRUPlus768PKEModel.
require import NTRUPlus768ROMOracles NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
require import NTRUPlus768CCAGame NTRUPlus768CCADecapOracle NTRUPlus768SimModel.
import IntOrder.

(* Only INJ's inner reducer samples two psi polynomials and encrypts a
   challenge. DO already counts these in RTOWKernel; CO has neither. *)
op rt_inj_complete_profile(k:rt_kernel_profile) =
 rtk_add k(rtk_profile 0 0 0 0 k.`rtk_adversary 0 0 0 (2*k.`rtk_adversary) 0).
op rt_di_kernel_bound = rtk_profile 1 1 1 0 3 4 2 1 2 1.
op rt_do_kernel_bound = rtk_profile 1 1 1 0 1 0 1 0 2 1.
op rt_co_kernel_bound = rtk_profile 0 1 2 1 0 0 0 0 0 1.

module type RTNTRUAdversary = {
 proc measure(h:NTRUPoly.poly):bool*rt_profile*rt_kernel_profile
 proc run(h:NTRUPoly.poly):bool
}.
module type RTRLWEAdversary = {
 proc measure(a b:NTRUPoly.poly):NTRUPoly.poly*rt_profile*rt_kernel_profile
 proc run(a b:NTRUPoly.poly):NTRUPoly.poly
}.

(* Ledger reset occurs once, at the complete reducer entry. The protocol
   initializer later preserves this ledger. No last-profile global is
   introduced: run executes measure and discards its two certificates. *)
module RT_DI(S:RTHistory,A:CCAExtendedAdversary) = {
 proc measure(h:NTRUPoly.poly):bool*rt_profile*rt_kernel_profile = {
  var out:bool*rt_kernel_profile;var profile:rt_profile;
  S.reset_cost();
  out<@RTINJNTRUReduction(RTAuxINJ(S,A)).run(h);
  profile<@S.metrics();
  return(out.`1,profile,rt_inj_complete_profile out.`2);
 }
 proc run(h:NTRUPoly.poly):bool = {
  var out:bool*rt_profile*rt_kernel_profile;
  out<@measure(h);return out.`1;
 }
}.
module RT_DO(S:RTHistory,A:CCAExtendedAdversary) = {
 proc measure(h:NTRUPoly.poly):bool*rt_profile*rt_kernel_profile = {
  var out:bool*rt_kernel_profile;var profile:rt_profile;
  S.reset_cost();
  out<@RTOWNTRUReduction(RTAuxOW(S,A)).run(h);
  profile<@S.metrics();return(out.`1,profile,out.`2);
 }
 proc run(h:NTRUPoly.poly):bool = {
  var out:bool*rt_profile*rt_kernel_profile;
  out<@measure(h);return out.`1;
 }
}.
module RT_CO(S:RTHistory,A:CCAExtendedAdversary) = {
 proc measure(a b:NTRUPoly.poly):NTRUPoly.poly*rt_profile*rt_kernel_profile = {
  var out:NTRUPoly.poly*rt_kernel_profile;var profile:rt_profile;
  S.reset_cost();
  out<@RTOWRLWESolver(RTAuxOW(S,A)).run(a,b);
  profile<@S.metrics();return(out.`1,profile,out.`2);
 }
 proc run(a b:NTRUPoly.poly):NTRUPoly.poly = {
  var out:NTRUPoly.poly*rt_profile*rt_kernel_profile;
  out<@measure(a,b);return out.`1;
 }
}.

lemma rt_inj_complete_bound k :
 rtk_le k(rtk_profile 1 1 1 0 2 4 2 1 0 1)=>
 rtk_le(rt_inj_complete_profile k)rt_di_kernel_bound.
proof.
 rewrite /rtk_le /rt_inj_complete_profile /rt_di_kernel_bound /rtk_add /rtk_profile;
 smt().
qed.
lemma rt_inj_complete_zero k : k.`rtk_adversary=0=>rt_inj_complete_profile k=k.
proof.
 case k=>s u e r p t q c d a /=;move=>h.
 by rewrite /rt_inj_complete_profile /rtk_add /rtk_profile /=;smt().
qed.
lemma rt_inj_complete_calls k : (rt_inj_complete_profile k).`rtk_adversary=k.`rtk_adversary.
proof. by rewrite /rt_inj_complete_profile /rtk_add /rtk_profile. qed.
lemma rt_inj_complete_once k : k.`rtk_adversary=1=>
 rt_inj_complete_profile k=rtk_add k rt_inj_inner_profile.
proof. by move=>h;rewrite /rt_inj_complete_profile /rt_inj_inner_profile h. qed.

lemma rt_di_kernel_profile (S<:RTHistory)(A<:CCAExtendedAdversary) :
 hoare[RT_DI(S,A).measure:true ==>rtk_le res.`3 rt_di_kernel_bound].
proof.
 proc;call(_:true ==>true);first by trivial.
 call(rt_inj_ntru_profile (RTAuxINJ(S,A))).
 call(_:true ==>true);first by trivial.
 auto=> />;smt(rt_inj_complete_bound).
qed.
lemma rt_do_kernel_profile (S<:RTHistory)(A<:CCAExtendedAdversary) :
 hoare[RT_DO(S,A).measure:true ==>rtk_le res.`3 rt_do_kernel_bound].
proof.
 proc;call(_:true ==>true);first by trivial.
 call(rt_ow_ntru_profile (RTAuxOW(S,A))).
 call(_:true ==>true);first by trivial.
 auto=> />;rewrite /rt_do_kernel_bound;smt().
qed.
lemma rt_co_kernel_profile (S<:RTHistory)(A<:CCAExtendedAdversary) :
 hoare[RT_CO(S,A).measure:true ==>rtk_le res.`3 rt_co_kernel_bound].
proof.
 proc;call(_:true ==>true);first by trivial.
 call(rt_rlwe_profile (RTAuxOW(S,A))).
 call(_:true ==>true);first by trivial.
 auto=> />;rewrite /rt_co_kernel_bound;smt().
qed.

lemma rt_result_metrics_value (S<:RTHistory)(view:(glob S)->ah_state)(cost:(glob S)->rt_profile) :
 (forall st p,hoare[S.metrics:view(glob S)=st /\ cost(glob S)=p ==>
 res=p /\ view(glob S)=st /\ cost(glob S)=p])=>
 hoare[S.metrics:true ==>res=cost(glob S)].
proof.
 move=>hm;proc*;exists* (view(glob S)),(cost(glob S));elim*=>st p.
 call(hm st p);auto=> />;smt().
qed.
lemma rt_di_profile_read (S<:RTHistory)(A<:CCAExtendedAdversary)
 (view:(glob S)->ah_state)(cost:(glob S)->rt_profile) :
 (forall st p,hoare[S.metrics:view(glob S)=st /\ cost(glob S)=p ==>
 res=p /\ view(glob S)=st /\ cost(glob S)=p])=>
 hoare[RT_DI(S,A).measure:true ==>res.`2=cost(glob S)].
proof.
 move=>hm;proc;call(rt_result_metrics_value S view cost hm).
 call(_:true ==>true);first by trivial.
 call(_:true ==>true);first by trivial.
 auto.
qed.
lemma rt_do_profile_read (S<:RTHistory)(A<:CCAExtendedAdversary)
 (view:(glob S)->ah_state)(cost:(glob S)->rt_profile) :
 (forall st p,hoare[S.metrics:view(glob S)=st /\ cost(glob S)=p ==>
 res=p /\ view(glob S)=st /\ cost(glob S)=p])=>
 hoare[RT_DO(S,A).measure:true ==>res.`2=cost(glob S)].
proof.
 move=>hm;proc;call(rt_result_metrics_value S view cost hm).
 call(_:true ==>true);first by trivial.
 call(_:true ==>true);first by trivial.
 auto.
qed.
lemma rt_co_profile_read (S<:RTHistory)(A<:CCAExtendedAdversary)
 (view:(glob S)->ah_state)(cost:(glob S)->rt_profile) :
 (forall st p,hoare[S.metrics:view(glob S)=st /\ cost(glob S)=p ==>
 res=p /\ view(glob S)=st /\ cost(glob S)=p])=>
 hoare[RT_CO(S,A).measure:true ==>res.`2=cost(glob S)].
proof.
 move=>hm;proc;call(rt_result_metrics_value S view cost hm).
 call(_:true ==>true);first by trivial.
 call(_:true ==>true);first by trivial.
 auto.
qed.

lemma rt_ntru_measure_same(M<:RTNTRUAdversary) :
 equiv[M.measure ~ M.measure: ={arg,glob M} ==> ={res,glob M}].
proof. proc true;auto. qed.
lemma rt_rlwe_measure_same(M<:RTRLWEAdversary) :
 equiv[M.measure ~ M.measure: ={arg,glob M} ==> ={res,glob M}].
proof. proc true;auto. qed.

lemma rt_di_run_measure
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory}) h0 &m :
 Pr[RT_DI(S,A).run(h0)@&m:res]=Pr[RT_DI(S,A).measure(h0)@&m:res.`1].
proof.
 byequiv(_: ={arg,glob RT_DI(S,A)} ==>res{1}=res{2}.`1)=> //.
 proc*;inline{1} RT_DI(S,A).run;wp;call(rt_ntru_measure_same (RT_DI(S,A)));auto.
qed.
lemma rt_do_run_measure
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory}) h0 &m :
 Pr[RT_DO(S,A).run(h0)@&m:res]=Pr[RT_DO(S,A).measure(h0)@&m:res.`1].
proof.
 byequiv(_: ={arg,glob RT_DO(S,A)} ==>res{1}=res{2}.`1)=> //.
 proc*;inline{1} RT_DO(S,A).run;wp;call(rt_ntru_measure_same (RT_DO(S,A)));auto.
qed.
lemma rt_co_run_measure
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory}) a0 b0 answer &m :
 Pr[RT_CO(S,A).run(a0,b0)@&m:res=answer]=
 Pr[RT_CO(S,A).measure(a0,b0)@&m:res.`1=answer].
proof.
 byequiv(_: ={arg,glob RT_CO(S,A)} ==>res{1}=res{2}.`1)=> //.
 proc*;inline{1} RT_CO(S,A).run;wp;call(rt_rlwe_measure_same (RT_CO(S,A)));auto.
qed.

lemma rt_di_outer_projection
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (view:(glob S)->ah_state) :
 islossless S.charge_extract=>
 (forall st n,hoare[S.charge_extract:view(glob S)=st /\ visits=n ==>view(glob S)=st])=>
 equiv[RTTranscript(S,A).run ~ AHActualTranscript(S,A).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2} ==>
 res{1}.`1=res{2} /\ ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2}]=>
 equiv[RTINJNTRUReduction(RTAuxINJ(S,A)).run ~ AHActual_DI(S,A).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2} ==>
 res{1}.`1=res{2} /\ ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2}].
proof.
 move=>xl hx ht.
 proc;inline{2} INJFieldKernel(SecINJAuxAdapter(AHActualINJReducer(S,A))).guess;wp.
 seq 10 2:(={h} /\ ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2} /\ a{1}=ow_scale3 h{1} /\ a{2}=a{1} /\
 accept{1}=ow_unit_test a{1} /\ !win{1} /\ !win0{2}).
 + wp;ecall{1}(ow_unit_test_correct (ow_scale3 h{1}));auto.
 if;first by auto.
 + inline{2} INJKernel(SecINJAuxAdapter(AHActualINJReducer(S,A))).run;wp.
   ecall{1}(rt_inj_check_correct pk{1} collision{1});wp.
   call(rt_inj_aux_projection S A view xl hx ht).
   wp;ecall{1}(ow_encode_correct a{1});auto=> />;smt(ow_encode_canonical).
 auto=> />;smt().
qed.

lemma rt_do_outer_projection
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (view:(glob S)->ah_state) :
 islossless S.charge_extract=>
 (forall st n,hoare[S.charge_extract:view(glob S)=st /\ visits=n ==>view(glob S)=st])=>
 equiv[RTTranscript(S,A).run ~ AHActualTranscript(S,A).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2} ==>
 res{1}.`1=res{2} /\ ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2}]=>
 equiv[RTOWNTRUReduction(RTAuxOW(S,A)).run ~ AHActual_DO(S,A).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2} ==>
 res{1}.`1=res{2} /\ ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2}].
proof.
 move=>xl hx ht.
 proc;inline{2} OWFieldKernel(SecOWAuxAdapter(AHActualOWReducer(S,A))).guess;wp.
 seq 9 2:(={h} /\ ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2} /\ a{1}=ow_scale3 h{1} /\ a{2}=a{1} /\
 accept{1}=ow_unit_test a{1} /\ !win{1} /\ !win0{2}).
 + wp;ecall{1}(ow_unit_test_correct (ow_scale3 h{1}));auto.
 if;first by auto.
 + inline RTOWKernel(RTAuxOW(S,A)).run OWKernel(SecOWAuxAdapter(AHActualOWReducer(S,A))).run;wp.
   ecall{1}(rt_poly_equal_correct answer{1} code{1});wp.
   call(rt_ow_aux_projection S A view xl hx ht);wp.
   ecall{1}(rt_encrypt_correct pk{1} code{1} r{1});wp;rnd;wp;rnd;wp.
   ecall{1}(ow_encode_correct a{1});auto=> />.
   move=> &1 &2 _ _ _ _ code hc r hr.
   split;first exact(ow_encode_canonical _).
   split;rewrite /pke_domain;[exact(pke_psi1_trits code hc)|exact(pke_psi1_trits r hr)].
 auto=> />;smt().
qed.

lemma rt_co_outer_projection
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (view:(glob S)->ah_state) :
 islossless S.charge_extract=>
 (forall st n,hoare[S.charge_extract:view(glob S)=st /\ visits=n ==>view(glob S)=st])=>
 equiv[RTTranscript(S,A).run ~ AHActualTranscript(S,A).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2} ==>
 res{1}.`1=res{2} /\ ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2}]=>
 equiv[RTOWRLWESolver(RTAuxOW(S,A)).run ~ AHActual_CO(S,A).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2} ==>
 res{1}.`1=res{2} /\ ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2}].
proof.
 move=>xl hx ht.
 proc;seq 7 1:(={a,b} /\ ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2} /\ accept{1}=ow_unit_test a{1} /\
 answer{1}=NTRUPoly.poly0 /\ answer{2}=NTRUPoly.poly0).
 + wp;ecall{1}(ow_unit_test_correct a{1});auto.
 if;first by auto.
 + wp;ecall{1}(ow_recover_correct a{1} b{1} code{1});wp.
   call(rt_ow_aux_projection S A view xl hx ht).
   wp;ecall{1}(ow_encode_correct b{1});wp;ecall{1}(ow_encode_correct a{1});auto.
 auto.
qed.

lemma rt_reset_view(S<:RTHistory)(view:(glob S)->ah_state) st :
 islossless S.reset_cost=>
 (forall st,hoare[S.reset_cost:view(glob S)=st ==>view(glob S)=st])=>
 phoare[S.reset_cost:view(glob S)=st ==>view(glob S)=st]=1%r.
proof. move=>hl hv;conseq hl(hv st);smt(). qed.

lemma rt_di_projection
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (view:(glob S)->ah_state) :
 islossless S.charge_extract=>
 (forall st n,hoare[S.charge_extract:view(glob S)=st /\ visits=n ==>view(glob S)=st])=>
 equiv[RTTranscript(S,A).run ~ AHActualTranscript(S,A).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2} ==>
 res{1}.`1=res{2} /\ ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2}]=>
 islossless S.reset_cost=>islossless S.metrics=>
 (forall st,hoare[S.reset_cost:view(glob S)=st ==>view(glob S)=st])=>
 (forall st,hoare[S.metrics:view(glob S)=st ==>view(glob S)=st])=>
 equiv[RT_DI(S,A).run ~ AHActual_DI(S,A).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2} ==>
 ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2}].
proof.
 move=>xl hx ht zl ml hz hm.
 proc*;inline{1} RT_DI(S,A).run RT_DI(S,A).measure;wp.
 ecall{1}(rt_metrics_view S view (view(glob S){2}) ml hm).
 call(rt_di_outer_projection S A view xl hx ht).
 ecall{1}(rt_reset_view S view (view(glob S){2}) zl hz).
 auto.
qed.

lemma rt_do_projection
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (view:(glob S)->ah_state) :
 islossless S.charge_extract=>
 (forall st n,hoare[S.charge_extract:view(glob S)=st /\ visits=n ==>view(glob S)=st])=>
 equiv[RTTranscript(S,A).run ~ AHActualTranscript(S,A).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2} ==>
 res{1}.`1=res{2} /\ ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2}]=>
 islossless S.reset_cost=>islossless S.metrics=>
 (forall st,hoare[S.reset_cost:view(glob S)=st ==>view(glob S)=st])=>
 (forall st,hoare[S.metrics:view(glob S)=st ==>view(glob S)=st])=>
 equiv[RT_DO(S,A).run ~ AHActual_DO(S,A).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2} ==>
 ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2}].
proof.
 move=>xl hx ht zl ml hz hm.
 proc*;inline{1} RT_DO(S,A).run RT_DO(S,A).measure;wp.
 ecall{1}(rt_metrics_view S view (view(glob S){2}) ml hm).
 call(rt_do_outer_projection S A view xl hx ht).
 ecall{1}(rt_reset_view S view (view(glob S){2}) zl hz).
 auto.
qed.

lemma rt_co_projection
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (view:(glob S)->ah_state) :
 islossless S.charge_extract=>
 (forall st n,hoare[S.charge_extract:view(glob S)=st /\ visits=n ==>view(glob S)=st])=>
 equiv[RTTranscript(S,A).run ~ AHActualTranscript(S,A).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2} ==>
 res{1}.`1=res{2} /\ ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2}]=>
 islossless S.reset_cost=>islossless S.metrics=>
 (forall st,hoare[S.reset_cost:view(glob S)=st ==>view(glob S)=st])=>
 (forall st,hoare[S.metrics:view(glob S)=st ==>view(glob S)=st])=>
 equiv[RT_CO(S,A).run ~ AHActual_CO(S,A).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2} ==>
 ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2}].
proof.
 move=>xl hx ht zl ml hz hm.
 proc*;inline{1} RT_CO(S,A).run RT_CO(S,A).measure;wp.
 ecall{1}(rt_metrics_view S view (view(glob S){2}) ml hm).
 call(rt_co_outer_projection S A view xl hx ht).
 ecall{1}(rt_reset_view S view (view(glob S){2}) zl hz).
 auto.
qed.

(* The flag is the actual outer B-call counter. A rejected input has no
   current-execution transcript or extraction; an accepted input has
   one completed transcript followed by exactly one extraction. *)
op [opaque] rt_invocation_profile(calls:int)(p:rt_profile) =
 (calls=0 /\ p=rt_zero) \/ (calls=1 /\ rt_reducer_profile p).
lemma rt_invocation_bounds calls p : rt_invocation_profile calls p=>
 rt_cost_ok p /\ rt_callback_ok p /\ p.`rp_xcalls=calls /\
 0<=calls<=1 /\ p.`rp_xvisits<=rt_g_length p.
proof.
 rewrite /rt_invocation_profile;case.
 + move=>[-> ->];have hz:=rt_zero_ok.
   rewrite /rt_callback_ok /rt_zero /rt_g_length /=;smt().
 move=>[-> hp];move:hp;rewrite /rt_reducer_profile;move=>[hc [hb hx]].
 have hv:p.`rp_xvisits<=rt_g_length p
  by move:hc;rewrite /rt_cost_ok /rt_g_length hx;smt().
 smt().
qed.
lemma rt_inj_checker_calls : hoare[RTINJCheck.run:true ==>res.`2.`rtk_adversary=0].
proof. conseq rt_inj_check_profile=> //;rewrite /rtk_le /rtk_profile;smt(). qed.
lemma rt_ow_kernel_calls(B<:SecOWAdversary) :
 hoare[RTOWKernel(B).run:true ==>res.`2.`rtk_adversary=1].
proof.
 proc;wp;call(_:true ==>true);first by trivial.
 wp;call(_:true ==>true);first by trivial.
 call rt_encrypt_profile;wp;rnd;wp;rnd;auto=> />;rewrite /rtk_add /rtk_profile /=;smt().
qed.
lemma rt_di_outer_history(S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})(cost:(glob S)->rt_profile) :
 hoare[RTAuxINJ(S,A).run:cost(glob S)=rt_zero ==>rt_reducer_profile(cost(glob S))]=>
 hoare[RTINJNTRUReduction(RTAuxINJ(S,A)).run:cost(glob S)=rt_zero ==>
 rt_invocation_profile res.`2.`rtk_adversary(cost(glob S))].
proof.
 move=>hb;proc;seq 10:(cost(glob S)=rt_zero /\ calls=0 /\
 profile=rtk_profile 0 0 0 0 0 0 0 0 0 0).
 + wp;call(_:true ==>true);first by trivial. auto.
 if;last by auto=> />;rewrite /rt_invocation_profile /rtk_add /rtk_profile /=;smt().
 wp;call rt_inj_checker_calls;wp;call hb;wp;call(_:true ==>true);first by trivial.
 auto=> />;rewrite /rt_invocation_profile /rtk_add /rtk_profile /=;smt().
qed.
lemma rt_ow_kernel_history(S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})(cost:(glob S)->rt_profile) :
 hoare[RTAuxOW(S,A).run:cost(glob S)=rt_zero ==>rt_reducer_profile(cost(glob S))]=>
 hoare[RTOWKernel(RTAuxOW(S,A)).run:cost(glob S)=rt_zero ==>
 res.`2.`rtk_adversary=1 /\ rt_reducer_profile(cost(glob S))].
proof.
 move=>hb;proc;wp;call(_:true ==>true);first by trivial.
 wp;call hb;call rt_encrypt_profile;wp;rnd;wp;rnd;auto=> />;
 rewrite /rtk_add /rtk_profile /=;smt().
qed.
lemma rt_do_outer_history(S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})(cost:(glob S)->rt_profile) :
 hoare[RTAuxOW(S,A).run:cost(glob S)=rt_zero ==>rt_reducer_profile(cost(glob S))]=>
 hoare[RTOWNTRUReduction(RTAuxOW(S,A)).run:cost(glob S)=rt_zero ==>
 rt_invocation_profile res.`2.`rtk_adversary(cost(glob S))].
proof.
 move=>hb;proc;seq 9:(cost(glob S)=rt_zero /\ profile=rtk_profile 0 0 0 0 0 0 0 0 0 0).
 + wp;call(_:true ==>true);first by trivial. auto.
 if;last by auto=> />;rewrite /rt_invocation_profile /rtk_add /rtk_profile /=;smt().
 wp;call(rt_ow_kernel_history S A cost hb);wp;call(_:true ==>true);first by trivial.
 auto=> />;rewrite /rt_invocation_profile /rtk_add /rtk_profile /=;smt().
qed.
lemma rt_co_outer_history(S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})(cost:(glob S)->rt_profile) :
 hoare[RTAuxOW(S,A).run:cost(glob S)=rt_zero ==>rt_reducer_profile(cost(glob S))]=>
 hoare[RTOWRLWESolver(RTAuxOW(S,A)).run:cost(glob S)=rt_zero ==>
 rt_invocation_profile res.`2.`rtk_adversary(cost(glob S))].
proof.
 move=>hb;proc;seq 7:(cost(glob S)=rt_zero /\ calls=0).
 + wp;call(_:true ==>true);first by trivial. auto.
 if;last by auto=> />;rewrite /rt_invocation_profile /rtk_profile /=;smt().
 wp;call(_:true ==>true);first by trivial.
 wp;call hb;wp;call(_:true ==>true);first by trivial.
 wp;call(_:true ==>true);first by trivial.
 auto=> />;rewrite /rt_invocation_profile /rtk_profile /=;smt().
qed.
lemma rt_metrics_preserve_profile(S<:RTHistory)(view:(glob S)->ah_state)(cost:(glob S)->rt_profile) p0 :
 (forall st p,hoare[S.metrics:view(glob S)=st /\ cost(glob S)=p ==>
 res=p /\ view(glob S)=st /\ cost(glob S)=p])=>
 hoare[S.metrics:cost(glob S)=p0 ==>res=p0 /\ cost(glob S)=p0].
proof.
 move=>hm;proc*;exists* (view(glob S));elim*=>st.
 call(hm st p0);auto=> />;smt().
qed.

lemma rt_di_history_profile
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (view:(glob S)->ah_state)(cost:(glob S)->rt_profile) :
 (forall st p n,hoare[S.charge_extract:
 view(glob S)=st /\ cost(glob S)=p /\ visits=n ==>
 view(glob S)=st /\ cost(glob S)=rt_extract p n])=>
 hoare[RTTranscript(S,A).run:cost(glob S)=rt_zero ==>
 rt_transcript_ok res.`1 res.`2 /\ cost(glob S)=res.`2 /\ SecGHistory.queries=res.`1]=>
 hoare[S.reset_cost:true ==>cost(glob S)=rt_zero]=>
 (forall st p,hoare[S.metrics:view(glob S)=st /\ cost(glob S)=p ==>
 res=p /\ view(glob S)=st /\ cost(glob S)=p])=>
 hoare[RT_DI(S,A).measure:true ==>
 rt_invocation_profile res.`3.`rtk_adversary res.`2].
proof.
 move=>hx hb hz hm;proc.
 seq 2:(rt_invocation_profile out.`2.`rtk_adversary(cost(glob S))).
 + call(rt_di_outer_history S A cost (rt_inj_aux_profile S A view cost hx hb)).
   call hz;auto.
 exists* (cost(glob S));elim*=>p0.
 call(rt_metrics_preserve_profile S view cost p0 hm);auto=> />.
 clear hx hb hz hm;smt(rt_inj_complete_calls).
qed.

lemma rt_do_history_profile
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (view:(glob S)->ah_state)(cost:(glob S)->rt_profile) :
 (forall st p n,hoare[S.charge_extract:
 view(glob S)=st /\ cost(glob S)=p /\ visits=n ==>
 view(glob S)=st /\ cost(glob S)=rt_extract p n])=>
 hoare[RTTranscript(S,A).run:cost(glob S)=rt_zero ==>
 rt_transcript_ok res.`1 res.`2 /\ cost(glob S)=res.`2 /\ SecGHistory.queries=res.`1]=>
 hoare[S.reset_cost:true ==>cost(glob S)=rt_zero]=>
 (forall st p,hoare[S.metrics:view(glob S)=st /\ cost(glob S)=p ==>
 res=p /\ view(glob S)=st /\ cost(glob S)=p])=>
 hoare[RT_DO(S,A).measure:true ==>
 rt_invocation_profile res.`3.`rtk_adversary res.`2].
proof.
 move=>hx hb hz hm;proc.
 seq 2:(rt_invocation_profile out.`2.`rtk_adversary(cost(glob S))).
 + call(rt_do_outer_history S A cost (rt_ow_aux_profile S A view cost hx hb)).
   call hz;auto.
 exists* (cost(glob S));elim*=>p0.
 call(rt_metrics_preserve_profile S view cost p0 hm);auto=> />.
qed.

lemma rt_co_history_profile
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (view:(glob S)->ah_state)(cost:(glob S)->rt_profile) :
 (forall st p n,hoare[S.charge_extract:
 view(glob S)=st /\ cost(glob S)=p /\ visits=n ==>
 view(glob S)=st /\ cost(glob S)=rt_extract p n])=>
 hoare[RTTranscript(S,A).run:cost(glob S)=rt_zero ==>
 rt_transcript_ok res.`1 res.`2 /\ cost(glob S)=res.`2 /\ SecGHistory.queries=res.`1]=>
 hoare[S.reset_cost:true ==>cost(glob S)=rt_zero]=>
 (forall st p,hoare[S.metrics:view(glob S)=st /\ cost(glob S)=p ==>
 res=p /\ view(glob S)=st /\ cost(glob S)=p])=>
 hoare[RT_CO(S,A).measure:true ==>
 rt_invocation_profile res.`3.`rtk_adversary res.`2].
proof.
 move=>hx hb hz hm;proc.
 seq 2:(rt_invocation_profile out.`2.`rtk_adversary(cost(glob S))).
 + call(rt_co_outer_history S A cost (rt_ow_aux_profile S A view cost hx hb)).
   call hz;auto.
 exists* (cost(glob S));elim*=>p0.
 call(rt_metrics_preserve_profile S view cost p0 hm);auto=> />.
qed.

lemma rt_di_real_probability
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (view:(glob S)->ah_state) &m :
 equiv[RT_DI(S,A).run ~ AHActual_DI(S,A).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2} ==>
 ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2}]=>
 Pr[OWNTRURealGame(RT_DI(S,A)).run()@&m:res]=
 Pr[OWNTRURealGame(AHActual_DI(S,A)).run()@&m:res].
proof.
 move=>hp;byequiv(_: ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2} ==> ={res})=> //.
 proc;call hp;rnd;auto.
qed.

lemma rt_di_uniform_probability
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (view:(glob S)->ah_state) &m :
 equiv[RT_DI(S,A).run ~ AHActual_DI(S,A).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2} ==>
 ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2}]=>
 Pr[OWNTRUUniformGame(RT_DI(S,A)).run()@&m:res]=
 Pr[OWNTRUUniformGame(AHActual_DI(S,A)).run()@&m:res].
proof.
 move=>hp;byequiv(_: ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2} ==> ={res})=> //.
 proc;call hp;rnd;auto.
qed.

lemma rt_do_real_probability
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (view:(glob S)->ah_state) &m :
 equiv[RT_DO(S,A).run ~ AHActual_DO(S,A).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2} ==>
 ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2}]=>
 Pr[OWNTRURealGame(RT_DO(S,A)).run()@&m:res]=
 Pr[OWNTRURealGame(AHActual_DO(S,A)).run()@&m:res].
proof.
 move=>hp;byequiv(_: ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2} ==> ={res})=> //.
 proc;call hp;rnd;auto.
qed.

lemma rt_do_uniform_probability
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (view:(glob S)->ah_state) &m :
 equiv[RT_DO(S,A).run ~ AHActual_DO(S,A).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2} ==>
 ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2}]=>
 Pr[OWNTRUUniformGame(RT_DO(S,A)).run()@&m:res]=
 Pr[OWNTRUUniformGame(AHActual_DO(S,A)).run()@&m:res].
proof.
 move=>hp;byequiv(_: ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2} ==> ={res})=> //.
 proc;call hp;rnd;auto.
qed.

lemma rt_co_rlwe_probability
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (view:(glob S)->ah_state) &m :
 equiv[RT_CO(S,A).run ~ AHActual_CO(S,A).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2} ==>
 ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2}]=>
 Pr[OWRLWEGame(RT_CO(S,A)).run()@&m:res]=
 Pr[OWRLWEGame(AHActual_CO(S,A)).run()@&m:res].
proof.
 move=>hp;byequiv(_: ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2} ==> ={res})=> //.
 proc;wp;call hp;wp;rnd;rnd;rnd;auto.
qed.
