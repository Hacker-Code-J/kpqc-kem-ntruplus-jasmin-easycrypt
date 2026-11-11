require import AllCore List Distr FMap.
from Jasmin require import JWord.
require import Array32 Array768 Array1152.
require import NTRUPlus768PKEModel NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768CyclotomicFactorization NTRUPlus768OWCodec NTRUPlus768OWGames.
require import NTRUPlus768RTModel NTRUPlus768RTStore NTRUPlus768RTKernelTypes.
require import NTRUPlus768RTProjection NTRUPlus768RTReduction NTRUPlus768RTAdaptive.
require import NTRUPlus768RTWordKernels NTRUPlus768RTWordGames.
require import NTRUPlus768AHState NTRUPlus768CCAGame NTRUPlus768CCADecapOracle.
require import NTRUPlus768ROMOracles NTRUPlus768RawXOFStreams NTRUPlus768SecGOracles.

(* The executable interfaces carry only fixed arrays. Polynomials are
   specification/challenger values and never read by these procedures. *)
module type RTWordNTRUMeasured = {
 proc measure(h:pke_poly):bool*rt_profile*rt_kernel_profile
 proc run(h:pke_poly):bool
}.
module type RTWordRLWEMeasured = {
 proc measure(a b:pke_poly):pke_poly*rt_profile*rt_kernel_profile
 proc run(a b:pke_poly):pke_poly
}.
module RTWord_DI(S:RTHistory,A:CCAExtendedAdversary) = {
 proc measure(h:pke_poly):bool*rt_profile*rt_kernel_profile = {
  var out:bool*rt_kernel_profile;var profile:rt_profile;
  S.reset_cost();out<@RTWordINJNTRUReduction(RTAuxINJ(S,A)).run(h);
  profile<@S.metrics();return(out.`1,profile,rt_inj_complete_profile out.`2);
 }
 proc run(h:pke_poly):bool = {
  var out:bool*rt_profile*rt_kernel_profile;
  out<@measure(h);return out.`1;
 }
}.
module RTWord_DO(S:RTHistory,A:CCAExtendedAdversary) = {
 proc measure(h:pke_poly):bool*rt_profile*rt_kernel_profile = {
  var out:bool*rt_kernel_profile;var profile:rt_profile;
  S.reset_cost();out<@RTWordOWNTRUReduction(RTAuxOW(S,A)).run(h);
  profile<@S.metrics();return(out.`1,profile,out.`2);
 }
 proc run(h:pke_poly):bool = {
  var out:bool*rt_profile*rt_kernel_profile;
  out<@measure(h);return out.`1;
 }
}.
module RTWord_CO(S:RTHistory,A:CCAExtendedAdversary) = {
 proc measure(a b:pke_poly):pke_poly*rt_profile*rt_kernel_profile = {
  var out:pke_poly*rt_kernel_profile;var profile:rt_profile;
  S.reset_cost();out<@RTWordOWRLWESolver(RTAuxOW(S,A)).run(a,b);
  profile<@S.metrics();return(out.`1,profile,out.`2);
 }
 proc run(a b:pke_poly):pke_poly = {
  var out:pke_poly*rt_profile*rt_kernel_profile;
  out<@measure(a,b);return out.`1;
 }
}.

lemma rt_word_di_measure_projection
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory}) :
 equiv[RTWord_DI(S,A).measure ~ RT_DI(S,A).measure:
 h{1}=ow_coeff_words h{2} /\ ={glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} ==> ={res,glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries}].
proof.
 proc;call(_: ={arg,glob S} ==> ={res,glob S});first by proc true;auto.
 call(rt_word_inj_projection (RTAuxINJ(S,A))).
 call(_: ={arg,glob S} ==> ={res,glob S});first by proc true;auto.
 auto.
qed.

lemma rt_word_di_projection
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory}) :
 equiv[RTWord_DI(S,A).run ~ RT_DI(S,A).run:
 h{1}=ow_coeff_words h{2} /\ ={glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} ==> ={res,glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries}].
proof. proc;call(rt_word_di_measure_projection S A);auto. qed.

lemma rt_word_do_measure_projection
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory}) :
 equiv[RTWord_DO(S,A).measure ~ RT_DO(S,A).measure:
 h{1}=ow_coeff_words h{2} /\ ={glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} ==> ={res,glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries}].
proof.
 proc;call(_: ={arg,glob S} ==> ={res,glob S});first by proc true;auto.
 call(rt_word_ow_projection (RTAuxOW(S,A))).
 call(_: ={arg,glob S} ==> ={res,glob S});first by proc true;auto.
 auto.
qed.

lemma rt_word_do_projection
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory}) :
 equiv[RTWord_DO(S,A).run ~ RT_DO(S,A).run:
 h{1}=ow_coeff_words h{2} /\ ={glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} ==> ={res,glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries}].
proof. proc;call(rt_word_do_measure_projection S A);auto. qed.

lemma rt_word_co_measure_projection
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory}) :
 equiv[RTWord_CO(S,A).measure ~ RT_CO(S,A).measure:
 a{1}=ow_coeff_words a{2} /\ b{1}=ow_coeff_words b{2} /\ ={glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} ==> input_poly res{1}.`1=res{2}.`1 /\ res{1}.`2=res{2}.`2 /\ res{1}.`3=res{2}.`3 /\ ={glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries}].
proof.
 proc;call(_: ={arg,glob S} ==> ={res,glob S});first by proc true;auto.
 call(rt_word_rlwe_projection (RTAuxOW(S,A))).
 call(_: ={arg,glob S} ==> ={res,glob S});first by proc true;auto.
 auto.
qed.

lemma rt_word_co_projection
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory}) :
 equiv[RTWord_CO(S,A).run ~ RT_CO(S,A).run:
 a{1}=ow_coeff_words a{2} /\ b{1}=ow_coeff_words b{2} /\ ={glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} ==> input_poly res{1}=res{2} /\ ={glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries}].
proof. proc;call(rt_word_co_measure_projection S A);auto. qed.

(* Transfer a predicate of the actual returned profiles and store state.
   The right initial memory is chosen identically, with the represented
   polynomial input; no new probability or cost assumption is introduced. *)
lemma rt_word_di_profile_transport
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory}) p0
 (post:rt_profile->rt_kernel_profile->(glob S)->bool) :
 hoare[RT_DI(S,A).measure:true ==>post res.`2 res.`3(glob S)]=>
 hoare[RTWord_DI(S,A).measure:h=ow_coeff_words p0 ==>post res.`2 res.`3(glob S)].
proof.
 move=>hp;conseq(rt_word_di_measure_projection S A)hp.
 + move=> &1 hinput.
   exists (glob A){1} (glob S){1} ROE.m{1} ROF.m{1} ROG.m{1} ROH.m{1}
    RawXOFStreams.es{1} RawXOFStreams.fs{1} RawXOFStreams.gs{1} RawXOFStreams.other{1}
    SecGHistory.queries{1} p0;smt().
 smt().
qed.
lemma rt_word_di_kernel_profile
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory}) p0 :
 hoare[RTWord_DI(S,A).measure:h=ow_coeff_words p0 ==>rtk_le res.`3 rt_di_kernel_bound].
proof.
 exact(rt_word_di_profile_transport S A p0
  (fun p k gs=>rtk_le k rt_di_kernel_bound)(rt_di_kernel_profile S A)).
qed.

(* Transfer a predicate of the actual returned profiles and store state.
   The right initial memory is chosen identically, with the represented
   polynomial input; no new probability or cost assumption is introduced. *)
lemma rt_word_do_profile_transport
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory}) p0
 (post:rt_profile->rt_kernel_profile->(glob S)->bool) :
 hoare[RT_DO(S,A).measure:true ==>post res.`2 res.`3(glob S)]=>
 hoare[RTWord_DO(S,A).measure:h=ow_coeff_words p0 ==>post res.`2 res.`3(glob S)].
proof.
 move=>hp;conseq(rt_word_do_measure_projection S A)hp.
 + move=> &1 hinput.
   exists (glob A){1} (glob S){1} ROE.m{1} ROF.m{1} ROG.m{1} ROH.m{1}
    RawXOFStreams.es{1} RawXOFStreams.fs{1} RawXOFStreams.gs{1} RawXOFStreams.other{1}
    SecGHistory.queries{1} p0;smt().
 smt().
qed.
lemma rt_word_do_kernel_profile
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory}) p0 :
 hoare[RTWord_DO(S,A).measure:h=ow_coeff_words p0 ==>rtk_le res.`3 rt_do_kernel_bound].
proof.
 exact(rt_word_do_profile_transport S A p0
  (fun p k gs=>rtk_le k rt_do_kernel_bound)(rt_do_kernel_profile S A)).
qed.

(* Transfer a predicate of the actual returned profiles and store state.
   The right initial memory is chosen identically, with the represented
   polynomial input; no new probability or cost assumption is introduced. *)
lemma rt_word_co_profile_transport
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory}) p0 q0
 (post:rt_profile->rt_kernel_profile->(glob S)->bool) :
 hoare[RT_CO(S,A).measure:true ==>post res.`2 res.`3(glob S)]=>
 hoare[RTWord_CO(S,A).measure:a=ow_coeff_words p0 /\ b=ow_coeff_words q0 ==>post res.`2 res.`3(glob S)].
proof.
 move=>hp;conseq(rt_word_co_measure_projection S A)hp.
 + move=> &1 hinput.
   exists (glob A){1} (glob S){1} ROE.m{1} ROF.m{1} ROG.m{1} ROH.m{1}
    RawXOFStreams.es{1} RawXOFStreams.fs{1} RawXOFStreams.gs{1} RawXOFStreams.other{1}
    SecGHistory.queries{1} (p0,q0);smt().
 smt().
qed.
lemma rt_word_co_kernel_profile
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory}) p0 q0 :
 hoare[RTWord_CO(S,A).measure:a=ow_coeff_words p0 /\ b=ow_coeff_words q0 ==>rtk_le res.`3 rt_co_kernel_bound].
proof.
 exact(rt_word_co_profile_transport S A p0 q0
  (fun p k gs=>rtk_le k rt_co_kernel_bound)(rt_co_kernel_profile S A)).
qed.

lemma rt_word_di_history_profile
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (view:(glob S)->ah_state)(cost:(glob S)->rt_profile) p0 :
 (forall st p n,hoare[S.charge_extract:
 view(glob S)=st /\ cost(glob S)=p /\ visits=n ==>
 view(glob S)=st /\ cost(glob S)=rt_extract p n])=>
 hoare[RTTranscript(S,A).run:cost(glob S)=rt_zero ==>
 rt_transcript_ok res.`1 res.`2 /\ cost(glob S)=res.`2 /\ SecGHistory.queries=res.`1]=>
 hoare[S.reset_cost:true ==>cost(glob S)=rt_zero]=>
 (forall st p,hoare[S.metrics:view(glob S)=st /\ cost(glob S)=p ==>
 res=p /\ view(glob S)=st /\ cost(glob S)=p])=>
 hoare[RTWord_DI(S,A).measure:h=ow_coeff_words p0 ==>
 rt_invocation_profile res.`3.`rtk_adversary res.`2].
proof.
 move=>hx hb hz hm.
 exact(rt_word_di_profile_transport S A p0
  (fun p k gs=>rt_invocation_profile k.`rtk_adversary p)
  (rt_di_history_profile S A view cost hx hb hz hm)).
qed.
lemma rt_word_di_profile_read
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (view:(glob S)->ah_state)(cost:(glob S)->rt_profile) p0 :
 (forall st p,hoare[S.metrics:view(glob S)=st /\ cost(glob S)=p ==>
 res=p /\ view(glob S)=st /\ cost(glob S)=p])=>
 hoare[RTWord_DI(S,A).measure:h=ow_coeff_words p0 ==>res.`2=cost(glob S)].
proof.
 move=>hm;exact(rt_word_di_profile_transport S A p0
  (fun p k gs=>p=cost gs)(rt_di_profile_read S A view cost hm)).
qed.

lemma rt_word_do_history_profile
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (view:(glob S)->ah_state)(cost:(glob S)->rt_profile) p0 :
 (forall st p n,hoare[S.charge_extract:
 view(glob S)=st /\ cost(glob S)=p /\ visits=n ==>
 view(glob S)=st /\ cost(glob S)=rt_extract p n])=>
 hoare[RTTranscript(S,A).run:cost(glob S)=rt_zero ==>
 rt_transcript_ok res.`1 res.`2 /\ cost(glob S)=res.`2 /\ SecGHistory.queries=res.`1]=>
 hoare[S.reset_cost:true ==>cost(glob S)=rt_zero]=>
 (forall st p,hoare[S.metrics:view(glob S)=st /\ cost(glob S)=p ==>
 res=p /\ view(glob S)=st /\ cost(glob S)=p])=>
 hoare[RTWord_DO(S,A).measure:h=ow_coeff_words p0 ==>
 rt_invocation_profile res.`3.`rtk_adversary res.`2].
proof.
 move=>hx hb hz hm.
 exact(rt_word_do_profile_transport S A p0
  (fun p k gs=>rt_invocation_profile k.`rtk_adversary p)
  (rt_do_history_profile S A view cost hx hb hz hm)).
qed.
lemma rt_word_do_profile_read
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (view:(glob S)->ah_state)(cost:(glob S)->rt_profile) p0 :
 (forall st p,hoare[S.metrics:view(glob S)=st /\ cost(glob S)=p ==>
 res=p /\ view(glob S)=st /\ cost(glob S)=p])=>
 hoare[RTWord_DO(S,A).measure:h=ow_coeff_words p0 ==>res.`2=cost(glob S)].
proof.
 move=>hm;exact(rt_word_do_profile_transport S A p0
  (fun p k gs=>p=cost gs)(rt_do_profile_read S A view cost hm)).
qed.

lemma rt_word_co_history_profile
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (view:(glob S)->ah_state)(cost:(glob S)->rt_profile) p0 q0 :
 (forall st p n,hoare[S.charge_extract:
 view(glob S)=st /\ cost(glob S)=p /\ visits=n ==>
 view(glob S)=st /\ cost(glob S)=rt_extract p n])=>
 hoare[RTTranscript(S,A).run:cost(glob S)=rt_zero ==>
 rt_transcript_ok res.`1 res.`2 /\ cost(glob S)=res.`2 /\ SecGHistory.queries=res.`1]=>
 hoare[S.reset_cost:true ==>cost(glob S)=rt_zero]=>
 (forall st p,hoare[S.metrics:view(glob S)=st /\ cost(glob S)=p ==>
 res=p /\ view(glob S)=st /\ cost(glob S)=p])=>
 hoare[RTWord_CO(S,A).measure:a=ow_coeff_words p0 /\ b=ow_coeff_words q0 ==>
 rt_invocation_profile res.`3.`rtk_adversary res.`2].
proof.
 move=>hx hb hz hm.
 exact(rt_word_co_profile_transport S A p0 q0
  (fun p k gs=>rt_invocation_profile k.`rtk_adversary p)
  (rt_co_history_profile S A view cost hx hb hz hm)).
qed.
lemma rt_word_co_profile_read
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (view:(glob S)->ah_state)(cost:(glob S)->rt_profile) p0 q0 :
 (forall st p,hoare[S.metrics:view(glob S)=st /\ cost(glob S)=p ==>
 res=p /\ view(glob S)=st /\ cost(glob S)=p])=>
 hoare[RTWord_CO(S,A).measure:a=ow_coeff_words p0 /\ b=ow_coeff_words q0 ==>res.`2=cost(glob S)].
proof.
 move=>hm;exact(rt_word_co_profile_transport S A p0 q0
  (fun p k gs=>p=cost gs)(rt_co_profile_read S A view cost hm)).
qed.

lemma rt_word_di_real_probability
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory}) &m :
 Pr[RTWordNTRURealGame(RTWord_DI(S,A)).run()@&m:res]=
 Pr[OWNTRURealGame(RT_DI(S,A)).run()@&m:res].
proof.
 byequiv(_: ={glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} ==> ={res})=> //.
 proc;call(rt_word_di_projection S A);rnd;auto.
qed.

lemma rt_word_di_uniform_probability
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory}) &m :
 Pr[RTWordNTRUUniformGame(RTWord_DI(S,A)).run()@&m:res]=
 Pr[OWNTRUUniformGame(RT_DI(S,A)).run()@&m:res].
proof.
 byequiv(_: ={glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} ==> ={res})=> //.
 proc;call(rt_word_di_projection S A);rnd;auto.
qed.

lemma rt_word_do_real_probability
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory}) &m :
 Pr[RTWordNTRURealGame(RTWord_DO(S,A)).run()@&m:res]=
 Pr[OWNTRURealGame(RT_DO(S,A)).run()@&m:res].
proof.
 byequiv(_: ={glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} ==> ={res})=> //.
 proc;call(rt_word_do_projection S A);rnd;auto.
qed.

lemma rt_word_do_uniform_probability
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory}) &m :
 Pr[RTWordNTRUUniformGame(RTWord_DO(S,A)).run()@&m:res]=
 Pr[OWNTRUUniformGame(RT_DO(S,A)).run()@&m:res].
proof.
 byequiv(_: ={glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} ==> ={res})=> //.
 proc;call(rt_word_do_projection S A);rnd;auto.
qed.

lemma rt_word_co_rlwe_probability
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory}) &m :
 Pr[RTWordRLWEGame(RTWord_CO(S,A)).run()@&m:res]=
 Pr[OWRLWEGame(RT_CO(S,A)).run()@&m:res].
proof.
 byequiv(_: ={glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} ==> ={res})=> //.
 proc;wp;call(rt_word_co_projection S A);wp;rnd;rnd;rnd;auto.
qed.

lemma rt_word_ntru_measure_same(M<:RTWordNTRUMeasured) :
 equiv[M.measure ~ M.measure: ={arg,glob M} ==> ={res,glob M}].
proof. proc true;auto. qed.
lemma rt_word_rlwe_measure_same(M<:RTWordRLWEMeasured) :
 equiv[M.measure ~ M.measure: ={arg,glob M} ==> ={res,glob M}].
proof. proc true;auto. qed.

lemma rt_word_di_run_measure
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory}) h0 &m :
 Pr[RTWord_DI(S,A).run(h0)@&m:res]=
 Pr[RTWord_DI(S,A).measure(h0)@&m:res.`1].
proof.
 byequiv(_: ={arg,glob RTWord_DI(S,A)} ==>res{1}=res{2}.`1)=> //.
 proc*;inline{1} RTWord_DI(S,A).run;wp;call(rt_word_ntru_measure_same (RTWord_DI(S,A)));auto.
qed.

lemma rt_word_do_run_measure
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory}) h0 &m :
 Pr[RTWord_DO(S,A).run(h0)@&m:res]=
 Pr[RTWord_DO(S,A).measure(h0)@&m:res.`1].
proof.
 byequiv(_: ={arg,glob RTWord_DO(S,A)} ==>res{1}=res{2}.`1)=> //.
 proc*;inline{1} RTWord_DO(S,A).run;wp;call(rt_word_ntru_measure_same (RTWord_DO(S,A)));auto.
qed.

lemma rt_word_co_run_measure
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory}) a0 b0 answer &m :
 Pr[RTWord_CO(S,A).run(a0,b0)@&m:input_poly res=answer]=
 Pr[RTWord_CO(S,A).measure(a0,b0)@&m:input_poly res.`1=answer].
proof.
 byequiv(_: ={arg,glob RTWord_CO(S,A)} ==>res{1}=res{2}.`1)=> //.
 proc*;inline{1} RTWord_CO(S,A).run;wp;call(rt_word_rlwe_measure_same (RTWord_CO(S,A)));auto.
qed.
