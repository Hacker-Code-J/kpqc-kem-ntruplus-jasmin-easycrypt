require import AllCore List Distr FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152.
require import NTRUPlus768AHState NTRUPlus768AHAdapter NTRUPlus768AHFreshBound NTRUPlus768AHCallbacks.
require import NTRUPlus768FOModel NTRUPlus768FOEagerG NTRUPlus768FOGAdapters NTRUPlus768FOQueryBudget.
require import NTRUPlus768SimModel NTRUPlus768SimSampling NTRUPlus768SimOracles NTRUPlus768SimPublicError NTRUPlus768SimPublicInstances.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDomains NTRUPlus768RawXOFSampling NTRUPlus768RawXOFStreams NTRUPlus768RawXOF NTRUPlus768CCAQueryCodec.
require import NTRUPlus768CCAOraclePorts NTRUPlus768ACWC2Oracle NTRUPlus768FONativeBridge.

lemma ah_raw_port_same (O<:CCAExtendedOraclePort) :
 equiv[O.raw ~ O.raw: ={arg,glob O} ==> ={res,glob O}].
proof. proc true;auto. qed.

lemma ah_raw_non_h_forward (S<:AHStore)(O<:CCAExtendedOraclePort) input0 n0 :
 (!(0<=n0<=raw_xof_max_output) \/ forall x,decode_typed input0<>Some(H x)) =>
 equiv[AHOracles(S,O).raw ~ O.raw:
 ={arg,glob O} /\ input{1}=input0 /\ outlen{1}=n0 ==> ={res,glob O}].
proof.
 move=>hn;proc*;inline{1} AHOracles(S,O).raw;sp 2 0;if{1}.
 + match{1}.
   - wp;call(ah_raw_port_same O);auto.
   match{1}.
   - wp;call(ah_raw_port_same O);auto.
   - wp;call(ah_raw_port_same O);auto.
   - wp;call(ah_raw_port_same O);auto.
   exfalso=> />;smt().
 wp;call(ah_raw_port_same O);auto.
qed.

lemma ah_fresh_raw_non_h_history log0 :
 hoare[AHFreshOracles.raw:SimHistory.h=log0 /\ !fo_raw_h input outlen ==>SimHistory.h=log0].
proof.
 proc;wp;call(sim_raw_non_h_history FOGActual (SimPublicErrorH(SimHActual)) log0);auto.
qed.

lemma ah_raw_g_cache g :
 hoare[FOGRawStreams(FOGActual).g:acwc2_cache_matches g ROG.m ==>acwc2_cache_matches g ROG.m].
proof.
 proc;seq 1:(acwc2_cache_matches g ROG.m).
 + ecall(rog_get_value ROG.m input);auto=> />;smt(fo_cache_extension).
 if;auto.
qed.
lemma ah_raw_full_cache g :
 hoare[SimRaw(FOGActual,SimPublicErrorH(SimHActual)).full:
 acwc2_cache_matches g ROG.m ==>acwc2_cache_matches g ROG.m].
proof.
 proc;match;first by call(_:true ==>true);first by trivial. auto.
 match.
 + call(_:true ==>true);first by trivial. auto.
 + call(_:true ==>true);first by trivial. auto.
 + call(ah_raw_g_cache g);auto.
 call(_:true ==>true);first by trivial. auto.
qed.
lemma ah_fresh_raw_cache g :
 hoare[AHFreshOracles.raw:acwc2_cache_matches g ROG.m ==>acwc2_cache_matches g ROG.m].
proof.
 proc;inline SimRaw(FOGActual,SimPublicErrorH(SimHActual)).get;sp;if;last by auto.
 wp;call(ah_raw_full_cache g);auto.
qed.

lemma ah_raw_latched
 (S<:AHStore {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-FOContext,-SimPublic,-SimHistory,-SimBad}) :
 hoare[AHOracles(S,AHFreshOracles).raw:SimBad.corr ==>SimBad.corr].
proof.
 proc;if;last by call ah_fresh_raw_latched;auto.
 match;first by call ah_fresh_raw_latched;auto.
 match.
 + call ah_fresh_raw_latched;auto.
 + call ah_fresh_raw_latched;auto.
 + call ah_fresh_raw_latched;auto.
 wp;call(ah_record_h_latched S);auto.
qed.

lemma ah_raw_non_h_same log0 :
 equiv[AHFreshOracles.raw ~ AHFreshOracles.raw:
 ={arg,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SimHistory.h,
   FOContext.w,FOContext.g,FOContext.challenge_h,SimBad.corr} /\
 SimHistory.h{1}=log0 /\ !fo_raw_h input{1} outlen{1} ==>
 ={res,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SimHistory.h,
   FOContext.w,FOContext.g,FOContext.challenge_h,SimBad.corr} /\ SimHistory.h{1}=log0].
proof.
 conseq(_: ={arg,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SimHistory.h,
   FOContext.w,FOContext.g,FOContext.challenge_h,SimBad.corr} ==>
 ={res,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SimHistory.h,
   FOContext.w,FOContext.g,FOContext.challenge_h,SimBad.corr})
 (ah_fresh_raw_non_h_history log0) _=> //;by sim.
qed.

(* A valid raw H request is exactly one full typed H call followed by
   prefix extraction. This includes output length zero. *)
lemma ah_fresh_raw_h_as_typed x0 n0 :
 equiv[AHFreshOracles.raw ~ AHFreshOracles.h:
 ={ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SimHistory.h,FOContext.w,FOContext.g,FOContext.challenge_h,SimBad.corr} /\
 input{1}=raw_query(H x0) /\ outlen{1}=n0 /\ input{2}=x0 /\
 0<=n0<=raw_xof_max_output ==>
 ={ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SimHistory.h,FOContext.w,FOContext.g,FOContext.challenge_h,SimBad.corr} /\
 res{1}=Some(raw_xof_output n0 res{2})].
proof.
 have he:=decode_typed_encode(H x0).
 proc;inline{1} SimRaw(FOGActual,SimPublicErrorH(SimHActual)).get;sp.
 rcondt{1} 1;first by auto.
 inline{1} SimRaw(FOGActual,SimPublicErrorH(SimHActual)).full;sp.
 match Some{1} 1;first by auto=> />;smt().
 sp;match H{1} 1;first by auto=> />;smt().
 wp;call(_: ={arg,ROH.m,SimHistory.h,FOContext.w,FOContext.g,FOContext.challenge_h,SimBad.corr} ==>
 ={res,ROH.m,SimHistory.h,FOContext.w,FOContext.g,FOContext.challenge_h,SimBad.corr});first by sim.
 auto=> />;smt().
qed.

lemma ah_fresh_raw_h_update w g x0 n0 log0 b0 :
 equiv[AHFreshOracles.raw ~ AHFreshOracles.h:
 ={ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SimHistory.h,FOContext.w,FOContext.g,FOContext.challenge_h,SimBad.corr} /\
 input{1}=raw_query(H x0) /\ outlen{1}=n0 /\ input{2}=x0 /\
 0<=n0<=raw_xof_max_output /\ SimHistory.h{1}=log0 /\ SimBad.corr{1}=b0 /\
 FOContext.w{1}=w /\ FOContext.g{1}=g /\ FOContext.challenge_h{1}=None ==>
 ={ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SimHistory.h,FOContext.w,FOContext.g,FOContext.challenge_h,SimBad.corr} /\
 res{1}=Some(raw_xof_output n0 res{2}) /\ SimHistory.h{1}=log0.[x0<-res{2}]].
proof.
 conseq(ah_fresh_raw_h_as_typed x0 n0) _ (ah_h_exact w g x0 log0 b0)=> //.
qed.

lemma ah_raw_core_coupling
 (S<:AHStore {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-FOContext,-SimPublic,-SimHistory,-SimBad})
 (view:(glob S)->ah_state) w g pk suffix star :
 islossless S.record=>
 (forall st x y,hoare[S.record:view(glob S)=st /\ input=x /\ hout=y ==>
 view(glob S)=ah_record_state st x y])=>
 equiv[AHFreshOracles.raw ~ AHOracles(S,AHFreshOracles).raw:
 ={arg,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SimHistory.h,
   FOContext.w,FOContext.g,FOContext.challenge_h,SimBad.corr} /\
 FOContext.w{1}=w /\ FOContext.g{1}=g /\ FOContext.challenge_h{1}=None /\
 ah_view_rep(view(glob S){2}) pk suffix star SimHistory.h{1} ==>
 ={res,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SimHistory.h,
   FOContext.w,FOContext.g,FOContext.challenge_h,SimBad.corr} /\
 FOContext.w{1}=w /\ FOContext.g{1}=g /\ FOContext.challenge_h{1}=None /\
 ah_view_rep(view(glob S){2}) pk suffix star SimHistory.h{1}].
proof.
 move=>hll hr.
 have hc : forall st x y, phoare[S.record:view(glob S)=st /\ input=x /\ hout=y ==>
 view(glob S)=ah_record_state st x y]=1%r.
 + move=>st x y;conseq hll (hr st x y);smt().
 proc*;exists* (view(glob S){2}),SimHistory.h{1},SimBad.corr{1},input{1},outlen{1}.
 elim*=>st0 log0 b0 input0 n0.
 inline{2} AHOracles(S,AHFreshOracles).raw;sp 0 2;if{2}.
 + match{2}.
   - wp;call(ah_raw_non_h_same log0);auto=> />;
     clear hll hr hc;smt(fo_raw_h_classification).
   match{2}.
   - wp;call(ah_raw_non_h_same log0);auto=> />;
     clear hll hr hc;smt(fo_raw_h_classification).
   - wp;call(ah_raw_non_h_same log0);auto=> />;
     clear hll hr hc;smt(fo_raw_h_classification).
   - wp;call(ah_raw_non_h_same log0);auto=> />;
     clear hll hr hc;smt(fo_raw_h_classification).
   inline{2} AHRecordH(S,AHFreshOracles).get;wp.
   ecall{2}(hc st0 payload{2} hout0{2}).
   ecall(ah_fresh_raw_h_update w g payload{2} n0 log0 b0).
   auto=> />;clear hll hr hc;smt(ah_view_record decode_typed_sound).
 wp;call(ah_raw_non_h_same log0);auto=> />;
 clear hll hr hc;smt(fo_raw_h_classification).
qed.

lemma ah_raw_invariants w g :
 hoare[AHFreshOracles.raw:
 acwc2_cache_matches g ROG.m /\
 ah_fresh_inv w g (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) SimBad.corr ==>
 acwc2_cache_matches g ROG.m /\
 ah_fresh_inv w g (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) SimBad.corr].
proof. conseq(ah_fresh_raw_cache g)(ah_fresh_raw_invariant w g);smt(). qed.

(* Both raw ports retain the same physical tables and correction flag.
   No equality of lookup counters or internal G-query order is asserted. *)
lemma ah_raw_coupling
 (S<:AHStore {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-FOContext,-SimPublic,-SimHistory,-SimBad})
 (view:(glob S)->ah_state) w g pk suffix star :
 islossless S.record=>
 (forall st x y,hoare[S.record:view(glob S)=st /\ input=x /\ hout=y ==>
 view(glob S)=ah_record_state st x y])=>
 equiv[AHFreshOracles.raw ~ AHOracles(S,AHFreshOracles).raw:
 ={arg,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SimHistory.h,
   FOContext.w,FOContext.g,FOContext.challenge_h,SimBad.corr} /\
 FOContext.w{1}=w /\ FOContext.g{1}=g /\ FOContext.challenge_h{1}=None /\
 ah_view_rep(view(glob S){2}) pk suffix star SimHistory.h{1} /\
 acwc2_cache_matches g ROG.m{1} /\
 ah_fresh_inv w g (FOContext.w{1},FOContext.g{1},FOContext.challenge_h{1},SimHistory.h{1},ROH.m{1}) SimBad.corr{1} ==>
 ={res,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SimHistory.h,
   FOContext.w,FOContext.g,FOContext.challenge_h,SimBad.corr} /\
 FOContext.w{1}=w /\ FOContext.g{1}=g /\ FOContext.challenge_h{1}=None /\
 ah_view_rep(view(glob S){2}) pk suffix star SimHistory.h{1} /\
 acwc2_cache_matches g ROG.m{1} /\
 ah_fresh_inv w g (FOContext.w{1},FOContext.g{1},FOContext.challenge_h{1},SimHistory.h{1},ROH.m{1}) SimBad.corr{1}].
proof.
 move=>hll hr;conseq(ah_raw_core_coupling S view w g pk suffix star hll hr)(ah_raw_invariants w g) _=> //.
qed.
