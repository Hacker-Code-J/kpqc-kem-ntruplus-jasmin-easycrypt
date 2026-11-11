require import AllCore List Distr FMap.
require import NTRUPlus768PKEModel.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152.
require import NTRUPlus768AHState NTRUPlus768AHAdapter NTRUPlus768AHFreshBound.
require import NTRUPlus768HistModel NTRUPlus768HistLookup NTRUPlus768HistOrder.
require import NTRUPlus768ACWC2Oracle.
require import NTRUPlus768FOModel NTRUPlus768FOEagerG NTRUPlus768FOGAdapters NTRUPlus768FONativeBridge.
require import NTRUPlus768SimPublicInstances.
require import NTRUPlus768SimModel NTRUPlus768SimLookup NTRUPlus768SimSampling NTRUPlus768SimPublicError.
require import NTRUPlus768ROMOracles NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768DecapCompleteSpec NTRUPlus768CCAStatusAdapter.

(* Only the view of the private store is related to the old public map.
   The old lookup counter and the order of internal G calls are excluded. *)
op [opaque] ah_view_rep (st:ah_state) pk suffix star log =
 hist_rep st.`ah_rows log /\ ah_context st=(pk,suffix,star).

lemma ah_view_initial pk suffix star : ah_view_rep(ah_initial pk suffix star)pk suffix star empty.
proof. rewrite /ah_view_rep;split;[exact ah_initial_rep|exact ah_initial_context]. qed.
lemma ah_view_record st pk suffix star log input hout :
 ah_view_rep st pk suffix star log=>
 ah_view_rep(ah_record_state st input hout)pk suffix star log.[input<-hout].
proof.
 rewrite /ah_view_rep;move=>[hr hc];split.
 exact(ah_record_rep st input hout log hr).
 by rewrite ah_record_context.
qed.

lemma ah_g_cache g : hoare[AHFreshOracles.g:
 acwc2_cache_matches g ROG.m ==>acwc2_cache_matches g ROG.m].
proof.
 proc;ecall(rog_get_value ROG.m input);auto=> />;smt(fo_cache_extension).
qed.
lemma ah_g_same g : equiv[AHFreshOracles.g ~ AHFreshOracles.g:
 ={arg,ROG.m} /\ acwc2_cache_matches g ROG.m{1} ==>
 ={res,ROG.m} /\ acwc2_cache_matches g ROG.m{1}].
proof.
 conseq(_: ={arg,ROG.m} ==> ={res,ROG.m})(ah_g_cache g) _=> //;by sim.
qed.

lemma ah_h_exact w g x0 log0 b0 :
 hoare[AHFreshOracles.h:
 FOContext.w=w /\ FOContext.g=g /\ FOContext.challenge_h=None /\
 input=x0 /\ SimHistory.h=log0 /\ SimBad.corr=b0 ==>
 SimHistory.h=log0.[x0<-res]].
proof. proc;wp;call(ah_fresh_h_base_exact w g x0 log0 b0);auto. qed.

lemma ah_h_base w g x0 log0 b0 :
 equiv[AHFreshOracles.h ~ AHFreshOracles.h:
 ={arg,ROH.m,SimHistory.h,FOContext.w,FOContext.g,FOContext.challenge_h,SimBad.corr} /\
 input{1}=x0 /\ SimHistory.h{1}=log0 /\ SimBad.corr{1}=b0 /\
 FOContext.w{1}=w /\ FOContext.g{1}=g /\ FOContext.challenge_h{1}=None ==>
 ={res,ROH.m,SimHistory.h,FOContext.w,FOContext.g,FOContext.challenge_h,SimBad.corr} /\
 SimHistory.h{1}=log0.[x0<-res{1}]].
proof.
 conseq(_: ={arg,ROH.m,SimHistory.h,FOContext.w,FOContext.g,FOContext.challenge_h,SimBad.corr} ==>
 ={res,ROH.m,SimHistory.h,FOContext.w,FOContext.g,FOContext.challenge_h,SimBad.corr})
 (ah_h_exact w g x0 log0 b0) _=> //;by sim.
qed.

lemma ah_h_record_coupling
 (S<:AHStore {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-FOContext,-SimPublic,-SimHistory,-SimBad})
 (view:(glob S)->ah_state) w g st0 x0 log0 b0 :
 islossless S.record =>
 (forall st x y,hoare[S.record:view(glob S)=st /\ input=x /\ hout=y ==>
 view(glob S)=ah_record_state st x y])=>
 equiv[AHFreshOracles.h ~ AHOracles(S,AHFreshOracles).h:
 ={arg,ROH.m,SimHistory.h,FOContext.w,FOContext.g,FOContext.challenge_h,SimBad.corr} /\
 input{1}=x0 /\ SimHistory.h{1}=log0 /\ SimBad.corr{1}=b0 /\ view(glob S){2}=st0 /\
 FOContext.w{1}=w /\ FOContext.g{1}=g /\ FOContext.challenge_h{1}=None ==>
 ={res,ROH.m,SimHistory.h,FOContext.w,FOContext.g,FOContext.challenge_h,SimBad.corr} /\
 SimHistory.h{1}=log0.[x0<-res{1}] /\
 view(glob S){2}=ah_record_state st0 x0 res{1}].
proof.
 move=>hll hr.
 have hc : forall st x y, phoare[S.record:view(glob S)=st /\ input=x /\ hout=y ==>
  view(glob S)=ah_record_state st x y]=1%r.
 + move=>st x y;conseq hll (hr st x y);smt().
 proc*;inline{2} AHRecordH(S,AHFreshOracles).get;wp.
 ecall{2}(hc st0 x0 hout{2});call(ah_h_base w g x0 log0 b0);auto.
qed.

(* These forwarding layers call the same physical G oracle. *)
lemma ah_public_g_actual : equiv[AHPublicG(AHFreshOracles).get ~ FOGActual.get:
 ={arg,ROG.m} ==> ={res,ROG.m}].
proof.
 proc*;inline{1} AHPublicG(AHFreshOracles).get AHFreshOracles.g;wp.
 call(_: ={arg,ROG.m} ==> ={res,ROG.m});first by sim.
 auto.
qed.

module type AHLookupContext(G:FOGPort) = {
 proc run(xs:hist_table,pk:W8.t Array1152.t,suffix:W8.t Array32.t,
 cstar:W8.t Array1152.t option,ct:W8.t Array1152.t):cca_reply*int*int*int {G.get}
}.
lemma ah_lookup_context (C<:AHLookupContext {-ROG}) :
 equiv[C(AHPublicG(AHFreshOracles)).run ~ C(FOGActual).run:
 ={arg,glob C,ROG.m} ==> ={res,glob C,ROG.m}].
proof. proc(={ROG.m})=> //;exact ah_public_g_actual. qed.

lemma ah_lookup_public_g :
 equiv[HistLookup(AHPublicG(AHFreshOracles)).run ~ HistLookup(FOGActual).run:
 ={arg,ROG.m} ==> ={res,ROG.m}].
proof. conseq(ah_lookup_context HistLookup);smt(). qed.

lemma ah_h_coupling
 (S<:AHStore {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-FOContext,-SimPublic,-SimHistory,-SimBad})
 (view:(glob S)->ah_state) w g pk suffix star :
 islossless S.record =>
 (forall st x y,hoare[S.record:view(glob S)=st /\ input=x /\ hout=y ==>
 view(glob S)=ah_record_state st x y])=>
 equiv[AHFreshOracles.h ~ AHOracles(S,AHFreshOracles).h:
 ={arg,ROH.m,SimHistory.h,FOContext.w,FOContext.g,FOContext.challenge_h,SimBad.corr} /\
 FOContext.w{1}=w /\ FOContext.g{1}=g /\ FOContext.challenge_h{1}=None /\
 ah_view_rep(view(glob S){2}) pk suffix star SimHistory.h{1} /\
 ah_fresh_inv w g (FOContext.w{1},FOContext.g{1},FOContext.challenge_h{1},SimHistory.h{1},ROH.m{1}) SimBad.corr{1} ==>
 ={res,ROH.m,SimHistory.h,FOContext.w,FOContext.g,FOContext.challenge_h,SimBad.corr} /\
 FOContext.w{1}=w /\ FOContext.g{1}=g /\ FOContext.challenge_h{1}=None /\
 ah_view_rep(view(glob S){2}) pk suffix star SimHistory.h{1} /\
 ah_fresh_inv w g (FOContext.w{1},FOContext.g{1},FOContext.challenge_h{1},SimHistory.h{1},ROH.m{1}) SimBad.corr{1}].
proof.
 move=>hll hr.
 conseq(_: _ ==> ={res,ROH.m,SimHistory.h,FOContext.w,FOContext.g,FOContext.challenge_h,SimBad.corr} /\
 FOContext.w{1}=w /\ FOContext.g{1}=g /\ FOContext.challenge_h{1}=None /\
 ah_view_rep(view(glob S){2}) pk suffix star SimHistory.h{1})
 (ah_fresh_h_invariant w g) _=> //.
 proc*;exists* (view(glob S){2}),input{1},SimHistory.h{1},SimBad.corr{1}.
 elim*=>st0 x0 log0 b0.
 ecall(ah_h_record_coupling S view w g st0 x0 log0 b0 hll hr).
 clear hll hr;auto=> &1 &2 hpre;split.
 + smt().
 move=>hcall resultL resultR mL corrL hL sR mR corrR hR hpost.
 have hp:ah_view_rep st0 pk suffix star log0 by smt().
 have hn:=ah_view_record st0 pk suffix star log0 x0 resultL hp.
 smt().
qed.

lemma ah_lookup_prepared pk0 suffix0 star0 rows0 ct0 g gm0 :
 acwc2_cache_matches g gm0=>
 hoare[HistLookup(AHPublicG(AHFreshOracles)).run:
 xs=rows0 /\ pk=pk0 /\ suffix=suffix0 /\ cstar=star0 /\ ct=ct0 /\ ROG.m=gm0 ==>
 res.`1=hist_lookup_spec pk0 suffix0 star0 g rows0 ct0 /\ ROG.m=gm0].
proof.
 move=>hg;conseq ah_lookup_public_g (hist_lookup_prepared pk0 suffix0 star0 rows0 ct0 g gm0 hg);smt().
qed.
lemma ah_lookup_correct pk0 suffix0 star0 rows0 ct0 g gm0 :
 acwc2_cache_matches g gm0=>
 phoare[HistLookup(AHPublicG(AHFreshOracles)).run:
 xs=rows0 /\ pk=pk0 /\ suffix=suffix0 /\ cstar=star0 /\ ct=ct0 /\ ROG.m=gm0 ==>
 res.`1=hist_lookup_spec pk0 suffix0 star0 g rows0 ct0 /\ ROG.m=gm0]=1%r.
proof.
 move=>hg;conseq(hist_lookup_lossless (AHPublicG(AHFreshOracles)) (ah_public_g_ll AHFreshOracles sim_public_g_ll))
 (ah_lookup_prepared pk0 suffix0 star0 rows0 ct0 g gm0 hg);smt().
qed.

lemma ah_decap_coupling
 (S<:AHStore {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-FOContext,-SimPublic,-SimHistory,-SimBad})
 (view:(glob S)->ah_state) w g :
 pke_key_relation w=>
 islossless S.snapshot=>
 (forall st,hoare[S.snapshot:view(glob S)=st ==>res=st /\ view(glob S)=st])=>
 equiv[SimLookup(FOGActual).decap ~ AHDecap(S,AHFreshOracles).decap:
 ={arg,ROG.m} /\ SimPublic.pk{1}=w.`kg_pk /\
 SimPublic.suffix{1}=complete_sk_suffix w.`kg_sk /\
 ah_view_rep(view(glob S){2}) SimPublic.pk{1} SimPublic.suffix{1} SimPublic.cstar{1} SimHistory.h{1} /\
 fo_hcache_good w g None SimHistory.h{1} /\ acwc2_cache_matches g ROG.m{1} ==>
 ={res,ROG.m} /\ SimPublic.pk{1}=w.`kg_pk /\
 SimPublic.suffix{1}=complete_sk_suffix w.`kg_sk /\
 ah_view_rep(view(glob S){2}) SimPublic.pk{1} SimPublic.suffix{1} SimPublic.cstar{1} SimHistory.h{1} /\
 fo_hcache_good w g None SimHistory.h{1} /\ acwc2_cache_matches g ROG.m{1}].
proof.
 move=>hk hll hs.
 have hc : forall st, phoare[S.snapshot:view(glob S)=st ==>res=st /\ view(glob S)=st]=1%r.
 + move=>st;conseq hll (hs st);smt().
 proc*;exists* (view(glob S){2}),SimHistory.h{1},SimPublic.count{1},SimPublic.cstar{1},ct{1},ROG.m{1}.
 elim*=>st0 log0 count0 star0 ct0 gm0.
 have [hg|hg]:acwc2_cache_matches g gm0 \/ !acwc2_cache_matches g gm0 by smt().
 + inline{2} AHDecap(S,AHFreshOracles).decap;wp.
 ecall{1}(sim_lookup_correct w.`kg_pk (complete_sk_suffix w.`kg_sk) star0 log0 count0 ct0 g gm0 hg).
 ecall{2}(ah_lookup_correct w.`kg_pk (complete_sk_suffix w.`kg_sk) star0 st0.`ah_rows ct0 g gm0 hg).
 ecall{2}(hc st0).
 auto=> />;rewrite /ah_view_rep /ah_context;
 smt(hist_lookup_order_good).
 exfalso=> />;smt().
qed.

lemma ah_fresh_h_ll : islossless AHFreshOracles.h.
proof. proc;wp;call sim_public_h_ll;auto. qed.
lemma ah_fresh_raw_ll : islossless AHFreshOracles.raw.
proof. proc;wp;call sim_public_raw_ll;auto. qed.
lemma ah_fresh_h_latched : hoare[AHFreshOracles.h:SimBad.corr ==>SimBad.corr].
proof. proc;wp;call sim_public_h_latched;auto. qed.
lemma ah_fresh_raw_latched : hoare[AHFreshOracles.raw:SimBad.corr ==>SimBad.corr].
proof. proc;wp;call sim_public_raw_latched;auto. qed.
lemma ah_record_h_latched
 (S<:AHStore {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-FOContext,-SimPublic,-SimHistory,-SimBad}) :
 hoare[AHOracles(S,AHFreshOracles).h:SimBad.corr ==>SimBad.corr].
proof.
 proc;call(_:true ==>true);first by trivial.
 call ah_fresh_h_latched;auto.
qed.
