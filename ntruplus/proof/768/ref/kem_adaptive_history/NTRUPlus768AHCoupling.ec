require import AllCore List Distr FMap.
require import NTRUPlus768PKEModel NTRUPlus768SimPublicBound NTRUPlus768CCAOraclePorts.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152.
require import NTRUPlus768AHState NTRUPlus768AHAdapter NTRUPlus768AHFreshBound.
require import NTRUPlus768AHCallbacks NTRUPlus768AHRawCallbacks.
require import NTRUPlus768HistModel NTRUPlus768FOModel NTRUPlus768ACWC2Oracle.
require import NTRUPlus768SimModel NTRUPlus768SimLookup NTRUPlus768SimSampling NTRUPlus768SimPublicError NTRUPlus768SimPublicInstances.
require import NTRUPlus768ROMOracles NTRUPlus768RawXOFStreams NTRUPlus768FOGAdapters.
require import NTRUPlus768RawXOF NTRUPlus768FOEagerG.
require import NTRUPlus768CCAGame NTRUPlus768CCADecapOracle NTRUPlus768DecapCompleteSpec.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768FOQueryBudget NTRUPlus768CCAStatusAdapter.

lemma ah_adversary_coupling
 (S<:AHStore {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-FOContext,-SimPublic,-SimHistory,-SimBad})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-FOContext,-SimPublic,-SimHistory,-SimBad})
 (view:(glob S)->ah_state) w g :
 pke_key_relation w=>islossless S.snapshot=>islossless S.record=>
 (forall st,hoare[S.snapshot:view(glob S)=st ==>res=st /\ view(glob S)=st])=>
 (forall st x y,hoare[S.record:view(glob S)=st /\ input=x /\ hout=y ==>
 view(glob S)=ah_record_state st x y])=>
 (forall (H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
 islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
 islossless D.decap=>islossless A(H,D).guess)=>
 equiv[A(AHFreshOracles,SimLookup(FOGActual)).guess ~
 A(AHOracles(S,AHFreshOracles),AHDecap(S,AHFreshOracles)).guess:
 ={arg,glob A} /\ ={ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SimHistory.h,SimPublic.pk,SimPublic.suffix,SimPublic.cstar,FOContext.w,FOContext.g,FOContext.challenge_h,SimBad.corr} /\
 SimPublic.pk{1}=w.`kg_pk /\ SimPublic.suffix{1}=complete_sk_suffix w.`kg_sk /\
 FOContext.w{1}=w /\ FOContext.g{1}=g /\ FOContext.challenge_h{1}=None /\
 ah_view_rep(view(glob S){2}) SimPublic.pk{1} SimPublic.suffix{1} SimPublic.cstar{1} SimHistory.h{1} /\
 ah_fresh_inv w g (FOContext.w{1},FOContext.g{1},FOContext.challenge_h{1},SimHistory.h{1},ROH.m{1}) SimBad.corr{1} /\ acwc2_cache_matches g ROG.m{1} /\ !SimBad.corr{1} ==>
 ={SimBad.corr} /\ (!SimBad.corr{1}=> ={res,glob A} /\ ={ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SimHistory.h,SimPublic.pk,SimPublic.suffix,SimPublic.cstar,FOContext.w,FOContext.g,FOContext.challenge_h,SimBad.corr} /\
 SimPublic.pk{1}=w.`kg_pk /\ SimPublic.suffix{1}=complete_sk_suffix w.`kg_sk /\
 FOContext.w{1}=w /\ FOContext.g{1}=g /\ FOContext.challenge_h{1}=None /\
 ah_view_rep(view(glob S){2}) SimPublic.pk{1} SimPublic.suffix{1} SimPublic.cstar{1} SimHistory.h{1} /\
 ah_fresh_inv w g (FOContext.w{1},FOContext.g{1},FOContext.challenge_h{1},SimHistory.h{1},ROH.m{1}) SimBad.corr{1} /\ acwc2_cache_matches g ROG.m{1})].
proof.
 move=>hk sl rl hs hr all.
 have hl:=ah_fresh_h_ll.
 have rawl:=ah_fresh_raw_ll.
 have dh:=sim_lookup_lossless FOGActual rog_get_ll.
 have rhl:=ah_record_h_ll S AHFreshOracles hl rl.
 have rrl:=ah_oracles_raw_ll S AHFreshOracles hl rawl rl.
 have rd:=ah_decap_ll S AHFreshOracles sl sim_public_g_ll.
 have al:=all AHFreshOracles (SimLookup(FOGActual)) cca_e_ll cca_f_ll sim_public_g_ll hl rawl dh.
 have ar:=all (AHOracles(S,AHFreshOracles)) (AHDecap(S,AHFreshOracles)) cca_e_ll cca_f_ll sim_public_g_ll rhl rrl rd.
 proc*;call(_:SimBad.corr, ={ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SimHistory.h,SimPublic.pk,SimPublic.suffix,SimPublic.cstar,FOContext.w,FOContext.g,FOContext.challenge_h,SimBad.corr} /\
 SimPublic.pk{1}=w.`kg_pk /\ SimPublic.suffix{1}=complete_sk_suffix w.`kg_sk /\
 FOContext.w{1}=w /\ FOContext.g{1}=g /\ FOContext.challenge_h{1}=None /\
 ah_view_rep(view(glob S){2}) SimPublic.pk{1} SimPublic.suffix{1} SimPublic.cstar{1} SimHistory.h{1} /\
 ah_fresh_inv w g (FOContext.w{1},FOContext.g{1},FOContext.challenge_h{1},SimHistory.h{1},ROH.m{1}) SimBad.corr{1} /\ acwc2_cache_matches g ROG.m{1}, ={SimBad.corr}).
 + conseq(_: ={arg,ROE.m} ==> ={res,ROE.m})=> //;by sim.
 + move=> &2 h;clear hk all al ar;conseq cca_e_ll;smt().
 + move=> &1;clear hk all al ar;conseq cca_e_ll;smt().
 + conseq(_: ={arg,ROF.m} ==> ={res,ROF.m})=> //;by sim.
 + move=> &2 h;clear hk all al ar;conseq cca_f_ll;smt().
 + move=> &1;clear hk all al ar;conseq cca_f_ll;smt().
 + clear hk all al ar;conseq(ah_g_same g);smt().
 + move=> &2 h;clear hk all al ar;conseq sim_public_g_ll;smt().
 + move=> &1;clear hk all al ar;conseq sim_public_g_ll;smt().
 + clear hk all al ar;proc*;exists* SimPublic.cstar{1};elim*=>star.
   ecall(ah_h_coupling S view w g w.`kg_pk (complete_sk_suffix w.`kg_sk) star rl hr).
   auto=> />;smt().
 + move=> &2 h;clear hk all al ar;conseq hl ah_fresh_h_latched;smt().
 + move=> &1;clear hk all al ar;conseq rhl (ah_record_h_latched S);smt().
 + clear hk all al ar;proc*;exists* SimPublic.cstar{1};elim*=>star.
   ecall(ah_raw_coupling S view w g w.`kg_pk (complete_sk_suffix w.`kg_sk) star rl hr).
   auto=> />;smt().
 + move=> &2 h;clear hk all al ar;conseq rawl ah_fresh_raw_latched;smt().
 + move=> &1;clear hk all al ar;conseq rrl (ah_raw_latched S);smt().
 + clear all al ar;conseq(ah_decap_coupling S view w g hk sl hs);rewrite /ah_fresh_inv;smt().
 + move=> &2 h;clear hk all al ar;conseq dh;smt().
 + move=> &1;clear hk all al ar;conseq rd;smt().
 clear hk all al ar;auto=> />;smt().
qed.

lemma ah_phase_coupling
 (S<:AHStore {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-FOContext,-SimPublic,-SimHistory,-SimBad})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-FOContext,-SimPublic,-SimHistory,-SimBad})
 (view:(glob S)->ah_state) w g :
 pke_key_relation w=>islossless S.init=>islossless S.snapshot=>islossless S.record=>
 (forall pk suffix star,hoare[S.init:arg=(pk,suffix,star) ==>
 view(glob S)=ah_initial pk suffix star])=>
 (forall st,hoare[S.snapshot:view(glob S)=st ==>res=st /\ view(glob S)=st])=>
 (forall st x y,hoare[S.record:view(glob S)=st /\ input=x /\ hout=y ==>
 view(glob S)=ah_record_state st x y])=>
 (forall (H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
 islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
 islossless D.decap=>islossless A(H,D).guess)=>
 equiv[AHFreshPhase(A).run ~ AHFreshPhase(AHWrapper(S,A)).run:
 ={pk,ct,key,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams} /\
 w0{1}=w /\ g0{1}=g /\ w0{2}=w /\ g0{2}=g /\ pk{1}=w.`kg_pk /\
 ROF.m{1}.[w.`kg_pk]=Some(complete_sk_suffix w.`kg_sk) /\
 ROH.m{1}=empty /\ acwc2_cache_matches g ROG.m{1} ==>
 ={SimBad.corr} /\ (!SimBad.corr{1}=>
 ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SimHistory.h,SimPublic.pk,SimPublic.suffix,SimPublic.cstar})].
proof.
 move=>hk il sl rl hi hs hr all.
 have hic : forall pk suffix star, phoare[S.init:arg=(pk,suffix,star) ==>
  view(glob S)=ah_initial pk suffix star]=1%r.
 + move=>pk suffix star;conseq il (hi pk suffix star);smt().
 have fcache : forall fm x y,
  phoare[ROF.get:ROF.m=fm /\ input=x /\ fm.[x]=Some y ==>res=y /\ ROF.m=fm]=1%r.
 + move=>fm x y;conseq rof_get_ll (rof_get_cached fm x y);smt().
 proc;inline{2} AHWrapper(S,A,AHFreshOracles,SimLookup(FOGActual)).guess.
 wp.
 call(ah_adversary_coupling S A view w g hk sl rl hs hr all).
 ecall{2}(hic pk{2} suffix0{2} (Some ct{2})).
 inline{2} AHFreshOracles.f;wp.
 ecall{2}(fcache ROF.m{2} pk{2} (complete_sk_suffix w.`kg_sk)).
 inline SimPublic.init SimHistory.init;wp.
 ecall{1}(fcache ROF.m{1} pk{1} (complete_sk_suffix w.`kg_sk)).
 ecall{2}(fcache ROF.m{2} pk{2} (complete_sk_suffix w.`kg_sk)).
 auto=> />;rewrite /ah_fresh_inv /sim_public_inv /sim_log_included /sim_h_cover /fo_hcache_good;
 smt(ah_view_initial mem_empty emptyE).
qed.
