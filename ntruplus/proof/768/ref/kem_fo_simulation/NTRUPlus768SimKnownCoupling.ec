require import AllCore Distr FMap StdOrder.
from Jasmin require import JWord.
require import Array32 Array192 Array224 Array1152 Array2336.
require import NTRUPlus768ROMOracles NTRUPlus768RawXOFStreams NTRUPlus768RawXOF NTRUPlus768CCAGame.
require import NTRUPlus768CCAStatusAdapter NTRUPlus768CCADecapOracle NTRUPlus768CCAOraclePorts.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768PKEModel NTRUPlus768EncapGuardSpec.
require import NTRUPlus768PKEAlgebra.
require import NTRUPlus768FOModel NTRUPlus768FOChallenge NTRUPlus768FOEagerG NTRUPlus768FOGAdapters NTRUPlus768FONativeBridge.
require import NTRUPlus768ACWC2Oracle NTRUPlus768RRecModel NTRUPlus768RRecNativeComparison NTRUPlus768DecapCompleteSpec.
require import NTRUPlus768SimModel NTRUPlus768SimSampling NTRUPlus768SimOracles NTRUPlus768SimPrefix.
require import NTRUPlus768SimKnown NTRUPlus768SimKnownAlgebra NTRUPlus768SimLookup NTRUPlus768SimGErasure.
require import NTRUPlus768SimPublicError NTRUPlus768SimPublicBound.
import RealOrder.

lemma sim_known_answer_exact w ct0 g log0 hm0 gm0 :
 pke_key_relation w=>
 sim_matching_good w g log0 ct0=>sim_log_included log0 hm0=>
 phoare[SimKnownAnswer(FOGActual,SimHActual).answer:
 complete_entry_accepts ct0 w.`kg_sk /\ q=sim_request_of w ct0 (oget gm0.[rrec_native_bytes w ct0]) /\
 ROG.m=gm0 /\ ROH.m=hm0 /\ SimHistory.h=log0 /\ acwc2_cache_matches g gm0 ==>
 res=sim_lookup_result w.`kg_pk (complete_sk_suffix w.`kg_sk) g log0 ct0 /\
 ROG.m=gm0 /\ ROH.m=hm0 /\ SimHistory.h=log0 /\ acwc2_cache_matches g gm0]=1%r.
proof.
 move=>hk hm hi;case(complete_entry_accepts ct0 w.`kg_sk)=>ha;last by exfalso=> />.
 case(acwc2_cache_matches g gm0)=>hg;last by exfalso=> />.
 have hp:encap_key_canonical(sim_request_of w ct0 (oget gm0.[rrec_native_bytes w ct0])).`sr_pk.
 + rewrite /sim_request_of /=;exact(pke_key_canonical w hk).
 have hv:sim_known_answer_value g log0(sim_request_of w ct0 (oget gm0.[rrec_native_bytes w ct0]))=
  sim_lookup_result w.`kg_pk (complete_sk_suffix w.`kg_sk) g log0 ct0.
 + rewrite(sim_known_request_value w g log0 ct0 (oget gm0.[rrec_native_bytes w ct0]) ha).
   exact(sim_known_lookup_result w g log0 ct0 (oget gm0.[rrec_native_bytes w ct0]) hk hm
     (fo_cache_pad_consistent g gm0 _ hg)).
 conseq(sim_known_answer_ll FOGActual SimHActual rog_get_ll roh_get_ll)
  (sim_known_answer_functional (sim_request_of w ct0 (oget gm0.[rrec_native_bytes w ct0])) g gm0 hm0 log0 hp hg hi);smt().
qed.

lemma sim_lookup_exact_pre pk0 suffix0 star0 log0 n0 ct0 g gm0 :
 phoare[SimLookup(FOGActual).decap:
 ct=ct0 /\ SimPublic.pk=pk0 /\ SimPublic.suffix=suffix0 /\
 SimPublic.cstar=star0 /\ SimPublic.count=n0 /\ SimHistory.h=log0 /\
 ROG.m=gm0 /\ acwc2_cache_matches g gm0 ==>
 res=sim_lookup_spec pk0 suffix0 star0 g log0 ct0 /\ ROG.m=gm0 /\
 SimPublic.pk=pk0 /\ SimPublic.suffix=suffix0 /\ SimPublic.cstar=star0 /\
 SimPublic.count=n0+1 /\ SimHistory.h=log0 /\ acwc2_cache_matches g gm0]=1%r.
proof.
 case(acwc2_cache_matches g gm0)=>hg;last by exfalso=> />.
 conseq(sim_lookup_correct pk0 suffix0 star0 log0 n0 ct0 g gm0 hg);smt().
qed.

lemma sim_prefix_same_value w ct0 g :
 equiv[SimPrefix(FOGActual).run ~ SimPrefix(FOGActual).run:
 ={arg,ROG.m} /\ pk{1}=w.`kg_pk /\ ct{1}=ct0 /\ sk{1}=w.`kg_sk /\
 acwc2_cache_matches g ROG.m{1} ==>
 ={res,ROG.m} /\ acwc2_cache_matches g ROG.m{1} /\
 res{1}=(if complete_entry_accepts ct0 w.`kg_sk then
 Some(sim_request_of w ct0(oget ROG.m{1}.[rrec_native_bytes w ct0])) else None)].
proof.
 conseq(_: ={arg,ROG.m} ==> ={res,ROG.m})(sim_prefix_value w ct0 g) _=> //.
 by sim.
qed.

lemma sim_known_ghost_fixed w ct0 g log0 hm0 star0 n0 : pke_key_relation w=>
 equiv[SimKnownDecap(FOGActual,SimHActual).decap ~ SimGhostLookup(FOGActual).decap:
 ={ct,ROG.m,ROH.m,SimHistory.h,glob SimPublic,CCADecapOracle.sk} /\
 ct{1}=ct0 /\ SimPublic.pk{1}=w.`kg_pk /\ SimPublic.suffix{1}=complete_sk_suffix w.`kg_sk /\
 CCADecapOracle.sk{1}=w.`kg_sk /\ SimPublic.cstar{1}=star0 /\ SimPublic.count{1}=n0 /\
 SimHistory.h{1}=log0 /\ ROH.m{1}=hm0 /\ acwc2_cache_matches g ROG.m{1} /\
 sim_log_included log0 hm0 /\ (star0<>Some ct0=>sim_matching_good w g log0 ct0) ==>
 ={res,ROG.m,ROH.m,SimHistory.h,glob SimPublic,CCADecapOracle.sk} /\
 acwc2_cache_matches g ROG.m{1} /\ ROH.m{1}=hm0 /\ SimHistory.h{1}=log0 /\
 SimPublic.pk{1}=w.`kg_pk /\ SimPublic.suffix{1}=complete_sk_suffix w.`kg_sk /\
 CCADecapOracle.sk{1}=w.`kg_sk /\ SimPublic.cstar{1}=star0 /\ SimPublic.count{1}=n0+1].
proof.
 move=>hk;case(sim_log_included log0 hm0)=>hi;last by exfalso=> />.
 case(star0<>Some ct0=>sim_matching_good w g log0 ct0)=>hg;last by exfalso=> />.
 case(star0=Some ct0)=>hc;proc.
 + rcondf{1} 3;first by auto=> />;smt().
   rcondf{2} 1;first by auto=> />;smt().
   ecall{2}(sim_lookup_exact_pre w.`kg_pk (complete_sk_suffix w.`kg_sk) star0 log0 n0 ct0 g ROG.m{2}).
   auto=> />;rewrite /sim_lookup_spec hc;smt().
 rcondt{1} 3;first by auto=> />;smt().
 rcondt{2} 1;first by auto=> />;smt().
 inline{1} SimCore(FOGActual,SimKnownAnswer(FOGActual,SimHActual)).run.
 sp 5 0.
 seq 1 1:(={ROG.m,ROH.m,SimHistory.h,CCADecapOracle.sk} /\
  request{1}=request{2} /\ acwc2_cache_matches g ROG.m{1} /\
  request{1}=(if complete_entry_accepts ct0 w.`kg_sk then
   Some(sim_request_of w ct0(oget ROG.m{1}.[rrec_native_bytes w ct0])) else None) /\
  ct{1}=ct0 /\ ct{2}=ct0 /\ ROH.m{1}=hm0 /\ SimHistory.h{1}=log0 /\
  SimPublic.pk{1}=w.`kg_pk /\ SimPublic.pk{2}=w.`kg_pk /\
  SimPublic.suffix{1}=complete_sk_suffix w.`kg_sk /\ SimPublic.suffix{2}=complete_sk_suffix w.`kg_sk /\
  SimPublic.cstar{1}=star0 /\ SimPublic.cstar{2}=star0 /\
  SimPublic.count{1}=n0+1 /\ SimPublic.count{2}=n0 /\ CCADecapOracle.sk{1}=w.`kg_sk).
 + call(sim_prefix_same_value w ct0 g);auto=> />;smt().
 sp 1 0;if{1}.
 + wp;ecall{1}(sim_known_answer_exact w ct0 g log0 hm0 ROG.m{1} hk (hg hc) hi).
   ecall{2}(sim_lookup_exact_pre w.`kg_pk (complete_sk_suffix w.`kg_sk) star0 log0 n0 ct0 g ROG.m{2}).
   auto=> />;rewrite /sim_lookup_spec hc;smt().
 ecall{2}(sim_lookup_exact_pre w.`kg_pk (complete_sk_suffix w.`kg_sk) star0 log0 n0 ct0 g ROG.m{2}).
 auto=> />;rewrite /sim_lookup_spec hc;smt(sim_lookup_invalid).
qed.

require import NTRUPlus768SimPublicInstances NTRUPlus768SimAnswerErasure.

op [opaque] sim_known_invariant w g ex hs cs gm hm log b =
 acwc2_cache_matches g gm /\ sim_log_included log hm /\ sim_h_cover log hm ex /\
 fo_challenge_invariant w g ex hs cs hm /\ (!b=>fo_hcache_good w g ex log).

lemma sim_known_ghost_step w g ex hs cs ct0 : pke_key_relation w=>
 equiv[SimKnownDecap(FOGActual,SimHActual).decap ~ SimGhostLookup(FOGActual).decap:
 ={ct,ROG.m,ROH.m,SimHistory.h,glob SimPublic,CCADecapOracle.sk,SimBad.corr} /\
 ct{1}=ct0 /\ SimPublic.pk{1}=w.`kg_pk /\ SimPublic.suffix{1}=complete_sk_suffix w.`kg_sk /\
 CCADecapOracle.sk{1}=w.`kg_sk /\ SimPublic.cstar{1}=Some cs /\ !SimBad.corr{1} /\
 sim_known_invariant w g ex hs cs ROG.m{1} ROH.m{1} SimHistory.h{1} SimBad.corr{1} ==>
 ={res,ROG.m,ROH.m,SimHistory.h,glob SimPublic,CCADecapOracle.sk,SimBad.corr} /\
 SimPublic.pk{1}=w.`kg_pk /\ SimPublic.suffix{1}=complete_sk_suffix w.`kg_sk /\
 CCADecapOracle.sk{1}=w.`kg_sk /\ SimPublic.cstar{1}=Some cs /\ !SimBad.corr{1} /\
 sim_known_invariant w g ex hs cs ROG.m{1} ROH.m{1} SimHistory.h{1} SimBad.corr{1}].
proof.
 move=>hk;proc*;ecall(sim_known_ghost_fixed w ct0 g SimHistory.h{1} ROH.m{1} (Some cs) SimPublic.count{1} hk).
 clear hk;auto=> />;rewrite /sim_known_invariant;smt(sim_matching_challenge_good).
qed.

lemma sim_known_g_preserves w g ex hs cs : hoare[SimOracles(SimGActual,SimPublicErrorH(SimHActual)).g:
 sim_known_invariant w g ex hs cs ROG.m ROH.m SimHistory.h SimBad.corr ==>
 sim_known_invariant w g ex hs cs ROG.m ROH.m SimHistory.h SimBad.corr].
proof.
 proc;ecall(rog_get_value ROG.m input);auto=> />;rewrite /sim_known_invariant;smt(fo_cache_extension).
qed.
lemma sim_known_h_challenge w g ex hs cs : hoare[SimOracles(SimGActual,SimPublicErrorH(SimHActual)).h:
 fo_challenge_invariant w g ex hs cs ROH.m ==>fo_challenge_invariant w g ex hs cs ROH.m].
proof.
 proc;inline SimHistory.record SimPublicErrorH(SimHActual).get.
 wp;ecall(roh_get_value ROH.m input);auto=> />;smt(fo_challenge_cache_extends).
qed.
lemma sim_known_h_preserves w g ex hs cs : hoare[SimOracles(SimGActual,SimPublicErrorH(SimHActual)).h:
 FOContext.w=w /\ FOContext.g=g /\ FOContext.challenge_h=ex /\
 sim_known_invariant w g ex hs cs ROG.m ROH.m SimHistory.h SimBad.corr ==>
 FOContext.w=w /\ FOContext.g=g /\ FOContext.challenge_h=ex /\
 sim_known_invariant w g ex hs cs ROG.m ROH.m SimHistory.h SimBad.corr].
proof.
 conseq [-frame](sim_public_logged_good w g ex)
  (_:sim_public_inv w g ex(FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\
    fo_challenge_invariant w g ex hs cs ROH.m /\ acwc2_cache_matches g ROG.m ==>
    sim_public_inv w g ex(FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\
    fo_challenge_invariant w g ex hs cs ROH.m /\ acwc2_cache_matches g ROG.m);
  1,2:by rewrite /sim_known_invariant /sim_public_inv;progress.
 conseq(sim_public_h_state w g ex)(sim_known_h_challenge w g ex hs cs);smt().
qed.
lemma sim_known_raw_g_preserves w g ex hs cs : hoare[FOGRawStreams(SimGActual).g:
 sim_known_invariant w g ex hs cs ROG.m ROH.m SimHistory.h SimBad.corr ==>
 sim_known_invariant w g ex hs cs ROG.m ROH.m SimHistory.h SimBad.corr].
proof.
 proc;seq 1:(sim_known_invariant w g ex hs cs ROG.m ROH.m SimHistory.h SimBad.corr).
 + ecall(rog_get_value ROG.m input);auto=> />;rewrite /sim_known_invariant;smt(fo_cache_extension).
 if;auto.
qed.
lemma sim_known_raw_full_preserves w g ex hs cs : hoare[SimRaw(SimGActual,SimPublicErrorH(SimHActual)).full:
 FOContext.w=w /\ FOContext.g=g /\ FOContext.challenge_h=ex /\
 sim_known_invariant w g ex hs cs ROG.m ROH.m SimHistory.h SimBad.corr ==>
 FOContext.w=w /\ FOContext.g=g /\ FOContext.challenge_h=ex /\
 sim_known_invariant w g ex hs cs ROG.m ROH.m SimHistory.h SimBad.corr].
proof.
 proc;match.
 + call(_:true ==>true);first by trivial. auto.
 match.
 + call(_:true ==>true);first by trivial. auto.
 + call(_:true ==>true);first by trivial. auto.
 + call(sim_known_raw_g_preserves w g ex hs cs);auto.
 call(sim_known_h_preserves w g ex hs cs);auto.
qed.
lemma sim_known_raw_preserves w g ex hs cs : hoare[SimRaw(SimGActual,SimPublicErrorH(SimHActual)).get:
 FOContext.w=w /\ FOContext.g=g /\ FOContext.challenge_h=ex /\
 sim_known_invariant w g ex hs cs ROG.m ROH.m SimHistory.h SimBad.corr ==>
 FOContext.w=w /\ FOContext.g=g /\ FOContext.challenge_h=ex /\
 sim_known_invariant w g ex hs cs ROG.m ROH.m SimHistory.h SimBad.corr].
proof. proc;sp 1;if;last by auto. wp;call(sim_known_raw_full_preserves w g ex hs cs);auto. qed.

lemma sim_known_g_same w g ex hs cs :
 equiv[SimOracles(SimGActual,SimPublicErrorH(SimHActual)).g ~ SimOracles(SimGActual,SimPublicErrorH(SimHActual)).g:
 ={arg,ROG.m} /\ sim_known_invariant w g ex hs cs ROG.m{1} ROH.m{1} SimHistory.h{1} SimBad.corr{1} ==>
 ={res,ROG.m} /\ sim_known_invariant w g ex hs cs ROG.m{1} ROH.m{1} SimHistory.h{1} SimBad.corr{1}].
proof.
 conseq(_: ={arg,ROG.m} ==> ={res,ROG.m})(sim_known_g_preserves w g ex hs cs) _=> //;by sim.
qed.
lemma sim_known_h_same w g ex hs cs :
 equiv[SimOracles(SimGActual,SimPublicErrorH(SimHActual)).h ~ SimOracles(SimGActual,SimPublicErrorH(SimHActual)).h:
 ={arg,ROH.m,SimHistory.h,glob FOContext,SimBad.corr} /\
 FOContext.w{1}=w /\ FOContext.g{1}=g /\ FOContext.challenge_h{1}=ex /\
 sim_known_invariant w g ex hs cs ROG.m{1} ROH.m{1} SimHistory.h{1} SimBad.corr{1} ==>
 ={res,ROH.m,SimHistory.h,glob FOContext,SimBad.corr} /\
 FOContext.w{1}=w /\ FOContext.g{1}=g /\ FOContext.challenge_h{1}=ex /\
 sim_known_invariant w g ex hs cs ROG.m{1} ROH.m{1} SimHistory.h{1} SimBad.corr{1}].
proof.
 conseq(_: ={arg,ROH.m,SimHistory.h,glob FOContext,SimBad.corr} ==>
 ={res,ROH.m,SimHistory.h,glob FOContext,SimBad.corr})(sim_known_h_preserves w g ex hs cs) _=> //;by sim.
qed.
lemma sim_known_raw_same w g ex hs cs :
 equiv[SimOracles(SimGActual,SimPublicErrorH(SimHActual)).raw ~ SimOracles(SimGActual,SimPublicErrorH(SimHActual)).raw:
 ={arg,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,SimHistory.h,glob FOContext,SimBad.corr} /\
 FOContext.w{1}=w /\ FOContext.g{1}=g /\ FOContext.challenge_h{1}=ex /\
 sim_known_invariant w g ex hs cs ROG.m{1} ROH.m{1} SimHistory.h{1} SimBad.corr{1} ==>
 ={res,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,SimHistory.h,glob FOContext,SimBad.corr} /\
 FOContext.w{1}=w /\ FOContext.g{1}=g /\ FOContext.challenge_h{1}=ex /\
 sim_known_invariant w g ex hs cs ROG.m{1} ROH.m{1} SimHistory.h{1} SimBad.corr{1}].
proof.
 conseq(_: ={arg,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,SimHistory.h,glob FOContext,SimBad.corr} ==>
 ={res,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,SimHistory.h,glob FOContext,SimBad.corr})
 (sim_known_raw_preserves w g ex hs cs) _=> //;by sim.
qed.

module SimCouplingOracles=SimOracles(SimGActual,SimPublicErrorH(SimHActual)).

(* The continuation may be adaptive. Robust losslessness is required for
   both continuations after the first public-correction failure. *)
lemma sim_known_ghost_adversary_upto
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOContext,-SimPublic,-SimHistory,-SimBad,-SimPublicBudget,-SimGRO.RO,-SimGRO.FRO}) w g ex hs cs :
 pke_key_relation w=>
 (forall (H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
 islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
 islossless D.decap=>islossless A(H,D).guess)=>
 equiv[A(SimCouplingOracles,SimKnownDecap(FOGActual,SimHActual)).guess ~
       A(SimCouplingOracles,SimGhostLookup(FOGActual)).guess:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,glob SimPublic,SimHistory.h,glob FOContext,SimBad.corr} /\ SimPublic.pk{1}=w.`kg_pk /\ SimPublic.suffix{1}=complete_sk_suffix w.`kg_sk /\ CCADecapOracle.sk{1}=w.`kg_sk /\ SimPublic.cstar{1}=Some cs /\ FOContext.w{1}=w /\ FOContext.g{1}=g /\ FOContext.challenge_h{1}=ex /\ sim_known_invariant w g ex hs cs ROG.m{1} ROH.m{1} SimHistory.h{1} SimBad.corr{1} /\ !SimBad.corr{1} ==>
 ={SimBad.corr} /\ (!SimBad.corr{2}=> ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,glob SimPublic,SimHistory.h,glob FOContext,SimBad.corr} /\ SimPublic.pk{1}=w.`kg_pk /\ SimPublic.suffix{1}=complete_sk_suffix w.`kg_sk /\ CCADecapOracle.sk{1}=w.`kg_sk /\ SimPublic.cstar{1}=Some cs /\ FOContext.w{1}=w /\ FOContext.g{1}=g /\ FOContext.challenge_h{1}=ex /\ sim_known_invariant w g ex hs cs ROG.m{1} ROH.m{1} SimHistory.h{1} SimBad.corr{1})].
proof.
 move=>hk all.
 have gl:islossless SimCouplingOracles.g by proc;call rog_get_ll;auto.
 have hl:=sim_logged_h_ll (SimPublicErrorH(SimHActual)) (sim_public_error_ll SimHActual roh_get_ll).
 have rl:=sim_raw_get_ll FOGActual (SimPublicErrorH(SimHActual)) rog_get_ll (sim_public_error_ll SimHActual roh_get_ll).
 have kl:=sim_known_decap_ll FOGActual SimHActual rog_get_ll roh_get_ll.
 have dl:=sim_ghost_lookup_ll FOGActual rog_get_ll.
 have al:=all SimCouplingOracles (SimKnownDecap(FOGActual,SimHActual)) cca_e_ll cca_f_ll gl hl rl kl.
 have ar:=all SimCouplingOracles (SimGhostLookup(FOGActual)) cca_e_ll cca_f_ll gl hl rl dl.
 proc*;call(_:SimBad.corr, ={ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,glob SimPublic,SimHistory.h,glob FOContext,SimBad.corr} /\ SimPublic.pk{1}=w.`kg_pk /\ SimPublic.suffix{1}=complete_sk_suffix w.`kg_sk /\ CCADecapOracle.sk{1}=w.`kg_sk /\ SimPublic.cstar{1}=Some cs /\ FOContext.w{1}=w /\ FOContext.g{1}=g /\ FOContext.challenge_h{1}=ex /\ sim_known_invariant w g ex hs cs ROG.m{1} ROH.m{1} SimHistory.h{1} SimBad.corr{1}, ={SimBad.corr}).
 + conseq(_: ={arg,ROE.m} ==> ={res,ROE.m})=> //;by sim.
 + move=> &2 h;clear hk all al ar;conseq cca_e_ll;smt().
 + move=> &1;clear hk all al ar;conseq cca_e_ll;smt().
 + conseq(_: ={arg,ROF.m} ==> ={res,ROF.m})=> //;by sim.
 + move=> &2 h;clear hk all al ar;conseq cca_f_ll;smt().
 + move=> &1;clear hk all al ar;conseq cca_f_ll;smt().
 + clear hk all al ar;conseq(sim_known_g_same w g ex hs cs);smt().
 + move=> &2 h;clear hk all al ar;conseq gl;smt().
 + move=> &1;clear hk all al ar;conseq gl;smt().
 + clear hk all al ar;conseq(sim_known_h_same w g ex hs cs);smt().
 + move=> &2 h;clear hk all al ar;conseq hl sim_public_h_latched;smt().
 + move=> &1;clear hk all al ar;conseq hl sim_public_h_latched;smt().
 + clear hk all al ar;conseq(sim_known_raw_same w g ex hs cs);smt().
 + move=> &2 h;clear hk all al ar;conseq rl sim_public_raw_latched;smt().
 + move=> &1;clear hk all al ar;conseq rl sim_public_raw_latched;smt().
 + proc*;ecall(sim_known_ghost_step w g ex hs cs ct{1} hk).
   clear hk all al ar;auto=> />;smt().
 + move=> &2 h;clear hk all al ar;conseq kl;smt().
 + move=> &1;clear hk all al ar;conseq dl;smt().
 clear hk all al ar;auto=> />;smt().
qed.

lemma sim_known_monitor_projection
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOContext,-SimPublic,-SimHistory,-SimBad,-SimPublicBudget,-SimGRO.RO,-SimGRO.FRO}) :
 equiv[A(SimCouplingOracles,SimKnownDecap(FOGActual,SimHActual)).guess ~ A(SimOracles(FOGActual,SimHActual),SimKnownDecap(FOGActual,SimHActual)).guess:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,glob SimPublic,SimHistory.h,glob FOContext} ==> ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,glob SimPublic,SimHistory.h,glob FOContext}].
proof.
 proc(={ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,glob SimPublic,SimHistory.h,glob FOContext})=> //.
 + by sim.
 + by sim.
 + by sim.
 + conseq sim_public_logged_error_projection;smt().
 + conseq sim_public_raw_error_projection;smt().
 by sim.
qed.

lemma sim_ghost_monitor_projection
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOContext,-SimPublic,-SimHistory,-SimBad,-SimPublicBudget,-SimGRO.RO,-SimGRO.FRO}) :
 equiv[A(SimCouplingOracles,SimGhostLookup(FOGActual)).guess ~ A(SimOracles(FOGActual,SimHActual),SimGhostLookup(FOGActual)).guess:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,glob SimPublic,SimHistory.h,glob FOContext} ==> ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,glob SimPublic,SimHistory.h,glob FOContext}].
proof.
 proc(={ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,glob SimPublic,SimHistory.h,glob FOContext})=> //.
 + by sim.
 + by sim.
 + by sim.
 + conseq sim_public_logged_error_projection;smt().
 + conseq sim_public_raw_error_projection;smt().
 by sim.
qed.

lemma sim_known_ghost_distance_bad
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOContext,-SimPublic,-SimHistory,-SimBad,-SimPublicBudget,-SimGRO.RO,-SimGRO.FRO}) w g ex hs cs pk0 ct0 key0 &m (event:bool->bool) :
 pke_key_relation w=>(SimPublic.pk{m}=w.`kg_pk /\ SimPublic.suffix{m}=complete_sk_suffix w.`kg_sk /\
 CCADecapOracle.sk{m}=w.`kg_sk /\ SimPublic.cstar{m}=Some cs /\
 FOContext.w{m}=w /\ FOContext.g{m}=g /\ FOContext.challenge_h{m}=ex /\
 sim_known_invariant w g ex hs cs ROG.m{m} ROH.m{m} SimHistory.h{m} SimBad.corr{m} /\ !SimBad.corr{m})=>(forall (H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
 islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
 islossless D.decap=>islossless A(H,D).guess)=>
 `|Pr[A(SimCouplingOracles,SimKnownDecap(FOGActual,SimHActual)).guess(pk0,ct0,key0) @ &m:event res]-Pr[A(SimCouplingOracles,SimGhostLookup(FOGActual)).guess(pk0,ct0,key0) @ &m:event res]|<=
 Pr[A(SimCouplingOracles,SimKnownDecap(FOGActual,SimHActual)).guess(pk0,ct0,key0) @ &m:SimBad.corr].
proof.
 move=>hk hi all.
 have eqv:=sim_known_ghost_adversary_upto A w g ex hs cs hk all.
 have good:Pr[A(SimCouplingOracles,SimKnownDecap(FOGActual,SimHActual)).guess(pk0,ct0,key0) @ &m:event res /\ !SimBad.corr]=
  Pr[A(SimCouplingOracles,SimGhostLookup(FOGActual)).guess(pk0,ct0,key0) @ &m:event res /\ !SimBad.corr].
 + byequiv eqv=> //;clear hk all;smt().
 have bad:Pr[A(SimCouplingOracles,SimKnownDecap(FOGActual,SimHActual)).guess(pk0,ct0,key0) @ &m:SimBad.corr]=
  Pr[A(SimCouplingOracles,SimGhostLookup(FOGActual)).guess(pk0,ct0,key0) @ &m:SimBad.corr].
 + byequiv eqv=> //;clear hk all;smt().
 have hn:Pr[A(SimCouplingOracles,SimKnownDecap(FOGActual,SimHActual)).guess(pk0,ct0,key0) @ &m:event res /\ SimBad.corr]<=
  Pr[A(SimCouplingOracles,SimKnownDecap(FOGActual,SimHActual)).guess(pk0,ct0,key0) @ &m:SimBad.corr] by rewrite Pr[mu_sub].
 have hd:Pr[A(SimCouplingOracles,SimGhostLookup(FOGActual)).guess(pk0,ct0,key0) @ &m:event res /\ SimBad.corr]<=
  Pr[A(SimCouplingOracles,SimGhostLookup(FOGActual)).guess(pk0,ct0,key0) @ &m:SimBad.corr] by rewrite Pr[mu_sub].
 rewrite Pr[mu_split SimBad.corr].
 have ->:Pr[A(SimCouplingOracles,SimGhostLookup(FOGActual)).guess(pk0,ct0,key0) @ &m:event res]=
  Pr[A(SimCouplingOracles,SimGhostLookup(FOGActual)).guess(pk0,ct0,key0) @ &m:event res /\ SimBad.corr]+
  Pr[A(SimCouplingOracles,SimGhostLookup(FOGActual)).guess(pk0,ct0,key0) @ &m:event res /\ !SimBad.corr]
  by rewrite Pr[mu_split SimBad.corr].
 clear hk hi all eqv;smt(mu_bounded).
qed.

require import NTRUPlus768SimPublicCapRemoval NTRUPlus768FOQueryBudget NTRUPlus768FOError.


lemma sim_known_backend_projection
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOContext,-SimPublic,-SimHistory,-SimBad,-SimPublicBudget,-SimGRO.RO,-SimGRO.FRO}) :
 equiv[A(SimCouplingOracles,SimKnownDecap(FOGActual,SimHActual)).guess ~
 A(FOHashView(SimKnownPublicBackend),FODecapView(SimKnownPublicBackend)).guess:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,glob SimPublic,SimHistory.h,glob FOContext,SimBad.corr} ==> ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,glob SimPublic,SimHistory.h,glob FOContext,SimBad.corr}].
proof. proc(={ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,glob SimPublic,SimHistory.h,glob FOContext,SimBad.corr})=> //;sim. qed.

lemma sim_known_ghost_distance
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOContext,-SimPublic,-SimHistory,-SimBad,-SimPublicBudget,-SimGRO.RO,-SimGRO.FRO}) w g ex hs cs qH pk0 ct0 key0 &m (event:bool->bool) :
 pke_key_relation w=>(SimPublic.pk{m}=w.`kg_pk /\ SimPublic.suffix{m}=complete_sk_suffix w.`kg_sk /\
 CCADecapOracle.sk{m}=w.`kg_sk /\ SimPublic.cstar{m}=Some cs /\
 FOContext.w{m}=w /\ FOContext.g{m}=g /\ FOContext.challenge_h{m}=ex /\
 sim_known_invariant w g ex hs cs ROG.m{m} ROH.m{m} SimHistory.h{m} SimBad.corr{m} /\ !SimBad.corr{m})=>0<=qH=>(forall (H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
 islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
 islossless D.decap=>islossless A(H,D).guess)=>
 hoare[SimPublicCountedA(A,FOHashView(SimKnownPublicBackend),FODecapView(SimKnownPublicBackend)).guess:
 sim_public_budget_initial qH SimPublicBudget.nh SimPublicBudget.limit SimPublicBudget.overflow ==>
 SimPublicBudget.nh<=qH]=>
 `|Pr[A(SimOracles(FOGActual,SimHActual),SimKnownDecap(FOGActual,SimHActual)).guess(pk0,ct0,key0) @ &m:event res]-Pr[A(SimOracles(FOGActual,SimHActual),SimGhostLookup(FOGActual)).guess(pk0,ct0,key0) @ &m:event res]|<=qH%r*fo_error w g.
proof.
 move=>hk hi hq all bounded.
 have hpub:sim_public_inv w g ex(FOContext.w{m},FOContext.g{m},FOContext.challenge_h{m},SimHistory.h{m},ROH.m{m}).
 + move:hi;rewrite /sim_known_invariant /sim_public_inv;smt().
 have hnb:!SimBad.corr{m} by smt().
 have hb:Pr[A(SimCouplingOracles,SimKnownDecap(FOGActual,SimHActual)).guess(pk0,ct0,key0) @ &m:SimBad.corr]<=qH%r*fo_error w g.
 + have ->:Pr[A(SimCouplingOracles,SimKnownDecap(FOGActual,SimHActual)).guess(pk0,ct0,key0) @ &m:SimBad.corr]=
     Pr[A(FOHashView(SimKnownPublicBackend),FODecapView(SimKnownPublicBackend)).guess(pk0,ct0,key0) @ &m:SimBad.corr]
     by byequiv(sim_known_backend_projection A)=> //.
   exact(sim_public_known_uncapped_corr A w g ex qH pk0 ct0 key0 &m hq hpub hnb all bounded).
 have hp:Pr[A(SimCouplingOracles,SimKnownDecap(FOGActual,SimHActual)).guess(pk0,ct0,key0) @ &m:event res]=Pr[A(SimOracles(FOGActual,SimHActual),SimKnownDecap(FOGActual,SimHActual)).guess(pk0,ct0,key0) @ &m:event res]
  by byequiv(sim_known_monitor_projection A)=> //.
 have hg:Pr[A(SimCouplingOracles,SimGhostLookup(FOGActual)).guess(pk0,ct0,key0) @ &m:event res]=Pr[A(SimOracles(FOGActual,SimHActual),SimGhostLookup(FOGActual)).guess(pk0,ct0,key0) @ &m:event res]
  by byequiv(sim_ghost_monitor_projection A)=> //.
 have hdiff:=sim_known_ghost_distance_bad A w g ex hs cs pk0 ct0 key0 &m event hk hi all.
 rewrite hp hg in hdiff;exact(ler_trans _ _ _ hdiff hb).
qed.

require import NTRUPlus768SimPorts NTRUPlus768SimGames.


lemma sim_known_phase_probability
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOContext,-SimPublic,-SimHistory,-SimBad,-SimPublicBudget,-SimGRO.RO,-SimGRO.FRO,-SimPhaseInput}) &m s0 :
 Pr[SimDirectPhase(A,SimOracles(FOGActual,SimHActual),SimKnownDecap(FOGActual,SimHActual)).distinguish(s0) @ &m:res]=
 Pr[A(SimOracles(FOGActual,SimHActual),SimKnownDecap(FOGActual,SimHActual)).guess(SimPhaseInput.pk{m},SimPhaseInput.ct{m},SimPhaseInput.key{m}) @ &m:res=SimPhaseInput.bit{m}].
proof.
 byequiv(_: ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,glob SimPublic,SimHistory.h,glob FOContext,SimBad.corr} /\ pk{2}=SimPhaseInput.pk{1} /\
  ct{2}=SimPhaseInput.ct{1} /\ key{2}=SimPhaseInput.key{1} /\ SimPhaseInput.bit{1}=SimPhaseInput.bit{m} ==>
  res{1}=(res{2}=SimPhaseInput.bit{m}))=> //.
 proc*;inline{1} SimDirectPhase(A,SimOracles(FOGActual,SimHActual),SimKnownDecap(FOGActual,SimHActual)).distinguish;wp.
 call(_: ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,glob SimPublic,SimHistory.h,glob FOContext,SimBad.corr} ==> ={res}).
 + proc(={ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,glob SimPublic,SimHistory.h,glob FOContext,SimBad.corr})=> //;sim.
 auto.
qed.

lemma sim_ghost_phase_probability
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOContext,-SimPublic,-SimHistory,-SimBad,-SimPublicBudget,-SimGRO.RO,-SimGRO.FRO,-SimPhaseInput}) &m s0 :
 Pr[SimDirectPhase(A,SimOracles(FOGActual,SimHActual),SimGhostLookup(FOGActual)).distinguish(s0) @ &m:res]=
 Pr[A(SimOracles(FOGActual,SimHActual),SimGhostLookup(FOGActual)).guess(SimPhaseInput.pk{m},SimPhaseInput.ct{m},SimPhaseInput.key{m}) @ &m:res=SimPhaseInput.bit{m}].
proof.
 byequiv(_: ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,glob SimPublic,SimHistory.h,glob FOContext,SimBad.corr} /\ pk{2}=SimPhaseInput.pk{1} /\
  ct{2}=SimPhaseInput.ct{1} /\ key{2}=SimPhaseInput.key{1} /\ SimPhaseInput.bit{1}=SimPhaseInput.bit{m} ==>
  res{1}=(res{2}=SimPhaseInput.bit{m}))=> //.
 proc*;inline{1} SimDirectPhase(A,SimOracles(FOGActual,SimHActual),SimGhostLookup(FOGActual)).distinguish;wp.
 call(_: ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,glob SimPublic,SimHistory.h,glob FOContext,SimBad.corr} ==> ={res}).
 + proc(={ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,glob SimPublic,SimHistory.h,glob FOContext,SimBad.corr})=> //;sim.
 auto.
qed.
lemma sim_g_ghost_lookup_phase
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOContext,-SimPublic,-SimHistory,-SimBad,-SimPublicBudget,-SimGRO.RO,-SimGRO.FRO,-SimPhaseInput}) &m s0 :
 Pr[SimDirectPhase(A,SimOracles(FOGActual,SimHActual),SimGhostLookup(FOGActual)).distinguish(s0) @ &m:res]=
 Pr[SimDirectPhase(A,SimOracles(FOGActual,SimHActual),SimLookup(FOGActual)).distinguish(s0) @ &m:res].
proof.
 have hleft:Pr[SimGGetWorld(SimDirectPhase(A),FOGActual).distinguish(s0) @ &m:res]=
  Pr[SimDirectPhase(A,SimOracles(FOGActual,SimHActual),SimGhostLookup(FOGActual)).distinguish(s0) @ &m:res].
 + byequiv(_: ={arg,glob A,glob SimPhaseInput,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,glob SimPublic,SimHistory.h,glob FOContext,SimBad.corr} ==> ={res})=> //.
   proc*;inline{1} SimGGetWorld(SimDirectPhase(A),FOGActual).distinguish;sim.
 have hright:Pr[SimGLookupWorld(SimDirectPhase(A),FOGActual).distinguish(s0) @ &m:res]=
  Pr[SimDirectPhase(A,SimOracles(FOGActual,SimHActual),SimLookup(FOGActual)).distinguish(s0) @ &m:res].
 + byequiv(_: ={arg,glob A,glob SimPhaseInput,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,glob SimPublic,SimHistory.h,glob FOContext,SimBad.corr} ==> ={res})=> //.
   proc*;inline{1} SimGLookupWorld(SimDirectPhase(A),FOGActual).distinguish;sim.
 have h:=sim_g_ghost_lookup_probability (SimDirectPhase(A)) &m s0 (fun b=>b).
 by move:h;rewrite hleft hright.
qed.

(* The final comparison contains the actual uncapped adversary and both
   actual decapsulation implementations. The sole query contract is for
   public typed/raw H requests in the Known backend. *)
lemma sim_known_lookup_phase_bound
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOContext,-SimPublic,-SimHistory,-SimBad,-SimPublicBudget,-SimGRO.RO,-SimGRO.FRO,-SimPhaseInput}) w g ex hs cs qH &m s0 :
 pke_key_relation w=>(SimPublic.pk{m}=w.`kg_pk /\ SimPublic.suffix{m}=complete_sk_suffix w.`kg_sk /\
 CCADecapOracle.sk{m}=w.`kg_sk /\ SimPublic.cstar{m}=Some cs /\
 FOContext.w{m}=w /\ FOContext.g{m}=g /\ FOContext.challenge_h{m}=ex /\
 sim_known_invariant w g ex hs cs ROG.m{m} ROH.m{m} SimHistory.h{m} SimBad.corr{m} /\ !SimBad.corr{m})=>0<=qH=>(forall (H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
 islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
 islossless D.decap=>islossless A(H,D).guess)=>
 hoare[SimPublicCountedA(A,FOHashView(SimKnownPublicBackend),FODecapView(SimKnownPublicBackend)).guess:
 sim_public_budget_initial qH SimPublicBudget.nh SimPublicBudget.limit SimPublicBudget.overflow ==>
 SimPublicBudget.nh<=qH]=>
 `|Pr[SimDirectPhase(A,SimOracles(FOGActual,SimHActual),SimKnownDecap(FOGActual,SimHActual)).distinguish(s0) @ &m:res]-
   Pr[SimDirectPhase(A,SimOracles(FOGActual,SimHActual),SimLookup(FOGActual)).distinguish(s0) @ &m:res]|<=qH%r*fo_error w g.
proof.
 move=>hk hi hq all bounded.
 rewrite -(sim_g_ghost_lookup_phase A &m s0).
 rewrite (sim_known_phase_probability A &m s0)
  (sim_ghost_phase_probability A &m s0).
 exact(sim_known_ghost_distance A w g ex hs cs qH SimPhaseInput.pk{m} SimPhaseInput.ct{m} SimPhaseInput.key{m}
  &m (fun b=>b=SimPhaseInput.bit{m}) hk hi hq all bounded).
qed.
