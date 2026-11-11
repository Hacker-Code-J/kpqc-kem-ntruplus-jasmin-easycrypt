require import AllCore Distr FMap.
from Jasmin require import JWord.
require import Array32 Array192 Array224 Array1152 Array2336.
require import NTRUPlus768SimModel NTRUPlus768SimSampling NTRUPlus768SimAnswer NTRUPlus768SimPrefix.
require import NTRUPlus768SimKnownAlgebra NTRUPlus768SimLookup NTRUPlus768SimSpreadHash.
require import NTRUPlus768FOEagerG NTRUPlus768FOGAdapters NTRUPlus768FOProcedures NTRUPlus768FONativeBridge.
require import NTRUPlus768FOAlgebra NTRUPlus768FOModel NTRUPlus768ACWC2Model NTRUPlus768ACWC2Oracle.
require import NTRUPlus768CCAStatusAdapter NTRUPlus768CCADecapOracle.
require import NTRUPlus768ROMOracles NTRUPlus768ROMPayloadHash.
require import NTRUPlus768PKEModel NTRUPlus768PKEAlgebra NTRUPlus768EncapGuardSpec NTRUPlus768RRecModel.
require import NTRUPlus768DecapCompleteSpec NTRUPlus768KEMPayloadSpec.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768DecapCompleteProof.
require import NTRUPlus768DecapR2CompCaller NTRUPlus768DecapMessageSpec NTRUPlus768DecapMessageProof NTRUPlus768DecapMessageAlgebra.
require import NTRUPlus768PolySOTPDecodeAlgebra NTRUPlus768PolyToBytesProof.
require import NTRUPlus768RRecNativeComparison.

module SimKnownAnswer(G:FOGPort,H:SimHPort) : SimAnswer = {
 proc answer(q:sim_request) : W8.t Array32.t option = {
  var result:W8.t Array32.t option;
  result<-None;
  if(sim_h_input q \in SimHistory.h){result<@SimAnswerReal(G,H).answer(q);}
  return result;
 }
}.
module SimKnownDecap(G:FOGPort,H:SimHPort) : CCADecapPort = {
 proc decap(ct:W8.t Array1152.t) : cca_reply = {
  var result:cca_reply;
  result<-None;SimPublic.count<-SimPublic.count+1;
  if(SimPublic.cstar<>Some ct){
   result<@SimCore(G,SimKnownAnswer(G,H)).run(SimPublic.pk,ct,CCADecapOracle.sk);
  }
  return result;
 }
}.

lemma sim_known_answer_ll (G<:FOGPort)(H<:SimHPort) :
 islossless G.get=>islossless H.get=>islossless SimKnownAnswer(G,H).answer.
proof. move=>hg hh;proc;sp;if;last by auto. call(sim_answer_real_ll G H hg hh);auto. qed.
lemma sim_known_decap_ll (G<:FOGPort)(H<:SimHPort) :
 islossless G.get=>islossless H.get=>islossless SimKnownDecap(G,H).decap.
proof.
 move=>hg hh;proc;sp;if;last by auto.
 call(sim_core_ll G (SimKnownAnswer(G,H)) hg (sim_known_answer_ll G H hg hh));auto.
qed.

lemma sim_regenerate_actual_functional pk0 ct0 m0 msg0 hout0 df0 g gm0 :
 encap_key_canonical pk0=>acwc2_cache_matches g gm0=>
 hoare[FORegenerateFinish(FOGHash(FOGActual)).run:
 pk=pk0 /\ ct=ct0 /\ m1=m0 /\ msg=msg0 /\ hashout=hout0 /\ decode_fail=df0 /\ ROG.m=gm0 ==>
 res=fo_result hout0(df0=W32.zero /\ rrec_spec pk0 m0 ct0<>None /\
 pke_enc_spec pk0(acwc2_code g msg0(fo_randomness hout0))(fo_randomness hout0)=Some ct0) /\ ROG.m=gm0].
proof.
 move=>hp hg;conseq sim_regenerate_g_actual
  (sim_regenerate_functional pk0 ct0 m0 msg0 hout0 df0 g gm0 hp hg);smt().
qed.

lemma sim_answer_cached_value q0 g gm0 hm0 hout0 :
 encap_key_canonical q0.`sr_pk=>acwc2_cache_matches g gm0=>hm0.[sim_h_input q0]=Some hout0=>
 hoare[SimAnswerReal(FOGActual,SimHActual).answer:
 q=q0 /\ ROG.m=gm0 /\ ROH.m=hm0 ==>
 res=sim_answer_value g q0 hout0 /\ ROG.m=gm0 /\ ROH.m=hm0].
proof.
 move=>hp hg hh;proc.
 call(sim_regenerate_actual_functional q0.`sr_pk q0.`sr_ct q0.`sr_code q0.`sr_msg hout0 q0.`sr_fail g gm0 hp hg).
 call(roh_get_cached hm0 (sim_h_input q0) hout0).
 auto=> />;rewrite sim_fo_option_result /sim_answer_value;done.
qed.

lemma sim_known_answer_functional q0 g gm0 hm0 log0 :
 encap_key_canonical q0.`sr_pk=>acwc2_cache_matches g gm0=>sim_log_included log0 hm0=>
 hoare[SimKnownAnswer(FOGActual,SimHActual).answer:
 q=q0 /\ ROG.m=gm0 /\ ROH.m=hm0 /\ SimHistory.h=log0 ==>
 res=sim_known_answer_value g log0 q0 /\ ROG.m=gm0 /\ ROH.m=hm0 /\ SimHistory.h=log0].
proof.
 move=>hp hg hi;case(sim_h_input q0 \in log0)=>hm;proc.
 + rcondt 2;first by auto.
   have hl:log0.[sim_h_input q0]=Some(oget log0.[sim_h_input q0]) by apply some_oget;by move:hm;rewrite domE.
   call(sim_answer_cached_value q0 g gm0 hm0 (oget log0.[sim_h_input q0]) hp hg (hi _ _ hl)).
   auto=> />;by rewrite /sim_known_answer_value hm.
 rcondf 2;first by auto.
 auto=> />;by rewrite /sim_known_answer_value hm.
qed.

lemma sim_answer_h_cached hm0 :
 hoare[SimAnswerReal(FOGActual,SimHActual).answer:
 ROH.m=hm0 /\ sim_h_input q \in hm0 ==>ROH.m=hm0].
proof.
 proc;call(_:true ==>true);first by trivial.
 inline ROH.get;rcondf 2;auto.
qed.

lemma sim_known_answer_h_frame log0 hm0 : sim_log_included log0 hm0=>
 hoare[SimKnownAnswer(FOGActual,SimHActual).answer:
 ROH.m=hm0 /\ SimHistory.h=log0 ==>ROH.m=hm0 /\ SimHistory.h=log0].
proof.
 move=>hi;proc;sp;if;last by auto.
 call(sim_answer_h_cached hm0);auto=> /> &hr hx.
 have hl:log0.[sim_h_input q{hr}]=Some(oget log0.[sim_h_input q{hr}]).
 + apply some_oget;by move:hx;rewrite domE.
 have hh:=hi _ _ hl;by rewrite domE hh.
qed.

lemma sim_known_decap_h_frame log0 hm0 : sim_log_included log0 hm0=>
 hoare[SimKnownDecap(FOGActual,SimHActual).decap:
 ROH.m=hm0 /\ SimHistory.h=log0 ==>ROH.m=hm0 /\ SimHistory.h=log0].
proof.
 move=>hi;proc;sp;if;last by auto.
 inline SimCore(FOGActual,SimKnownAnswer(FOGActual,SimHActual)).run.
 sp.
 seq 2:(ROH.m=hm0 /\ SimHistory.h=log0).
 + wp;call(_:true ==>true);first by trivial. auto.
 wp;if;last by auto.
 call(sim_known_answer_h_frame log0 hm0 hi);auto.
qed.

lemma sim_known_decap_h_frame_pre log0 hm0 :
 hoare[SimKnownDecap(FOGActual,SimHActual).decap:
 ROH.m=hm0 /\ SimHistory.h=log0 /\ sim_log_included log0 hm0 ==>
 ROH.m=hm0 /\ SimHistory.h=log0].
proof.
 case(sim_log_included log0 hm0)=>hi;last by conseq(_:false ==>_)=> //;smt().
 conseq(sim_known_decap_h_frame log0 hm0 hi);smt().
qed.

lemma sim_message_g_actual :
 equiv[DecapMessage(FOGHash(FOGActual)).run ~ DecapMessage(SHAKEGROM).run:
 ={arg,ROG.m} ==> ={res,ROG.m}].
proof. proc;sim. qed.

lemma sim_message_prepared g r20 m10 :
 NTRUPlus768PolyToBytesProof.poly_tobytes_input_qrange r20=>poly_sotp_trit_input m10=>
 hoare[DecapMessage(FOGHash(FOGActual)).run:
 serialized=witness /\ input=witness /\ msg=witness /\ r2=r20 /\ m1=m10 /\
 acwc2_cache_matches g ROG.m ==>
 res.`1=NTRUPlus768PolyToBytesProof.poly_tobytes_spec r20 /\
 res.`2=poly_sotp_decode_msg_spec m10 (oget ROG.m.[res.`1]) /\
 res.`3=W32.of_int(b2i(poly_sotp_decode_fail_spec m10 (oget ROG.m.[res.`1]))) /\
 acwc2_cache_matches g ROG.m].
proof.
 move=>hr hm;conseq sim_message_g_actual (fo_message_prepared g r20 m10 hr hm);smt().
qed.

(* The prefix may add a nontrit G entry. Its returned request is expressed
   using that realized reply, and only the prepared trit cache is fixed. *)
lemma sim_prefix_value w ct0 g :
 hoare[SimPrefix(FOGActual).run:
 pk=w.`kg_pk /\ ct=ct0 /\ sk=w.`kg_sk /\ acwc2_cache_matches g ROG.m ==>
 acwc2_cache_matches g ROG.m /\
 res=(if complete_entry_accepts ct0 w.`kg_sk then
  Some(sim_request_of w ct0 (oget ROG.m.[rrec_native_bytes w ct0])) else None)].
proof.
 case(complete_entry_accepts ct0 w.`kg_sk)=>ha;proc.
 + have [hr hm]:=message_caller_input_closure ct0 (complete_sk_poly w.`kg_sk) ha.
   rcondt 3.
   - wp;call(guarded_r2_functional witness witness witness witness witness encap_zero_ss ct0 (complete_sk_poly w.`kg_sk)).
     auto=> />;by rewrite complete_guarded_prefix ha.
   wp;call(sim_message_prepared g (message_r2 ct0 (complete_sk_poly w.`kg_sk))
     (message_candidate ct0 (complete_sk_poly w.`kg_sk)) hr hm).
   wp;call(guarded_r2_functional witness witness witness witness witness encap_zero_ss ct0 (complete_sk_poly w.`kg_sk)).
   skip;rewrite complete_guarded_prefix ha /= fo_native_bytesE rrec_native_messageE
    /sim_request_of /fo_candidate_message /fo_candidate_failed;auto=> />;smt().
 rcondf 3.
 + wp;call(guarded_r2_functional witness witness witness witness witness encap_zero_ss ct0 (complete_sk_poly w.`kg_sk)).
   auto=> />;rewrite complete_guarded_prefix ha;smt(W32.to_uint0 W32.to_uint1).
 wp;call(guarded_r2_functional witness witness witness witness witness encap_zero_ss ct0 (complete_sk_poly w.`kg_sk)).
 auto=> />;by rewrite ha.
qed.

lemma sim_known_request_functional w ct0 g log0 hm0 gm1 :
 pke_key_relation w=>complete_entry_accepts ct0 w.`kg_sk=>
 sim_matching_good w g log0 ct0=>sim_log_included log0 hm0=>
 hoare[SimKnownAnswer(FOGActual,SimHActual).answer:
 q=sim_request_of w ct0 (oget gm1.[rrec_native_bytes w ct0]) /\
 ROG.m=gm1 /\ ROH.m=hm0 /\ SimHistory.h=log0 /\ acwc2_cache_matches g gm1 ==>
 res=sim_lookup_result w.`kg_pk (complete_sk_suffix w.`kg_sk) g log0 ct0 /\
 acwc2_cache_matches g ROG.m /\ ROH.m=hm0 /\ SimHistory.h=log0].
proof.
 move=>hk ha hg hi;case(acwc2_cache_matches g gm1)=>hgm;last first.
 + conseq(_:false ==>_)=> //;smt().
 have hp:encap_key_canonical(sim_request_of w ct0 (oget gm1.[rrec_native_bytes w ct0])).`sr_pk.
 + rewrite /sim_request_of /=;exact(pke_key_canonical w hk).
 have hv:sim_known_answer_value g log0(sim_request_of w ct0 (oget gm1.[rrec_native_bytes w ct0]))=
  sim_lookup_result w.`kg_pk (complete_sk_suffix w.`kg_sk) g log0 ct0.
 + rewrite(sim_known_request_value w g log0 ct0 (oget gm1.[rrec_native_bytes w ct0]) ha).
   exact(sim_known_lookup_result w g log0 ct0 (oget gm1.[rrec_native_bytes w ct0]) hk hg (fo_cache_pad_consistent g gm1 _ hgm)).
 conseq(sim_known_answer_functional (sim_request_of w ct0 (oget gm1.[rrec_native_bytes w ct0])) g gm1 hm0 log0 hp hgm hi);smt().
qed.

lemma sim_known_core_functional w ct0 g log0 hm0 :
 pke_key_relation w=>sim_matching_good w g log0 ct0=>sim_log_included log0 hm0=>
 hoare[SimCore(FOGActual,SimKnownAnswer(FOGActual,SimHActual)).run:
 pk=w.`kg_pk /\ ct=ct0 /\ sk=w.`kg_sk /\ acwc2_cache_matches g ROG.m /\
 ROH.m=hm0 /\ SimHistory.h=log0 ==>
 res=sim_lookup_result w.`kg_pk (complete_sk_suffix w.`kg_sk) g log0 ct0 /\
 acwc2_cache_matches g ROG.m /\ ROH.m=hm0 /\ SimHistory.h=log0].
proof.
 move=>hk hg hi;case(complete_entry_accepts ct0 w.`kg_sk)=>ha;proc.
 + seq 2:(request=Some(sim_request_of w ct0 (oget ROG.m.[rrec_native_bytes w ct0])) /\
    acwc2_cache_matches g ROG.m /\ ROH.m=hm0 /\ SimHistory.h=log0).
   - wp;call(sim_prefix_value w ct0 g);auto=> />;by rewrite ha.
   rcondt 1;first by auto.
   exists* ROG.m;elim*=>gm1.
   call(sim_known_request_functional w ct0 g log0 hm0 gm1 hk ha hg hi);auto.
 rcondf 3.
 + wp;call(sim_prefix_value w ct0 g);auto=> />;by rewrite ha.
 wp;call(sim_prefix_value w ct0 g);auto=> />.
 by rewrite(sim_lookup_invalid w g log0 ct0 hk ha).
qed.

lemma sim_known_decap_value w ct0 g log0 hm0 star0 :
 pke_key_relation w=>sim_matching_good w g log0 ct0=>sim_log_included log0 hm0=>
 hoare[SimKnownDecap(FOGActual,SimHActual).decap:
 ct=ct0 /\ SimPublic.pk=w.`kg_pk /\ CCADecapOracle.sk=w.`kg_sk /\
 SimPublic.cstar=star0 /\ SimHistory.h=log0 /\ ROH.m=hm0 /\ acwc2_cache_matches g ROG.m ==>
 res=sim_lookup_spec w.`kg_pk (complete_sk_suffix w.`kg_sk) star0 g log0 ct0 /\
 acwc2_cache_matches g ROG.m /\ ROH.m=hm0 /\ SimHistory.h=log0].
proof.
 move=>hk hg hi;case(star0=Some ct0)=>hc;proc.
 + rcondf 3;first by auto.
   auto=> />;by rewrite /sim_lookup_spec hc.
 rcondt 3;first by auto.
 call(sim_known_core_functional w ct0 g log0 hm0 hk hg hi).
 auto=> />;by rewrite /sim_lookup_spec hc.
qed.

lemma sim_known_decap_frame pk0 suffix0 star0 log0 sk0 n0 :
 hoare[SimKnownDecap(FOGActual,SimHActual).decap:
 SimPublic.pk=pk0 /\ SimPublic.suffix=suffix0 /\ SimPublic.cstar=star0 /\ SimPublic.count=n0 /\
 SimHistory.h=log0 /\ CCADecapOracle.sk=sk0 ==>
 SimPublic.pk=pk0 /\ SimPublic.suffix=suffix0 /\ SimPublic.cstar=star0 /\ SimPublic.count=n0+1 /\
 SimHistory.h=log0 /\ CCADecapOracle.sk=sk0].
proof. proc;sp;if;last by auto. call(_:true ==>true);first by trivial. auto. qed.

lemma sim_known_decap_functional w ct0 g log0 hm0 star0 n0 :
 pke_key_relation w=>sim_matching_good w g log0 ct0=>sim_log_included log0 hm0=>
 hoare[SimKnownDecap(FOGActual,SimHActual).decap:
 ct=ct0 /\ SimPublic.pk=w.`kg_pk /\ SimPublic.suffix=complete_sk_suffix w.`kg_sk /\
 CCADecapOracle.sk=w.`kg_sk /\ SimPublic.cstar=star0 /\ SimPublic.count=n0 /\
 SimHistory.h=log0 /\ ROH.m=hm0 /\ acwc2_cache_matches g ROG.m ==>
 res=sim_lookup_spec w.`kg_pk (complete_sk_suffix w.`kg_sk) star0 g log0 ct0 /\
 acwc2_cache_matches g ROG.m /\ ROH.m=hm0 /\ SimHistory.h=log0 /\
 SimPublic.pk=w.`kg_pk /\ SimPublic.suffix=complete_sk_suffix w.`kg_sk /\
 SimPublic.cstar=star0 /\ SimPublic.count=n0+1 /\ CCADecapOracle.sk=w.`kg_sk].
proof.
 move=>hk hg hi;conseq(sim_known_decap_value w ct0 g log0 hm0 star0 hk hg hi)
 (sim_known_decap_frame w.`kg_pk (complete_sk_suffix w.`kg_sk) star0 log0 w.`kg_sk n0);smt().
qed.

lemma sim_known_decap_challenge_functional w ct0 g log0 hm0 ex hs cs n0 :
 pke_key_relation w=>sim_log_included log0 hm0=>fo_hcache_good w g ex log0=>
 NTRUPlus768FOChallenge.fo_challenge_invariant w g ex hs cs hm0=>
 hoare[SimKnownDecap(FOGActual,SimHActual).decap:
 ct=ct0 /\ SimPublic.pk=w.`kg_pk /\ SimPublic.suffix=complete_sk_suffix w.`kg_sk /\
 CCADecapOracle.sk=w.`kg_sk /\ SimPublic.cstar=Some cs /\ SimPublic.count=n0 /\
 SimHistory.h=log0 /\ ROH.m=hm0 /\ acwc2_cache_matches g ROG.m ==>
 res=sim_lookup_spec w.`kg_pk (complete_sk_suffix w.`kg_sk) (Some cs) g log0 ct0 /\
 acwc2_cache_matches g ROG.m /\ ROH.m=hm0 /\ SimHistory.h=log0 /\
 SimPublic.pk=w.`kg_pk /\ SimPublic.suffix=complete_sk_suffix w.`kg_sk /\
 SimPublic.cstar=Some cs /\ SimPublic.count=n0+1 /\ CCADecapOracle.sk=w.`kg_sk].
proof.
 move=>hk hi hg hc;case(ct0=cs)=>he.
 + proc;rcondf 3;first by auto=> />;smt().
   auto=> />;by rewrite /sim_lookup_spec he.
 exact(sim_known_decap_functional w ct0 g log0 hm0 (Some cs) n0 hk
   (sim_matching_challenge_good w g log0 hm0 ex hs cs ct0 hi hg hc he) hi).
qed.

lemma sim_known_decap_challenge_correct w ct0 g log0 hm0 ex hs cs n0 :
 pke_key_relation w=>sim_log_included log0 hm0=>fo_hcache_good w g ex log0=>
 NTRUPlus768FOChallenge.fo_challenge_invariant w g ex hs cs hm0=>
 phoare[SimKnownDecap(FOGActual,SimHActual).decap:
 ct=ct0 /\ SimPublic.pk=w.`kg_pk /\ SimPublic.suffix=complete_sk_suffix w.`kg_sk /\
 CCADecapOracle.sk=w.`kg_sk /\ SimPublic.cstar=Some cs /\ SimPublic.count=n0 /\
 SimHistory.h=log0 /\ ROH.m=hm0 /\ acwc2_cache_matches g ROG.m ==>
 res=sim_lookup_spec w.`kg_pk (complete_sk_suffix w.`kg_sk) (Some cs) g log0 ct0 /\
 acwc2_cache_matches g ROG.m /\ ROH.m=hm0 /\ SimHistory.h=log0 /\
 SimPublic.pk=w.`kg_pk /\ SimPublic.suffix=complete_sk_suffix w.`kg_sk /\
 SimPublic.cstar=Some cs /\ SimPublic.count=n0+1 /\ CCADecapOracle.sk=w.`kg_sk]=1%r.
proof.
 move=>hk hi hg hc;by conseq(sim_known_decap_ll FOGActual SimHActual rog_get_ll roh_get_ll)
 (sim_known_decap_challenge_functional w ct0 g log0 hm0 ex hs cs n0 hk hi hg hc).
qed.
