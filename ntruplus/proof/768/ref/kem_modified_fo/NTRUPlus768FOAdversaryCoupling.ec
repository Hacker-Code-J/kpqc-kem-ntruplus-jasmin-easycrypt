require import AllCore List Distr FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152 Array2336.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768PKEModel.
require import NTRUPlus768ACWC2Model NTRUPlus768ACWC2Oracle.
require import NTRUPlus768ROMOracles NTRUPlus768CCAOraclePorts NTRUPlus768CCAGame.
require import NTRUPlus768RawXOFStreams NTRUPlus768RawXOF NTRUPlus768CCADecapOracle.
require import NTRUPlus768FOModel NTRUPlus768FOHMonitor NTRUPlus768FOChallenge NTRUPlus768FOMonitorBridge.
require import NTRUPlus768FOQueryBudget NTRUPlus768FOBackendContracts NTRUPlus768FOBadBound.
require import NTRUPlus768FOKEMGame NTRUPlus768FONativeBridge.

op [opaque] fo_adversary_invariant w g ex hs cs gm (st:(glob FOSHAKEH)) =
 acwc2_cache_matches g gm /\ fo_monitor_invariant w g ex hs cs st.

lemma fo_adversary_invariant_context w g ex hs cs gm st :
 fo_adversary_invariant w g ex hs cs gm st=>st.`5=w /\ st.`4=g.
proof. rewrite /fo_adversary_invariant /fo_monitor_invariant; smt(). qed.

lemma fo_adversary_g_preserves g : hoare[FOSharedOracles.g:
 acwc2_cache_matches g ROG.m ==>acwc2_cache_matches g ROG.m].
proof. proc; ecall(rog_get_value ROG.m input); auto=> />; smt(fo_cache_extension). qed.

lemma fo_adversary_h_challenge w g ex hs cs : hoare[FOHMonitor.get:
 fo_challenge_invariant w g ex hs cs ROH.m ==>fo_challenge_invariant w g ex hs cs ROH.m].
proof.
 proc; seq 2:(fo_challenge_invariant w g ex hs cs ROH.m).
 + ecall(roh_get_value ROH.m input); auto=> />; smt(fo_challenge_cache_extends).
 if; auto.
qed.
lemma fo_adversary_h_preserves w g ex hs cs : hoare[FOHMonitor.get:
 fo_adversary_invariant w g ex hs cs ROG.m (glob FOSHAKEH) ==>
 fo_adversary_invariant w g ex hs cs ROG.m (glob FOSHAKEH)].
proof.
 rewrite /fo_adversary_invariant /fo_monitor_invariant.
 conseq(fo_hmonitor_invariant w g ex) (fo_adversary_h_challenge w g ex hs cs)=> />; smt().
qed.
lemma fo_adversary_raw_g_preserves g : hoare[RawXOFStreams.g:
 acwc2_cache_matches g ROG.m ==>acwc2_cache_matches g ROG.m].
proof.
 proc; seq 1:(acwc2_cache_matches g ROG.m).
 + call(fo_adversary_g_preserves g); auto.
 if; auto.
qed.
lemma fo_adversary_raw_full_preserves w g ex hs cs : hoare[FOHRawXOF.full:
 fo_adversary_invariant w g ex hs cs ROG.m (glob FOSHAKEH) ==>
 fo_adversary_invariant w g ex hs cs ROG.m (glob FOSHAKEH)].
proof.
 proc; match.
 + call(_:true ==>true); first by trivial. auto.
 match.
 + call(_:true ==>true); first by trivial. auto.
 + call(_:true ==>true); first by trivial. auto.
 + call(fo_adversary_raw_g_preserves g); auto; rewrite /fo_adversary_invariant; smt().
 call(fo_adversary_h_preserves w g ex hs cs); auto.
qed.
lemma fo_adversary_raw_preserves w g ex hs cs : hoare[FOHRawXOF.get:
 fo_adversary_invariant w g ex hs cs ROG.m (glob FOSHAKEH) ==>
 fo_adversary_invariant w g ex hs cs ROG.m (glob FOSHAKEH)].
proof. proc; sp; if; last by auto. wp; call(fo_adversary_raw_full_preserves w g ex hs cs); auto. qed.

lemma fo_adversary_h_frame w g b : hoare[FOHMonitor.get:
 FOContext.w=w /\ FOContext.g=g /\ FOBadState.bad=b ==>
 FOContext.w=w /\ FOContext.g=g /\ (b=>FOBadState.bad)].
proof.
 proc; seq 2:(FOContext.w=w /\ FOContext.g=g /\ FOBadState.bad=b).
 + call(_:true ==>true); first by trivial. auto.
 if; auto; smt().
qed.
lemma fo_adversary_raw_full_frame w g b : hoare[FOHRawXOF.full:
 FOContext.w=w /\ FOContext.g=g /\ FOBadState.bad=b ==>
 FOContext.w=w /\ FOContext.g=g /\ (b=>FOBadState.bad)].
proof.
 proc; match.
 + call(_:true ==>true); first by trivial. auto.
 match.
 + call(_:true ==>true); first by trivial. auto.
 + call(_:true ==>true); first by trivial. auto.
 + call(_:true ==>true); first by trivial. auto.
 call(fo_adversary_h_frame w g b); auto.
qed.
lemma fo_adversary_raw_frame w g b : hoare[FOHRawXOF.get:
 FOContext.w=w /\ FOContext.g=g /\ FOBadState.bad=b ==>
 FOContext.w=w /\ FOContext.g=g /\ (b=>FOBadState.bad)].
proof. proc; sp; if; last by auto. wp; call(fo_adversary_raw_full_frame w g b); auto. qed.
lemma fo_adversary_raw_full_ll : islossless FOHRawXOF.full.
proof.
 proc; match.
 + by call raw_stream_untyped_ll; auto.
 match.
 + by call raw_stream_e_ll; auto.
 + by call raw_stream_f_ll; auto.
 + by call raw_stream_g_ll; auto.
 by call fo_hmonitor_ll; auto.
qed.
lemma fo_adversary_raw_ll : islossless FOHRawXOF.get.
proof. proc; sp; if; last by auto. wp; call fo_adversary_raw_full_ll; auto. qed.

lemma fo_adversary_g_same g :
 equiv[FOSharedOracles.g ~ FOSharedOracles.g:
 ={arg,ROG.m} /\ acwc2_cache_matches g ROG.m{1} ==>
 ={res,ROG.m} /\ acwc2_cache_matches g ROG.m{1}].
proof.
 conseq(_: ={arg,ROG.m} ==> ={res,ROG.m}) (fo_adversary_g_preserves g) _=> //.
 by sim.
qed.
lemma fo_adversary_h_same w g ex hs cs :
 equiv[FOHMonitor.get ~ FOHMonitor.get:
 ={arg,ROG.m,ROH.m,glob FOContext,glob FOBadState} /\
 fo_adversary_invariant w g ex hs cs ROG.m{1} (glob FOSHAKEH){1} ==>
 ={res,ROG.m,ROH.m,glob FOContext,glob FOBadState} /\
 fo_adversary_invariant w g ex hs cs ROG.m{1} (glob FOSHAKEH){1}].
proof.
 conseq(_: ={arg,ROG.m,ROH.m,glob FOContext,glob FOBadState} ==>
 ={res,ROG.m,ROH.m,glob FOContext,glob FOBadState}) (fo_adversary_h_preserves w g ex hs cs) _=> //.
 by sim.
qed.
lemma fo_adversary_raw_same w g ex hs cs :
 equiv[FOHRawXOF.get ~ FOHRawXOF.get:
 ={arg,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,glob FOContext,glob FOBadState} /\
 fo_adversary_invariant w g ex hs cs ROG.m{1} (glob FOSHAKEH){1} ==>
 ={res,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,glob FOContext,glob FOBadState} /\
 fo_adversary_invariant w g ex hs cs ROG.m{1} (glob FOSHAKEH){1}].
proof.
 conseq(_: ={arg,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,glob FOContext,glob FOBadState} ==>
 ={res,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,glob FOContext,glob FOBadState})
 (fo_adversary_raw_preserves w g ex hs cs) _=> //.
 by sim.
qed.

lemma fo_adversary_decap_step w g ex hs cs ct0 : pke_key_relation w=>
 equiv[FONativeBackend.decap ~ FOFullBackend.decap:
 ct{1}=ct0 /\ ct{2}=ct0 /\
 ={ROG.m,ROH.m,glob FOContext,glob FOBadState,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk} /\
 FOPublicKey.pk{1}=w.`kg_pk /\ CCADecapOracle.sk{1}=w.`kg_sk /\ CCADecapOracle.cstar{1}=Some cs /\
 fo_adversary_invariant w g ex hs cs ROG.m{1} (glob FOSHAKEH){1} ==>
 ={ROG.m,ROH.m,glob FOContext,glob FOBadState,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk} /\
 fo_adversary_invariant w g ex hs cs ROG.m{1} (glob FOSHAKEH){1} /\
 (!FOBadState.bad{1}=>res{1}=res{2})].
proof.
 move=>hk; case(ct0=cs)=>hn; proc.
 + rcondt{1} 2; first by auto=> />; smt().
   rcondt{2} 2; first by auto=> />; smt().
   auto.
 rcondf{1} 2; first by auto=> />; smt().
 rcondf{2} 2; first by auto=> />; smt().
 wp; call(fo_monitored_decaps_equiv w g ex hs cs ct0 hk hn).
 clear hk; rewrite /fo_adversary_invariant /fo_monitor_invariant; auto=> />; smt().
qed.

lemma fo_adversary_cap_e_frame w g b : hoare[FOCapHPort(FOSharedOracles).e:
 FOContext.w=w /\ FOContext.g=g /\ FOBadState.bad=b ==>
 FOContext.w=w /\ FOContext.g=g /\ (b=>FOBadState.bad)].
proof. proc; wp; call(fo_shared_e_frame w g b); auto. qed.

lemma fo_adversary_cap_f_frame w g b : hoare[FOCapHPort(FOSharedOracles).f:
 FOContext.w=w /\ FOContext.g=g /\ FOBadState.bad=b ==>
 FOContext.w=w /\ FOContext.g=g /\ (b=>FOBadState.bad)].
proof. proc; wp; call(fo_shared_f_frame w g b); auto. qed.

lemma fo_adversary_cap_g_frame w g b : hoare[FOCapHPort(FOSharedOracles).g:
 FOContext.w=w /\ FOContext.g=g /\ FOBadState.bad=b ==>
 FOContext.w=w /\ FOContext.g=g /\ (b=>FOBadState.bad)].
proof. proc; wp; call(fo_shared_g_frame w g b); auto. qed.

lemma fo_adversary_cap_h_frame w g b : hoare[FOCapHPort(FOSharedOracles).h:
 FOContext.w=w /\ FOContext.g=g /\ FOBadState.bad=b ==>
 FOContext.w=w /\ FOContext.g=g /\ (b=>FOBadState.bad)].
proof.
 proc; seq 2:(FOContext.w=w /\ FOContext.g=g /\ FOBadState.bad=b).
 + inline FOQueryRequest.h; auto.
 wp; if; last by auto.
 call(fo_adversary_h_frame w g b); auto.
qed.

lemma fo_adversary_cap_raw_frame w g b : hoare[FOCapHPort(FOSharedOracles).raw:
 FOContext.w=w /\ FOContext.g=g /\ FOBadState.bad=b ==>
 FOContext.w=w /\ FOContext.g=g /\ (b=>FOBadState.bad)].
proof.
 proc; seq 3:(FOContext.w=w /\ FOContext.g=g /\ FOBadState.bad=b).
 + inline FOQueryRequest.h; auto.
 wp; if; last by auto.
 call(fo_adversary_raw_frame w g b); auto.
qed.

lemma fo_adversary_cap_native_frame w g b : hoare[FOCapDPort(FONativeDecap(SHAKEGROM,FOSHAKEH)).decap:
 FOContext.w=w /\ FOContext.g=g /\ FOBadState.bad=b ==>
 FOContext.w=w /\ FOContext.g=g /\ (b=>FOBadState.bad)].
proof.
 proc; seq 2:(FOContext.w=w /\ FOContext.g=g /\ FOBadState.bad=b).
 + inline FOQueryRequest.d; auto.
 wp; if; last by auto.
 call(fo_native_decap_frame w g b); auto.
qed.

lemma fo_adversary_cap_full_frame w g b : hoare[FOCapDPort(FOReencryptDecap(SHAKEGROM,FOSHAKEH)).decap:
 FOContext.w=w /\ FOContext.g=g /\ FOBadState.bad=b ==>
 FOContext.w=w /\ FOContext.g=g /\ (b=>FOBadState.bad)].
proof.
 proc; seq 2:(FOContext.w=w /\ FOContext.g=g /\ FOBadState.bad=b).
 + inline FOQueryRequest.d; auto.
 wp; if; last by auto.
 call(fo_full_decap_frame w g b); auto.
qed.

lemma fo_adversary_cap_g_same w g ex hs cs :
 equiv[FOCapHPort(FOSharedOracles).g ~ FOCapHPort(FOSharedOracles).g:
 ={arg,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk,glob FOContext,glob FOBadState,glob FOBudgetState} /\ fo_adversary_invariant w g ex hs cs ROG.m{1} (glob FOSHAKEH){1} ==>
 ={res,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk,glob FOContext,glob FOBadState,glob FOBudgetState} /\ fo_adversary_invariant w g ex hs cs ROG.m{1} (glob FOSHAKEH){1}].
proof.
 proc; wp; call(fo_adversary_g_same g); rewrite /fo_adversary_invariant; auto=> />; smt().
qed.

lemma fo_adversary_cap_h_same w g ex hs cs :
 equiv[FOCapHPort(FOSharedOracles).h ~ FOCapHPort(FOSharedOracles).h:
 ={arg,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk,glob FOContext,glob FOBadState,glob FOBudgetState} /\ fo_adversary_invariant w g ex hs cs ROG.m{1} (glob FOSHAKEH){1} ==>
 ={res,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk,glob FOContext,glob FOBadState,glob FOBudgetState} /\ fo_adversary_invariant w g ex hs cs ROG.m{1} (glob FOSHAKEH){1}].
proof.
 proc; wp; seq 2 2:(={allowed,result,input,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk,glob FOContext,glob FOBadState,glob FOBudgetState} /\ fo_adversary_invariant w g ex hs cs ROG.m{1} (glob FOSHAKEH){1}).
 + inline FOQueryRequest.h; auto.
 if; first by auto.
 + call(fo_adversary_h_same w g ex hs cs); auto.
 auto.
qed.

lemma fo_adversary_cap_raw_same w g ex hs cs :
 equiv[FOCapHPort(FOSharedOracles).raw ~ FOCapHPort(FOSharedOracles).raw:
 ={arg,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk,glob FOContext,glob FOBadState,glob FOBudgetState} /\ fo_adversary_invariant w g ex hs cs ROG.m{1} (glob FOSHAKEH){1} ==>
 ={res,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk,glob FOContext,glob FOBadState,glob FOBudgetState} /\ fo_adversary_invariant w g ex hs cs ROG.m{1} (glob FOSHAKEH){1}].
proof.
 proc; wp; seq 3 3:(={allowed,result,input,outlen,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk,glob FOContext,glob FOBadState,glob FOBudgetState} /\ fo_adversary_invariant w g ex hs cs ROG.m{1} (glob FOSHAKEH){1}).
 + inline FOQueryRequest.h; auto.
 if; first by auto.
 + call(fo_adversary_raw_same w g ex hs cs); auto.
 auto.
qed.

lemma fo_adversary_cap_decap w g ex hs cs ct0 : pke_key_relation w=>
 equiv[FOCapDPort(FONativeDecap(SHAKEGROM,FOSHAKEH)).decap ~ FOCapDPort(FOReencryptDecap(SHAKEGROM,FOSHAKEH)).decap:
 ct{1}=ct0 /\ ct{2}=ct0 /\ ={ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk,glob FOContext,glob FOBadState,glob FOBudgetState} /\
 FOPublicKey.pk{1}=w.`kg_pk /\ CCADecapOracle.sk{1}=w.`kg_sk /\ CCADecapOracle.cstar{1}=Some cs /\
 fo_adversary_invariant w g ex hs cs ROG.m{1} (glob FOSHAKEH){1} ==>
 ={ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk,glob FOContext,glob FOBadState,glob FOBudgetState} /\ fo_adversary_invariant w g ex hs cs ROG.m{1} (glob FOSHAKEH){1} /\ (!FOBadState.bad{1}=>res{1}=res{2})].
proof.
 move=>hk; proc; wp.
 seq 2 2:(ct{1}=ct0 /\ ct{2}=ct0 /\ ={allowed,result,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk,glob FOContext,glob FOBadState,glob FOBudgetState} /\
 FOPublicKey.pk{1}=w.`kg_pk /\ CCADecapOracle.sk{1}=w.`kg_sk /\ CCADecapOracle.cstar{1}=Some cs /\ fo_adversary_invariant w g ex hs cs ROG.m{1} (glob FOSHAKEH){1}).
 + inline FOQueryRequest.d; auto.
 if; first by auto.
 + call(fo_adversary_decap_step w g ex hs cs ct0 hk); auto.
 auto.
qed.

(* Robust adversary losslessness is explicit. A finite oracle cap by itself
   does not imply that the adversary returns after the first bad response. *)
lemma fo_capped_adversary_upto
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOContext,-FOBadState,-FOBudgetState}) w g ex hs cs :
 pke_key_relation w=>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
 islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
 islossless D.decap=>islossless A(H,D).guess) =>
 equiv[FOCappedA(A,FOSharedOracles,FONativeDecap(SHAKEGROM,FOSHAKEH)).guess ~
       FOCappedA(A,FOSharedOracles,FOReencryptDecap(SHAKEGROM,FOSHAKEH)).guess:
 ={pk,ct,key,glob A,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk,glob FOContext,glob FOBadState,glob FOBudgetState} /\ FOPublicKey.pk{1}=w.`kg_pk /\ CCADecapOracle.sk{1}=w.`kg_sk /\ CCADecapOracle.cstar{1}=Some cs /\ fo_adversary_invariant w g ex hs cs ROG.m{1} (glob FOSHAKEH){1} /\
 !FOBadState.bad{1} /\ !FOBadState.bad{2} ==>
 ={FOBadState.bad} /\ (!FOBadState.bad{2}=>
 ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk,glob FOContext,glob FOBadState,glob FOBudgetState} /\ fo_adversary_invariant w g ex hs cs ROG.m{1} (glob FOSHAKEH){1})].
proof.
 move=>hk all.
 have hn:=fo_native_decap_ll SHAKEGROM FOSHAKEH ro_g_shake_ll fo_shakeh_ll.
 have hf:=fo_reencrypt_decap_ll SHAKEGROM FOSHAKEH ro_g_shake_ll fo_shakeh_ll.
 have al:=all (FOCapHPort(FOSharedOracles)) (FOCapDPort(FONativeDecap(SHAKEGROM,FOSHAKEH)))
  (fo_cap_e_ll FOSharedOracles cca_extended_e_ll) (fo_cap_f_ll FOSharedOracles cca_extended_f_ll)
  (fo_cap_g_ll FOSharedOracles cca_extended_g_ll) (fo_cap_h_ll FOSharedOracles fo_hmonitor_ll)
  (fo_cap_raw_ll FOSharedOracles fo_adversary_raw_ll) (fo_cap_d_ll (FONativeDecap(SHAKEGROM,FOSHAKEH)) hn).
 have ar:=all (FOCapHPort(FOSharedOracles)) (FOCapDPort(FOReencryptDecap(SHAKEGROM,FOSHAKEH)))
  (fo_cap_e_ll FOSharedOracles cca_extended_e_ll) (fo_cap_f_ll FOSharedOracles cca_extended_f_ll)
  (fo_cap_g_ll FOSharedOracles cca_extended_g_ll) (fo_cap_h_ll FOSharedOracles fo_hmonitor_ll)
  (fo_cap_raw_ll FOSharedOracles fo_adversary_raw_ll) (fo_cap_d_ll (FOReencryptDecap(SHAKEGROM,FOSHAKEH)) hf).
 proc*; call(_:FOBadState.bad,
 ={ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk,glob FOContext,glob FOBadState,glob FOBudgetState} /\ FOPublicKey.pk{1}=w.`kg_pk /\ CCADecapOracle.sk{1}=w.`kg_sk /\ CCADecapOracle.cstar{1}=Some cs /\ fo_adversary_invariant w g ex hs cs ROG.m{1} (glob FOSHAKEH){1},
 ={FOBadState.bad} /\ FOContext.w{1}=w /\ FOContext.w{2}=w /\ FOContext.g{1}=g /\ FOContext.g{2}=g).
 + proc; wp; call(_: ={arg,ROE.m} ==> ={res,ROE.m}); first by sim.
   auto=> />; smt(fo_adversary_invariant_context).
 + move=> &2 h; clear hk all al ar; conseq(fo_cap_e_ll FOSharedOracles cca_extended_e_ll) (fo_adversary_cap_e_frame w g true); smt().
 + move=> &1; clear hk all al ar; conseq(fo_cap_e_ll FOSharedOracles cca_extended_e_ll) (fo_adversary_cap_e_frame w g true); smt().
 + proc; wp; call(_: ={arg,ROF.m} ==> ={res,ROF.m}); first by sim.
   auto=> />; smt(fo_adversary_invariant_context).
 + move=> &2 h; clear hk all al ar; conseq(fo_cap_f_ll FOSharedOracles cca_extended_f_ll) (fo_adversary_cap_f_frame w g true); smt().
 + move=> &1; clear hk all al ar; conseq(fo_cap_f_ll FOSharedOracles cca_extended_f_ll) (fo_adversary_cap_f_frame w g true); smt().
 + clear hk all hn hf al ar; conseq(fo_adversary_cap_g_same w g ex hs cs); smt(fo_adversary_invariant_context).
 + move=> &2 h; clear hk all al ar; conseq(fo_cap_g_ll FOSharedOracles cca_extended_g_ll) (fo_adversary_cap_g_frame w g true); smt().
 + move=> &1; clear hk all al ar; conseq(fo_cap_g_ll FOSharedOracles cca_extended_g_ll) (fo_adversary_cap_g_frame w g true); smt().
 + clear hk all hn hf al ar; conseq(fo_adversary_cap_h_same w g ex hs cs); smt(fo_adversary_invariant_context).
 + move=> &2 h; clear hk all al ar; conseq(fo_cap_h_ll FOSharedOracles fo_hmonitor_ll) (fo_adversary_cap_h_frame w g true); smt().
 + move=> &1; clear hk all al ar; conseq(fo_cap_h_ll FOSharedOracles fo_hmonitor_ll) (fo_adversary_cap_h_frame w g true); smt().
 + clear hk all hn hf al ar; conseq(fo_adversary_cap_raw_same w g ex hs cs); smt(fo_adversary_invariant_context).
 + move=> &2 h; clear hk all al ar; conseq(fo_cap_raw_ll FOSharedOracles fo_adversary_raw_ll) (fo_adversary_cap_raw_frame w g true); smt().
 + move=> &1; clear hk all al ar; conseq(fo_cap_raw_ll FOSharedOracles fo_adversary_raw_ll) (fo_adversary_cap_raw_frame w g true); smt().
 + proc*; ecall(fo_adversary_cap_decap w g ex hs cs ct{1} hk).
   clear hk all al ar; auto=> />; smt(fo_adversary_invariant_context).
 + move=> &2 h; clear hk all al ar; conseq(fo_cap_d_ll (FONativeDecap(SHAKEGROM,FOSHAKEH)) hn) (fo_adversary_cap_native_frame w g true); smt().
 + move=> &1; clear hk all al ar; conseq(fo_cap_d_ll (FOReencryptDecap(SHAKEGROM,FOSHAKEH)) hf) (fo_adversary_cap_full_frame w g true); smt().
 clear hk all hn hf al ar; auto=> />; smt().
qed.

lemma fo_capped_native_identity
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOContext,-FOBadState,-FOBudgetState}) :
 equiv[FOCappedA(A,FOHashView(FONativeBackend),FODecapView(FONativeBackend)).guess ~
 FOCappedA(A,FOSharedOracles,FONativeDecap(SHAKEGROM,FOSHAKEH)).guess:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk,glob FOContext,glob FOBadState,glob FOBudgetState} ==> ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk,glob FOContext,glob FOBadState,glob FOBudgetState}].
proof. proc(={ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk,glob FOContext,glob FOBadState,glob FOBudgetState})=> //; sim. qed.

lemma fo_capped_full_identity
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOContext,-FOBadState,-FOBudgetState}) :
 equiv[FOCappedA(A,FOHashView(FOFullBackend),FODecapView(FOFullBackend)).guess ~
 FOCappedA(A,FOSharedOracles,FOReencryptDecap(SHAKEGROM,FOSHAKEH)).guess:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk,glob FOContext,glob FOBadState,glob FOBudgetState} ==> ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk,glob FOContext,glob FOBadState,glob FOBudgetState}].
proof. proc(={ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk,glob FOContext,glob FOBadState,glob FOBudgetState})=> //; sim. qed.

lemma fo_observed_phase_upto
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOContext,-FOBadState,-FOBudgetState}) w g ex hs cs :
 pke_key_relation w=>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
 islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
 islossless D.decap=>islossless A(H,D).guess) =>
 equiv[FOBadPhase(A,FONativeBackend).run ~ FOBadPhase(A,FOFullBackend).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk,glob FOContext,glob FOBadState,glob FOBudgetState} /\ FOPublicKey.pk{1}=w.`kg_pk /\ CCADecapOracle.sk{1}=w.`kg_sk /\ CCADecapOracle.cstar{1}=Some cs /\
 acwc2_cache_matches g ROG.m{1} /\
 FOContext.w{1}=w /\ FOContext.g{1}=g /\ FOContext.challenge_h{1}=ex /\
 fo_hcache_good w g ex ROH.m{1} /\ fo_challenge_invariant w g ex hs cs ROH.m{1} ==>
 ={FOBadState.bad} /\ (!FOBadState.bad{2}=>
 ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk,glob FOContext,glob FOBadState,glob FOBudgetState} /\ fo_adversary_invariant w g ex hs cs ROG.m{1} (glob FOSHAKEH){1})].
proof.
 move=>hk all; proc.
 rewrite equiv[{1} 4 (fo_capped_native_identity A)].
 rewrite equiv[{2} 4 (fo_capped_full_identity A)].
 call(fo_capped_adversary_upto A w g ex hs cs hk all).
 inline FOBadState.init FOBudgetState.configure; clear hk all;
 rewrite /fo_adversary_invariant /fo_monitor_invariant; auto=> />; smt().
qed.
