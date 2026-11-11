require import AllCore FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array129 Array192 Array224 Array1152.
require import NTRUPlus768FOModel NTRUPlus768FOAlgebra NTRUPlus768FOChallenge NTRUPlus768FOHMonitor.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDomains NTRUPlus768ROMPayloadHash NTRUPlus768DecapHashHPrepareProof.
require import NTRUPlus768DecapCompleteSpec NTRUPlus768KeygenCompleteProof.

(* The challenge's response is exempt from the error monitor, but its
   ciphertext is excluded by the decryption oracle. *)
op fo_monitor_invariant w g ex hs cs (st:(glob FOSHAKEH)) =
 st.`5=w /\ st.`4=g /\ st.`3=ex /\
 (!st.`1=>fo_hcache_good w g ex st.`6) /\
 fo_challenge_invariant w g ex hs cs st.`6.
op fo_monitor_good (st:(glob FOSHAKEH)) = !st.`1.

lemma fo_monitor_invariantE w g ex hs cs :
 forall &m,fo_monitor_invariant w g ex hs cs (glob FOSHAKEH){m}=
 (FOContext.w{m}=w /\ FOContext.g{m}=g /\ FOContext.challenge_h{m}=ex /\
  (!FOBadState.bad{m}=>fo_hcache_good w g ex ROH.m{m}) /\
  fo_challenge_invariant w g ex hs cs ROH.m{m}).
proof. by rewrite /fo_monitor_invariant. qed.
lemma fo_monitor_goodE : forall &m,fo_monitor_good(glob FOSHAKEH){m}=!FOBadState.bad{m}.
proof. by rewrite /fo_monitor_good. qed.

lemma fo_monitored_hash_cache w g ex hs cs x0 :
 hoare[FOSHAKEH.shake:
 input=x0 /\ fo_challenge_invariant w g ex hs cs ROH.m ==>
 ROH.m.[peel_h x0]=Some res /\ fo_challenge_invariant w g ex hs cs ROH.m].
proof.
 proc; call(_:input=peel_h x0 /\ fo_challenge_invariant w g ex hs cs ROH.m ==>
   ROH.m.[peel_h x0]=Some res /\ fo_challenge_invariant w g ex hs cs ROH.m).
 + proc; seq 2:(ROH.m.[peel_h x0]=Some result /\ fo_challenge_invariant w g ex hs cs ROH.m).
   - ecall(roh_get_value ROH.m (peel_h x0)); auto=> />; smt(fo_challenge_cache_extends).
   if; auto.
 auto.
qed.

lemma fo_monitored_hash_state w g ex hs cs x0 :
 hoare[FOSHAKEH.shake:
 input=x0 /\ fo_monitor_invariant w g ex hs cs (glob FOSHAKEH) ==>
 fo_monitor_invariant w g ex hs cs (glob FOSHAKEH) /\ ROH.m.[peel_h x0]=Some res].
proof.
 rewrite /fo_monitor_invariant.
 conseq(fo_shakeh_invariant w g ex) (fo_monitored_hash_cache w g ex hs cs x0)=> />; smt().
qed.
lemma fo_monitored_response_good w g ex hs cs hm msg hout ct :
 fo_challenge_invariant w g ex hs cs hm=>
 hm.[(msg,complete_sk_suffix w.`kg_sk)]=Some hout=>ct<>cs=>
 (Some(msg,complete_sk_suffix w.`kg_sk)=ex \/ !fo_base_bad w g msg hout)=>
 !fo_base_bad w g msg hout \/ fo_reencryption w g msg hout<>Some ct.
proof.
 move=>hc hh hn; case=>hi; last by left.
 right; exact(fo_challenge_reencryption_other w g ex hs cs hm msg hout ct hc hi hh hn).
qed.
lemma fo_monitored_hash_contract w g ex hs cs ct msg : ct<>cs=>
 hoare[FOSHAKEH.shake:
 input=hash_h_prepare_spec msg (complete_sk_suffix w.`kg_sk) /\
 fo_monitor_invariant w g ex hs cs (glob FOSHAKEH) ==>
 fo_monitor_invariant w g ex hs cs (glob FOSHAKEH) /\
 (fo_monitor_good(glob FOSHAKEH)=>(!fo_base_bad w g msg res \/ fo_reencryption w g msg res<>Some ct))].
proof.
 move=>hn.
 conseq(fo_monitored_hash_state w g ex hs cs (hash_h_prepare_spec msg (complete_sk_suffix w.`kg_sk)))
 (fo_shakeh_good w g (hash_h_prepare_spec msg (complete_sk_suffix w.`kg_sk)))=> />.
 move=> &hr _ _ result bad fresh hm _ hc hh hg hb.
 rewrite payload_h_preparation peel_encode_h /= in hh.
 rewrite payload_h_preparation peel_encode_h /= in hg.
 rewrite /fo_monitor_good /= in hb.
 exact(fo_monitored_response_good _ g ex hs cs hm msg result ct hc hh hn (hg hb)).
qed.
