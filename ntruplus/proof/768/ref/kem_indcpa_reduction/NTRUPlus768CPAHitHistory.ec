require import AllCore FMap.
require import NTRUPlus768CPAHitOracles.
require import NTRUPlus768SimModel NTRUPlus768SimOracles NTRUPlus768SimLookup.
require import NTRUPlus768FOGAdapters NTRUPlus768FOEagerG.
require import NTRUPlus768ROMOracles NTRUPlus768RawXOFStreams.
require import NTRUPlus768CCAOraclePorts NTRUPlus768CCAGame NTRUPlus768CCADecapOracle.

lemma cpa_hit_logged_history :
 hoare[SimLoggedH(CPAHitH).get :
 CPAHitState.hit=(CPAHitState.target \in SimHistory.h) ==>
 CPAHitState.hit=(CPAHitState.target \in SimHistory.h)].
proof.
 proc;inline CPAHitH.get SimHistory.record;wp.
 call(_:true ==>true);first by trivial.
 auto;smt(mem_set).
qed.
lemma cpa_hit_raw_full_history :
 hoare[SimRaw(FOGActual,CPAHitH).full :
 CPAHitState.hit=(CPAHitState.target \in SimHistory.h) ==>
 CPAHitState.hit=(CPAHitState.target \in SimHistory.h)].
proof.
 proc;match.
 + call(_:true ==>true);first by trivial. auto.
 match.
 + call(_:true ==>true);first by trivial. auto.
 + call(_:true ==>true);first by trivial. auto.
 + call(_:true ==>true);first by trivial. auto.
 call cpa_hit_logged_history;auto.
qed.
lemma cpa_hit_raw_history :
 hoare[SimRaw(FOGActual,CPAHitH).get :
 CPAHitState.hit=(CPAHitState.target \in SimHistory.h) ==>
 CPAHitState.hit=(CPAHitState.target \in SimHistory.h)].
proof. proc;sp;if;last by auto. wp;call cpa_hit_raw_full_history;auto. qed.
lemma cpa_hit_lookup_history :
 hoare[SimLookup(FOGActual).decap :
 CPAHitState.hit=(CPAHitState.target \in SimHistory.h) ==>
 CPAHitState.hit=(CPAHitState.target \in SimHistory.h)].
proof. proc*;call(_:true ==>true);first by trivial. auto. qed.
lemma cpa_hit_adversary_history
 (A<:CCAExtendedAdversary {-CPAHitState,-SimHistory,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-CCADecapOracle}) :
 hoare[A(SimOracles(FOGActual,CPAHitH),SimLookup(FOGActual)).guess :
 CPAHitState.hit=(CPAHitState.target \in SimHistory.h) ==>
 CPAHitState.hit=(CPAHitState.target \in SimHistory.h)].
proof.
 proc(CPAHitState.hit=(CPAHitState.target \in SimHistory.h))=> //.
 + proc*;call(_:true ==>true);first by trivial. auto.
 + proc*;call(_:true ==>true);first by trivial. auto.
 + proc*;call(_:true ==>true);first by trivial. auto.
 + exact cpa_hit_logged_history.
 + exact cpa_hit_raw_history.
 + exact cpa_hit_lookup_history.
qed.
