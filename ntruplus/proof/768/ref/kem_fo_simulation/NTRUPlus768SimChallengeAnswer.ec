require import AllCore Distr FMap.
from Jasmin require import JWord.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768PKEModel NTRUPlus768PKEAlgebra.
require import NTRUPlus768EncapGuardSpec.
require import NTRUPlus768ACWC2Model NTRUPlus768ACWC2Oracle.
require import NTRUPlus768FOModel NTRUPlus768FOChallenge NTRUPlus768FOEagerG.
require import NTRUPlus768FOGAdapters NTRUPlus768ROMOracles.
require import NTRUPlus768SimModel NTRUPlus768SimSampling NTRUPlus768SimAnswer.
require import NTRUPlus768SimKnownAlgebra NTRUPlus768SimKnown.

lemma sim_challenge_request_cache w g q0 hm0 ex hs cs :
 fo_challenge_invariant w g ex hs cs hm0=>Some(sim_h_input q0)=ex=>
 hm0.[sim_h_input q0]=Some hs.
proof.
 rewrite /fo_challenge_invariant;move=>[x [he [hr hh]]] hq.
 have hx:sim_h_input q0=x by move:hq;rewrite he /=.
 by rewrite hx.
qed.

(* A challenge-H answer cannot reencrypt a distinct ciphertext, regardless
   of the supplied recovered polynomial or decode-status word. *)
lemma sim_challenge_answer_value w g q0 hm0 ex hs cs :
 fo_challenge_invariant w g ex hs cs hm0=>Some(sim_h_input q0)=ex=>
 q0.`sr_pk=w.`kg_pk=>q0.`sr_ct<>cs=>sim_answer_value g q0 hs=None.
proof.
 move=>hc hq hp hn.
 have hh:=sim_challenge_request_cache w g q0 hm0 ex hs cs hc hq.
 have he:=fo_challenge_cached_other w g ex hs cs hm0 (sim_h_input q0) hs q0.`sr_ct hc hq hh hn.
 move:he;rewrite /sim_h_input /= -hp=>he.
 by rewrite /sim_answer_value /acwc2_code he /=.
qed.

lemma sim_answer_challenge_functional w g q0 gm0 hm0 ex hs cs :
 pke_key_relation w=>acwc2_cache_matches g gm0=>fo_challenge_invariant w g ex hs cs hm0=>
 q0.`sr_pk=w.`kg_pk=>q0.`sr_ct<>cs=>Some(sim_h_input q0)=ex=>
 hoare[SimAnswerReal(FOGActual,SimHActual).answer:
 q=q0 /\ ROG.m=gm0 /\ ROH.m=hm0 ==>res=None /\ ROG.m=gm0 /\ ROH.m=hm0].
proof.
 move=>hk hg hc hp hn hq.
 have hpk:encap_key_canonical q0.`sr_pk by rewrite hp;exact(pke_key_canonical w hk).
 have hh:=sim_challenge_request_cache w g q0 hm0 ex hs cs hc hq.
 have hv:=sim_challenge_answer_value w g q0 hm0 ex hs cs hc hq hp hn.
 conseq(sim_answer_cached_value q0 g gm0 hm0 hs hpk hg hh);smt().
qed.

lemma sim_answer_challenge_correct w g q0 gm0 hm0 ex hs cs :
 pke_key_relation w=>acwc2_cache_matches g gm0=>fo_challenge_invariant w g ex hs cs hm0=>
 q0.`sr_pk=w.`kg_pk=>q0.`sr_ct<>cs=>Some(sim_h_input q0)=ex=>
 phoare[SimAnswerReal(FOGActual,SimHActual).answer:
 q=q0 /\ ROG.m=gm0 /\ ROH.m=hm0 ==>res=None /\ ROG.m=gm0 /\ ROH.m=hm0]=1%r.
proof.
 move=>hk hg hc hp hn hq;by conseq(sim_answer_real_ll FOGActual SimHActual rog_get_ll roh_get_ll)
  (sim_answer_challenge_functional w g q0 gm0 hm0 ex hs cs hk hg hc hp hn hq).
qed.
