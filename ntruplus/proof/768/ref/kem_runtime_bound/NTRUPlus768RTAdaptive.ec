require import AllCore List Distr FMap StdOrder.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152.
require import NTRUPlus768RTModel NTRUPlus768RTStore NTRUPlus768RTOracles.
require import NTRUPlus768HistModel.
require import NTRUPlus768AHState NTRUPlus768AHAdapter NTRUPlus768AHActualReduction.
require import NTRUPlus768FOModel NTRUPlus768FOEagerG NTRUPlus768FOGAdapters.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
require import NTRUPlus768CCAGame.
require import NTRUPlus768CCAStatusAdapter NTRUPlus768CCADecapOracle NTRUPlus768SecGOracles.
import IntOrder.

(* H, D and direct G occupy disjoint completed public callbacks. Other
   typed queries and every invalid raw request still consume Q. *)
op rt_callback_ok(p:rt_profile) = p.`rp_h+p.`rp_d+p.`rp_g<=p.`rp_q.
op [opaque] rt_adaptive_ok(st:ah_state)(p:rt_profile)(queries:W8.t Array1152.t list) =
 rt_store_ok st p /\ rt_callback_ok p /\ size queries=rt_g_length p.

module RTWrapper(S:RTHistory,A:CCAExtendedAdversary,O:CCAExtendedOraclePort,D:CCADecapPort) = {
 proc guess(pk ct:W8.t Array1152.t,key:W8.t Array32.t):bool = {
  var suffix:W8.t Array32.t;var answer:bool;
  suffix<@O.f(pk);S.init(pk,suffix,Some ct);
  answer<@A(RTOracles(S,O),RTDecap(S,O)).guess(pk,ct,key);
  return answer;
 }
}.
module RTActualPhase(S:RTHistory,A:CCAExtendedAdversary,G:FOGPort) = {
 proc run(pk ct:W8.t Array1152.t,key:W8.t Array32.t):bool = {
  var suffix:W8.t Array32.t;var answer:bool;
  suffix<@ROF.get(pk);
  answer<@RTWrapper(S,A,AHActualOracles(G),AHRejectD).guess(pk,ct,key);
  return answer;
 }
}.
module RTTranscript(S:RTHistory,A:CCAExtendedAdversary) = {
 proc run(pk ct:W8.t Array1152.t):W8.t Array1152.t list*rt_profile = {
  var key:W8.t Array32.t;var ignored:bool;var profile:rt_profile;
  SecGHistory.init();key<$uniform32;
  ignored<@RTActualPhase(S,A,SecGLogged(FOGActual)).run(pk,ct,key);
  profile<@S.metrics();return(SecGHistory.queries,profile);
 }
}.

lemma rt_public_call st p ig bytes : rt_store_ok st p=>rt_callback_ok p=>0<=bytes=>
 rt_store_ok st (rt_call p ig bytes) /\ rt_callback_ok(rt_call p ig bytes).
proof.
 rewrite /rt_store_ok;move=>[hu [hn hp]] hb hbytes;split.
 + rewrite /rt_store_ok;split;first exact hu.
   split;first by rewrite /rt_call.
   exact(rt_call_ok p ig bytes hp hbytes).
 move:hb;rewrite /rt_callback_ok /rt_call;smt(b2i0 b2i1).
qed.
lemma rt_public_h st p x y bytes : rt_store_ok st p=>rt_callback_ok p=>0<=bytes=>
 rt_store_ok(ah_record_state st x y)(rt_record_cost st (rt_call p false bytes) x) /\
 rt_callback_ok(rt_record_cost st (rt_call p false bytes) x) /\
 rt_g_length(rt_record_cost st (rt_call p false bytes) x)=rt_g_length p.
proof.
 move=>hs hb hbytes.
 have [hc _]:=rt_public_call st p false bytes hs hb hbytes.
 split;first exact(rt_record_store_ok st (rt_call p false bytes) x y hc).
 split.
 + move:hb;rewrite /rt_callback_ok /rt_record_cost /rt_record /rt_call;smt().
 by rewrite /rt_record_cost rt_record_g_length rt_call_g_length /=.
qed.
lemma rt_public_decap st p v k c : rt_store_ok st p=>rt_callback_ok p=>
 0<=k<=v=>v<=size st.`ah_rows=>0<=c<=1152+32*v+1152*k=>
 rt_store_ok st (rt_decap(rt_call p false 0)v k c) /\
 rt_callback_ok(rt_decap(rt_call p false 0)v k c) /\
 rt_g_length(rt_decap(rt_call p false 0)v k c)=rt_g_length p+k.
proof.
 move=>hs hb hkv hv hc.
 have [hs1 _]:=rt_public_call st p false 0 hs hb _;first smt().
 move:hs1;rewrite /rt_store_ok;move=>[hu [hn hp]].
 split.
 + rewrite /rt_store_ok;split;first exact hu.
   split;first by rewrite /rt_decap.
   apply(rt_decap_ok (rt_call p false 0) v k c hp hkv _ hc);smt().
 split.
 + move:hb;rewrite /rt_callback_ok /rt_decap /rt_call;smt().
 by rewrite rt_decap_g_length rt_call_g_length /=.
qed.
lemma rt_public_raw st p input n st1 p1 :
 rt_store_ok st p=>rt_callback_ok p=>rt_raw_effect st p input n st1 p1=>
 rt_store_ok st1 p1 /\ rt_callback_ok p1 /\
 rt_g_length p1=rt_g_length p+b2i(rt_raw_g input n).
proof.
 move=>hs hb;rewrite /rt_raw_effect.
 move=>[[hn [-> ->]]|[x y [hv [hd [-> ->]]]]].
 + have [hc hcb]:=rt_public_call st p (rt_raw_g input n) (size input) hs hb (size_ge0 input).
   split;first exact hc. split;first exact hcb.
   exact(rt_call_g_length p (rt_raw_g input n) (size input)).
 have hg:!rt_raw_g input n by rewrite /rt_raw_g;smt().
 have [hc [hcb he]]:=rt_public_h st p x y (size input) hs hb (size_ge0 input).
 split;first exact hc. split;first exact hcb.
 by rewrite he hg /=.
qed.

lemma rt_adaptive_call st p qs qs1 ig bytes :
 rt_adaptive_ok st p qs=>0<=bytes=>size qs1=size qs+b2i ig=>
 rt_adaptive_ok st (rt_call p ig bytes) qs1.
proof.
 rewrite /rt_adaptive_ok;move=>[hs [hb hn]] hbytes hlen.
 have [hc hcb]:=rt_public_call st p ig bytes hs hb hbytes.
 split;first exact hc. split;first exact hcb.
 by rewrite rt_call_g_length -hn.
qed.
lemma rt_adaptive_h st p qs qs1 x y :
 rt_adaptive_ok st p qs=>size qs1=size qs=>
 rt_adaptive_ok(ah_record_state st x y)(rt_record_cost st (rt_call p false 0) x) qs1.
proof.
 rewrite /rt_adaptive_ok;move=>[hs [hb hn]] hlen.
 have [hc [hcb he]]:=rt_public_h st p x y 0 hs hb _;first smt().
 split;first exact hc. split;first exact hcb.
 by rewrite he -hn.
qed.
lemma rt_adaptive_raw st p qs qs1 input n st1 p1 :
 rt_adaptive_ok st p qs=>rt_raw_effect st p input n st1 p1=>
 size qs1=size qs+b2i(rt_raw_g input n)=>rt_adaptive_ok st1 p1 qs1.
proof.
 rewrite /rt_adaptive_ok;move=>[hs [hb hn]] he hlen.
 have [hc [hcb hg]]:=rt_public_raw st p input n st1 p1 hs hb he.
 split;first exact hc. split;first exact hcb.
 by rewrite hg -hn.
qed.
lemma rt_adaptive_decap st p qs qs1 v k c :
 rt_adaptive_ok st p qs=>0<=k<=v=>v<=size st.`ah_rows=>
 0<=c<=1152+32*v+1152*k=>size qs1=size qs+k=>
 rt_adaptive_ok st (rt_decap(rt_call p false 0)v k c) qs1.
proof.
 rewrite /rt_adaptive_ok;move=>[hs [hb hn]] hkv hv hc hlen.
 have [hd [hcb hg]]:=rt_public_decap st p v k c hs hb hkv hv hc.
 split;first exact hd. split;first exact hcb.
 by rewrite hg -hn.
qed.

op [opaque] rt_phase_ok st p qs =
 rt_adaptive_ok st p qs /\ p.`rp_xcalls=0 /\ p.`rp_xvisits=0.
lemma rt_phase_call st p qs qs1 ig bytes :
 rt_phase_ok st p qs=>0<=bytes=>size qs1=size qs+b2i ig=>
 rt_phase_ok st (rt_call p ig bytes) qs1.
proof.
 rewrite /rt_phase_ok;move=>[ha hx] hb hn;split.
 + exact(rt_adaptive_call st p qs qs1 ig bytes ha hb hn).
 by rewrite /rt_call.
qed.
lemma rt_phase_h st p qs qs1 x y :
 rt_phase_ok st p qs=>size qs1=size qs=>
 rt_phase_ok(ah_record_state st x y)(rt_record_cost st (rt_call p false 0) x) qs1.
proof.
 rewrite /rt_phase_ok;move=>[ha hx] hn;split.
 + exact(rt_adaptive_h st p qs qs1 x y ha hn).
 by rewrite /rt_record_cost /rt_record /rt_call.
qed.
lemma rt_phase_raw st p qs qs1 input n st1 p1 :
 rt_phase_ok st p qs=>rt_raw_effect st p input n st1 p1=>
 size qs1=size qs+b2i(rt_raw_g input n)=>rt_phase_ok st1 p1 qs1.
proof.
 rewrite /rt_phase_ok;move=>[ha hx] he hn;split.
 + exact(rt_adaptive_raw st p qs qs1 input n st1 p1 ha he hn).
 move:he;rewrite /rt_raw_effect /rt_record_cost /rt_record /rt_call;smt().
qed.
lemma rt_phase_decap st p qs qs1 v k c :
 rt_phase_ok st p qs=>0<=k<=v=>v<=size st.`ah_rows=>
 0<=c<=1152+32*v+1152*k=>size qs1=size qs+k=>
 rt_phase_ok st (rt_decap(rt_call p false 0)v k c) qs1.
proof.
 rewrite /rt_phase_ok;move=>[ha hx] hk hv hc hn;split.
 + exact(rt_adaptive_decap st p qs qs1 v k c ha hk hv hc hn).
 by rewrite /rt_decap /rt_call.
qed.

(* The invariant is discharged at the actual adaptive oracle boundary.
   No trace list is supplied as an assumption. A may choose its next
   typed/raw/decapsulation query from every previous answer. *)
lemma rt_adversary_invariant
 (S<:RTHistory {-SecGHistory,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams})
 (A<:CCAExtendedAdversary {-S,-SecGHistory,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams})
 (view:(glob S)->ah_state)(cost:(glob S)->rt_profile) :
 (forall st p ig b,hoare[S.charge_call:view(glob S)=st /\ cost(glob S)=p /\ arg=(ig,b) ==>
 view(glob S)=st /\ cost(glob S)=rt_call p ig b])=>
 (forall st p,hoare[S.snapshot:view(glob S)=st /\ cost(glob S)=p ==>
 res=st /\ view(glob S)=st /\ cost(glob S)=p])=>
 (forall st p x y,hoare[S.record:view(glob S)=st /\ cost(glob S)=p /\ input=x /\ hout=y ==>
 view(glob S)=ah_record_state st x y /\ cost(glob S)=rt_record_cost st p x])=>
 (forall st p v k c,hoare[S.charge_decap:view(glob S)=st /\ cost(glob S)=p /\ arg=(v,k,c) ==>
 view(glob S)=st /\ cost(glob S)=rt_decap p v k c])=>
 hoare[A(RTOracles(S,AHActualOracles(SecGLogged(FOGActual))),
 RTDecap(S,AHActualOracles(SecGLogged(FOGActual)))).guess:
 rt_phase_ok (view(glob S)) (cost(glob S)) SecGHistory.queries ==>
 rt_phase_ok (view(glob S)) (cost(glob S)) SecGHistory.queries].
proof.
 move=>hc hs hr hd.
 proc(rt_phase_ok (view(glob S)) (cost(glob S)) SecGHistory.queries)=> //.
 + proc*;exists* (view(glob S)),(cost(glob S)),SecGHistory.queries;elim*=>st0 p0 qs0.
   call(rt_call_e S (AHActualOracles(SecGLogged(FOGActual))) view cost st0 p0 hc).
   clear hc hs hr hd;auto=> />;smt(rt_phase_call).
 + proc*;exists* (view(glob S)),(cost(glob S)),SecGHistory.queries;elim*=>st0 p0 qs0.
   call(rt_call_f S (AHActualOracles(SecGLogged(FOGActual))) view cost st0 p0 hc).
   clear hc hs hr hd;auto=> />;smt(rt_phase_call).
 + proc*;exists* (view(glob S)),(cost(glob S)),SecGHistory.queries;elim*=>st0 p0 qs0.
   call(rt_call_g_summary S view cost st0 p0 (size qs0) hc).
   clear hc hs hr hd;auto=> />;smt(rt_phase_call).
 + proc*;exists* (view(glob S)),(cost(glob S)),SecGHistory.queries,input;elim*=>st0 p0 qs0 x0.
   call(rt_call_h S (AHActualOracles(SecGLogged(FOGActual))) view cost st0 p0 x0 hc hr).
   clear hc hs hr hd;auto=> />;smt(rt_phase_h).
 + proc*;exists* (view(glob S)),(cost(glob S)),SecGHistory.queries,input,outlen;elim*=>st0 p0 qs0 x0 n0.
   call(rt_call_raw_summary S view cost st0 p0 x0 n0 (size qs0) hc hr).
   clear hc hs hr hd;auto=> />;smt(rt_phase_raw).
 proc*;exists* (view(glob S)),(cost(glob S)),SecGHistory.queries;elim*=>st0 p0 qs0.
 call(rt_call_decap S view cost st0 p0 (size qs0) hc hs hd).
 clear hc hs hr hd;auto=> />;smt(rt_phase_decap).
qed.

op [opaque] rt_transcript_ok(qs:W8.t Array1152.t list)(p:rt_profile) =
 rt_cost_ok p /\ rt_callback_ok p /\ size qs=rt_g_length p /\
 p.`rp_xcalls=0 /\ p.`rp_xvisits=0.
lemma rt_phase_initial pk suffix star :
 rt_phase_ok(ah_initial pk suffix star)rt_zero [].
proof.
 rewrite /rt_phase_ok /rt_adaptive_ok /rt_store_ok /rt_callback_ok.
 rewrite ah_initial_rows /hist_unique /hist_keys /=.
 have hz:=rt_zero_ok.
 by rewrite /rt_zero /rt_g_length /=.
qed.
lemma rt_phase_output st p qs : rt_phase_ok st p qs=>rt_transcript_ok qs p.
proof. rewrite /rt_phase_ok /rt_adaptive_ok /rt_store_ok /rt_transcript_ok;smt(). qed.

lemma rt_wrapper_bound
 (S<:RTHistory {-SecGHistory,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams})
 (A<:CCAExtendedAdversary {-S,-SecGHistory,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams})
 (view:(glob S)->ah_state)(cost:(glob S)->rt_profile) :
 (forall p pk suffix star,hoare[S.init:cost(glob S)=p /\ arg=(pk,suffix,star) ==>
 view(glob S)=ah_initial pk suffix star /\ cost(glob S)=p])=>
 (forall st p ig b,hoare[S.charge_call:view(glob S)=st /\ cost(glob S)=p /\ arg=(ig,b) ==>
 view(glob S)=st /\ cost(glob S)=rt_call p ig b])=>
 (forall st p,hoare[S.snapshot:view(glob S)=st /\ cost(glob S)=p ==>
 res=st /\ view(glob S)=st /\ cost(glob S)=p])=>
 (forall st p x y,hoare[S.record:view(glob S)=st /\ cost(glob S)=p /\ input=x /\ hout=y ==>
 view(glob S)=ah_record_state st x y /\ cost(glob S)=rt_record_cost st p x])=>
 (forall st p v k c,hoare[S.charge_decap:view(glob S)=st /\ cost(glob S)=p /\ arg=(v,k,c) ==>
 view(glob S)=st /\ cost(glob S)=rt_decap p v k c])=>
 hoare[RTWrapper(S,A,AHActualOracles(SecGLogged(FOGActual)),AHRejectD).guess:
 cost(glob S)=rt_zero /\ SecGHistory.queries=[] ==>
 rt_phase_ok(view(glob S))(cost(glob S))SecGHistory.queries].
proof.
 move=>hi hc hs hr hd;proc;call(rt_adversary_invariant S A view cost hc hs hr hd).
 ecall(hi rt_zero pk suffix (Some ct)).
 call(_:true ==>true);first by trivial.
 clear hi hc hs hr hd;auto=> />;smt(rt_phase_initial).
qed.
lemma rt_actual_phase_bound
 (S<:RTHistory {-SecGHistory,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams})
 (A<:CCAExtendedAdversary {-S,-SecGHistory,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams})
 (view:(glob S)->ah_state)(cost:(glob S)->rt_profile) :
 (forall p pk suffix star,hoare[S.init:cost(glob S)=p /\ arg=(pk,suffix,star) ==>
 view(glob S)=ah_initial pk suffix star /\ cost(glob S)=p])=>
 (forall st p ig b,hoare[S.charge_call:view(glob S)=st /\ cost(glob S)=p /\ arg=(ig,b) ==>
 view(glob S)=st /\ cost(glob S)=rt_call p ig b])=>
 (forall st p,hoare[S.snapshot:view(glob S)=st /\ cost(glob S)=p ==>
 res=st /\ view(glob S)=st /\ cost(glob S)=p])=>
 (forall st p x y,hoare[S.record:view(glob S)=st /\ cost(glob S)=p /\ input=x /\ hout=y ==>
 view(glob S)=ah_record_state st x y /\ cost(glob S)=rt_record_cost st p x])=>
 (forall st p v k c,hoare[S.charge_decap:view(glob S)=st /\ cost(glob S)=p /\ arg=(v,k,c) ==>
 view(glob S)=st /\ cost(glob S)=rt_decap p v k c])=>
 hoare[RTActualPhase(S,A,SecGLogged(FOGActual)).run:
 cost(glob S)=rt_zero /\ SecGHistory.queries=[] ==>
 rt_phase_ok(view(glob S))(cost(glob S))SecGHistory.queries].
proof.
 move=>hi hc hs hr hd;proc;call(rt_wrapper_bound S A view cost hi hc hs hr hd).
 call(_:true ==>true);first by trivial. auto.
qed.

lemma rt_metrics_output
 (S<:RTHistory {-SecGHistory,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams})
 (view:(glob S)->ah_state)(cost:(glob S)->rt_profile) :
 (forall st p,hoare[S.metrics:view(glob S)=st /\ cost(glob S)=p ==>
 res=p /\ view(glob S)=st /\ cost(glob S)=p])=>
 hoare[S.metrics:rt_phase_ok(view(glob S))(cost(glob S))SecGHistory.queries ==>
 rt_transcript_ok SecGHistory.queries res /\ cost(glob S)=res].
proof.
 move=>hm;proc*;exists* (view(glob S)),(cost(glob S));elim*=>st0 p0.
 call(hm st0 p0);clear hm;auto=> />;smt(rt_phase_output).
qed.
lemma rt_transcript_bound
 (S<:RTHistory {-SecGHistory,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams})
 (A<:CCAExtendedAdversary {-S,-SecGHistory,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams})
 (view:(glob S)->ah_state)(cost:(glob S)->rt_profile) :
 (forall p pk suffix star,hoare[S.init:cost(glob S)=p /\ arg=(pk,suffix,star) ==>
 view(glob S)=ah_initial pk suffix star /\ cost(glob S)=p])=>
 (forall st p ig b,hoare[S.charge_call:view(glob S)=st /\ cost(glob S)=p /\ arg=(ig,b) ==>
 view(glob S)=st /\ cost(glob S)=rt_call p ig b])=>
 (forall st p,hoare[S.snapshot:view(glob S)=st /\ cost(glob S)=p ==>
 res=st /\ view(glob S)=st /\ cost(glob S)=p])=>
 (forall st p x y,hoare[S.record:view(glob S)=st /\ cost(glob S)=p /\ input=x /\ hout=y ==>
 view(glob S)=ah_record_state st x y /\ cost(glob S)=rt_record_cost st p x])=>
 (forall st p v k c,hoare[S.charge_decap:view(glob S)=st /\ cost(glob S)=p /\ arg=(v,k,c) ==>
 view(glob S)=st /\ cost(glob S)=rt_decap p v k c])=>
 (forall st p,hoare[S.metrics:view(glob S)=st /\ cost(glob S)=p ==>
 res=p /\ view(glob S)=st /\ cost(glob S)=p])=>
 hoare[RTTranscript(S,A).run:cost(glob S)=rt_zero ==>
 rt_transcript_ok res.`1 res.`2 /\ cost(glob S)=res.`2 /\ SecGHistory.queries=res.`1].
proof.
 move=>hi hc hs hr hd hm;proc;wp;call(rt_metrics_output S view cost hm).
 call(rt_actual_phase_bound S A view cost hi hc hs hr hd).
 rnd;inline SecGHistory.init;auto.
qed.
