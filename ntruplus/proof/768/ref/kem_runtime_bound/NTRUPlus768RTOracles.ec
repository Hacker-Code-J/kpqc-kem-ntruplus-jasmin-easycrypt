require import AllCore List Distr FMap StdOrder.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152.
require import NTRUPlus768AHState NTRUPlus768AHAdapter NTRUPlus768AHActualReduction.
require import NTRUPlus768HistModel NTRUPlus768HistLookup NTRUPlus768FOModel.
require import NTRUPlus768FOEagerG NTRUPlus768FOGAdapters NTRUPlus768SimModel NTRUPlus768SimOracles.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions NTRUPlus768ROMDomains.
require import NTRUPlus768RawXOF NTRUPlus768RawXOFStreams NTRUPlus768RawXOFSampling NTRUPlus768CCAQueryCodec.
require import NTRUPlus768CCADecapOracle.
require import NTRUPlus768CCAStatusAdapter NTRUPlus768SecGOracles.
require import NTRUPlus768RTModel NTRUPlus768RTStore.
import IntOrder.

(* A valid raw G call uses G even if the requested output is empty, and
   every repeated query remains in the actual extraction transcript. *)
op rt_raw_g(input:W8.t list)(outlen:int) =
 0<=outlen<=raw_xof_max_output /\ exists x,decode_typed input=Some(G x).
op rt_raw_h(input:W8.t list)(outlen:int) =
 0<=outlen<=raw_xof_max_output /\ exists x,decode_typed input=Some(H x).
op rt_full_g(input:W8.t list) = exists x,decode_typed input=Some(G x).

(* Executable tag/length classification; the existential specification
   above is used only in proofs. No payload is enumerated or chosen. *)
op rt_raw_g_exec(input:W8.t list)(outlen:int) =
 0<=outlen<=raw_xof_max_output /\ size input=1153 /\ nth W8.zero input 0=W8.one.
lemma rt_raw_g_exec_eq input n : rt_raw_g_exec input n=rt_raw_g input n.
proof. rewrite /rt_raw_g_exec /rt_raw_g /decode_typed;smt(tag_zero_neq_one). qed.

(* Charge every public callback exactly once. Internal G calls in
   HistLookup bypass these public entry wrappers and are counted by the
   actual returned encryption count instead. *)
module RTOracles(S:RTHistory,O:CCAExtendedOraclePort) : CCAExtendedOraclePort = {
 proc e(input:W8.t Array32.t):W8.t Array192.t = {
  var out;S.charge_call(false,0);out<@O.e(input);return out;
 }
 proc f(input:W8.t Array1152.t):W8.t Array32.t = {
  var out;S.charge_call(false,0);out<@O.f(input);return out;
 }
 proc g(input:W8.t Array1152.t):W8.t Array192.t = {
  var out;S.charge_call(true,0);out<@O.g(input);return out;
 }
 proc h(input:fo_h_input):W8.t Array224.t = {
  var out;S.charge_call(false,0);out<@AHRecordH(S,O).get(input);return out;
 }
 proc raw(input:W8.t list,outlen:int):W8.t list option = {
  var out;S.charge_call(rt_raw_g_exec input outlen,size input);
  out<@AHOracles(S,O).raw(input,outlen);return out;
 }
}.
module RTDecap(S:RTHistory,O:CCAExtendedOraclePort) : CCADecapPort = {
 proc decap(ct:W8.t Array1152.t):cca_reply = {
  var st:ah_state;var out:cca_reply*int*int*int;
  S.charge_call(false,0);st<@S.snapshot();
  out<@HistLookup(AHPublicG(O)).run(st.`ah_rows,st.`ah_pk,st.`ah_suffix,st.`ah_cstar,ct);
  S.charge_decap(out.`2,out.`3,out.`4);return out.`1;
 }
}.

lemma rt_raw_g_nonnegative input n : 0<=b2i(rt_raw_g input n)<=1.
proof. smt(b2i0 b2i1). qed.
lemma rt_raw_invalid input n : !(0<=n<=raw_xof_max_output)=>
 !rt_raw_g input n /\ !rt_raw_h input n.
proof. rewrite /rt_raw_g /rt_raw_h;smt(). qed.

lemma rt_actual_g_history n0 :
 hoare[AHActualOracles(SecGLogged(FOGActual)).g:
 size SecGHistory.queries=n0 ==>size SecGHistory.queries=n0+1].
proof.
 proc;inline SecGLogged(FOGActual).get;wp;call(_:true ==>true);first by trivial.
 auto=> />;smt().
qed.
lemma rt_raw_stream_g_history n0 :
 hoare[FOGRawStreams(SecGLogged(FOGActual)).g:
 size SecGHistory.queries=n0 ==>size SecGHistory.queries=n0+1].
proof.
 proc;seq 1:(size SecGHistory.queries=n0+1).
 + inline SecGLogged(FOGActual).get;wp;call(_:true ==>true);first by trivial.
   auto=> />;smt().
 if;auto.
qed.
lemma rt_raw_full_history input0 n0 :
 hoare[FOGRaw(SecGLogged(FOGActual)).full:
 input=input0 /\ size SecGHistory.queries=n0 ==>
 size SecGHistory.queries=n0+b2i(rt_full_g input0)].
proof.
 proc;match.
 + call(_:true ==>true);first by trivial.
   auto=> />;rewrite /rt_full_g;smt().
 match.
 + call(_:true ==>true);first by trivial.
   auto=> />;rewrite /rt_full_g;smt().
 + call(_:true ==>true);first by trivial.
   auto=> />;rewrite /rt_full_g;smt().
 + call(rt_raw_stream_g_history n0);auto=> />;rewrite /rt_full_g;smt().
 call(_:true ==>true);first by trivial.
 auto=> />;rewrite /rt_full_g;smt().
qed.
lemma rt_actual_raw_history input0 outlen0 n0 :
 hoare[AHActualOracles(SecGLogged(FOGActual)).raw:
 input=input0 /\ outlen=outlen0 /\ size SecGHistory.queries=n0 ==>
 size SecGHistory.queries=n0+b2i(rt_raw_g input0 outlen0)].
proof.
 proc;sp;if.
 + wp;call(rt_raw_full_history input0 n0);auto=> />;
   rewrite /rt_raw_g /rt_full_g;smt().
 auto=> />;rewrite /rt_raw_g;smt().
qed.

(* This equality keeps the complete real G transcript, not just its size. *)
lemma rt_public_g_projection (G<:FOGPort) :
 equiv[AHPublicG(AHActualOracles(G)).get ~ G.get:
 ={arg,glob G} ==> ={res,glob G}].
proof.
 proc*;inline{1} AHPublicG(AHActualOracles(G)).get AHActualOracles(G).g;wp.
 call(_: ={arg,glob G} ==> ={res,glob G});first by proc true;auto.
 auto.
qed.
module type RTLookupContext(G:FOGPort) = {
 proc run(xs:hist_table,pk:W8.t Array1152.t,suffix:W8.t Array32.t,
 cstar:W8.t Array1152.t option,ct:W8.t Array1152.t):cca_reply*int*int*int {G.get}
}.
lemma rt_lookup_context (G<:FOGPort)(C<:RTLookupContext {-G}) :
 equiv[C(AHPublicG(AHActualOracles(G))).run ~ C(G).run:
 ={arg,glob C,glob G} ==> ={res,glob C,glob G}].
proof. proc(={glob G})=> //;exact(rt_public_g_projection G). qed.
lemma rt_lookup_logged_projection :
 equiv[HistLookup(AHPublicG(AHActualOracles(SecGLogged(FOGActual)))).run ~
 HistLookup(SecGLogged(FOGActual)).run:
 ={arg,ROG.m,SecGHistory.queries} ==> ={res,ROG.m,SecGHistory.queries}].
proof. conseq(rt_lookup_context (SecGLogged(FOGActual)) HistLookup);smt(). qed.
lemma rt_lookup_history n0 :
 hoare[HistLookup(AHPublicG(AHActualOracles(SecGLogged(FOGActual)))).run:
 size SecGHistory.queries=n0 ==>size SecGHistory.queries=n0+res.`3].
proof.
 conseq rt_lookup_logged_projection (hist_lookup_g_calls n0);smt().
qed.

lemma rt_call_e (S<:RTHistory)(O<:CCAExtendedOraclePort {-S})
 (view:(glob S)->ah_state)(cost:(glob S)->rt_profile) st0 p0 :
 (forall st p ig b,hoare[S.charge_call:view(glob S)=st /\ cost(glob S)=p /\ arg=(ig,b) ==>
 view(glob S)=st /\ cost(glob S)=rt_call p ig b])=>
 hoare[RTOracles(S,O).e:view(glob S)=st0 /\ cost(glob S)=p0 ==>
 view(glob S)=st0 /\ cost(glob S)=rt_call p0 false 0].
proof.
 move=>hc;proc;call(_:true ==>true);first by trivial.
 call(hc st0 p0 false 0);auto.
qed.
lemma rt_call_f (S<:RTHistory)(O<:CCAExtendedOraclePort {-S})
 (view:(glob S)->ah_state)(cost:(glob S)->rt_profile) st0 p0 :
 (forall st p ig b,hoare[S.charge_call:view(glob S)=st /\ cost(glob S)=p /\ arg=(ig,b) ==>
 view(glob S)=st /\ cost(glob S)=rt_call p ig b])=>
 hoare[RTOracles(S,O).f:view(glob S)=st0 /\ cost(glob S)=p0 ==>
 view(glob S)=st0 /\ cost(glob S)=rt_call p0 false 0].
proof.
 move=>hc;proc;call(_:true ==>true);first by trivial.
 call(hc st0 p0 false 0);auto.
qed.
lemma rt_call_g (S<:RTHistory)(O<:CCAExtendedOraclePort {-S})
 (view:(glob S)->ah_state)(cost:(glob S)->rt_profile) st0 p0 :
 (forall st p ig b,hoare[S.charge_call:view(glob S)=st /\ cost(glob S)=p /\ arg=(ig,b) ==>
 view(glob S)=st /\ cost(glob S)=rt_call p ig b])=>
 hoare[RTOracles(S,O).g:view(glob S)=st0 /\ cost(glob S)=p0 ==>
 view(glob S)=st0 /\ cost(glob S)=rt_call p0 true 0].
proof.
 move=>hc;proc;call(_:true ==>true);first by trivial.
 call(hc st0 p0 true 0);auto.
qed.
lemma rt_record_h (S<:RTHistory)(O<:CCAExtendedOraclePort {-S})
 (view:(glob S)->ah_state)(cost:(glob S)->rt_profile) st0 p0 x0 :
 (forall st p x y,hoare[S.record:view(glob S)=st /\ cost(glob S)=p /\ input=x /\ hout=y ==>
 view(glob S)=ah_record_state st x y /\ cost(glob S)=rt_record_cost st p x])=>
 hoare[AHRecordH(S,O).get:view(glob S)=st0 /\ cost(glob S)=p0 /\ input=x0 ==>
 view(glob S)=ah_record_state st0 x0 res /\ cost(glob S)=rt_record_cost st0 p0 x0].
proof.
 move=>hr;proc;ecall(hr st0 p0 x0 hout).
 call(_:true ==>true);first by trivial. auto.
qed.
lemma rt_call_h (S<:RTHistory)(O<:CCAExtendedOraclePort {-S})
 (view:(glob S)->ah_state)(cost:(glob S)->rt_profile) st0 p0 x0 :
 (forall st p ig b,hoare[S.charge_call:view(glob S)=st /\ cost(glob S)=p /\ arg=(ig,b) ==>
 view(glob S)=st /\ cost(glob S)=rt_call p ig b])=>
 (forall st p x y,hoare[S.record:view(glob S)=st /\ cost(glob S)=p /\ input=x /\ hout=y ==>
 view(glob S)=ah_record_state st x y /\ cost(glob S)=rt_record_cost st p x])=>
 hoare[RTOracles(S,O).h:view(glob S)=st0 /\ cost(glob S)=p0 /\ input=x0 ==>
 view(glob S)=ah_record_state st0 x0 res /\
 cost(glob S)=rt_record_cost st0 (rt_call p0 false 0) x0].
proof.
 move=>hc hr;proc;call(rt_record_h S O view cost st0 (rt_call p0 false 0) x0 hr).
 call(hc st0 p0 false 0);auto.
qed.

op rt_raw_effect (st0:ah_state)(p0:rt_profile)(input:W8.t list)(n:int)(st:ah_state)(p:rt_profile) =
 (!rt_raw_h input n /\ st=st0 /\ p=rt_call p0 (rt_raw_g input n) (size input)) \/
 (exists x y,0<=n<=raw_xof_max_output /\ decode_typed input=Some(H x) /\
 st=ah_record_state st0 x y /\ p=rt_record_cost st0 (rt_call p0 false (size input)) x).

lemma rt_call_raw (S<:RTHistory)(O<:CCAExtendedOraclePort {-S})
 (view:(glob S)->ah_state)(cost:(glob S)->rt_profile) st0 p0 input0 n0 :
 (forall st p ig b,hoare[S.charge_call:view(glob S)=st /\ cost(glob S)=p /\ arg=(ig,b) ==>
 view(glob S)=st /\ cost(glob S)=rt_call p ig b])=>
 (forall st p x y,hoare[S.record:view(glob S)=st /\ cost(glob S)=p /\ input=x /\ hout=y ==>
 view(glob S)=ah_record_state st x y /\ cost(glob S)=rt_record_cost st p x])=>
 hoare[RTOracles(S,O).raw:
 view(glob S)=st0 /\ cost(glob S)=p0 /\ input=input0 /\ outlen=n0 ==>
 rt_raw_effect st0 p0 input0 n0 (view(glob S)) (cost(glob S))].
proof.
 move=>hc hr;proc;inline AHOracles(S,O).raw.
 seq 1:(view(glob S)=st0 /\ cost(glob S)=rt_call p0 (rt_raw_g input0 n0) (size input0) /\
 input=input0 /\ outlen=n0).
 + call(hc st0 p0 (rt_raw_g input0 n0) (size input0));auto=> />;smt(rt_raw_g_exec_eq).
 sp;if.
 + match.
   - wp;call(_:true ==>true);first by trivial.
     auto=> />;rewrite /rt_raw_effect /rt_raw_h;smt().
   match.
   - wp;call(_:true ==>true);first by trivial.
     auto=> />;rewrite /rt_raw_effect /rt_raw_h;smt().
   - wp;call(_:true ==>true);first by trivial.
     auto=> />;rewrite /rt_raw_effect /rt_raw_h;smt().
   - wp;call(_:true ==>true);first by trivial.
     auto=> />;rewrite /rt_raw_effect /rt_raw_h;smt().
   wp;ecall(rt_record_h S O view cost st0 (rt_call p0 (rt_raw_g input0 n0) (size input0)) payload hr).
   auto=> />;rewrite /rt_raw_effect /rt_raw_g;smt().
 wp;call(_:true ==>true);first by trivial.
 auto=> />;rewrite /rt_raw_effect /rt_raw_h;smt().
qed.

lemma rt_ah_raw_history
 (S<:RTHistory {-SecGHistory,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams}) input0 outlen0 n0 :
 hoare[AHOracles(S,AHActualOracles(SecGLogged(FOGActual))).raw:
 input=input0 /\ outlen=outlen0 /\ size SecGHistory.queries=n0 ==>
 size SecGHistory.queries=n0+b2i(rt_raw_g input0 outlen0)].
proof.
 proc;if.
 + match.
   - call(rt_actual_raw_history input0 outlen0 n0);auto.
   match.
   - call(rt_actual_raw_history input0 outlen0 n0);auto.
   - call(rt_actual_raw_history input0 outlen0 n0);auto.
   - call(rt_actual_raw_history input0 outlen0 n0);auto.
   wp;call(_:true ==>true);first by trivial.
   auto=> />;rewrite /rt_raw_g;smt().
 call(rt_actual_raw_history input0 outlen0 n0);auto.
qed.
lemma rt_call_g_history
 (S<:RTHistory {-SecGHistory,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams}) n0 :
 hoare[RTOracles(S,AHActualOracles(SecGLogged(FOGActual))).g:
 size SecGHistory.queries=n0 ==>size SecGHistory.queries=n0+1].
proof. proc;call(rt_actual_g_history n0);call(_:true ==>true);first by trivial. auto. qed.
lemma rt_call_raw_history
 (S<:RTHistory {-SecGHistory,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams}) input0 outlen0 n0 :
 hoare[RTOracles(S,AHActualOracles(SecGLogged(FOGActual))).raw:
 input=input0 /\ outlen=outlen0 /\ size SecGHistory.queries=n0 ==>
 size SecGHistory.queries=n0+b2i(rt_raw_g input0 outlen0)].
proof.
 proc;call(rt_ah_raw_history S input0 outlen0 n0);call(_:true ==>true);first by trivial. auto.
qed.

lemma rt_lookup_summary xs0 n0 :
 hoare[HistLookup(AHPublicG(AHActualOracles(SecGLogged(FOGActual)))).run:
 xs=xs0 /\ size SecGHistory.queries=n0 ==>
 0<=res.`3 /\ res.`3<=res.`2 /\ res.`2<=size xs0 /\
 0<=res.`4<=1152+32*res.`2+1152*res.`3 /\
 size SecGHistory.queries=n0+res.`3].
proof.
 conseq [-frame](hist_lookup_bounds (AHPublicG(AHActualOracles(SecGLogged(FOGActual)))) xs0)
 (rt_lookup_history n0);smt().
qed.

lemma rt_call_decap
 (S<:RTHistory {-SecGHistory,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams})
 (view:(glob S)->ah_state)(cost:(glob S)->rt_profile) st0 p0 n0 :
 (forall st p ig b,hoare[S.charge_call:view(glob S)=st /\ cost(glob S)=p /\ arg=(ig,b) ==>
 view(glob S)=st /\ cost(glob S)=rt_call p ig b])=>
 (forall st p,hoare[S.snapshot:view(glob S)=st /\ cost(glob S)=p ==>
 res=st /\ view(glob S)=st /\ cost(glob S)=p])=>
 (forall st p v k c,hoare[S.charge_decap:view(glob S)=st /\ cost(glob S)=p /\ arg=(v,k,c) ==>
 view(glob S)=st /\ cost(glob S)=rt_decap p v k c])=>
 hoare[RTDecap(S,AHActualOracles(SecGLogged(FOGActual))).decap:
 view(glob S)=st0 /\ cost(glob S)=p0 /\ size SecGHistory.queries=n0 ==>
 view(glob S)=st0 /\ exists v k c,
 cost(glob S)=rt_decap (rt_call p0 false 0) v k c /\
 0<=k /\ k<=v /\ v<=size st0.`ah_rows /\
 0<=c<=1152+32*v+1152*k /\ size SecGHistory.queries=n0+k].
proof.
 move=>hc hs hd;proc;ecall(hd st0 (rt_call p0 false 0) out.`2 out.`3 out.`4).
 call(rt_lookup_summary st0.`ah_rows n0).
 call(hs st0 (rt_call p0 false 0)).
 call(hc st0 p0 false 0);auto=> />;smt().
qed.

lemma rt_e_ll(S<:RTHistory)(O<:CCAExtendedOraclePort):
 islossless S.charge_call=>islossless O.e=>islossless RTOracles(S,O).e.
proof. move=>hs ho;proc;call ho;call hs;auto. qed.
lemma rt_f_ll(S<:RTHistory)(O<:CCAExtendedOraclePort):
 islossless S.charge_call=>islossless O.f=>islossless RTOracles(S,O).f.
proof. move=>hs ho;proc;call ho;call hs;auto. qed.
lemma rt_g_ll(S<:RTHistory)(O<:CCAExtendedOraclePort):
 islossless S.charge_call=>islossless O.g=>islossless RTOracles(S,O).g.
proof. move=>hs ho;proc;call ho;call hs;auto. qed.
lemma rt_h_ll(S<:RTHistory)(O<:CCAExtendedOraclePort):
 islossless S.charge_call=>islossless S.record=>islossless O.h=>islossless RTOracles(S,O).h.
proof. move=>hc hr ho;proc;call(ah_record_h_ll S O ho hr);call hc;auto. qed.
lemma rt_raw_ll(S<:RTHistory)(O<:CCAExtendedOraclePort):
 islossless S.charge_call=>islossless S.record=>islossless O.h=>islossless O.raw=>
 islossless RTOracles(S,O).raw.
proof. move=>hc hr hh ho;proc;call(ah_oracles_raw_ll S O hh ho hr);call hc;auto. qed.
lemma rt_decap_ll(S<:RTHistory)(O<:CCAExtendedOraclePort):
 islossless S.charge_call=>islossless S.snapshot=>islossless S.charge_decap=>islossless O.g=>
 islossless RTDecap(S,O).decap.
proof.
 move=>hc hs hd hg;proc;call hd;
 call(hist_lookup_lossless (AHPublicG(O)) (ah_public_g_ll O hg));call hs;call hc;auto.
qed.

lemma rt_call_g_summary
 (S<:RTHistory {-SecGHistory,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams})
 (view:(glob S)->ah_state)(cost:(glob S)->rt_profile) st0 p0 n0 :
 (forall st p ig b,hoare[S.charge_call:view(glob S)=st /\ cost(glob S)=p /\ arg=(ig,b) ==>
 view(glob S)=st /\ cost(glob S)=rt_call p ig b])=>
 hoare[RTOracles(S,AHActualOracles(SecGLogged(FOGActual))).g:
 view(glob S)=st0 /\ cost(glob S)=p0 /\ size SecGHistory.queries=n0 ==>
 view(glob S)=st0 /\ cost(glob S)=rt_call p0 true 0 /\ size SecGHistory.queries=n0+1].
proof.
 move=>hc;conseq [-frame]
 (rt_call_g S (AHActualOracles(SecGLogged(FOGActual))) view cost st0 p0 hc)
 (rt_call_g_history S n0);smt().
qed.
lemma rt_call_raw_summary
 (S<:RTHistory {-SecGHistory,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams})
 (view:(glob S)->ah_state)(cost:(glob S)->rt_profile) st0 p0 input0 outlen0 n0 :
 (forall st p ig b,hoare[S.charge_call:view(glob S)=st /\ cost(glob S)=p /\ arg=(ig,b) ==>
 view(glob S)=st /\ cost(glob S)=rt_call p ig b])=>
 (forall st p x y,hoare[S.record:view(glob S)=st /\ cost(glob S)=p /\ input=x /\ hout=y ==>
 view(glob S)=ah_record_state st x y /\ cost(glob S)=rt_record_cost st p x])=>
 hoare[RTOracles(S,AHActualOracles(SecGLogged(FOGActual))).raw:
 view(glob S)=st0 /\ cost(glob S)=p0 /\ input=input0 /\ outlen=outlen0 /\ size SecGHistory.queries=n0 ==>
 rt_raw_effect st0 p0 input0 outlen0 (view(glob S)) (cost(glob S)) /\
 size SecGHistory.queries=n0+b2i(rt_raw_g input0 outlen0)].
proof.
 move=>hc hr;conseq [-frame]
 (rt_call_raw S (AHActualOracles(SecGLogged(FOGActual))) view cost st0 p0 input0 outlen0 hc hr)
 (rt_call_raw_history S input0 outlen0 n0);smt().
qed.
