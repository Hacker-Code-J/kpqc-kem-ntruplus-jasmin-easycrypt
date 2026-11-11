require import AllCore List Distr FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152.
require import NTRUPlus768RTModel NTRUPlus768RTStore NTRUPlus768RTOracles NTRUPlus768RTAdaptive.
require import NTRUPlus768AHState NTRUPlus768AHAdapter NTRUPlus768AHActualReduction.
require import NTRUPlus768HistModel NTRUPlus768HistLookup NTRUPlus768FOModel NTRUPlus768FOEagerG.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
require import NTRUPlus768CCAGame NTRUPlus768CCADecapOracle NTRUPlus768CCAStatusAdapter.
require import NTRUPlus768SecGOracles.

(* Equal protocol views are enough. A measured call may change ledger
   fields, so no equality of the complete store globals is assumed. *)
lemma rt_store_snapshot_same (S<:RTHistory)(view:(glob S)->ah_state) :
 islossless S.snapshot=>
 (forall st,hoare[S.snapshot:view(glob S)=st ==>res=st /\ view(glob S)=st])=>
 equiv[S.snapshot ~ S.snapshot:
 view(glob S){1}=view(glob S){2} ==>
 ={res} /\ view(glob S){1}=view(glob S){2}].
proof.
 move=>hl hv;exists* (view(glob S){1});elim*=>st.
 have hc:phoare[S.snapshot:view(glob S)=st ==>res=st /\ view(glob S)=st]=1%r
  by conseq hl(hv st);smt().
 proc*;ecall{1}(hc);ecall{2}(hc);auto=> />;smt().
qed.

lemma rt_store_init_same (S<:RTHistory)(view:(glob S)->ah_state) :
 islossless S.init=>
 (forall pk suffix star,hoare[S.init:arg=(pk,suffix,star) ==>
  view(glob S)=ah_initial pk suffix star])=>
 equiv[S.init ~ S.init:
 ={arg} ==>view(glob S){1}=view(glob S){2}].
proof.
 move=>hl hv;exists* pk{1},suffix{1},cstar{1};elim*=>pk0 suffix0 star0.
 have hc:phoare[S.init:arg=(pk0,suffix0,star0) ==>
  view(glob S)=ah_initial pk0 suffix0 star0]=1%r
  by conseq hl(hv pk0 suffix0 star0);smt().
 proc*;ecall{1}(hc);ecall{2}(hc);auto=> />;smt().
qed.

lemma rt_store_record_same (S<:RTHistory)(view:(glob S)->ah_state) :
 islossless S.record=>
 (forall st x y,hoare[S.record:view(glob S)=st /\ input=x /\ hout=y ==>
  view(glob S)=ah_record_state st x y])=>
 equiv[S.record ~ S.record:
 ={arg} /\ view(glob S){1}=view(glob S){2} ==>
 view(glob S){1}=view(glob S){2}].
proof.
 move=>hl hv;exists* (view(glob S){1}),input{1},hout{1};elim*=>st x y.
 have hc:phoare[S.record:view(glob S)=st /\ input=x /\ hout=y ==>
  view(glob S)=ah_record_state st x y]=1%r
  by conseq hl(hv st x y);smt().
 proc*;ecall{1}(hc);ecall{2}(hc);auto=> />;smt().
qed.

lemma rt_charge_call_view(S<:RTHistory)(view:(glob S)->ah_state) st :
 islossless S.charge_call=>
 (forall st,hoare[S.charge_call:view(glob S)=st ==>view(glob S)=st])=>
 phoare[S.charge_call:view(glob S)=st ==>view(glob S)=st]=1%r.
proof. move=>hl hv;conseq hl(hv st);smt(). qed.
lemma rt_charge_decap_view(S<:RTHistory)(view:(glob S)->ah_state) st :
 islossless S.charge_decap=>
 (forall st,hoare[S.charge_decap:view(glob S)=st ==>view(glob S)=st])=>
 phoare[S.charge_decap:view(glob S)=st ==>view(glob S)=st]=1%r.
proof. move=>hl hv;conseq hl(hv st);smt(). qed.
lemma rt_metrics_view(S<:RTHistory)(view:(glob S)->ah_state) st :
 islossless S.metrics=>
 (forall st,hoare[S.metrics:view(glob S)=st ==>view(glob S)=st])=>
 phoare[S.metrics:view(glob S)=st ==>view(glob S)=st]=1%r.
proof. move=>hl hv;conseq hl(hv st);smt(). qed.

lemma rt_record_h_view_same(S<:RTHistory)(O<:CCAExtendedOraclePort {-S})(view:(glob S)->ah_state) :
 islossless S.record=>
 (forall st x y,hoare[S.record:view(glob S)=st /\ input=x /\ hout=y ==>
 view(glob S)=ah_record_state st x y])=>
 equiv[AHRecordH(S,O).get ~ AHRecordH(S,O).get:
 ={arg,glob O} /\ view(glob S){1}=view(glob S){2} ==>
 ={res,glob O} /\ view(glob S){1}=view(glob S){2}].
proof.
 move=>hl hv;proc;call(rt_store_record_same S view hl hv).
 call(_: ={arg,glob O} ==> ={res,glob O});first by proc true;auto.
 auto.
qed.
lemma rt_ah_raw_view_same(S<:RTHistory)(O<:CCAExtendedOraclePort {-S})(view:(glob S)->ah_state) :
 islossless S.record=>
 (forall st x y,hoare[S.record:view(glob S)=st /\ input=x /\ hout=y ==>
 view(glob S)=ah_record_state st x y])=>
 equiv[AHOracles(S,O).raw ~ AHOracles(S,O).raw:
 ={arg,glob O} /\ view(glob S){1}=view(glob S){2} ==>
 ={res,glob O} /\ view(glob S){1}=view(glob S){2}].
proof.
 move=>hl hv;proc;if=> //.
 + match=> //.
   - call(_: ={arg,glob O} ==> ={res,glob O});first by proc true;auto. auto.
   move=>query1 query2;match;1,2,3,4: by smt().
   - move=>payload1 payload2;call(_: ={arg,glob O} ==> ={res,glob O});first by proc true;auto. auto.
   - move=>payload1 payload2;call(_: ={arg,glob O} ==> ={res,glob O});first by proc true;auto. auto.
   - move=>payload1 payload2;call(_: ={arg,glob O} ==> ={res,glob O});first by proc true;auto. auto.
   move=>payload1 payload2;wp;call(rt_record_h_view_same S O view hl hv);auto=> />;smt().
 call(_: ={arg,glob O} ==> ={res,glob O});first by proc true;auto. auto.
qed.

lemma rt_lookup_context_same(G<:FOGPort)(C<:RTLookupContext {-G}) :
 equiv[C(G).run ~ C(G).run: ={arg,glob C,glob G} ==> ={res,glob C,glob G}].
proof. proc(={glob G})=> //;proc true;auto. qed.
lemma rt_lookup_same(O<:CCAExtendedOraclePort) :
 equiv[HistLookup(AHPublicG(O)).run ~ HistLookup(AHPublicG(O)).run:
 ={arg,glob O} ==> ={res,glob O}].
proof. conseq(rt_lookup_context_same (AHPublicG(O)) HistLookup);smt(). qed.

lemma rt_e_view_projection(S<:RTHistory)(O<:CCAExtendedOraclePort {-S})(view:(glob S)->ah_state) :
 islossless S.charge_call=>
 (forall st,hoare[S.charge_call:view(glob S)=st ==>view(glob S)=st])=>
 equiv[RTOracles(S,O).e ~ O.e:
 ={arg,glob O} /\ view(glob S){1}=view(glob S){2} ==>
 ={res,glob O} /\ view(glob S){1}=view(glob S){2}].
proof.
 move=>hl hv;exists* (view(glob S){1});elim*=>st0.
 proc*;inline{1} RTOracles(S,O).e;wp.
 call(_: ={arg,glob O} ==> ={res,glob O});first by proc true;auto.
 ecall{1}(rt_charge_call_view S view st0 hl hv);auto=> />;smt().
qed.

lemma rt_f_view_projection(S<:RTHistory)(O<:CCAExtendedOraclePort {-S})(view:(glob S)->ah_state) :
 islossless S.charge_call=>
 (forall st,hoare[S.charge_call:view(glob S)=st ==>view(glob S)=st])=>
 equiv[RTOracles(S,O).f ~ O.f:
 ={arg,glob O} /\ view(glob S){1}=view(glob S){2} ==>
 ={res,glob O} /\ view(glob S){1}=view(glob S){2}].
proof.
 move=>hl hv;exists* (view(glob S){1});elim*=>st0.
 proc*;inline{1} RTOracles(S,O).f;wp.
 call(_: ={arg,glob O} ==> ={res,glob O});first by proc true;auto.
 ecall{1}(rt_charge_call_view S view st0 hl hv);auto=> />;smt().
qed.

lemma rt_g_view_projection(S<:RTHistory)(O<:CCAExtendedOraclePort {-S})(view:(glob S)->ah_state) :
 islossless S.charge_call=>
 (forall st,hoare[S.charge_call:view(glob S)=st ==>view(glob S)=st])=>
 equiv[RTOracles(S,O).g ~ O.g:
 ={arg,glob O} /\ view(glob S){1}=view(glob S){2} ==>
 ={res,glob O} /\ view(glob S){1}=view(glob S){2}].
proof.
 move=>hl hv;exists* (view(glob S){1});elim*=>st0.
 proc*;inline{1} RTOracles(S,O).g;wp.
 call(_: ={arg,glob O} ==> ={res,glob O});first by proc true;auto.
 ecall{1}(rt_charge_call_view S view st0 hl hv);auto=> />;smt().
qed.

lemma rt_h_view_projection(S<:RTHistory)(O<:CCAExtendedOraclePort {-S})(view:(glob S)->ah_state) :
 islossless S.charge_call=>islossless S.record=>
 (forall st,hoare[S.charge_call:view(glob S)=st ==>view(glob S)=st])=>
 (forall st x y,hoare[S.record:view(glob S)=st /\ input=x /\ hout=y ==>
 view(glob S)=ah_record_state st x y])=>
 equiv[RTOracles(S,O).h ~ AHOracles(S,O).h:
 ={arg,glob O} /\ view(glob S){1}=view(glob S){2} ==>
 ={res,glob O} /\ view(glob S){1}=view(glob S){2}].
proof.
 move=>cl rl hc hr;exists* (view(glob S){1});elim*=>st0.
 proc*;inline{1} RTOracles(S,O).h;wp.
 call(rt_record_h_view_same S O view rl hr).
 ecall{1}(rt_charge_call_view S view st0 cl hc);auto=> />;smt().
qed.

lemma rt_raw_view_projection(S<:RTHistory)(O<:CCAExtendedOraclePort {-S})(view:(glob S)->ah_state) :
 islossless S.charge_call=>islossless S.record=>
 (forall st,hoare[S.charge_call:view(glob S)=st ==>view(glob S)=st])=>
 (forall st x y,hoare[S.record:view(glob S)=st /\ input=x /\ hout=y ==>
 view(glob S)=ah_record_state st x y])=>
 equiv[RTOracles(S,O).raw ~ AHOracles(S,O).raw:
 ={arg,glob O} /\ view(glob S){1}=view(glob S){2} ==>
 ={res,glob O} /\ view(glob S){1}=view(glob S){2}].
proof.
 move=>cl rl hc hr;exists* (view(glob S){1});elim*=>st0.
 proc*;inline{1} RTOracles(S,O).raw;wp.
 call(rt_ah_raw_view_same S O view rl hr).
 ecall{1}(rt_charge_call_view S view st0 cl hc);auto=> />;smt().
qed.

lemma rt_decap_view_projection(S<:RTHistory)(O<:CCAExtendedOraclePort {-S})(view:(glob S)->ah_state) :
 islossless S.charge_call=>islossless S.snapshot=>islossless S.charge_decap=>
 (forall st,hoare[S.charge_call:view(glob S)=st ==>view(glob S)=st])=>
 (forall st,hoare[S.snapshot:view(glob S)=st ==>res=st /\ view(glob S)=st])=>
 (forall st,hoare[S.charge_decap:view(glob S)=st ==>view(glob S)=st])=>
 equiv[RTDecap(S,O).decap ~ AHDecap(S,O).decap:
 ={arg,glob O} /\ view(glob S){1}=view(glob S){2} ==>
 ={res,glob O} /\ view(glob S){1}=view(glob S){2}].
proof.
 move=>cl sl dl hc hs hd;exists* (view(glob S){1});elim*=>st0.
 have hp:phoare[S.snapshot:view(glob S)=st0 ==>res=st0 /\ view(glob S)=st0]=1%r
  by conseq sl(hs st0);smt().
 proc;wp;ecall{1}(rt_charge_decap_view S view st0 dl hd).
 call(rt_lookup_same O);ecall{1}(hp);ecall{2}(hp);
 ecall{1}(rt_charge_call_view S view st0 cl hc);auto=> />;smt().
qed.

lemma rt_adversary_view_projection
 (S<:RTHistory)(A<:CCAExtendedAdversary {-S})(O<:CCAExtendedOraclePort {-S,-A})
 (view:(glob S)->ah_state) :
 islossless S.snapshot=>islossless S.record=>islossless S.charge_call=>islossless S.charge_decap=>
 (forall st,hoare[S.snapshot:view(glob S)=st ==>res=st /\ view(glob S)=st])=>
 (forall st x y,hoare[S.record:view(glob S)=st /\ input=x /\ hout=y ==>
 view(glob S)=ah_record_state st x y])=>
 (forall st,hoare[S.charge_call:view(glob S)=st ==>view(glob S)=st])=>
 (forall st,hoare[S.charge_decap:view(glob S)=st ==>view(glob S)=st])=>
 equiv[A(RTOracles(S,O),RTDecap(S,O)).guess ~ A(AHOracles(S,O),AHDecap(S,O)).guess:
 ={arg,glob A,glob O} /\ view(glob S){1}=view(glob S){2} ==>
 ={res,glob A,glob O} /\ view(glob S){1}=view(glob S){2}].
proof.
 move=>sl rl cl dl hs hr hc hd.
 proc(={glob O} /\ view(glob S){1}=view(glob S){2})=> //.
 + conseq(rt_e_view_projection S O view cl hc);smt().
 + conseq(rt_f_view_projection S O view cl hc);smt().
 + conseq(rt_g_view_projection S O view cl hc);smt().
 + conseq(rt_h_view_projection S O view cl rl hc hr);smt().
 + conseq(rt_raw_view_projection S O view cl rl hc hr);smt().
 conseq(rt_decap_view_projection S O view cl sl dl hc hs hd);smt().
qed.

lemma rt_wrapper_view_projection
 (S<:RTHistory)(A<:CCAExtendedAdversary {-S})(O<:CCAExtendedOraclePort {-S,-A})(D<:CCADecapPort)
 (view:(glob S)->ah_state) :
 islossless S.init=>islossless S.snapshot=>islossless S.record=>islossless S.charge_call=>islossless S.charge_decap=>
 (forall pk suffix star,hoare[S.init:arg=(pk,suffix,star) ==>
 view(glob S)=ah_initial pk suffix star])=>
 (forall st,hoare[S.snapshot:view(glob S)=st ==>res=st /\ view(glob S)=st])=>
 (forall st x y,hoare[S.record:view(glob S)=st /\ input=x /\ hout=y ==>
 view(glob S)=ah_record_state st x y])=>
 (forall st,hoare[S.charge_call:view(glob S)=st ==>view(glob S)=st])=>
 (forall st,hoare[S.charge_decap:view(glob S)=st ==>view(glob S)=st])=>
 equiv[RTWrapper(S,A,O,D).guess ~ AHWrapper(S,A,O,D).guess:
 ={arg,glob A,glob O} /\ view(glob S){1}=view(glob S){2} ==>
 ={res,glob A,glob O} /\ view(glob S){1}=view(glob S){2}].
proof.
 move=>il sl rl cl dl hi hs hr hc hd;proc.
 call(rt_adversary_view_projection S A O view sl rl cl dl hs hr hc hd).
 call(rt_store_init_same S view il hi).
 call(_: ={arg,glob O} ==> ={res,glob O});first by proc true;auto.
 auto.
qed.

lemma rt_phase_view_projection
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (view:(glob S)->ah_state) :
 islossless S.init=>islossless S.snapshot=>islossless S.record=>islossless S.charge_call=>islossless S.charge_decap=>
 (forall pk suffix star,hoare[S.init:arg=(pk,suffix,star) ==>
 view(glob S)=ah_initial pk suffix star])=>
 (forall st,hoare[S.snapshot:view(glob S)=st ==>res=st /\ view(glob S)=st])=>
 (forall st x y,hoare[S.record:view(glob S)=st /\ input=x /\ hout=y ==>
 view(glob S)=ah_record_state st x y])=>
 (forall st,hoare[S.charge_call:view(glob S)=st ==>view(glob S)=st])=>
 (forall st,hoare[S.charge_decap:view(glob S)=st ==>view(glob S)=st])=>
 equiv[RTActualPhase(S,A,SecGLogged(FOGActual)).run ~ AHActualPhase(S,A,SecGLogged(FOGActual)).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\
 view(glob S){1}=view(glob S){2} ==>
 ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\
 view(glob S){1}=view(glob S){2}].
proof.
 move=>il sl rl cl dl hi hs hr hc hd;proc.
 call(rt_wrapper_view_projection S A (AHActualOracles(SecGLogged(FOGActual))) AHRejectD view
 il sl rl cl dl hi hs hr hc hd).
 call(_: ={arg,ROF.m} ==> ={res,ROF.m});first by sim.
 auto.
qed.

lemma rt_transcript_view_projection
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (view:(glob S)->ah_state) :
 islossless S.init=>islossless S.snapshot=>islossless S.record=>
 islossless S.charge_call=>islossless S.charge_decap=>islossless S.metrics=>
 (forall pk suffix star,hoare[S.init:arg=(pk,suffix,star) ==>
 view(glob S)=ah_initial pk suffix star])=>
 (forall st,hoare[S.snapshot:view(glob S)=st ==>res=st /\ view(glob S)=st])=>
 (forall st x y,hoare[S.record:view(glob S)=st /\ input=x /\ hout=y ==>
 view(glob S)=ah_record_state st x y])=>
 (forall st,hoare[S.charge_call:view(glob S)=st ==>view(glob S)=st])=>
 (forall st,hoare[S.charge_decap:view(glob S)=st ==>view(glob S)=st])=>
 (forall st,hoare[S.metrics:view(glob S)=st ==>view(glob S)=st])=>
 equiv[RTTranscript(S,A).run ~ AHActualTranscript(S,A).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\
 view(glob S){1}=view(glob S){2} ==>
 res{1}.`1=res{2} /\ ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\
 view(glob S){1}=view(glob S){2}].
proof.
 move=>il sl rl cl dl ml hi hs hr hc hd hm;proc.
 seq 3 3:(={glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\
 view(glob S){1}=view(glob S){2}).
 + call(rt_phase_view_projection S A view il sl rl cl dl hi hs hr hc hd).
   rnd;inline SecGHistory.init;auto.
 exists* (view(glob S){1});elim*=>st0.
 ecall{1}(rt_metrics_view S view st0 ml hm);auto=> />;smt().
qed.

(* Public adapter for the same concrete store contracts used by the
   adaptive resource theorem. The ledger may differ in the two worlds. *)
lemma rt_transcript_projection
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (view:(glob S)->ah_state)(cost:(glob S)->rt_profile) :
 islossless S.init=>islossless S.snapshot=>islossless S.record=>
 islossless S.charge_call=>islossless S.charge_decap=>islossless S.metrics=>
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
 equiv[RTTranscript(S,A).run ~ AHActualTranscript(S,A).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\
 view(glob S){1}=view(glob S){2} ==>
 res{1}.`1=res{2} /\ ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\
 view(glob S){1}=view(glob S){2}].
proof.
 move=>il sl rl cl dl ml hi hc hs hr hd hm.
 have hi0:forall pk suffix star,hoare[S.init:arg=(pk,suffix,star) ==>
  view(glob S)=ah_initial pk suffix star].
 + move=>pk0 suffix0 star0;proc*;exists* (cost(glob S));elim*=>p0.
   call(hi p0 pk0 suffix0 star0);auto.
 have hs0:forall st,hoare[S.snapshot:view(glob S)=st ==>res=st /\ view(glob S)=st].
 + move=>st0;proc*;exists* (cost(glob S));elim*=>p0.
   call(hs st0 p0);auto.
 have hr0:forall st x y,hoare[S.record:view(glob S)=st /\ input=x /\ hout=y ==>
  view(glob S)=ah_record_state st x y].
 + move=>st0 x0 y0;proc*;exists* (cost(glob S));elim*=>p0.
   call(hr st0 p0 x0 y0);auto.
 have hc0:forall st,hoare[S.charge_call:view(glob S)=st ==>view(glob S)=st].
 + move=>st0;proc*;exists* (cost(glob S)),is_g,bytes;elim*=>p0 ig b.
   call(hc st0 p0 ig b);auto.
 have hd0:forall st,hoare[S.charge_decap:view(glob S)=st ==>view(glob S)=st].
 + move=>st0;proc*;exists* (cost(glob S)),visits,encryptions,comparisons;elim*=>p0 v k c.
   call(hd st0 p0 v k c);auto.
 have hm0:forall st,hoare[S.metrics:view(glob S)=st ==>view(glob S)=st].
 + move=>st0;proc*;exists* (cost(glob S));elim*=>p0.
   call(hm st0 p0);auto.
 exact(rt_transcript_view_projection S A view il sl rl cl dl ml hi0 hs0 hr0 hc0 hd0 hm0).
qed.
