require import AllCore List Distr FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array768 Array1152.
require import NTRUPlus768RTModel NTRUPlus768RTStore NTRUPlus768RTKernelTypes.
require import NTRUPlus768RTOracles NTRUPlus768RTAdaptive NTRUPlus768RTKernels NTRUPlus768RTView.
require import NTRUPlus768AHState NTRUPlus768AHAdapter NTRUPlus768AHActualReduction.
require import NTRUPlus768HistLookup NTRUPlus768CostExtract.
require import NTRUPlus768SecModel NTRUPlus768SecExtract NTRUPlus768SecExtractModel.
require import NTRUPlus768SecBaseGames NTRUPlus768SecGOracles.
require import NTRUPlus768PKEModel NTRUPlus768PKEKeyDistribution NTRUPlus768EncapGuardSpec.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions.
require import NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
require import NTRUPlus768CCAGame NTRUPlus768CCADecapOracle NTRUPlus768CCAOraclePorts.
require import NTRUPlus768FOModel NTRUPlus768FOEagerG.

(* The real extractor runs once. Its returned visit count, including
   unsuccessful candidates, is charged before the answer is returned. *)
module RTExtract(S:RTHistory) = {
 proc run(pk ct:W8.t Array1152.t,excluded:pke_poly option,
          queries:W8.t Array1152.t list):(pke_poly*pke_poly) option = {
  var out:((pke_poly*pke_poly) option)*int;
  out<@CostExtract.run(pk,ct,excluded,queries);
  S.charge_extract(out.`2);
  return out.`1;
 }
}.

(* This local certificate accounts for the actual two psi samples and
   the one challenge encryption inside an INJ-reducer invocation. The
   outer reducer multiplies it by its actual 0/1 invocation count. *)
op rt_inj_inner_profile : rt_kernel_profile = rtk_profile 0 0 0 0 1 0 0 0 2 0.
module RTMeasuredINJ(S:RTHistory,A:CCAExtendedAdversary) = {
 proc measure(pk:W8.t Array1152.t):sec_collision*rt_kernel_profile = {
  var code,r:pke_poly;var draws:int;var enc:W8.t Array1152.t*rt_kernel_profile;
  var transcript:W8.t Array1152.t list*rt_profile;
  var out:(pke_poly*pke_poly) option;var collision:sec_collision;
  draws<-0;
  code<$pke_psi1;draws<-draws+1;
  r<$pke_psi1;draws<-draws+1;
  enc<@RTEncrypt.run(pk,code,r);
  transcript<@RTTranscript(S,A).run(pk,enc.`1);
  out<@RTExtract(S).run(pk,enc.`1,Some r,transcript.`1);
  collision<-if out=None then (code,code,r,r) else (code,(oget out).`1,r,(oget out).`2);
  return(collision,rtk_add enc.`2(rtk_profile 0 0 0 0 0 0 0 0 draws 0));
 }
 proc run(pk:W8.t Array1152.t):sec_collision = {
  var out:sec_collision*rt_kernel_profile;
  out<@measure(pk);return out.`1;
 }
}.
module RTMeasuredOW(S:RTHistory,A:CCAExtendedAdversary) = {
 proc run(pk ct:W8.t Array1152.t):pke_poly = {
  var transcript:W8.t Array1152.t list*rt_profile;
  var out:(pke_poly*pke_poly) option;
  transcript<@RTTranscript(S,A).run(pk,ct);
  out<@RTExtract(S).run(pk,ct,None,transcript.`1);
  return if out=None then sec_zero else (oget out).`1;
 }
}.
module RTAuxINJ(S:RTHistory,A:CCAExtendedAdversary)=SecINJAuxAdapter(RTMeasuredINJ(S,A)).
module RTAuxOW(S:RTHistory,A:CCAExtendedAdversary)=SecOWAuxAdapter(RTMeasuredOW(S,A)).

lemma rt_inj_inner_profile_exact (S<:RTHistory)(A<:CCAExtendedAdversary) :
 hoare[RTMeasuredINJ(S,A).measure:true ==>res.`2=rt_inj_inner_profile].
proof.
 proc;wp;call(_:true ==>true);first by trivial.
 call(_:true ==>true);first by trivial.
 call rt_encrypt_profile.
 wp;rnd;wp;rnd;auto=> />.
 rewrite /rt_inj_inner_profile /rtk_add /rtk_profile /=.
 smt().
qed.

lemma rt_extract_ll (S<:RTHistory) :
 islossless S.charge_extract=>islossless RTExtract(S).run.
proof. move=>hl;proc;call hl;call cost_extract_ll;auto. qed.

lemma rt_extract_projection (S<:RTHistory)(view:(glob S)->ah_state) st0 :
 islossless S.charge_extract=>
 (forall st n,hoare[S.charge_extract:view(glob S)=st /\ visits=n ==>view(glob S)=st])=>
 equiv[RTExtract(S).run ~ SecExtract.run:
 ={arg} /\ view(glob S){1}=st0 ==>
 ={res} /\ view(glob S){1}=st0].
proof.
 move=>hl hv.
 have hc:forall n,phoare[S.charge_extract:view(glob S)=st0 /\ visits=n ==>
  view(glob S)=st0]=1%r by move=>n;conseq hl(hv st0 n).
 proc*;inline{1} RTExtract(S).run;wp.
 ecall{1}(hc out{1}.`2);call cost_extract_projection;auto.
qed.

lemma rt_extract_profile_exact
 (S<:RTHistory)(view:(glob S)->ah_state)(cost:(glob S)->rt_profile)
 st0 p0 pk0 ct0 ex0 qs0 :
 (forall st p n,hoare[S.charge_extract:
 view(glob S)=st /\ cost(glob S)=p /\ visits=n ==>
 view(glob S)=st /\ cost(glob S)=rt_extract p n])=>
 hoare[RTExtract(S).run:
 view(glob S)=st0 /\ cost(glob S)=p0 /\ pk=pk0 /\ ct=ct0 /\ excluded=ex0 /\ queries=qs0 ==>
 view(glob S)=st0 /\
 cost(glob S)=rt_extract p0(cost_first_visits(sec_eligible pk0 ct0 ex0)qs0)].
proof.
 move=>hc;proc;ecall(hc st0 p0 out.`2).
 call(cost_extract_visits pk0 ct0 ex0 qs0);auto=> />;smt().
qed.

lemma rt_extract_profile_bound
 (S<:RTHistory)(view:(glob S)->ah_state)(cost:(glob S)->rt_profile)
 st0 p0 pk0 ct0 ex0 qs0 :
 rt_cost_ok p0=>size qs0=rt_g_length p0=>
 (forall st p n,hoare[S.charge_extract:
 view(glob S)=st /\ cost(glob S)=p /\ visits=n ==>
 view(glob S)=st /\ cost(glob S)=rt_extract p n])=>
 hoare[RTExtract(S).run:
 view(glob S)=st0 /\ cost(glob S)=p0 /\ pk=pk0 /\ ct=ct0 /\ excluded=ex0 /\ queries=qs0 ==>
 rt_cost_ok(cost(glob S)) /\
 (cost(glob S)).`rp_xcalls=p0.`rp_xcalls+1 /\
 (cost(glob S)).`rp_xvisits=p0.`rp_xvisits+
  cost_first_visits(sec_eligible pk0 ct0 ex0)qs0 /\
 rt_g_length(cost(glob S))=rt_g_length p0].
proof.
 move=>hp hn hc;conseq(rt_extract_profile_exact S view cost st0 p0 pk0 ct0 ex0 qs0 hc)=> //.
 move=> &hr _ gs [hview ->].
 have hv:0<=cost_first_visits(sec_eligible pk0 ct0 ex0)qs0<=rt_g_length p0
  by rewrite -hn;exact(cost_first_visits_bounds _ _).
 have ho:=rt_extract_ok p0 _ hp hv.
 rewrite rt_extract_g_length;split;first exact ho.
 by rewrite /rt_extract.
qed.


lemma rt_extract_view_projection(S<:RTHistory)(view:(glob S)->ah_state) :
 islossless S.charge_extract=>
 (forall st n,hoare[S.charge_extract:view(glob S)=st /\ visits=n ==>view(glob S)=st])=>
 equiv[RTExtract(S).run ~ SecExtract.run:
 ={arg} /\ view(glob S){1}=view(glob S){2} ==>
 ={res} /\ view(glob S){1}=view(glob S){2}].
proof.
 move=>hl hv;proc*;exists* (view(glob S){2});elim*=>st.
 call(rt_extract_projection S view st hl hv);auto.
qed.

lemma rt_inj_reducer_projection
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (view:(glob S)->ah_state) :
 islossless S.charge_extract=>
 (forall st n,hoare[S.charge_extract:view(glob S)=st /\ visits=n ==>view(glob S)=st])=>
 equiv[RTTranscript(S,A).run ~ AHActualTranscript(S,A).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2} ==>
 res{1}.`1=res{2} /\ ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2}]=>
 equiv[RTMeasuredINJ(S,A).run ~ AHActualINJReducer(S,A).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2} /\ encap_key_canonical pk{1} ==>
 ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2}].
proof.
 move=>xl hx ht.
 proc*;inline RTMeasuredINJ(S,A).run RTMeasuredINJ(S,A).measure AHActualINJReducer(S,A).run.
 wp;call(rt_extract_view_projection S view xl hx);call ht;wp.
 ecall{1}(rt_encrypt_correct pk1{1} code{1} r0{1}).
 wp;rnd;wp;rnd;auto=> />.
 move=> &1 &2 hview hk code hc r hr.
 split;[rewrite /pke_domain;exact(pke_psi1_trits code hc)|].
 rewrite /pke_domain;exact(pke_psi1_trits r hr).
qed.

lemma rt_ow_reducer_projection
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (view:(glob S)->ah_state) :
 islossless S.charge_extract=>
 (forall st n,hoare[S.charge_extract:view(glob S)=st /\ visits=n ==>view(glob S)=st])=>
 equiv[RTTranscript(S,A).run ~ AHActualTranscript(S,A).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2} ==>
 res{1}.`1=res{2} /\ ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2}]=>
 equiv[RTMeasuredOW(S,A).run ~ AHActualOWReducer(S,A).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2} ==>
 ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2}].
proof.
 move=>xl hx ht.
 proc;wp;call(rt_extract_view_projection S view xl hx);call ht;auto.
qed.

lemma rt_inj_aux_projection
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (view:(glob S)->ah_state) :
 islossless S.charge_extract=>
 (forall st n,hoare[S.charge_extract:view(glob S)=st /\ visits=n ==>view(glob S)=st])=>
 equiv[RTTranscript(S,A).run ~ AHActualTranscript(S,A).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2} ==>
 res{1}.`1=res{2} /\ ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2}]=>
 equiv[RTAuxINJ(S,A).run ~ SecINJAuxAdapter(AHActualINJReducer(S,A)).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2} /\ encap_key_canonical pk{1} ==>
 ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2}].
proof.
 move=>xl hx ht;proc;call(rt_inj_reducer_projection S A view xl hx ht).
 call(_: ={arg,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams} ==>
 ={glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams});first by sim.
 auto.
qed.

lemma rt_ow_aux_projection
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (view:(glob S)->ah_state) :
 islossless S.charge_extract=>
 (forall st n,hoare[S.charge_extract:view(glob S)=st /\ visits=n ==>view(glob S)=st])=>
 equiv[RTTranscript(S,A).run ~ AHActualTranscript(S,A).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2} ==>
 res{1}.`1=res{2} /\ ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2}]=>
 equiv[RTAuxOW(S,A).run ~ SecOWAuxAdapter(AHActualOWReducer(S,A)).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2} ==>
 ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} /\ view(glob S){1}=view(glob S){2}].
proof.
 move=>xl hx ht;proc;call(rt_ow_reducer_projection S A view xl hx ht).
 call(_: ={arg,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams} ==>
 ={glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams});first by sim.
 auto.
qed.

(* Exactly one extractor call follows a completed transcript. The
   transcript theorem counts all adaptive callbacks, and the scan is
   bounded by that same execution's concrete G-query list. *)
op [opaque] rt_reducer_profile(p:rt_profile) =
 rt_cost_ok p /\ rt_callback_ok p /\ p.`rp_xcalls=1.
lemma rt_extracted_transcript_ok pk ct ex qs p : rt_transcript_ok qs p=>
 rt_reducer_profile(rt_extract p(cost_first_visits(sec_eligible pk ct ex)qs)).
proof.
 rewrite /rt_transcript_ok;move=>[hp [hc [hn [hx hv]]]].
 have hn0:0<=cost_first_visits(sec_eligible pk ct ex)qs<=rt_g_length p
  by rewrite -hn;exact(cost_first_visits_bounds _ _).
 have ho:=rt_extract_ok p _ hp hn0.
 rewrite /rt_reducer_profile;split;first exact ho.
 by move:hc;rewrite /rt_callback_ok /rt_extract hx /=.
qed.

lemma rt_inj_reducer_profile
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (view:(glob S)->ah_state)(cost:(glob S)->rt_profile) :
 (forall st p n,hoare[S.charge_extract:
 view(glob S)=st /\ cost(glob S)=p /\ visits=n ==>
 view(glob S)=st /\ cost(glob S)=rt_extract p n])=>
 hoare[RTTranscript(S,A).run:cost(glob S)=rt_zero ==>
 rt_transcript_ok res.`1 res.`2 /\ cost(glob S)=res.`2 /\ SecGHistory.queries=res.`1]=>
 hoare[RTMeasuredINJ(S,A).run:cost(glob S)=rt_zero ==>rt_reducer_profile(cost(glob S))].
proof.
 move=>hx hb;proc;inline RTMeasuredINJ(S,A).measure;wp.
 seq 8:(rt_transcript_ok transcript.`1 transcript.`2 /\ cost(glob S)=transcript.`2).
 + call hb;call(_:true ==>true);first by trivial.
   wp;rnd;wp;rnd;auto.
 exists* (view(glob S)),transcript.`1,transcript.`2,pk0,enc.`1,(Some r);
 elim*=>st0 qs0 p0 pkv ctv exv.
 ecall(rt_extract_profile_exact S view cost st0 p0 pkv ctv exv qs0 hx).
 clear hx hb;auto=> />;smt(rt_extracted_transcript_ok).
qed.

lemma rt_ow_reducer_profile
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (view:(glob S)->ah_state)(cost:(glob S)->rt_profile) :
 (forall st p n,hoare[S.charge_extract:
 view(glob S)=st /\ cost(glob S)=p /\ visits=n ==>
 view(glob S)=st /\ cost(glob S)=rt_extract p n])=>
 hoare[RTTranscript(S,A).run:cost(glob S)=rt_zero ==>
 rt_transcript_ok res.`1 res.`2 /\ cost(glob S)=res.`2 /\ SecGHistory.queries=res.`1]=>
 hoare[RTMeasuredOW(S,A).run:cost(glob S)=rt_zero ==>rt_reducer_profile(cost(glob S))].
proof.
 move=>hx hb;proc;wp.
 seq 1:(rt_transcript_ok transcript.`1 transcript.`2 /\ cost(glob S)=transcript.`2).
 + call hb;auto.
 exists* (view(glob S)),transcript.`1,transcript.`2,pk,ct,(None<:pke_poly>);
 elim*=>st0 qs0 p0 pk0 ct0 ex0.
 ecall(rt_extract_profile_exact S view cost st0 p0 pk0 ct0 ex0 qs0 hx).
 clear hx hb;auto=> />;smt(rt_extracted_transcript_ok).
qed.

lemma rt_inj_aux_profile
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (view:(glob S)->ah_state)(cost:(glob S)->rt_profile) :
 (forall st p n,hoare[S.charge_extract:
 view(glob S)=st /\ cost(glob S)=p /\ visits=n ==>
 view(glob S)=st /\ cost(glob S)=rt_extract p n])=>
 hoare[RTTranscript(S,A).run:cost(glob S)=rt_zero ==>
 rt_transcript_ok res.`1 res.`2 /\ cost(glob S)=res.`2 /\ SecGHistory.queries=res.`1]=>
 hoare[RTAuxINJ(S,A).run:cost(glob S)=rt_zero ==>rt_reducer_profile(cost(glob S))].
proof.
 move=>hx hb;proc;call(rt_inj_reducer_profile S A view cost hx hb).
 call(_:true ==>true);first by trivial.
 auto.
qed.

lemma rt_ow_aux_profile
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (view:(glob S)->ah_state)(cost:(glob S)->rt_profile) :
 (forall st p n,hoare[S.charge_extract:
 view(glob S)=st /\ cost(glob S)=p /\ visits=n ==>
 view(glob S)=st /\ cost(glob S)=rt_extract p n])=>
 hoare[RTTranscript(S,A).run:cost(glob S)=rt_zero ==>
 rt_transcript_ok res.`1 res.`2 /\ cost(glob S)=res.`2 /\ SecGHistory.queries=res.`1]=>
 hoare[RTAuxOW(S,A).run:cost(glob S)=rt_zero ==>rt_reducer_profile(cost(glob S))].
proof.
 move=>hx hb;proc;call(rt_ow_reducer_profile S A view cost hx hb).
 call(_:true ==>true);first by trivial.
 auto.
qed.
