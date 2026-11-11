require import AllCore List Distr FMap StdOrder StdBigop.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152.
require import NTRUPlus768CPAModel NTRUPlus768CPAReduction.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768ACWC2Oracle.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions NTRUPlus768ROMDomains.
require import NTRUPlus768RawXOF NTRUPlus768RawXOFStreams NTRUPlus768RawXOFSampling NTRUPlus768CCAQueryCodec.
require import NTRUPlus768FOModel NTRUPlus768FOError NTRUPlus768FOQueryBudget NTRUPlus768FOHMonitor NTRUPlus768FOBadBound.
require import NTRUPlus768FOEagerG NTRUPlus768FOGAdapters NTRUPlus768CCAGame NTRUPlus768CCADecapOracle.
require import NTRUPlus768SimModel NTRUPlus768SimSampling NTRUPlus768SimOracles NTRUPlus768SimLookup.
require import NTRUPlus768SimPublicError NTRUPlus768SimPublicBound NTRUPlus768SimPublicInstances.
import RealOrder StdBigop.Bigreal.BRA.

(* The rank is the actual cardinality of the original public H record.
   Cached calls and valid raw zero-output calls still execute the original
   backend. A duplicate H input contributes no new rank increment. *)
op ah_fresh_full (input:W8.t list) (log:(fo_h_input,W8.t Array224.t)fmap) =
 exists x,decode_typed input=Some(H x) /\ x \notin log.
op ah_fresh_raw input outlen log =
 0<=outlen<=raw_xof_max_output /\ ah_fresh_full input log.
op ah_fresh_inv w g (s:sim_public_snapshot) (bad:bool) =
 sim_public_inv w g None s /\ (!bad=>fo_hcache_good w g None s.`4).

(* Identity assignments expose complete public callbacks to FEL. They
   preserve the actual log, including its size and every stored value. *)
module AHFreshOracles : CCAExtendedOraclePort = {
 proc e=SimOracles(FOGActual,SimPublicErrorH(SimHActual)).e
 proc f=SimOracles(FOGActual,SimPublicErrorH(SimHActual)).f
 proc g=SimOracles(FOGActual,SimPublicErrorH(SimHActual)).g
 proc h(input:fo_h_input):W8.t Array224.t = {
  var hout;hout<@SimOracles(FOGActual,SimPublicErrorH(SimHActual)).h(input);
  SimHistory.h<-SimHistory.h;return hout;
 }
 proc raw(input:W8.t list,outlen:int):W8.t list option = {
  var out;out<@SimOracles(FOGActual,SimPublicErrorH(SimHActual)).raw(input,outlen);
  SimHistory.h<-SimHistory.h;return out;
 }
}.
module AHFreshPhase(A:CCAExtendedAdversary) = {
 proc run(w0:keygen_witness,g0:acwc2_g_function,
          pk ct:W8.t Array1152.t,key:W8.t Array32.t):bool = {
  var suffix:W8.t Array32.t;var answer:bool;
  FOContext.w<-w0;FOContext.g<-g0;FOContext.challenge_h<-None;
  SimBad.corr<-false;
  suffix<@ROF.get(pk);SimPublic.init(pk,suffix,ct);SimHistory.init();
  answer<@A(AHFreshOracles,SimLookup(FOGActual)).guess(pk,ct,key);
  return answer;
 }
}.

lemma ah_fresh_full_h input log x : decode_typed input=Some(H x)=>
 ah_fresh_full input log=(x \notin log).
proof. rewrite /ah_fresh_full;smt(). qed.
lemma ah_fresh_full_other input log : (forall x,decode_typed input<>Some(H x))=>
 !ah_fresh_full input log.
proof. rewrite /ah_fresh_full;smt(). qed.

lemma ah_fresh_h_base_exact w0 g0 x0 log0 b0 :
 hoare[SimLoggedH(SimPublicErrorH(SimHActual)).get:
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOContext.challenge_h=None /\
 input=x0 /\ SimHistory.h=log0 /\ SimBad.corr=b0 ==>
 SimHistory.h=log0.[x0<-res] /\
 SimBad.corr=(b0 \/ (x0 \notin log0 /\ fo_base_bad w0 g0 x0.`1 res))].
proof.
 proc;inline SimPublicErrorH(SimHActual).get SimHistory.record.
 wp;call(_:true ==>true);first by trivial.
 auto=> />;smt().
qed.
lemma ah_fresh_h_base_rank w0 g0 x0 log0 b0 :
 hoare[SimLoggedH(SimPublicErrorH(SimHActual)).get:
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOContext.challenge_h=None /\
 input=x0 /\ SimHistory.h=log0 /\ SimBad.corr=b0 ==>
 fsize SimHistory.h=fsize log0+b2i(x0 \notin log0) /\
 (x0 \in log0=>SimBad.corr=b0) /\ (b0=>SimBad.corr)].
proof. conseq(ah_fresh_h_base_exact w0 g0 x0 log0 b0);smt(fsize_set). qed.

lemma ah_fresh_h_rank w0 g0 x0 log0 b0 :
 hoare[AHFreshOracles.h:
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOContext.challenge_h=None /\
 input=x0 /\ SimHistory.h=log0 /\ SimBad.corr=b0 ==>
 fsize SimHistory.h=fsize log0+b2i(x0 \notin log0) /\
 (x0 \in log0=>SimBad.corr=b0) /\ (b0=>SimBad.corr)].
proof. proc;wp;call(ah_fresh_h_base_rank w0 g0 x0 log0 b0);auto. qed.

lemma ah_fresh_raw_full_rank w0 g0 input0 log0 b0 :
 hoare[SimRaw(FOGActual,SimPublicErrorH(SimHActual)).full:
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOContext.challenge_h=None /\
 input=input0 /\ SimHistory.h=log0 /\ SimBad.corr=b0 ==>
 fsize SimHistory.h=fsize log0+b2i(ah_fresh_full input0 log0) /\
 (!ah_fresh_full input0 log0=>SimBad.corr=b0) /\ (b0=>SimBad.corr)].
proof.
 proc;match.
 + call(_:true ==>true);first by trivial.
   auto=> />;rewrite /ah_fresh_full;smt().
 match.
 + call(_:true ==>true);first by trivial.
   auto=> />;rewrite /ah_fresh_full;smt().
 + call(_:true ==>true);first by trivial.
   auto=> />;rewrite /ah_fresh_full;smt().
 + call(_:true ==>true);first by trivial.
   auto=> />;rewrite /ah_fresh_full;smt().
 ecall(ah_fresh_h_base_rank w0 g0 payload log0 b0).
 auto=> />;rewrite /ah_fresh_full;smt().
qed.
lemma ah_fresh_raw_rank w0 g0 input0 outlen0 log0 b0 :
 hoare[AHFreshOracles.raw:
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOContext.challenge_h=None /\
 input=input0 /\ outlen=outlen0 /\ SimHistory.h=log0 /\ SimBad.corr=b0 ==>
 fsize SimHistory.h=fsize log0+b2i(ah_fresh_raw input0 outlen0 log0) /\
 (!ah_fresh_raw input0 outlen0 log0=>SimBad.corr=b0) /\ (b0=>SimBad.corr)].
proof.
 proc;inline SimRaw(FOGActual,SimPublicErrorH(SimHActual)).get;sp;if.
 + wp;call(ah_fresh_raw_full_rank w0 g0 input0 log0 b0);auto=> />;
   rewrite /ah_fresh_raw;smt().
 auto=> />;rewrite /ah_fresh_raw;smt().
qed.

lemma ah_fresh_h_invariant w0 g0 :
 hoare[AHFreshOracles.h:
 ah_fresh_inv w0 g0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) SimBad.corr ==>
 ah_fresh_inv w0 g0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) SimBad.corr].
proof.
 proc;wp;call(_:ah_fresh_inv w0 g0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) SimBad.corr ==>
 ah_fresh_inv w0 g0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) SimBad.corr).
 + conseq [-frame](sim_public_h_state w0 g0 None)(sim_public_logged_good w0 g0 None);
   rewrite /ah_fresh_inv /sim_public_inv;smt().
 auto.
qed.
lemma ah_fresh_raw_invariant w0 g0 :
 hoare[AHFreshOracles.raw:
 ah_fresh_inv w0 g0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) SimBad.corr ==>
 ah_fresh_inv w0 g0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) SimBad.corr].
proof.
 proc;wp;call(sim_public_raw_invariants w0 g0 None);auto=> />;
 rewrite /ah_fresh_inv /sim_public_inv;smt().
qed.


lemma ah_fresh_raw_h input outlen log : ah_fresh_raw input outlen log=>fo_raw_h input outlen.
proof. rewrite /ah_fresh_raw /ah_fresh_full fo_raw_h_classification;smt(). qed.

lemma ah_fresh_h_summary w0 g0 x0 log0 b0 :
 hoare[AHFreshOracles.h:
 ah_fresh_inv w0 g0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) SimBad.corr /\
 input=x0 /\ SimHistory.h=log0 /\ SimBad.corr=b0 ==>
 ah_fresh_inv w0 g0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) SimBad.corr /\
 fsize SimHistory.h=fsize log0+b2i(x0 \notin log0) /\
 (x0 \in log0=>SimBad.corr=b0) /\ (b0=>SimBad.corr)].
proof.
 conseq [-frame](ah_fresh_h_invariant w0 g0)(ah_fresh_h_rank w0 g0 x0 log0 b0);
 rewrite /ah_fresh_inv /sim_public_inv;smt().
qed.
lemma ah_fresh_raw_summary w0 g0 input0 outlen0 log0 b0 :
 hoare[AHFreshOracles.raw:
 ah_fresh_inv w0 g0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) SimBad.corr /\
 input=input0 /\ outlen=outlen0 /\ SimHistory.h=log0 /\ SimBad.corr=b0 ==>
 ah_fresh_inv w0 g0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) SimBad.corr /\
 fsize SimHistory.h=fsize log0+b2i(ah_fresh_raw input0 outlen0 log0) /\
 (!ah_fresh_raw input0 outlen0 log0=>SimBad.corr=b0) /\ (b0=>SimBad.corr)].
proof.
 conseq [-frame](ah_fresh_raw_invariant w0 g0)(ah_fresh_raw_rank w0 g0 input0 outlen0 log0 b0);
 rewrite /ah_fresh_inv /sim_public_inv;smt().
qed.

lemma ah_fresh_h_projection :
 equiv[AHFreshOracles.h ~ SimOracles(FOGActual,SimHActual).h:
 ={input,ROH.m,SimHistory.h} ==> ={res,ROH.m,SimHistory.h}].
proof.
 proc*;inline{1} AHFreshOracles.h;wp;call sim_public_logged_error_projection;auto.
qed.
lemma ah_fresh_raw_projection :
 equiv[AHFreshOracles.raw ~ SimOracles(FOGActual,SimHActual).raw:
 ={arg,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SimHistory.h} ==>
 ={res,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SimHistory.h}].
proof.
 proc*;inline{1} AHFreshOracles.raw;wp;call sim_public_raw_error_projection;auto.
qed.

lemma ah_fresh_adversary_projection
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-FOContext,-SimBad}) :
 equiv[A(AHFreshOracles,SimLookup(FOGActual)).guess ~
 A(SimOracles(FOGActual,SimHActual),SimLookup(FOGActual)).guess:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h} ==>
 ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h}].
proof.
 proc(={ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h})=> //.
 + by sim.
 + by sim.
 + by sim.
 + conseq ah_fresh_h_projection=> /#.
 + conseq ah_fresh_raw_projection=> /#.
 by sim.
qed.
lemma ah_fresh_phase_projection
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-FOContext,-SimBad}) :
 equiv[AHFreshPhase(A).run ~ CPAPhase(A).run:
 ={pk,ct,key,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h} ==>
 ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h}].
proof.
 proc;call(ah_fresh_adversary_projection A).
 inline SimPublic.init SimHistory.init;wp.
 call(_: ={arg,ROF.m} ==> ={res,ROF.m});first by sim.
 auto.
qed.
lemma ah_fresh_phase_count
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-FOContext,-SimBad}) qC :
 hoare[CPAPhase(A).run:true ==>fsize SimHistory.h<=qC]=>
 hoare[AHFreshPhase(A).run:true ==>fsize SimHistory.h<=qC].
proof.
 move=>hcount;conseq(ah_fresh_phase_projection A) hcount.
 + move=> &1 _.
   exists (glob A){1} ROE.m{1} ROF.m{1} ROG.m{1} ROH.m{1}
    RawXOFStreams.es{1} RawXOFStreams.fs{1} RawXOFStreams.gs{1} RawXOFStreams.other{1}
    SimHistory.h{1} SimPublic.count{1} SimPublic.cstar{1} SimPublic.pk{1} SimPublic.suffix{1}
    (pk{1},ct{1},key{1});smt().
 smt().
qed.

lemma ah_fresh_adversary_invariant
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-FOContext,-SimBad}) w0 g0 :
 hoare[A(AHFreshOracles,SimLookup(FOGActual)).guess:
 ah_fresh_inv w0 g0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) SimBad.corr ==>
 ah_fresh_inv w0 g0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) SimBad.corr].
proof.
 proc(ah_fresh_inv w0 g0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) SimBad.corr)=> //.
 + proc*;call(_:true ==>true);first by trivial. auto.
 + proc*;call(_:true ==>true);first by trivial. auto.
 + proc*;call(_:true ==>true);first by trivial. auto.
 + exact(ah_fresh_h_invariant w0 g0).
 + exact(ah_fresh_raw_invariant w0 g0).
 proc*;call(_:true ==>true);first by trivial. auto.
qed.
lemma ah_fresh_phase_good
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-FOContext,-SimBad}) w1 g1 :
 hoare[AHFreshPhase(A).run:w0=w1 /\ g0=g1 /\ ROH.m=empty ==>
 ah_fresh_inv w1 g1 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) SimBad.corr].
proof.
 proc;call(ah_fresh_adversary_invariant A w1 g1).
 inline SimPublic.init SimHistory.init;wp;call(_:true ==>true);first by trivial.
 auto=> />;rewrite /ah_fresh_inv /sim_public_inv /sim_log_included /sim_h_cover /fo_hcache_good;
 smt(emptyE).
qed.

lemma ah_fresh_phase_bounded
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-FOContext,-SimBad})
 w0 g0 qC pk0 ct0 key0 &m :
 0<=qC=>ROH.m{m}=empty=>
 Pr[AHFreshPhase(A).run(w0,g0,pk0,ct0,key0)@&m:
 SimBad.corr /\ fsize SimHistory.h<=qC]<=qC%r*fo_error w0 g0.
proof.
 move=>hq hroh.
 fel 7 (fsize SimHistory.h) (fun _=>fo_error w0 g0) qC SimBad.corr
 [AHFreshOracles.h:(input \notin SimHistory.h);
  AHFreshOracles.raw:(ah_fresh_raw input outlen SimHistory.h)]
 (ah_fresh_inv w0 g0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) SimBad.corr)=> //.
 + by rewrite(fo_fel_cost_sum qC (fo_error w0 g0) hq).
 + inline SimPublic.init SimHistory.init;wp;call(_:true ==>true);first by trivial.
   auto=> />;rewrite ?fsize_empty /ah_fresh_inv /sim_public_inv
    /sim_log_included /sim_h_cover /fo_hcache_good;smt(emptyE).
 + proc;wp;call(sim_public_h_cost w0 g0 None);auto=> />;rewrite /ah_fresh_inv;smt().
 + move=>c;proc*;exists* input,SimHistory.h,SimBad.corr;elim*=>x0 log0 b0.
   call(ah_fresh_h_summary w0 g0 x0 log0 b0);auto=> />;smt().
 + move=>b c;proc*;exists* input,SimHistory.h;elim*=>x0 log0.
   call(ah_fresh_h_summary w0 g0 x0 log0 b);auto=> />;smt().
 + by proc;wp;call(sim_public_raw_bad_bound w0 g0);auto=> />.
 + move=>c;proc*;exists* input,outlen,SimHistory.h,SimBad.corr;elim*=>input0 outlen0 log0 b0.
   call(ah_fresh_raw_summary w0 g0 input0 outlen0 log0 b0);auto=> />;smt().
 move=>b c;proc*;exists* input,outlen,SimHistory.h;elim*=>input0 outlen0 log0.
 call(ah_fresh_raw_summary w0 g0 input0 outlen0 log0 b);auto=> />;smt().
qed.


(* This consumes exactly the original CPA endpoint cardinality contract.
   No assumption bounds the total number of H/raw calls. *)
lemma ah_fresh_phase_bound
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-FOContext,-SimBad})
 w0 g0 qC pk0 ct0 key0 &m :
 0<=qC=>ROH.m{m}=empty=>
 hoare[CPAPhase(A).run:true ==>fsize SimHistory.h<=qC]=>
 Pr[AHFreshPhase(A).run(w0,g0,pk0,ct0,key0)@&m:SimBad.corr]<=qC%r*fo_error w0 g0.
proof.
 move=>hq hroh hc.
 have htail:Pr[AHFreshPhase(A).run(w0,g0,pk0,ct0,key0)@&m:
 SimBad.corr /\ !(fsize SimHistory.h<=qC)]=0%r.
 + byphoare(_:true ==>_)=> //;hoare;conseq(ah_fresh_phase_count A qC hc);smt().
 rewrite Pr[mu_split (fsize SimHistory.h<=qC)] htail /=.
 exact(ah_fresh_phase_bounded A w0 g0 qC pk0 ct0 key0 &m hq hroh).
qed.
lemma ah_fresh_phase_ph
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-FOContext,-SimBad})
 w g qC : 0<=qC=>
 hoare[CPAPhase(A).run:true ==>fsize SimHistory.h<=qC]=>
 phoare[AHFreshPhase(A).run:w0=w /\ g0=g /\ ROH.m=empty ==>SimBad.corr]
 <=(qC%r*fo_error w g).
proof.
 move=>hq hc;bypr=> &m [hw [hg hroh]].
 rewrite hw hg;exact(ah_fresh_phase_bound A w g qC pk{m} ct{m} key{m} &m hq hroh hc).
qed.
