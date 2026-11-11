require import AllCore List Distr FMap StdOrder.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions NTRUPlus768ROMDomains.
require import NTRUPlus768FOModel NTRUPlus768FOError NTRUPlus768FOQueryBudget NTRUPlus768FOHMonitor.
require import NTRUPlus768RawXOF NTRUPlus768RawXOFStreams NTRUPlus768CCAQueryCodec.
require import NTRUPlus768FOEagerG NTRUPlus768FOGAdapters.
require import NTRUPlus768SimModel NTRUPlus768SimSampling NTRUPlus768SimOracles.
import RealOrder.

lemma sim_h_cover_fresh log table challenge x :
 sim_h_cover log table challenge=>x \notin log=>Some x<>challenge=>x \notin table.
proof. rewrite /sim_h_cover; smt(). qed.

(* Public-only ghost monitor. SimOracles wraps this port in SimLoggedH,
   which records the returned full output afterwards. Internal Decaps and
   challenge H calls must continue to use their unlogged H port. *)
module SimPublicErrorH(H:SimHPort) : SimHPort = {
 proc get(input:fo_h_input) : W8.t Array224.t = {
  var fresh:bool;var hout:W8.t Array224.t;
  fresh<-input \notin SimHistory.h /\ Some input<>FOContext.challenge_h;
  hout <@ H.get(input);
  if(fresh){SimBad.corr<-SimBad.corr \/ fo_base_bad FOContext.w FOContext.g input.`1 hout;}
  return hout;
 }
}.

lemma sim_public_error_ll (H<:SimHPort) :
 islossless H.get=>islossless SimPublicErrorH(H).get.
proof. move=>h;proc;wp;call h;auto. qed.
lemma sim_public_error_projection (H<:SimHPort {-SimBad}) :
 equiv[SimPublicErrorH(H).get ~ H.get: ={input,glob H} ==> ={res,glob H}].
proof.
 proc*;inline{1} SimPublicErrorH(H).get;wp.
 call(_: ={arg,glob H} ==> ={res,glob H});first by proc true;auto.
 auto.
qed.
lemma sim_public_error_latched (H<:SimHPort {-SimBad}) :
 hoare[SimPublicErrorH(H).get:SimBad.corr ==>SimBad.corr].
proof. proc;seq 2:SimBad.corr.
 + call(_:true ==>true);first by trivial. auto.
 if;auto;smt(). qed.
lemma sim_public_error_frame
 (H<:SimHPort {-FOContext,-SimHistory,-SimPublic,-SimBad}) w0 g0 ex0 log0 p0 hidden0 n0 :
 hoare[SimPublicErrorH(H).get:
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOContext.challenge_h=ex0 /\ SimHistory.h=log0 /\
 glob SimPublic=p0 /\ SimBad.hidden=hidden0 /\ SimBad.selected_calls=n0 ==>
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOContext.challenge_h=ex0 /\ SimHistory.h=log0 /\
 glob SimPublic=p0 /\ SimBad.hidden=hidden0 /\ SimBad.selected_calls=n0].
proof. proc;wp;call(_:true ==>true);first by trivial. auto. qed.

(* A missing public record is not, by itself, a fresh H query. The cover
   premise is used in the physically cached branch, where it rules out a
   newly monitored nonchallenge input. Repeated entries are not resampled. *)
lemma sim_public_error_bad_bound w0 g0 :
 phoare[SimPublicErrorH(SimHActual).get:
 FOContext.w=w0 /\ FOContext.g=g0 /\ !SimBad.corr /\
 sim_h_cover SimHistory.h ROH.m FOContext.challenge_h ==>SimBad.corr]
 <=(fo_error w0 g0).
proof.
 have [hn _]:=fo_error_range w0 g0.
 proc;inline ROH.get;sp 2;if.
 + case(input \in SimHistory.h \/ Some input=FOContext.challenge_h).
   - rcondf 4;first by auto=> />;smt().
     conseq(_: _ ==> _ : <=0%r)=> //;hoare;auto;smt().
   rcondt 4;first by auto=> />;smt().
   wp;rnd(fo_base_bad w0 g0 input.`1);skip=> />.
   rewrite ?get_set_sameE /=.
   move=> &hr _ _ _ _;split.
   - exact(fo_base_bad_bound w0 g0 input{hr}.`1).
   move=>_ v _;by rewrite get_set_sameE /=.
 rcondf 2;first by auto=> />;rewrite /sim_h_cover;smt().
 conseq(_: _ ==> _ : <=0%r)=> //;hoare;auto;smt().
qed.

lemma sim_public_logged_error_bad_bound w0 g0 :
 phoare[SimLoggedH(SimPublicErrorH(SimHActual)).get:
 FOContext.w=w0 /\ FOContext.g=g0 /\ !SimBad.corr /\
 sim_h_cover SimHistory.h ROH.m FOContext.challenge_h ==>SimBad.corr]
 <=(fo_error w0 g0).
proof.
 proc;inline SimHistory.record;wp;call(sim_public_error_bad_bound w0 g0);auto.
qed.

lemma sim_public_raw_full_bad_bound w0 g0 :
 phoare[SimRaw(SimGActual,SimPublicErrorH(SimHActual)).full:
 FOContext.w=w0 /\ FOContext.g=g0 /\ !SimBad.corr /\
 sim_h_cover SimHistory.h ROH.m FOContext.challenge_h ==>SimBad.corr]
 <=(fo_error w0 g0).
proof.
 have [hn _]:=fo_error_range w0 g0.
 proc;match.
 + conseq(_: _ ==> _ : <=0%r)=> //;hoare;call(_:true ==>true);first by trivial. auto.
 match.
 + conseq(_: _ ==> _ : <=0%r)=> //;hoare;call(_:true ==>true);first by trivial. auto.
 + conseq(_: _ ==> _ : <=0%r)=> //;hoare;call(_:true ==>true);first by trivial. auto.
 + conseq(_: _ ==> _ : <=0%r)=> //;hoare;call(_:true ==>true);first by trivial. auto.
 call(sim_public_logged_error_bad_bound w0 g0);auto.
qed.
lemma sim_public_raw_bad_bound w0 g0 :
 phoare[SimRaw(SimGActual,SimPublicErrorH(SimHActual)).get:
 FOContext.w=w0 /\ FOContext.g=g0 /\ !SimBad.corr /\
 sim_h_cover SimHistory.h ROH.m FOContext.challenge_h ==>SimBad.corr]
 <=(fo_error w0 g0).
proof.
 have [hn _]:=fo_error_range w0 g0.
 proc;sp 1;if;last by hoare;auto.
 wp;call(sim_public_raw_full_bad_bound w0 g0);auto.
qed.

lemma sim_public_logged_error_projection :
 equiv[SimLoggedH(SimPublicErrorH(SimHActual)).get ~ SimLoggedH(SimHActual).get:
 ={input,ROH.m,SimHistory.h} ==> ={res,ROH.m,SimHistory.h}].
proof.
 proc;inline SimHistory.record SimPublicErrorH(SimHActual).get;sim.
qed.
lemma sim_public_raw_error_projection :
 equiv[SimRaw(SimGActual,SimPublicErrorH(SimHActual)).get ~ SimRaw(SimGActual,SimHActual).get:
 ={arg,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SimHistory.h} ==>
 ={res,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SimHistory.h}].
proof.
 proc;inline SimRaw(SimGActual,SimPublicErrorH(SimHActual)).full SimRaw(SimGActual,SimHActual).full
 SimLoggedH(SimPublicErrorH(SimHActual)).get SimLoggedH(SimHActual).get
 SimPublicErrorH(SimHActual).get SimHistory.record;sim.
qed.

lemma sim_h_cover_set log table ex x y : sim_h_cover log table ex=>
 sim_h_cover log.[x<-y] table.[x<-y] ex.
proof. rewrite /sim_h_cover=>h z;rewrite !mem_set;smt(). qed.
lemma sim_h_actual_update table0 x0 : hoare[SimHActual.get:
 ROH.m=table0 /\ input=x0 ==>ROH.m=table0.[x0<-res]].
proof.
 proc;if;auto=> />.
 + move=>_ r _;by rewrite get_set_sameE.
 move=>hx;apply/eq_sym;apply get_set_id;apply some_oget;move:hx;by rewrite domE.
qed.

lemma sim_public_record_good w g ex log table x y b :
 sim_log_included log table=>table.[x]=Some y=>
 (!b=>fo_hcache_good w g ex log)=>
 !(b \/ (x \notin log /\ Some x<>ex /\ fo_base_bad w g x.`1 y))=>
 fo_hcache_good w g ex log.[x<-y].
proof.
 move=>hl hy hg hb.
 have hnb:!b by smt().
 apply fo_hcache_set;first exact(hg hnb).
 case(Some x=ex)=>hx;first done.
 rewrite /=;case(x \in log)=>hm.
 + have hv:log.[x]=Some(oget log.[x]) by apply some_oget;move:hm;rewrite domE.
   have ht:=hl x (oget log.[x]) hv.
   have ho:Some(oget log.[x])=Some y by rewrite -ht hy.
   have he:oget log.[x]=y by exact(congr1 (fun z:W8.t Array224.t option=>oget z) _ _ ho).
   have hgood:=hg hnb;have h:=hgood x (oget log.[x]) hv hx.
   by move:h;rewrite he.
 by move:hb;rewrite hm hx /=;case b.
qed.

lemma sim_public_logged_cover ex0 :
 hoare[SimLoggedH(SimPublicErrorH(SimHActual)).get:
 sim_h_cover SimHistory.h ROH.m ex0 ==>
 sim_h_cover SimHistory.h ROH.m ex0].
proof.
 proc;inline SimHistory.record SimPublicErrorH(SimHActual).get.
 exists* ROH.m,input;elim*=>table0 x0.
 wp;call(sim_h_actual_update table0 x0);auto;smt(sim_h_cover_set).
qed.
lemma sim_public_logged_included :
 hoare[SimLoggedH(SimPublicErrorH(SimHActual)).get:
 sim_log_included SimHistory.h ROH.m ==>
 sim_log_included SimHistory.h ROH.m].
proof.
 proc;inline SimHistory.record SimPublicErrorH(SimHActual).get.
 exists* ROH.m,input;elim*=>table0 x0.
 wp;call(roh_get_value table0 x0);auto;
 smt(sim_log_set_included sim_log_included_extends).
qed.
lemma sim_public_logged_good w0 g0 ex0 :
 hoare[SimLoggedH(SimPublicErrorH(SimHActual)).get:
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOContext.challenge_h=ex0 /\
 sim_log_included SimHistory.h ROH.m /\
 (!SimBad.corr=>fo_hcache_good w0 g0 ex0 SimHistory.h) ==>
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOContext.challenge_h=ex0 /\
 (!SimBad.corr=>fo_hcache_good w0 g0 ex0 SimHistory.h)].
proof.
 proc;inline SimHistory.record SimPublicErrorH(SimHActual).get.
 exists* ROH.m,input;elim*=>table0 x0.
 wp;call(roh_get_value table0 x0);auto=> />.
 smt(sim_public_record_good sim_log_included_extends).
qed.

lemma sim_public_raw_full_invariants w0 g0 ex0 :
 hoare[SimRaw(SimGActual,SimPublicErrorH(SimHActual)).full:
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOContext.challenge_h=ex0 /\
 sim_log_included SimHistory.h ROH.m /\ sim_h_cover SimHistory.h ROH.m ex0 /\
 (!SimBad.corr=>fo_hcache_good w0 g0 ex0 SimHistory.h) ==>
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOContext.challenge_h=ex0 /\
 sim_log_included SimHistory.h ROH.m /\ sim_h_cover SimHistory.h ROH.m ex0 /\
 (!SimBad.corr=>fo_hcache_good w0 g0 ex0 SimHistory.h)].
proof.
 proc;match.
 + call(_:true ==>true);first by trivial. auto.
 match.
 + call(_:true ==>true);first by trivial. auto.
 + call(_:true ==>true);first by trivial. auto.
 + call(_:true ==>true);first by trivial. auto.
 call(_:FOContext.w=w0 /\ FOContext.g=g0 /\ FOContext.challenge_h=ex0 /\
 sim_log_included SimHistory.h ROH.m /\ sim_h_cover SimHistory.h ROH.m ex0 /\
 (!SimBad.corr=>fo_hcache_good w0 g0 ex0 SimHistory.h) ==>
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOContext.challenge_h=ex0 /\
 sim_log_included SimHistory.h ROH.m /\ sim_h_cover SimHistory.h ROH.m ex0 /\
 (!SimBad.corr=>fo_hcache_good w0 g0 ex0 SimHistory.h)).
 + conseq(sim_public_logged_good w0 g0 ex0)
   (_:sim_log_included SimHistory.h ROH.m /\ sim_h_cover SimHistory.h ROH.m ex0 ==>
      sim_log_included SimHistory.h ROH.m /\ sim_h_cover SimHistory.h ROH.m ex0);1,2:smt().
   conseq sim_public_logged_included (sim_public_logged_cover ex0);smt().
 auto.
qed.
lemma sim_public_raw_invariants w0 g0 ex0 :
 hoare[SimRaw(SimGActual,SimPublicErrorH(SimHActual)).get:
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOContext.challenge_h=ex0 /\
 sim_log_included SimHistory.h ROH.m /\ sim_h_cover SimHistory.h ROH.m ex0 /\
 (!SimBad.corr=>fo_hcache_good w0 g0 ex0 SimHistory.h) ==>
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOContext.challenge_h=ex0 /\
 sim_log_included SimHistory.h ROH.m /\ sim_h_cover SimHistory.h ROH.m ex0 /\
 (!SimBad.corr=>fo_hcache_good w0 g0 ex0 SimHistory.h)].
proof.
 proc;sp 1;if;last by auto. wp;call(sim_public_raw_full_invariants w0 g0 ex0);auto.
qed.
