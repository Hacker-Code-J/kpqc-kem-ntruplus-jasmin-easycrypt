require import AllCore List Distr FMap StdOrder.
from Jasmin require import JWord.
require import Array32 Array96 Array129 Array192 Array224 Array1152.
require import NTRUPlus768ROMDistributions NTRUPlus768ROMOracles NTRUPlus768ROMDomains.
require import NTRUPlus768CCAOraclePorts NTRUPlus768CCAQueryCodec.
require import NTRUPlus768RawXOFSampling NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
require import NTRUPlus768FOModel NTRUPlus768FOError.
require import NTRUPlus768FOQueryBudget.
import RealOrder.

(* The original lazy oracle determines every response and cache update.
   Only fresh nonchallenge entries change the private bad monitor. *)
module FOHMonitor = {
 proc get(input:fo_h_input) : W8.t Array224.t = {
  var fresh:bool; var result:W8.t Array224.t;
  fresh <- input \notin ROH.m /\ Some input<>FOContext.challenge_h;
  result <@ ROH.get(input);
  if(fresh){
   FOBadState.fresh <- FOBadState.fresh+1;
   FOBadState.bad <- FOBadState.bad \/ fo_base_bad FOContext.w FOContext.g input.`1 result;
  }
  return result;
 }
}.
module FOSHAKEH = {
 proc shake(input:W8.t Array129.t) : W8.t Array224.t = {
  var result:W8.t Array224.t;
  result <@ FOHMonitor.get(peel_h input);
  return result;
 }
}.

(* Raw requests keep the existing typed classification and suffix caches.
   The H branch shares the same monitored ROH table as internal Decaps. *)
module FOHRawXOF = {
 proc full(input:W8.t list) : W8.t Array224.t = {
  var stream:W8.t Array224.t;
  match decode_typed input with
  | None => {stream <@ RawXOFStreams.untyped(input);}
  | Some query => {
   match query with
   | E seed => {stream <@ RawXOFStreams.e(seed);}
   | F pk => {stream <@ RawXOFStreams.f(pk);}
   | G serialized => {stream <@ RawXOFStreams.g(serialized);}
   | H payload => {stream <@ FOHMonitor.get(payload);}
   end;
  }
  end;
  return stream;
 }
 proc get(input:W8.t list,outlen:int) : W8.t list option = {
  var result:W8.t list option; var stream:W8.t Array224.t;
  result <- None;
  if(0<=outlen<=raw_xof_max_output){
   stream <@ full(input); result <- Some(raw_xof_output outlen stream);
  }
  return result;
 }
}.
module FOSharedOracles : CCAExtendedOraclePort = {
 proc e=SharedCCAExtendedOracles.e
 proc f=SharedCCAExtendedOracles.f
 proc g=SharedCCAExtendedOracles.g
 proc h=FOHMonitor.get
 proc raw=FOHRawXOF.get
}.

lemma fo_hcache_empty w g ex : fo_hcache_good w g ex empty.
proof. rewrite /fo_hcache_good; smt(emptyE). qed.
lemma fo_hcache_set w g ex m x y :
 fo_hcache_good w g ex m =>
 (Some x=ex \/ !fo_base_bad w g x.`1 y) =>
 fo_hcache_good w g ex m.[x<-y].
proof.
 rewrite /fo_hcache_good=>hm hy z v.
 case(z=x)=>[->|hne].
 + rewrite get_set_sameE.
   move=>heq he.
   have hv:y=v by move:(congr1 (fun z:W8.t Array224.t option=>oget z) _ _ heq); rewrite /=.
   rewrite -hv.
   case hy=>[hc|hb]; last exact hb.
   by move:he; rewrite hc.
 rewrite get_setE hne /=.
 exact(hm z v).
qed.

lemma fo_hmonitor_ll : islossless FOHMonitor.get.
proof. proc; seq 2:true; 1,4,5:by auto. by call roh_get_ll; auto. if; auto. qed.
lemma fo_shakeh_ll : islossless FOSHAKEH.shake.
proof. proc; call fo_hmonitor_ll; auto. qed.

lemma fo_hmonitor_projection :
 equiv[FOHMonitor.get ~ ROH.get : ={input,ROH.m} ==> ={res,ROH.m}].
proof.
 proc; inline{1} ROH.get; sp 2 0.
 seq 2 1 : (result{1}=oget ROH.m{2}.[input{2}] /\ ={ROH.m}).
 + wp; if; auto.
 if{1}; auto.
qed.
lemma fo_shakeh_projection :
 equiv[FOSHAKEH.shake ~ SHAKEHROM.shake : ={input,ROH.m} ==> ={res,ROH.m}].
proof. proc; call fo_hmonitor_projection; auto. qed.

lemma fo_hmonitor_context w0 g0 ex0 : hoare[FOHMonitor.get:
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOContext.challenge_h=ex0 ==>
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOContext.challenge_h=ex0].
proof.
 proc; seq 2 : (FOContext.w=w0 /\ FOContext.g=g0 /\ FOContext.challenge_h=ex0).
 + call(_:true ==>true); first by trivial. auto.
 if; auto.
qed.

lemma fo_hmonitor_value x0 : hoare[FOHMonitor.get:input=x0 ==>
 ROH.m.[x0]=Some res].
proof.
 proc; seq 2 : (ROH.m.[x0]=Some result).
 + ecall(roh_get_value ROH.m x0); auto.
 if; auto.
qed.

lemma fo_hmonitor_fresh_exact n0 m0 x0 ex0 : hoare[FOHMonitor.get:
 FOBadState.fresh=n0 /\ ROH.m=m0 /\ input=x0 /\ FOContext.challenge_h=ex0 ==>
 FOBadState.fresh=n0+b2i(x0 \notin m0 /\ Some x0<>ex0)].
proof.
 proc; seq 2 : (fresh=(x0 \notin m0 /\ Some x0<>ex0) /\ FOBadState.fresh=n0).
 + call(_:true ==>true); first by trivial. auto.
 if; auto; smt().
qed.
lemma fo_hmonitor_fresh_step n0 : hoare[FOHMonitor.get:FOBadState.fresh=n0 ==>
 n0<=FOBadState.fresh<=n0+1].
proof.
 proc; seq 2 : (FOBadState.fresh=n0).
 + call(_:true ==>true); first by trivial. auto.
 if; auto; smt().
qed.
lemma fo_hmonitor_bad_latched : hoare[FOHMonitor.get:FOBadState.bad ==>FOBadState.bad].
proof.
 proc; seq 2 : FOBadState.bad.
 + call(_:true ==>true); first by trivial. auto.
 if; auto; smt().
qed.

lemma fo_hmonitor_invariant w0 g0 ex0 : hoare[FOHMonitor.get:
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOContext.challenge_h=ex0 /\
 (!FOBadState.bad =>fo_hcache_good w0 g0 ex0 ROH.m) ==>
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOContext.challenge_h=ex0 /\
 (!FOBadState.bad =>fo_hcache_good w0 g0 ex0 ROH.m)].
proof.
 proc; inline ROH.get; sp 2; if.
 + case (Some input=ex0).
   - rcondf 4; first by auto=> />; smt().
     auto=> />.
     rewrite ?get_set_sameE /=.
     move=> &hr hin _ out _ hb.
     apply(fo_hcache_set w0 g0 (Some input{hr}) ROH.m{hr} input{hr} out (hin hb)).
     by left.
   rcondt 4; first by auto=> />; smt().
   auto=> />.
   rewrite ?get_set_sameE /=.
   move=> &hr hin _ _ out _.
   rewrite get_set_sameE /= negb_or.
   move=>hb; case hb=>hb hbad.
   apply(fo_hcache_set w0 g0 ex0 ROH.m{hr} input{hr} out (hin hb)).
   by right.
 rcondf 2; first by auto=> />; smt().
 auto.
qed.

lemma fo_hmonitor_good w0 g0 x0 : hoare[FOHMonitor.get:
 input=x0 /\ FOContext.w=w0 /\ FOContext.g=g0 /\
 (!FOBadState.bad =>fo_hcache_good w0 g0 FOContext.challenge_h ROH.m) ==>
 FOContext.w=w0 /\ FOContext.g=g0 /\
 (!FOBadState.bad =>Some x0=FOContext.challenge_h \/ !fo_base_bad w0 g0 x0.`1 res)].
proof.
 exists* FOContext.challenge_h; elim*=>ex0.
 conseq (fo_hmonitor_invariant w0 g0 ex0)
   (fo_hmonitor_value x0) => />; rewrite /fo_hcache_good; smt().
qed.

lemma fo_hmonitor_bad_bound w0 g0 :
 phoare[FOHMonitor.get:
 FOContext.w=w0 /\ FOContext.g=g0 /\ !FOBadState.bad ==>FOBadState.bad]
 <=(fo_error w0 g0).
proof.
 have [hn _]:=fo_error_range w0 g0.
 proc; inline ROH.get; sp 2; if.
 + case (Some input=FOContext.challenge_h).
   - rcondf 4; first by auto=> />; smt().
     conseq (_: _ ==> _ : <=0%r)=> //.
     hoare; auto; smt().
   rcondt 4; first by auto=> />; smt().
   wp; rnd (fo_base_bad w0 g0 input.`1); skip=> />.
   rewrite ?get_set_sameE /=.
   move=> &hr _ _ _; split.
   - exact(fo_base_bad_bound w0 g0 input{hr}.`1).
   move=>_ v _; by rewrite get_set_sameE /=.
 rcondf 2; first by auto=> />; smt().
 conseq (_: _ ==> _ : <=0%r)=> //.
 hoare; auto; smt().
qed.

lemma fo_shakeh_invariant w0 g0 ex0 : hoare[FOSHAKEH.shake:
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOContext.challenge_h=ex0 /\
 (!FOBadState.bad =>fo_hcache_good w0 g0 ex0 ROH.m) ==>
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOContext.challenge_h=ex0 /\
 (!FOBadState.bad =>fo_hcache_good w0 g0 ex0 ROH.m)].
proof. proc; call(fo_hmonitor_invariant w0 g0 ex0); auto. qed.
lemma fo_shakeh_good w0 g0 x0 : hoare[FOSHAKEH.shake:
 input=x0 /\ FOContext.w=w0 /\ FOContext.g=g0 /\
 (!FOBadState.bad =>fo_hcache_good w0 g0 FOContext.challenge_h ROH.m) ==>
 FOContext.w=w0 /\ FOContext.g=g0 /\
 (!FOBadState.bad =>Some(peel_h x0)=FOContext.challenge_h \/
   !fo_base_bad w0 g0 (peel_h x0).`1 res)].
proof. proc; call(fo_hmonitor_good w0 g0 (peel_h x0)); auto. qed.
lemma fo_shakeh_fresh_step n0 : hoare[FOSHAKEH.shake:FOBadState.fresh=n0 ==>
 n0<=FOBadState.fresh<=n0+1].
proof. proc; call(fo_hmonitor_fresh_step n0); auto. qed.
lemma fo_shakeh_bad_bound w0 g0 :
 phoare[FOSHAKEH.shake:FOContext.w=w0 /\ FOContext.g=g0 /\ !FOBadState.bad ==>FOBadState.bad]
 <=(fo_error w0 g0).
proof. proc; call(fo_hmonitor_bad_bound w0 g0); auto. qed.

lemma fo_hmonitor_frame w0 g0 b0 : hoare[FOHMonitor.get:
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b0 ==>
 FOContext.w=w0 /\ FOContext.g=g0 /\ (b0=>FOBadState.bad)].
proof.
 proc; seq 2 : (FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b0).
 + call(_:true ==>true); first by trivial. auto.
 if; auto; smt().
qed.
lemma fo_hmonitor_value_extends m0 x0 : hoare[FOHMonitor.get:
 ROH.m=m0 /\ input=x0 ==>
 ROH.m.[x0]=Some res /\ cache_extends m0 ROH.m].
proof.
 proc; seq 2 : (ROH.m.[x0]=Some result /\ cache_extends m0 ROH.m).
 + call(roh_get_value m0 x0); auto.
 if; auto.
qed.
lemma fo_shakeh_value_extends m0 x0 : hoare[FOSHAKEH.shake:
 ROH.m=m0 /\ input=x0 ==>
 ROH.m.[peel_h x0]=Some res /\ cache_extends m0 ROH.m].
proof. proc; call(fo_hmonitor_value_extends m0 (peel_h x0)); auto. qed.
lemma fo_shakeh_context w0 g0 ex0 : hoare[FOSHAKEH.shake:
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOContext.challenge_h=ex0 ==>
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOContext.challenge_h=ex0].
proof. proc; call(fo_hmonitor_context w0 g0 ex0); auto. qed.
lemma fo_shakeh_bad_latched : hoare[FOSHAKEH.shake:FOBadState.bad ==>FOBadState.bad].
proof. proc; call fo_hmonitor_bad_latched; auto. qed.

lemma fo_raw_full_ll : islossless FOHRawXOF.full.
proof.
 proc; match.
 + by call raw_stream_untyped_ll; auto.
 match.
 + by call raw_stream_e_ll; auto.
 + by call raw_stream_f_ll; auto.
 + by call raw_stream_g_ll; auto.
 by call fo_hmonitor_ll; auto.
qed.
lemma fo_raw_get_ll : islossless FOHRawXOF.get.
proof. proc; sp 1; if; last by auto. wp; call fo_raw_full_ll; auto. qed.

lemma fo_hmonitor_raw_projection :
 equiv[FOHMonitor.get ~ RawXOFStreams.h: ={input,ROH.m} ==> ={res,ROH.m}].
proof.
 proc*; inline{2} RawXOFStreams.h SharedCCAOracles.h; wp.
 call fo_hmonitor_projection; auto.
qed.
lemma fo_raw_full_projection :
 equiv[FOHRawXOF.full ~ RawXOF.full:
 ={input,glob RawXOFStreams} ==> ={res,glob RawXOFStreams}].
proof.
 proc; match; 1,2:by auto.
 + by sim.
 move=>q1 q2; match; 1..4:by auto; smt().
 + move=>x1 x2; call(_: ={arg,glob RawXOFStreams} ==> ={res,glob RawXOFStreams}); first by sim.
   auto; smt().
 + move=>x1 x2; call(_: ={arg,glob RawXOFStreams} ==> ={res,glob RawXOFStreams}); first by sim.
   auto; smt().
 + move=>x1 x2; call(_: ={arg,glob RawXOFStreams} ==> ={res,glob RawXOFStreams}); first by sim.
   auto; smt().
 move=>x1 x2; call fo_hmonitor_raw_projection; auto; smt().
qed.
lemma fo_raw_get_projection :
 equiv[FOHRawXOF.get ~ RawXOF.get:
 ={input,outlen,glob RawXOFStreams} ==> ={res,glob RawXOFStreams}].
proof. proc; sp 1 1; if; auto. wp; call fo_raw_full_projection; auto. qed.

lemma fo_raw_full_frame w0 g0 b0 : hoare[FOHRawXOF.full:
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b0 ==>
 FOContext.w=w0 /\ FOContext.g=g0 /\ (b0=>FOBadState.bad)].
proof.
 proc; match.
 + call(_:true ==>true); first by trivial. auto; smt().
 match.
 + call(_:true ==>true); first by trivial. auto; smt().
 + call(_:true ==>true); first by trivial. auto; smt().
 + call(_:true ==>true); first by trivial. auto; smt().
 call(fo_hmonitor_frame w0 g0 b0); auto.
qed.
lemma fo_raw_get_frame w0 g0 b0 : hoare[FOHRawXOF.get:
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b0 ==>
 FOContext.w=w0 /\ FOContext.g=g0 /\ (b0=>FOBadState.bad)].
proof.
 proc; sp 1; if; last by auto.
 wp; call(fo_raw_full_frame w0 g0 b0); auto.
qed.

lemma fo_raw_full_non_h_frame w0 g0 b0 : hoare[FOHRawXOF.full:
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b0 /\
 (forall x,decode_typed input<>Some(H x)) ==>
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b0].
proof.
 proc; match.
 + call(_:true ==>true); first by trivial. auto.
 match.
 + call(_:true ==>true); first by trivial. auto.
 + call(_:true ==>true); first by trivial. auto.
 + call(_:true ==>true); first by trivial. auto.
 conseq (_:false ==>true)=> //; smt().
qed.
lemma fo_raw_get_non_h_frame w0 g0 b0 : hoare[FOHRawXOF.get:
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b0 /\ !fo_raw_h input outlen ==>
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOBadState.bad=b0].
proof.
 proc; sp 1; if; last by auto.
 wp; call(fo_raw_full_non_h_frame w0 g0 b0); auto=> />.
 smt(fo_raw_h_classification).
qed.

lemma fo_raw_full_bad_bound w0 g0 :
 phoare[FOHRawXOF.full:FOContext.w=w0 /\ FOContext.g=g0 /\ !FOBadState.bad ==>FOBadState.bad]
 <=(fo_error w0 g0).
proof.
 have [hn _]:=fo_error_range w0 g0.
 proc; match.
 + conseq (_: _ ==> _ : <=0%r)=> //.
   hoare; call(_:true ==>true); first by trivial. auto.
 match.
 + conseq (_: _ ==> _ : <=0%r)=> //.
   hoare; call(_:true ==>true); first by trivial. auto.
 + conseq (_: _ ==> _ : <=0%r)=> //.
   hoare; call(_:true ==>true); first by trivial. auto.
 + conseq (_: _ ==> _ : <=0%r)=> //.
   hoare; call(_:true ==>true); first by trivial. auto.
 call(fo_hmonitor_bad_bound w0 g0); auto.
qed.
lemma fo_raw_get_bad_bound w0 g0 :
 phoare[FOHRawXOF.get:
 FOContext.w=w0 /\ FOContext.g=g0 /\ !FOBadState.bad /\ fo_raw_h input outlen ==>FOBadState.bad]
 <=(fo_error w0 g0).
proof.
 proc; rcondt 2; first by auto; rewrite /fo_raw_h; smt().
 wp; call(fo_raw_full_bad_bound w0 g0); auto.
qed.

lemma fo_raw_full_invariant w0 g0 ex0 : hoare[FOHRawXOF.full:
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOContext.challenge_h=ex0 /\
 (!FOBadState.bad=>fo_hcache_good w0 g0 ex0 ROH.m) ==>
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOContext.challenge_h=ex0 /\
 (!FOBadState.bad=>fo_hcache_good w0 g0 ex0 ROH.m)].
proof.
 proc; match.
 + call(_:true ==>true); first by trivial. auto.
 match.
 + call(_:true ==>true); first by trivial. auto.
 + call(_:true ==>true); first by trivial. auto.
 + call(_:true ==>true); first by trivial. auto.
 call(fo_hmonitor_invariant w0 g0 ex0); auto.
qed.
lemma fo_raw_get_invariant w0 g0 ex0 : hoare[FOHRawXOF.get:
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOContext.challenge_h=ex0 /\
 (!FOBadState.bad=>fo_hcache_good w0 g0 ex0 ROH.m) ==>
 FOContext.w=w0 /\ FOContext.g=g0 /\ FOContext.challenge_h=ex0 /\
 (!FOBadState.bad=>fo_hcache_good w0 g0 ex0 ROH.m)].
proof.
 proc; sp 1; if; last by auto.
 wp; call(fo_raw_full_invariant w0 g0 ex0); auto.
qed.
