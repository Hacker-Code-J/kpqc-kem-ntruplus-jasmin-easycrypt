require import AllCore List FMap Distr.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152.
require import NTRUPlus768ROMDistributions NTRUPlus768ROMOracles NTRUPlus768CCAOraclePorts NTRUPlus768RawXOFSampling.
require import NTRUPlus768HashPayloadSampling.

(* Existing typed tables store the first 192/32/192/224 bytes. Only the
   missing suffixes are sampled here. Honest typed calls and raw calls
   therefore share their answers even when their order is adversarial. *)
module RawXOFStreams = {
 var es : (W8.t Array32.t,W8.t Array32.t) fmap
 var fs : (W8.t Array1152.t,W8.t Array192.t) fmap
 var gs : (W8.t Array1152.t,W8.t Array32.t) fmap
 var other : (W8.t list,W8.t Array224.t) fmap
 proc init() = { es<-empty; fs<-empty; gs<-empty; other<-empty; }
 proc e(input:W8.t Array32.t) : W8.t Array224.t = {
  var prefix,suffix;
  prefix <@ SharedCCAOracles.e(input);
  if(input \notin es){suffix <$ uniform32; es.[input]<-suffix;}
  return raw_join192(prefix,oget es.[input]);
 }
 proc f(input:W8.t Array1152.t) : W8.t Array224.t = {
  var prefix,suffix;
  prefix <@ SharedCCAOracles.f(input);
  if(input \notin fs){suffix <$ uniform192; fs.[input]<-suffix;}
  return hash_join(prefix,oget fs.[input]);
 }
 proc g(input:W8.t Array1152.t) : W8.t Array224.t = {
  var prefix,suffix;
  prefix <@ SharedCCAOracles.g(input);
  if(input \notin gs){suffix <$ uniform32; gs.[input]<-suffix;}
  return raw_join192(prefix,oget gs.[input]);
 }
 proc h(input:W8.t Array96.t*W8.t Array32.t) : W8.t Array224.t = {
  var stream; stream <@ SharedCCAOracles.h(input); return stream;
 }
 proc untyped(input:W8.t list) : W8.t Array224.t = {
  var stream;
  if(input \notin other){stream <$ uniform224; other.[input]<-stream;}
  return oget other.[input];
 }
}.
lemma raw_stream_init_ll : islossless RawXOFStreams.init.
proof. by proc; auto. qed.
lemma raw_stream_init_empty : hoare[RawXOFStreams.init : true ==>
 RawXOFStreams.es=empty /\ RawXOFStreams.fs=empty /\
 RawXOFStreams.gs=empty /\ RawXOFStreams.other=empty].
proof. by proc; auto. qed.

lemma raw_stream_e_ll : islossless RawXOFStreams.e.
proof.
 proc; seq 1 : true; 1,4,5: by auto.
 + by call cca_e_ll; auto.
 if; auto=> /> &hr _; exact uniform32_ll.
qed.
lemma raw_stream_e_projection :
 equiv[RawXOFStreams.e ~ SharedCCAOracles.e :
  ={input,ROE.m,ROF.m,ROG.m,ROH.m} ==>
  raw_head192 res{1}=res{2} /\ ={ROE.m,ROF.m,ROG.m,ROH.m}].
proof.
 proc; seq 1 1 : (prefix{1}=r{2} /\ ={ROE.m,ROF.m,ROG.m,ROH.m}).
 + by call cca_e_identity; auto.
 wp; if {1}; auto=> />.
 + move=> &1 &2 _; rewrite uniform32_ll /= =>suffix0 _; exact(raw_join192_head _).
 move=> &1 &2 _; exact(raw_join192_head _).
qed.
lemma raw_stream_e_value m0 x0 : hoare[RawXOFStreams.e :
 ROE.m=m0 /\ input=x0 ==>
 ROE.m.[x0]=Some(raw_head192 res) /\ cache_extends m0 ROE.m /\
 x0 \in RawXOFStreams.es].
proof.
 proc; seq 1 : (input=x0 /\ ROE.m.[x0]=Some prefix /\ cache_extends m0 ROE.m).
 + by call(cca_e_value m0 x0); auto.
 if; auto=> />.
 + move=> &hr hc _ _ suffix0 _; by rewrite raw_join192_head /= hc mem_set /=.
 move=> &hr hc _ _; by rewrite raw_join192_head /= hc.
qed.
lemma raw_stream_e_cached m0 s0 x0 y0 z0 : hoare[RawXOFStreams.e :
 ROE.m=m0 /\ RawXOFStreams.es=s0 /\ input=x0 /\
 m0.[x0]=Some y0 /\ s0.[x0]=Some z0 ==>
 res=raw_join192(y0,z0) /\ ROE.m=m0 /\ RawXOFStreams.es=s0].
proof.
 proc; rcondf 2.
 + call(cca_e_cached m0 x0 y0); auto=> />; smt(domE).
 call(cca_e_cached m0 x0 y0); auto=> />; smt().
qed.

lemma raw_stream_f_ll : islossless RawXOFStreams.f.
proof.
 proc; seq 1 : true; 1,4,5: by auto.
 + by call cca_f_ll; auto.
 if; auto=> /> &hr _; exact uniform192_ll.
qed.
lemma raw_stream_f_projection :
 equiv[RawXOFStreams.f ~ SharedCCAOracles.f :
  ={input,ROE.m,ROF.m,ROG.m,ROH.m} ==>
  hash_head res{1}=res{2} /\ ={ROE.m,ROF.m,ROG.m,ROH.m}].
proof.
 proc; seq 1 1 : (prefix{1}=r{2} /\ ={ROE.m,ROF.m,ROG.m,ROH.m}).
 + by call cca_f_identity; auto.
 wp; if {1}; auto=> />.
 + move=> &1 &2 _; rewrite uniform192_ll /= =>suffix0 _; exact(hash_join_head _).
 move=> &1 &2 _; exact(hash_join_head _).
qed.
lemma raw_stream_f_value m0 x0 : hoare[RawXOFStreams.f :
 ROF.m=m0 /\ input=x0 ==>
 ROF.m.[x0]=Some(hash_head res) /\ cache_extends m0 ROF.m /\
 x0 \in RawXOFStreams.fs].
proof.
 proc; seq 1 : (input=x0 /\ ROF.m.[x0]=Some prefix /\ cache_extends m0 ROF.m).
 + by call(cca_f_value m0 x0); auto.
 if; auto=> />.
 + move=> &hr hc _ _ suffix0 _; by rewrite hash_join_head /= hc mem_set /=.
 move=> &hr hc _ _; by rewrite hash_join_head /= hc.
qed.
lemma raw_stream_f_cached m0 s0 x0 y0 z0 : hoare[RawXOFStreams.f :
 ROF.m=m0 /\ RawXOFStreams.fs=s0 /\ input=x0 /\
 m0.[x0]=Some y0 /\ s0.[x0]=Some z0 ==>
 res=hash_join(y0,z0) /\ ROF.m=m0 /\ RawXOFStreams.fs=s0].
proof.
 proc; rcondf 2.
 + call(cca_f_cached m0 x0 y0); auto=> />; smt(domE).
 call(cca_f_cached m0 x0 y0); auto=> />; smt().
qed.

lemma raw_stream_g_ll : islossless RawXOFStreams.g.
proof.
 proc; seq 1 : true; 1,4,5: by auto.
 + by call cca_g_ll; auto.
 if; auto=> /> &hr _; exact uniform32_ll.
qed.
lemma raw_stream_g_projection :
 equiv[RawXOFStreams.g ~ SharedCCAOracles.g :
  ={input,ROE.m,ROF.m,ROG.m,ROH.m} ==>
  raw_head192 res{1}=res{2} /\ ={ROE.m,ROF.m,ROG.m,ROH.m}].
proof.
 proc; seq 1 1 : (prefix{1}=r{2} /\ ={ROE.m,ROF.m,ROG.m,ROH.m}).
 + by call cca_g_identity; auto.
 wp; if {1}; auto=> />.
 + move=> &1 &2 _; rewrite uniform32_ll /= =>suffix0 _; exact(raw_join192_head _).
 move=> &1 &2 _; exact(raw_join192_head _).
qed.
lemma raw_stream_g_value m0 x0 : hoare[RawXOFStreams.g :
 ROG.m=m0 /\ input=x0 ==>
 ROG.m.[x0]=Some(raw_head192 res) /\ cache_extends m0 ROG.m /\
 x0 \in RawXOFStreams.gs].
proof.
 proc; seq 1 : (input=x0 /\ ROG.m.[x0]=Some prefix /\ cache_extends m0 ROG.m).
 + by call(cca_g_value m0 x0); auto.
 if; auto=> />.
 + move=> &hr hc _ _ suffix0 _; by rewrite raw_join192_head /= hc mem_set /=.
 move=> &hr hc _ _; by rewrite raw_join192_head /= hc.
qed.
lemma raw_stream_g_cached m0 s0 x0 y0 z0 : hoare[RawXOFStreams.g :
 ROG.m=m0 /\ RawXOFStreams.gs=s0 /\ input=x0 /\
 m0.[x0]=Some y0 /\ s0.[x0]=Some z0 ==>
 res=raw_join192(y0,z0) /\ ROG.m=m0 /\ RawXOFStreams.gs=s0].
proof.
 proc; rcondf 2.
 + call(cca_g_cached m0 x0 y0); auto=> />; smt(domE).
 call(cca_g_cached m0 x0 y0); auto=> />; smt().
qed.

lemma raw_stream_h_ll : islossless RawXOFStreams.h.
proof. by proc; call cca_h_ll; auto. qed.
lemma raw_stream_h_projection :
 equiv[RawXOFStreams.h ~ SharedCCAOracles.h :
  ={input,ROE.m,ROF.m,ROG.m,ROH.m} ==> ={res,ROE.m,ROF.m,ROG.m,ROH.m}].
proof. proc; inline *; sp; if; auto. qed.
lemma raw_stream_untyped_ll : islossless RawXOFStreams.untyped.
proof. proc; if; auto=> /> &hr _; exact uniform224_ll. qed.
lemma raw_stream_untyped_value m0 x0 : hoare[RawXOFStreams.untyped :
 RawXOFStreams.other=m0 /\ input=x0 ==>
 RawXOFStreams.other.[x0]=Some res /\ cache_extends m0 RawXOFStreams.other].
proof.
 proc; if.
 + auto=> /> hx r hr; rewrite get_set_sameE /=.
   exact(cache_extends_fresh m0 x0 r hx).
 auto=> /> hx; apply some_oget; move:hx; by rewrite domE.
qed.
lemma raw_stream_untyped_cached m0 x0 y0 : hoare[RawXOFStreams.untyped :
 RawXOFStreams.other=m0 /\ input=x0 /\ m0.[x0]=Some y0 ==>
 res=y0 /\ RawXOFStreams.other=m0].
proof. proc; if; auto=> />; smt(domE). qed.
lemma raw_stream_untyped_frame e0 f0 g0 h0 : hoare[RawXOFStreams.untyped :
 ROE.m=e0 /\ ROF.m=f0 /\ ROG.m=g0 /\ ROH.m=h0 ==>
 ROE.m=e0 /\ ROF.m=f0 /\ ROG.m=g0 /\ ROH.m=h0].
proof. proc; if; auto. qed.
lemma raw_stream_untyped_fresh m0 x0 y0 : phoare[RawXOFStreams.untyped :
 RawXOFStreams.other=m0 /\ input=x0 /\ x0 \notin m0 ==> res=y0]=(mu1 uniform224 y0).
proof.
 proc; rcondt 1; first by auto.
 wp; rnd(pred1 y0); skip; auto=> /> hx v hv; by rewrite get_set_sameE /=.
qed.
