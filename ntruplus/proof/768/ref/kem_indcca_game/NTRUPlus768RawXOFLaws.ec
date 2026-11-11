require import AllCore List FMap Distr.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152.
require import NTRUPlus768ROMDomains NTRUPlus768ROMDistributions NTRUPlus768ROMOracles.
require import NTRUPlus768CCAQueryCodec NTRUPlus768CCAOraclePorts.
require import NTRUPlus768DecapCompleteSpec NTRUPlus768HashPayloadSampling NTRUPlus768RawXOFSampling.
require import NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
import RField.

module RawFreshSampling = {
 proc split192() : W8.t Array224.t = {
  var prefix,suffix;
  prefix <$ uniform192; suffix <$ uniform32;
  return raw_join192(prefix,suffix);
 }
 proc split32() : W8.t Array224.t = {
  var prefix,suffix;
  prefix <$ uniform32; suffix <$ uniform192;
  return hash_join(prefix,suffix);
 }
 proc full() : W8.t Array224.t = {
  var stream; stream <$ uniform224; return stream;
 }
}.
lemma raw_fresh_split192 : equiv[RawFreshSampling.split192 ~ RawFreshSampling.full : true ==> ={res}].
proof.
 proc; rnd raw_join192 raw_split192 : *0 *0 => /=; auto=> />.
 rewrite dmap_id -dprod_dlet.
 have hp : forall s, mu1 uniform224 s=mu1 (uniform192 `*` uniform32) (raw_split192 s).
 + move=>s; rewrite /raw_split192 dprod1E uniform224_point uniform192_point uniform32_point.
   by rewrite -exprD_nneg //.
 split; first by move=>s _; rewrite raw_join192_split.
 move=>_; split; first by move=>s _; exact(hp s).
 move=>_ p _; by rewrite uniform224_fu /= raw_split192_join.
qed.
lemma raw_fresh_split32 : equiv[RawFreshSampling.split32 ~ RawFreshSampling.full : true ==> ={res}].
proof.
 proc; rnd hash_join hash_split : *0 *0 => /=; auto=> />.
 rewrite dmap_id -dprod_dlet.
 have hp : forall s, mu1 uniform224 s=mu1 (uniform32 `*` uniform192) (hash_split s).
 + move=>s; rewrite /hash_split dprod1E uniform224_point uniform192_point uniform32_point.
   by rewrite -exprD_nneg //.
 split; first by move=>s _; rewrite hash_join_split.
 move=>_; split; first by move=>s _; exact(hp s).
 move=>_ p _; by rewrite uniform224_fu /= hash_split_join.
qed.

lemma raw_stream_e_fresh m0 s0 x0 :
 equiv[RawXOFStreams.e ~ RawFreshSampling.split192 :
 ROE.m{1}=m0 /\ RawXOFStreams.es{1}=s0 /\ input{1}=x0 /\
 x0 \notin m0 /\ x0 \notin s0 ==> ={res}].
proof.
 proc; inline SharedCCAOracles.e ROE.get; sp.
 rcondt {1} 1; first by auto.
 rcondt {1} 5; first by auto.
 wp; rnd; wp; rnd; auto=> />.
 move=> _ _ p _ s _; by rewrite !get_set_sameE /=.
qed.
lemma raw_stream_f_fresh m0 s0 x0 :
 equiv[RawXOFStreams.f ~ RawFreshSampling.split32 :
 ROF.m{1}=m0 /\ RawXOFStreams.fs{1}=s0 /\ input{1}=x0 /\
 x0 \notin m0 /\ x0 \notin s0 ==> ={res}].
proof.
 proc; inline SharedCCAOracles.f ROF.get; sp.
 rcondt {1} 1; first by auto.
 rcondt {1} 5; first by auto.
 wp; rnd; wp; rnd; auto=> />.
 move=> _ _ p _ s _; by rewrite !get_set_sameE /=.
qed.
lemma raw_stream_g_fresh m0 s0 x0 :
 equiv[RawXOFStreams.g ~ RawFreshSampling.split192 :
 ROG.m{1}=m0 /\ RawXOFStreams.gs{1}=s0 /\ input{1}=x0 /\
 x0 \notin m0 /\ x0 \notin s0 ==> ={res}].
proof.
 proc; inline SharedCCAOracles.g ROG.get; sp.
 rcondt {1} 1; first by auto.
 rcondt {1} 5; first by auto.
 wp; rnd; wp; rnd; auto=> />.
 move=> _ _ p _ s _; by rewrite !get_set_sameE /=.
qed.

lemma raw_stream_e_uniform &m x0 (event:W8.t Array224.t->bool) :
 x0 \notin ROE.m{m} => x0 \notin RawXOFStreams.es{m} =>
 Pr[RawXOFStreams.e(x0) @ &m : event res]=mu uniform224 event.
proof.
 move=>hm hs.
 have h1 : Pr[RawXOFStreams.e(x0) @ &m : event res]=
   Pr[RawFreshSampling.split192() @ &m : event res].
 + by byequiv(raw_stream_e_fresh ROE.m{m} RawXOFStreams.es{m} x0).
 have h2 : Pr[RawFreshSampling.split192() @ &m : event res]=
   Pr[RawFreshSampling.full() @ &m : event res] by byequiv raw_fresh_split192.
 rewrite h1 h2; byphoare (_:true ==> _) => //; proc; rnd; auto.
qed.

lemma raw_stream_f_uniform &m x0 (event:W8.t Array224.t->bool) :
 x0 \notin ROF.m{m} => x0 \notin RawXOFStreams.fs{m} =>
 Pr[RawXOFStreams.f(x0) @ &m : event res]=mu uniform224 event.
proof.
 move=>hm hs.
 have h1 : Pr[RawXOFStreams.f(x0) @ &m : event res]=
   Pr[RawFreshSampling.split32() @ &m : event res].
 + by byequiv(raw_stream_f_fresh ROF.m{m} RawXOFStreams.fs{m} x0).
 have h2 : Pr[RawFreshSampling.split32() @ &m : event res]=
   Pr[RawFreshSampling.full() @ &m : event res] by byequiv raw_fresh_split32.
 rewrite h1 h2; byphoare (_:true ==> _) => //; proc; rnd; auto.
qed.

lemma raw_stream_g_uniform &m x0 (event:W8.t Array224.t->bool) :
 x0 \notin ROG.m{m} => x0 \notin RawXOFStreams.gs{m} =>
 Pr[RawXOFStreams.g(x0) @ &m : event res]=mu uniform224 event.
proof.
 move=>hm hs.
 have h1 : Pr[RawXOFStreams.g(x0) @ &m : event res]=
   Pr[RawFreshSampling.split192() @ &m : event res].
 + by byequiv(raw_stream_g_fresh ROG.m{m} RawXOFStreams.gs{m} x0).
 have h2 : Pr[RawFreshSampling.split192() @ &m : event res]=
   Pr[RawFreshSampling.full() @ &m : event res] by byequiv raw_fresh_split192.
 rewrite h1 h2; byphoare (_:true ==> _) => //; proc; rnd; auto.
qed.

lemma raw_stream_e_stored x0 : hoare[RawXOFStreams.e : input=x0 ==>
 ROE.m.[x0]=Some(raw_head192 res) /\ RawXOFStreams.es.[x0]=Some(raw_tail32 res)].
proof.
 proc; seq 1 : (input=x0 /\ ROE.m.[x0]=Some prefix).
 + ecall(cca_e_value ROE.m x0); auto.
 if; auto=> />.
 + move=> &hr hc _ suffix0 _; by rewrite raw_join192_head raw_join192_tail /= hc get_set_sameE /=.
 move=> &hr hc hx; rewrite raw_join192_head raw_join192_tail /= hc /=.
 apply some_oget; move:hx; by rewrite domE.
qed.

lemma raw_stream_f_stored x0 : hoare[RawXOFStreams.f : input=x0 ==>
 ROF.m.[x0]=Some(hash_head res) /\ RawXOFStreams.fs.[x0]=Some(complete_hash_tail res)].
proof.
 proc; seq 1 : (input=x0 /\ ROF.m.[x0]=Some prefix).
 + ecall(cca_f_value ROF.m x0); auto.
 if; auto=> />.
 + move=> &hr hc _ suffix0 _; by rewrite hash_join_head hash_join_tail /= hc get_set_sameE /=.
 move=> &hr hc hx; rewrite hash_join_head hash_join_tail /= hc /=.
 apply some_oget; move:hx; by rewrite domE.
qed.

lemma raw_stream_g_stored x0 : hoare[RawXOFStreams.g : input=x0 ==>
 ROG.m.[x0]=Some(raw_head192 res) /\ RawXOFStreams.gs.[x0]=Some(raw_tail32 res)].
proof.
 proc; seq 1 : (input=x0 /\ ROG.m.[x0]=Some prefix).
 + ecall(cca_g_value ROG.m x0); auto.
 if; auto=> />.
 + move=> &hr hc _ suffix0 _; by rewrite raw_join192_head raw_join192_tail /= hc get_set_sameE /=.
 move=> &hr hc hx; rewrite raw_join192_head raw_join192_tail /= hc /=.
 apply some_oget; move:hx; by rewrite domE.
qed.

op raw_typed_stored (q:typed_query) (s:W8.t Array224.t)
 (em:(W8.t Array32.t,W8.t Array192.t) fmap)
 (fm:(W8.t Array1152.t,W8.t Array32.t) fmap)
 (gm:(W8.t Array1152.t,W8.t Array192.t) fmap)
 (hm:(W8.t Array96.t*W8.t Array32.t,W8.t Array224.t) fmap)
 (es:(W8.t Array32.t,W8.t Array32.t) fmap)
 (fs:(W8.t Array1152.t,W8.t Array192.t) fmap)
 (gs:(W8.t Array1152.t,W8.t Array32.t) fmap) =
 with q=E x => em.[x]=Some(raw_head192 s) /\ es.[x]=Some(raw_tail32 s)
 with q=F x => fm.[x]=Some(hash_head s) /\ fs.[x]=Some(complete_hash_tail s)
 with q=G x => gm.[x]=Some(raw_head192 s) /\ gs.[x]=Some(raw_tail32 s)
 with q=H x => hm.[x]=Some s.
op raw_stored (input:W8.t list) (s:W8.t Array224.t) em fm gm hm es fs gs
 (other:(W8.t list,W8.t Array224.t) fmap) =
 if decode_typed input=None then other.[input]=Some s else
 raw_typed_stored (oget(decode_typed input)) s em fm gm hm es fs gs.

lemma raw_stream_h_stored x0 : hoare[RawXOFStreams.h : input=x0 ==> ROH.m.[x0]=Some res].
proof. proc; ecall(cca_h_value ROH.m x0); auto. qed.
lemma raw_full_stored x0 : hoare[RawXOF.full : input=x0 ==>
 raw_stored x0 res ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other].
proof.
 proc; match.
 + ecall(raw_stream_untyped_value RawXOFStreams.other x0); auto.
 match.
 + ecall(raw_stream_e_stored seed); auto.
   move=> &hr [hq [hd hx]] s em es hs; by rewrite /raw_stored -hx hd hq /=.
 + ecall(raw_stream_f_stored pk); auto.
   move=> &hr [hq [hd hx]] s fm fs hs; by rewrite /raw_stored -hx hd hq /=.
 + ecall(raw_stream_g_stored serialized); auto.
   move=> &hr [hq [hd hx]] s gm gs hs; by rewrite /raw_stored -hx hd hq /=.
 ecall(raw_stream_h_stored payload); auto.
 move=> &hr [hq [hd hx]] s hm hs; by rewrite /raw_stored -hx hd hq /=.
qed.

lemma raw_full_cached x0 s0 : hoare[RawXOF.full : input=x0 /\
 raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other ==>
 res=s0 /\ raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other].
proof.
 proc; match.
 + ecall(raw_stream_untyped_cached RawXOFStreams.other x0 s0); auto.
   move=> &hr [hd [hx hs]].
   rewrite /raw_stored -hx hd /= in hs.
   rewrite /raw_stored -hx hd /=; smt().
 match.
 + ecall(raw_stream_e_cached ROE.m RawXOFStreams.es seed (raw_head192 s0) (raw_tail32 s0)); auto.
   move=> &hr [hq [hd [hx hs]]].
   rewrite /raw_stored -hx hd hq /= in hs.
   rewrite /raw_stored -hx hd hq /=.
   have hj:=raw_join192_split s0; rewrite /raw_split192 in hj; smt().
 + ecall(raw_stream_f_cached ROF.m RawXOFStreams.fs pk (hash_head s0) (complete_hash_tail s0)); auto.
   move=> &hr [hq [hd [hx hs]]].
   rewrite /raw_stored -hx hd hq /= in hs.
   rewrite /raw_stored -hx hd hq /=.
   have hj:=hash_join_split s0; rewrite /hash_split in hj; smt().
 + ecall(raw_stream_g_cached ROG.m RawXOFStreams.gs serialized (raw_head192 s0) (raw_tail32 s0)); auto.
   move=> &hr [hq [hd [hx hs]]].
   rewrite /raw_stored -hx hd hq /= in hs.
   rewrite /raw_stored -hx hd hq /=.
   have hj:=raw_join192_split s0; rewrite /raw_split192 in hj; smt().
 inline RawXOFStreams.h; wp; ecall(cca_h_cached ROH.m payload s0); auto.
 move=> &hr [hq [hd [hx hs]]].
 rewrite /raw_stored -hx hd hq /= in hs.
 rewrite /raw_stored -hx hd hq /=; smt().
qed.

lemma raw_get_cached x0 n0 s0 : 0<=n0<=raw_xof_max_output =>
 hoare[RawXOF.get : input=x0 /\ outlen=n0 /\
 raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other ==>
 res=Some(raw_xof_output n0 s0) /\
 raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other].
proof.
 move=>hn; proc; rcondt 2; first by auto.
 wp; call(raw_full_cached x0 s0); auto.
qed.

module RawXOFQueryPair = {
 proc run(input:W8.t list,i:int,j:int) : W8.t list option * W8.t list option = {
  var a,b;
  a<@RawXOF.get(input,i); b<@RawXOF.get(input,j);
  return (a,b);
 }
}.
lemma raw_xof_two_lengths x0 i0 j0 : 0<=i0<=j0<=224 =>
 hoare[RawXOFQueryPair.run : input=x0 /\ i=i0 /\ j=j0 ==>
 res.`1<>None /\ res.`2<>None /\
 take i0(oget res.`2)=oget res.`1].
proof.
 move=>hn; proc; inline RawXOF.get; sp.
 rcondt 1; first by auto; smt().
 rcondt 7.
 + wp; call (_:true ==>true); first by conseq raw_xof_full_ll.
   auto; smt().
 wp; ecall(raw_full_cached x0 stream); wp; call(raw_full_stored x0); auto=> />.
 move=>s em fm gm hm es fs gs other _ em2 fm2 gm2 hm2 es2 fs2 gs2 other2 _.
 apply raw_xof_output_prefix; smt().
qed.

lemma raw_stream_e_prefix_cached m0 x0 y0 : hoare[RawXOFStreams.e :
 ROE.m=m0 /\ input=x0 /\ m0.[x0]=Some y0 ==>
 raw_head192 res=y0 /\ ROE.m=m0].
proof.
 proc; seq 1 : (prefix=y0 /\ ROE.m=m0).
 + by call(cca_e_cached m0 x0 y0); auto.
 if; auto=> />.
 + move=> &hr _ suffix0 _; exact(raw_join192_head _).
 move=> &hr _; exact(raw_join192_head _).
qed.
lemma raw_full_e_prefix_cached m0 x0 y0 : hoare[RawXOF.full :
 ROE.m=m0 /\ decode_typed input=Some(E x0) /\ m0.[x0]=Some y0 ==>
 raw_head192 res=y0 /\ ROE.m=m0].
proof.
 proc; match.
 + conseq (_:false ==>true)=> //; smt().
 match.
 + call(raw_stream_e_prefix_cached m0 x0 y0); auto; smt().
 + conseq (_:false ==>true)=> //; smt().
 + conseq (_:false ==>true)=> //; smt().
 + conseq (_:false ==>true)=> //; smt().
qed.

lemma raw_stream_f_prefix_cached m0 x0 y0 : hoare[RawXOFStreams.f :
 ROF.m=m0 /\ input=x0 /\ m0.[x0]=Some y0 ==>
 hash_head res=y0 /\ ROF.m=m0].
proof.
 proc; seq 1 : (prefix=y0 /\ ROF.m=m0).
 + by call(cca_f_cached m0 x0 y0); auto.
 if; auto=> />.
 + move=> &hr _ suffix0 _; exact(hash_join_head _).
 move=> &hr _; exact(hash_join_head _).
qed.
lemma raw_full_f_prefix_cached m0 x0 y0 : hoare[RawXOF.full :
 ROF.m=m0 /\ decode_typed input=Some(F x0) /\ m0.[x0]=Some y0 ==>
 hash_head res=y0 /\ ROF.m=m0].
proof.
 proc; match.
 + conseq (_:false ==>true)=> //; smt().
 match.
 + conseq (_:false ==>true)=> //; smt().
 + call(raw_stream_f_prefix_cached m0 x0 y0); auto; smt().
 + conseq (_:false ==>true)=> //; smt().
 + conseq (_:false ==>true)=> //; smt().
qed.

lemma raw_stream_g_prefix_cached m0 x0 y0 : hoare[RawXOFStreams.g :
 ROG.m=m0 /\ input=x0 /\ m0.[x0]=Some y0 ==>
 raw_head192 res=y0 /\ ROG.m=m0].
proof.
 proc; seq 1 : (prefix=y0 /\ ROG.m=m0).
 + by call(cca_g_cached m0 x0 y0); auto.
 if; auto=> />.
 + move=> &hr _ suffix0 _; exact(raw_join192_head _).
 move=> &hr _; exact(raw_join192_head _).
qed.
lemma raw_full_g_prefix_cached m0 x0 y0 : hoare[RawXOF.full :
 ROG.m=m0 /\ decode_typed input=Some(G x0) /\ m0.[x0]=Some y0 ==>
 raw_head192 res=y0 /\ ROG.m=m0].
proof.
 proc; match.
 + conseq (_:false ==>true)=> //; smt().
 match.
 + conseq (_:false ==>true)=> //; smt().
 + conseq (_:false ==>true)=> //; smt().
 + call(raw_stream_g_prefix_cached m0 x0 y0); auto; smt().
 + conseq (_:false ==>true)=> //; smt().
qed.

lemma raw_full_e_value x0 : hoare[RawXOF.full : input=raw_query(E x0) ==>
 ROE.m.[x0]=Some(raw_head192 res)].
proof.
 conseq(raw_full_stored(raw_query(E x0)))=> //.
 move=> &hr; by rewrite /raw_stored decode_typed_encode /=; smt().
qed.

lemma raw_full_f_value x0 : hoare[RawXOF.full : input=raw_query(F x0) ==>
 ROF.m.[x0]=Some(hash_head res)].
proof.
 conseq(raw_full_stored(raw_query(F x0)))=> //.
 move=> &hr; by rewrite /raw_stored decode_typed_encode /=; smt().
qed.

lemma raw_full_g_value x0 : hoare[RawXOF.full : input=raw_query(G x0) ==>
 ROG.m.[x0]=Some(raw_head192 res)].
proof.
 conseq(raw_full_stored(raw_query(G x0)))=> //.
 move=> &hr; by rewrite /raw_stored decode_typed_encode /=; smt().
qed.

module RawTypedQueryOrder = {
 proc e_raw_first(input:W8.t Array32.t) : bool = {
  var stream,prefix;
  stream<@RawXOF.full(raw_query(E input));
  prefix<@SharedCCAOracles.e(input);
  return prefix=raw_head192 stream;
 }
 proc e_typed_first(input:W8.t Array32.t) : bool = {
  var stream,prefix;
  prefix<@SharedCCAOracles.e(input);
  stream<@RawXOF.full(raw_query(E input));
  return prefix=raw_head192 stream;
 }
 proc f_raw_first(input:W8.t Array1152.t) : bool = {
  var stream,prefix;
  stream<@RawXOF.full(raw_query(F input));
  prefix<@SharedCCAOracles.f(input);
  return prefix=hash_head stream;
 }
 proc f_typed_first(input:W8.t Array1152.t) : bool = {
  var stream,prefix;
  prefix<@SharedCCAOracles.f(input);
  stream<@RawXOF.full(raw_query(F input));
  return prefix=hash_head stream;
 }
 proc g_raw_first(input:W8.t Array1152.t) : bool = {
  var stream,prefix;
  stream<@RawXOF.full(raw_query(G input));
  prefix<@SharedCCAOracles.g(input);
  return prefix=raw_head192 stream;
 }
 proc g_typed_first(input:W8.t Array1152.t) : bool = {
  var stream,prefix;
  prefix<@SharedCCAOracles.g(input);
  stream<@RawXOF.full(raw_query(G input));
  return prefix=raw_head192 stream;
 }
}.

lemma raw_typed_e_order : hoare[RawTypedQueryOrder.e_raw_first : true ==>res].
proof.
 proc; ecall(cca_e_cached ROE.m input (raw_head192 stream)).
 ecall(raw_full_e_value input); auto.
qed.
lemma typed_raw_e_order : hoare[RawTypedQueryOrder.e_typed_first : true ==>res].
proof.
 proc; ecall(raw_full_e_prefix_cached ROE.m input prefix).
 ecall(cca_e_value ROE.m input); auto=> />.
 move=> &hr result0 m0 _ _; exact(decode_typed_encode(E input{hr})).
qed.

lemma raw_typed_f_order : hoare[RawTypedQueryOrder.f_raw_first : true ==>res].
proof.
 proc; ecall(cca_f_cached ROF.m input (hash_head stream)).
 ecall(raw_full_f_value input); auto.
qed.
lemma typed_raw_f_order : hoare[RawTypedQueryOrder.f_typed_first : true ==>res].
proof.
 proc; ecall(raw_full_f_prefix_cached ROF.m input prefix).
 ecall(cca_f_value ROF.m input); auto=> />.
 move=> &hr result0 m0 _ _; exact(decode_typed_encode(F input{hr})).
qed.

lemma raw_typed_g_order : hoare[RawTypedQueryOrder.g_raw_first : true ==>res].
proof.
 proc; ecall(cca_g_cached ROG.m input (raw_head192 stream)).
 ecall(raw_full_g_value input); auto.
qed.
lemma typed_raw_g_order : hoare[RawTypedQueryOrder.g_typed_first : true ==>res].
proof.
 proc; ecall(raw_full_g_prefix_cached ROG.m input prefix).
 ecall(cca_g_value ROG.m input); auto=> />.
 move=> &hr result0 m0 _ _; exact(decode_typed_encode(G input{hr})).
qed.

lemma raw_stream_h_fresh m0 x0 :
 equiv[RawXOFStreams.h ~ RawFreshSampling.full :
 ROH.m{1}=m0 /\ input{1}=x0 /\ x0 \notin m0 ==> ={res}].
proof.
 proc; inline SharedCCAOracles.h ROH.get; sp.
 rcondt {1} 1; first by auto.
 wp; rnd; auto=> />.
 move=> _ s _; by rewrite get_set_sameE /=.
qed.
lemma raw_stream_h_uniform &m x0 (event:W8.t Array224.t->bool) :
 x0 \notin ROH.m{m} =>
 Pr[RawXOFStreams.h(x0) @ &m : event res]=mu uniform224 event.
proof.
 move=>hm.
 have he : Pr[RawXOFStreams.h(x0) @ &m : event res]=
   Pr[RawFreshSampling.full() @ &m : event res]
   by byequiv(raw_stream_h_fresh ROH.m{m} x0).
 rewrite he; byphoare (_:true ==> _) => //; proc; rnd; auto.
qed.
lemma raw_stream_other_uniform &m x0 (event:W8.t Array224.t->bool) :
 x0 \notin RawXOFStreams.other{m} =>
 Pr[RawXOFStreams.untyped(x0) @ &m : event res]=mu uniform224 event.
proof.
 move=>hx.
 have he : Pr[RawXOFStreams.untyped(x0) @ &m : event res]=
   Pr[RawFreshSampling.full() @ &m : event res].
 + byequiv (_:input{1}=x0 /\ x0 \notin RawXOFStreams.other{1} ==> ={res})=> //.
   proc; rcondt {1} 1; first by auto.
   wp; rnd; auto=> />.
   move=> &1 _ s _; by rewrite get_set_sameE /=.
 rewrite he; byphoare (_:true ==> _) => //; proc; rnd; auto.
qed.
lemma raw_full_malformed_frame e0 f0 g0 h0 :
 hoare[RawXOF.full : decode_typed input=None /\
 ROE.m=e0 /\ ROF.m=f0 /\ ROG.m=g0 /\ ROH.m=h0 ==>
 ROE.m=e0 /\ ROF.m=f0 /\ ROG.m=g0 /\ ROH.m=h0].
proof.
 proc; match.
 + call(raw_stream_untyped_frame e0 f0 g0 h0); auto.
 conseq (_:false ==>true)=> //; smt().
qed.
lemma raw_full_h_prefix_cached m0 x0 y0 : hoare[RawXOF.full :
 ROH.m=m0 /\ decode_typed input=Some(H x0) /\ m0.[x0]=Some y0 ==>
 res=y0 /\ ROH.m=m0].
proof.
 proc; match.
 + conseq (_:false ==>true)=> //; smt().
 match.
 + conseq (_:false ==>true)=> //; smt().
 + conseq (_:false ==>true)=> //; smt().
 + conseq (_:false ==>true)=> //; smt().
 inline RawXOFStreams.h; wp; call(cca_h_cached m0 x0 y0); auto; smt().
qed.
lemma raw_full_h_value x0 : hoare[RawXOF.full : input=raw_query(H x0) ==>
 ROH.m.[x0]=Some res].
proof.
 conseq(raw_full_stored(raw_query(H x0)))=> //.
 move=> &hr; by rewrite /raw_stored decode_typed_encode /=.
qed.
module RawHTypedQueryOrder = {
 proc raw_first(input:W8.t Array96.t*W8.t Array32.t) : bool = {
  var stream,prefix;
  stream<@RawXOF.full(raw_query(H input)); prefix<@SharedCCAOracles.h(input);
  return prefix=stream;
 }
 proc typed_first(input:W8.t Array96.t*W8.t Array32.t) : bool = {
  var stream,prefix;
  prefix<@SharedCCAOracles.h(input); stream<@RawXOF.full(raw_query(H input));
  return prefix=stream;
 }
}.
lemma raw_typed_h_order : hoare[RawHTypedQueryOrder.raw_first : true ==>res].
proof.
 proc; ecall(cca_h_cached ROH.m input stream).
 ecall(raw_full_h_value input); auto.
qed.
lemma typed_raw_h_order : hoare[RawHTypedQueryOrder.typed_first : true ==>res].
proof.
 proc; ecall(raw_full_h_prefix_cached ROH.m input prefix).
 ecall(cca_h_value ROH.m input); auto=> />.
 move=> &hr result0 m0 _ _; exact(decode_typed_encode(H input{hr})).
qed.

lemma raw_stream_e_extends m0 s0 : hoare[RawXOFStreams.e :
 ROE.m=m0 /\ RawXOFStreams.es=s0 ==>
 cache_extends m0 ROE.m /\ cache_extends s0 RawXOFStreams.es].
proof.
 proc; seq 1 : (cache_extends m0 ROE.m /\ RawXOFStreams.es=s0).
 + ecall(cca_e_value m0 input); auto.
 if; auto=> />.
 + move=> &hr he hx suffix0 _; exact(cache_extends_fresh s0 input{hr} suffix0 hx).
qed.

lemma raw_stream_f_extends m0 s0 : hoare[RawXOFStreams.f :
 ROF.m=m0 /\ RawXOFStreams.fs=s0 ==>
 cache_extends m0 ROF.m /\ cache_extends s0 RawXOFStreams.fs].
proof.
 proc; seq 1 : (cache_extends m0 ROF.m /\ RawXOFStreams.fs=s0).
 + ecall(cca_f_value m0 input); auto.
 if; auto=> />.
 + move=> &hr he hx suffix0 _; exact(cache_extends_fresh s0 input{hr} suffix0 hx).
qed.

lemma raw_stream_g_extends m0 s0 : hoare[RawXOFStreams.g :
 ROG.m=m0 /\ RawXOFStreams.gs=s0 ==>
 cache_extends m0 ROG.m /\ cache_extends s0 RawXOFStreams.gs].
proof.
 proc; seq 1 : (cache_extends m0 ROG.m /\ RawXOFStreams.gs=s0).
 + ecall(cca_g_value m0 input); auto.
 if; auto=> />.
 + move=> &hr he hx suffix0 _; exact(cache_extends_fresh s0 input{hr} suffix0 hx).
qed.

lemma raw_full_extends e0 f0 g0 h0 es0 fs0 gs0 other0 : hoare[RawXOF.full :
 ROE.m=e0 /\ ROF.m=f0 /\ ROG.m=g0 /\ ROH.m=h0 /\
 RawXOFStreams.es=es0 /\ RawXOFStreams.fs=fs0 /\
 RawXOFStreams.gs=gs0 /\ RawXOFStreams.other=other0 ==>
 cache_extends e0 ROE.m /\ cache_extends f0 ROF.m /\
 cache_extends g0 ROG.m /\ cache_extends h0 ROH.m /\
 cache_extends es0 RawXOFStreams.es /\ cache_extends fs0 RawXOFStreams.fs /\
 cache_extends gs0 RawXOFStreams.gs /\ cache_extends other0 RawXOFStreams.other].
proof.
 proc; match.
 + ecall(raw_stream_untyped_value other0 input); auto=> />; smt(cache_extends_refl).
 match.
 + call(raw_stream_e_extends e0 es0); auto=> />; smt(cache_extends_refl).
 + call(raw_stream_f_extends f0 fs0); auto=> />; smt(cache_extends_refl).
 + call(raw_stream_g_extends g0 gs0); auto=> />; smt(cache_extends_refl).
 inline RawXOFStreams.h; wp; ecall(cca_h_value h0 payload); auto=> />; smt(cache_extends_refl).
qed.
lemma raw_stored_mono input s e0 f0 g0 h0 es0 fs0 gs0 other0 e1 f1 g1 h1 es1 fs1 gs1 other1 :
 cache_extends e0 e1 => cache_extends f0 f1 => cache_extends g0 g1 => cache_extends h0 h1 =>
 cache_extends es0 es1 => cache_extends fs0 fs1 => cache_extends gs0 gs1 => cache_extends other0 other1 =>
 raw_stored input s e0 f0 g0 h0 es0 fs0 gs0 other0 =>
 raw_stored input s e1 f1 g1 h1 es1 fs1 gs1 other1.
proof.
 rewrite /cache_extends=>he hf hg hh hes hfs hgs ho.
 rewrite /raw_stored; case(decode_typed input=None)=>hd; first smt().
 case(oget(decode_typed input))=>x; smt().
qed.
lemma raw_full_preserves_known x0 s0 : hoare[RawXOF.full :
 raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other ==>
 raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other].
proof.
 proc.
 match.
 + ecall(raw_stream_untyped_value RawXOFStreams.other input); auto=> />; smt(raw_stored_mono cache_extends_refl).
 match.
 + ecall(raw_stream_e_extends ROE.m RawXOFStreams.es); auto=> />; smt(raw_stored_mono cache_extends_refl).
 + ecall(raw_stream_f_extends ROF.m RawXOFStreams.fs); auto=> />; smt(raw_stored_mono cache_extends_refl).
 + ecall(raw_stream_g_extends ROG.m RawXOFStreams.gs); auto=> />; smt(raw_stored_mono cache_extends_refl).
 inline RawXOFStreams.h; wp; ecall(cca_h_value ROH.m payload); auto=> />; smt(raw_stored_mono cache_extends_refl).
qed.

lemma raw_get_preserves_known x0 s0 : hoare[RawXOF.get :
 raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other ==> raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other].
proof. proc; sp; if; last by auto. wp; call(raw_full_preserves_known x0 s0); auto. qed.

lemma typed_e_preserves_raw_known x0 s0 : hoare[SharedCCAOracles.e :
 raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other ==> raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other].
proof.
 proc; ecall(roe_get_value ROE.m input); auto=> />;
 smt(raw_stored_mono cache_extends_refl).
qed.

lemma typed_f_preserves_raw_known x0 s0 : hoare[SharedCCAOracles.f :
 raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other ==> raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other].
proof.
 proc; ecall(rof_get_value ROF.m input); auto=> />;
 smt(raw_stored_mono cache_extends_refl).
qed.

lemma typed_g_preserves_raw_known x0 s0 : hoare[SharedCCAOracles.g :
 raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other ==> raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other].
proof.
 proc; ecall(rog_get_value ROG.m input); auto=> />;
 smt(raw_stored_mono cache_extends_refl).
qed.

lemma typed_h_preserves_raw_known x0 s0 : hoare[SharedCCAOracles.h :
 raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other ==> raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other].
proof.
 proc; ecall(roh_get_value ROH.m input); auto=> />;
 smt(raw_stored_mono cache_extends_refl).
qed.


lemma raw_get_e_projection x0 : hoare[RawXOF.get :
 input=raw_query(E x0) /\ outlen=192 ==>
 res=Some(Array192.to_list(oget ROE.m.[x0])) /\ x0 \in ROE.m].
proof.
 proc; rcondt 2; first by auto.
 wp; call(raw_full_e_value x0); auto=> />.
 move=>s m0 hc; by rewrite raw_xof_output_head192 hc /= domE hc /=.
qed.

lemma raw_get_f_projection x0 : hoare[RawXOF.get :
 input=raw_query(F x0) /\ outlen=32 ==>
 res=Some(Array32.to_list(oget ROF.m.[x0])) /\ x0 \in ROF.m].
proof.
 proc; rcondt 2; first by auto.
 wp; call(raw_full_f_value x0); auto=> />.
 move=>s m0 hc; by rewrite raw_xof_output_head32 hc /= domE hc /=.
qed.

lemma raw_get_g_projection x0 : hoare[RawXOF.get :
 input=raw_query(G x0) /\ outlen=192 ==>
 res=Some(Array192.to_list(oget ROG.m.[x0])) /\ x0 \in ROG.m].
proof.
 proc; rcondt 2; first by auto.
 wp; call(raw_full_g_value x0); auto=> />.
 move=>s m0 hc; by rewrite raw_xof_output_head192 hc /= domE hc /=.
qed.

lemma raw_get_h_projection x0 : hoare[RawXOF.get :
 input=raw_query(H x0) /\ outlen=224 ==>
 res=Some(Array224.to_list(oget ROH.m.[x0])) /\ x0 \in ROH.m].
proof.
 proc; rcondt 2; first by auto.
 wp; call(raw_full_h_value x0); auto=> />.
 move=>s m0 hc; by rewrite raw_xof_output_full hc /= domE hc /=.
qed.
module type RawQueryAdversary(H:CCAExtendedOraclePort) = {
 proc run() : bool {H.e,H.f,H.g,H.h,H.raw}
}.
(* Any query-only continuation preserves every previously fixed stream.
   It may choose inputs and lengths adaptively and need not be lossless.
   This is an invariant of this shared implementation, not an equivalence
   to a separate eager one-table oracle. *)
lemma raw_query_adversary_preserves
 (A <: RawQueryAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams}) x0 s0 :
 hoare[A(SharedCCAExtendedOracles).run : raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other ==> raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other].
proof.
 proc (raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other); 1,2: by auto.
 + exact(typed_e_preserves_raw_known x0 s0).
 + exact(typed_f_preserves_raw_known x0 s0).
 + exact(typed_g_preserves_raw_known x0 s0).
 + exact(typed_h_preserves_raw_known x0 s0).
 exact(raw_get_preserves_known x0 s0).
qed.
