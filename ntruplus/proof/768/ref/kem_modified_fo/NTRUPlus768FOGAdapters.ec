require import AllCore List Distr DBool FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152 Array1153 Array2336 Array13506 Array13634 Array14466.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions NTRUPlus768ROMDomains.
require import NTRUPlus768CCAQueryCodec NTRUPlus768CCAOraclePorts.
require import NTRUPlus768RawXOFSampling NTRUPlus768HashPayloadSampling.
require import NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
require import NTRUPlus768CCAStatusAdapter NTRUPlus768CCADecapOracle NTRUPlus768CCAGame.
require import NTRUPlus768DecapMessageSpec NTRUPlus768DecapCompleteProof.
require import NTRUPlus768EncapCompleteRNG NTRUPlus768KEMFailureModel NTRUPlus768NumericalDFRModel.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteProof NTRUPlus768StoppedKeygenModel.
require import NTRUPlus768FreshRetryLaw NTRUPlus768ROMCorrectness NTRUPlus768CCASetupGame.
require import NTRUPlus768FOEagerG NTRUPlus768FOProcedures NTRUPlus768FOKEMGame NTRUPlus768FOGCompletion.

(* The same query-only G backend is used by honest calls and both attacker
   query interfaces. Inputs outside the trit image remain ordinary queries. *)
module FOGHash(G:FOGPort) : MessageSHAKE = {
 proc shake(input:W8.t Array1153.t) : W8.t Array192.t = {
  var y; y <@ G.get(peel1153 input); return y;
 }
}.
module FOGRawStreams(G:FOGPort) = {
 proc e(input:W8.t Array32.t) : W8.t Array224.t = {
  var prefix,suffix;
  prefix <@ ROE.get(input);
  if(input \notin RawXOFStreams.es){suffix <$ uniform32; RawXOFStreams.es.[input]<-suffix;}
  return raw_join192(prefix,oget RawXOFStreams.es.[input]);
 }
 proc f(input:W8.t Array1152.t) : W8.t Array224.t = {
  var prefix,suffix;
  prefix <@ ROF.get(input);
  if(input \notin RawXOFStreams.fs){suffix <$ uniform192; RawXOFStreams.fs.[input]<-suffix;}
  return hash_join(prefix,oget RawXOFStreams.fs.[input]);
 }
 proc g(input:W8.t Array1152.t) : W8.t Array224.t = {
  var prefix,suffix;
  prefix <@ G.get(input);
  if(input \notin RawXOFStreams.gs){suffix <$ uniform32; RawXOFStreams.gs.[input]<-suffix;}
  return raw_join192(prefix,oget RawXOFStreams.gs.[input]);
 }
 proc h(input:W8.t Array96.t*W8.t Array32.t) : W8.t Array224.t = {
  var y; y <@ ROH.get(input); return y;
 }
 proc untyped(input:W8.t list) : W8.t Array224.t = {
  var y;
  if(input \notin RawXOFStreams.other){y <$ uniform224; RawXOFStreams.other.[input]<-y;}
  return oget RawXOFStreams.other.[input];
 }
}.
module FOGRaw(G:FOGPort) = {
 proc full(input:W8.t list) : W8.t Array224.t = {
  var stream;
  match decode_typed input with
  | None => {stream <@ FOGRawStreams(G).untyped(input);}
  | Some query => {
   match query with
   | E seed => {stream <@ FOGRawStreams(G).e(seed);}
   | F pk => {stream <@ FOGRawStreams(G).f(pk);}
   | G serialized => {stream <@ FOGRawStreams(G).g(serialized);}
   | H payload => {stream <@ FOGRawStreams(G).h(payload);}
   end;
  }
  end;
  return stream;
 }
 proc get(input:W8.t list,outlen:int) : W8.t list option = {
  var result,stream;
  result <- None;
  if(0<=outlen<=raw_xof_max_output){
   stream <@ full(input);
   result <- Some(raw_xof_output outlen stream);
  }
  return result;
 }
}.
module FOGOracles(G:FOGPort) : CCAExtendedOraclePort = {
 proc e(input:W8.t Array32.t) : W8.t Array192.t = {var y; y <@ ROE.get(input); return y;}
 proc f(input:W8.t Array1152.t) : W8.t Array32.t = {var y; y <@ ROF.get(input); return y;}
 proc g(input:W8.t Array1152.t) : W8.t Array192.t = {var y; y <@ G.get(input); return y;}
 proc h(input:W8.t Array96.t*W8.t Array32.t) : W8.t Array224.t = {var y; y <@ ROH.get(input); return y;}
 proc raw=FOGRaw(G).get
}.

module FOGNativeDecap(G:FOGPort) = FONativeDecap(FOGHash(G),SHAKEHROM).
module FOGFullDecap(G:FOGPort) = FOReencryptDecap(FOGHash(G),SHAKEHROM).
module FOGNativeContext(A:CCAExtendedAdversary,G:FOGPort) = {
 proc run(out:keygen_output) : bool = {
  var win;
  win <@ FOCCAChallenge(FOGHash(G),SHAKEHROM,FOGOracles(G),FOGNativeDecap(G),A).run(out.`1.`kg_pk,out.`1.`kg_sk);
  return win;
 }
}.
module FOGFullContext(A:CCAExtendedAdversary,G:FOGPort) = {
 proc run(out:keygen_output) : bool = {
  var win;
  win <@ FOCCAChallenge(FOGHash(G),SHAKEHROM,FOGOracles(G),FOGFullDecap(G),A).run(out.`1.`kg_pk,out.`1.`kg_sk);
  return win;
 }
}.

lemma fo_g_hash_actual :
 equiv[FOGHash(FOGActual).shake ~ SHAKEGROM.shake : ={arg,ROG.m} ==> ={res,ROG.m}].
proof. proc; sim. qed.
lemma fo_g_encap_actual :
 equiv[EncapRandom(SHAKEFROM,FOGHash(FOGActual),SHAKEHROM,UniformCoins).run ~
       EncapRandom(SHAKEFROM,SHAKEGROM,SHAKEHROM,UniformCoins).run :
   ={arg,ROF.m,ROG.m,ROH.m} ==> ={res,ROF.m,ROG.m,ROH.m}].
proof. proc; sim. qed.
lemma fo_g_native_decap_actual :
 equiv[FOGNativeDecap(FOGActual).decap ~ CCADecapOracle.decap :
   ={arg,ROG.m,ROH.m,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count} ==>
   ={res,ROG.m,ROH.m,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count}].
proof. proc; inline CCAStatusAdapter.run; sim. qed.

lemma fo_g_raw_actual :
 equiv[FOGRaw(FOGActual).get ~ RawXOF.get :
 ={arg,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other} ==>
 ={res,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other}].
proof.
 proc; inline FOGRaw(FOGActual).full RawXOF.full
 FOGRawStreams(FOGActual).e FOGRawStreams(FOGActual).f FOGRawStreams(FOGActual).g FOGRawStreams(FOGActual).h FOGRawStreams(FOGActual).untyped
 RawXOFStreams.e RawXOFStreams.f RawXOFStreams.g RawXOFStreams.h RawXOFStreams.untyped
 SharedCCAOracles.e SharedCCAOracles.f SharedCCAOracles.g SharedCCAOracles.h; sim.
qed.

(* Pads are private here. The continuation observes their values only through
   ordinary G queries, including queries outside the finite trit image. *)
module FOGPreparedContext(C:FOGContext) = {
 proc run(out:keygen_output) : bool = {
  var pads:W8.t Array192.t list; var win;
  pads <@ FOGIIDSetup.run();
  win <@ C(FOGActual).run(out);
  return win;
 }
}.

lemma fo_g_completed_iid_context
 (C<:FOGContext {-ROG,-FOGRO.RO,-FOGRO.FRO}) :
 equiv[FOGCompletedContext(C,FOGRO.RO).distinguish ~ FOGPreparedContext(C).run :
 ={arg,glob C} /\ FOGRO.RO.m{1}=empty /\ ROG.m{2}=empty ==>
 ={res,glob C} /\ FOGRO.RO.m{1}=ROG.m{2}].
proof.
 proc; wp.
 call (_: ={arg,glob C} /\ FOGRO.RO.m{1}=ROG.m{2} ==>
          ={res,glob C} /\ FOGRO.RO.m{1}=ROG.m{2}).
 + symmetry; conseq(fo_g_actual_context_adapter C); smt().
 call fo_g_completion_iid; auto.
qed.

lemma fo_g_completed_actual_context
 (C<:FOGContext {-ROG,-FOGRO.RO,-FOGRO.FRO}) :
 equiv[FOGCompletedContext(C,FOGRO.RO).distinguish ~ C(FOGActual).run :
 ={arg,glob C} /\ FOGRO.RO.m{1}=ROG.m{2} ==> ={res,glob C}].
proof.
 transitivity C(FOGPROMGet(FOGRO.RO)).run
  (={arg,glob C,FOGRO.RO.m} ==> ={res,glob C})
  (={arg,glob C} /\ FOGRO.RO.m{1}=ROG.m{2} ==> ={res,glob C})=> //.
 + move=> &1 &2 [[ha hc] hm]; exists (glob C){1} FOGRO.RO.m{1} arg{1}; smt().
 + exact(fo_g_partial_eager C).
 symmetry; conseq(fo_g_actual_context_adapter C); smt().
qed.

lemma fo_g_actual_partial_eager
 (C<:FOGContext {-ROG,-FOGRO.RO,-FOGRO.FRO}) :
 equiv[FOGPreparedContext(C).run ~ C(FOGActual).run :
 ={arg,glob C} /\ ROG.m{1}=empty /\ ROG.m{2}=empty ==> ={res,glob C}].
proof.
 transitivity FOGCompletedContext(C,FOGRO.RO).distinguish
  (={arg,glob C} /\ ROG.m{1}=empty /\ FOGRO.RO.m{2}=empty ==> ={res,glob C})
  (={arg,glob C} /\ FOGRO.RO.m{1}=ROG.m{2} ==> ={res,glob C})=> //.
 + move=> &1 &2 [[ha hc] [h1 h2]]; exists (glob C){1} empty arg{1}; smt().
 + symmetry; conseq(fo_g_completed_iid_context C); smt().
 exact(fo_g_completed_actual_context C).
qed.

module FOGSetupGame(C:FOGContext) = {
 proc run() : bool = {
  var out:keygen_output; var win;
  ROMInit.init(); RawXOFStreams.init(); CCADecapOracle.reset();
  out <@ KeygenInstrumented(UniformSeedRNG,FreshExpand,SHAKEFROM).run(witness);
  win <@ C(FOGActual).run(out);
  return win;
 }
}.
module FOGEagerGame(C:FOGContext) = {
 proc run() : bool = {
  var out:keygen_output; var win;
  ROMInit.init(); RawXOFStreams.init(); CCADecapOracle.reset();
  out <@ KeygenInstrumented(UniformSeedRNG,FreshExpand,SHAKEFROM).run(witness);
  win <@ FOGPreparedContext(C).run(out);
  return win;
 }
}.
module FOGEagerNativeGame(A:CCAExtendedAdversary) = FOGEagerGame(FOGNativeContext(A)).
module FOGEagerFullGame(A:CCAExtendedAdversary) = FOGEagerGame(FOGFullContext(A)).

lemma fo_g_native_setup_eager
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOGRO.RO,-FOGRO.FRO}) :
 equiv[FOGEagerGame(FOGNativeContext(A)).run ~ FOGSetupGame(FOGNativeContext(A)).run :
 ={glob A,FOPublicKey.pk} ==> ={res,glob A}].
proof.
 proc; call(fo_g_actual_partial_eager (FOGNativeContext(A))).
 call(_: ={workspace,ROF.m} ==> ={res,ROF.m}); first by sim.
 inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init CCADecapOracle.reset; auto.
qed.

lemma fo_g_native_context_challenge
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOGRO.RO,-FOGRO.FRO}) :
 equiv[FOGNativeContext(A,FOGActual).run ~
 FOCCAChallenge(SHAKEGROM,SHAKEHROM,SharedCCAExtendedOracles,FONativeDecap(SHAKEGROM,SHAKEHROM),A).run :
 out{1}.`1.`kg_pk=pk{2} /\ out{1}.`1.`kg_sk=sk{2} /\ ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk} ==>
 ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk}].
proof.
 proc; inline{1} FOCCAChallenge(FOGHash(FOGActual),SHAKEHROM,FOGOracles(FOGActual),FOGNativeDecap(FOGActual),A).run.
 wp; call(_: ={ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk}); 1..4:by sim.
 + conseq fo_g_raw_actual; smt().
 + by sim.
 inline FOPublicKey.init CCADecapOracle.init; wp; rnd; rnd.
 call fo_g_encap_actual; auto.
qed.

lemma fo_g_native_game_actual
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOGRO.RO,-FOGRO.FRO}) :
 equiv[FOGSetupGame(FOGNativeContext(A)).run ~ FOFreshNativeGame(A).run :
 ={glob A,FOPublicKey.pk} ==> ={res,glob A}].
proof.
 proc; call(fo_g_native_context_challenge A).
 inline{2} Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run; wp.
 call(_: ={workspace,ROF.m} ==> ={res,ROF.m}); first by sim.
 inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init CCADecapOracle.reset; auto.
qed.

lemma fo_g_full_setup_eager
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOGRO.RO,-FOGRO.FRO}) :
 equiv[FOGEagerGame(FOGFullContext(A)).run ~ FOGSetupGame(FOGFullContext(A)).run :
 ={glob A,FOPublicKey.pk} ==> ={res,glob A}].
proof.
 proc; call(fo_g_actual_partial_eager (FOGFullContext(A))).
 call(_: ={workspace,ROF.m} ==> ={res,ROF.m}); first by sim.
 inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init CCADecapOracle.reset; auto.
qed.

lemma fo_g_full_context_challenge
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOGRO.RO,-FOGRO.FRO}) :
 equiv[FOGFullContext(A,FOGActual).run ~
 FOCCAChallenge(SHAKEGROM,SHAKEHROM,SharedCCAExtendedOracles,FOReencryptDecap(SHAKEGROM,SHAKEHROM),A).run :
 out{1}.`1.`kg_pk=pk{2} /\ out{1}.`1.`kg_sk=sk{2} /\ ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk} ==>
 ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk}].
proof.
 proc; inline{1} FOCCAChallenge(FOGHash(FOGActual),SHAKEHROM,FOGOracles(FOGActual),FOGFullDecap(FOGActual),A).run.
 wp; call(_: ={ROE.m,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count,FOPublicKey.pk}); 1..4:by sim.
 + conseq fo_g_raw_actual; smt().
 + by sim.
 inline FOPublicKey.init CCADecapOracle.init; wp; rnd; rnd.
 call fo_g_encap_actual; auto.
qed.

lemma fo_g_full_game_actual
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOGRO.RO,-FOGRO.FRO}) :
 equiv[FOGSetupGame(FOGFullContext(A)).run ~ FOFreshReencryptGame(A).run :
 ={glob A,FOPublicKey.pk} ==> ={res,glob A}].
proof.
 proc; call(fo_g_full_context_challenge A).
 inline{2} Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run; wp.
 call(_: ={workspace,ROF.m} ==> ={res,ROF.m}); first by sim.
 inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init CCADecapOracle.reset; auto.
qed.

lemma fo_g_native_eager_probability
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOGRO.RO,-FOGRO.FRO}) &m (event:bool->bool) :
 Pr[CCASharedSetupGame(FreshExpand,A).run() @ &m:event res]=
 Pr[FOGEagerNativeGame(A).run() @ &m:event res].
proof.
 have he:Pr[FOGEagerNativeGame(A).run() @ &m:event res]=
   Pr[FOGSetupGame(FOGNativeContext(A)).run() @ &m:event res].
 + by byequiv(fo_g_native_setup_eager A)=> //.
 have ha:Pr[FOGSetupGame(FOGNativeContext(A)).run() @ &m:event res]=
   Pr[FOFreshNativeGame(A).run() @ &m:event res].
 + by byequiv(fo_g_native_game_actual A)=> //.
 by rewrite he ha (fo_fresh_native_game_event A &m event).
qed.

lemma fo_g_full_eager_probability
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOGRO.RO,-FOGRO.FRO}) &m (event:bool->bool) :
 Pr[FOFreshReencryptGame(A).run() @ &m:event res]=
 Pr[FOGEagerFullGame(A).run() @ &m:event res].
proof.
 have he:Pr[FOGEagerFullGame(A).run() @ &m:event res]=
   Pr[FOGSetupGame(FOGFullContext(A)).run() @ &m:event res].
 + by byequiv(fo_g_full_setup_eager A)=> //.
 rewrite he; apply/eq_sym; by byequiv(fo_g_full_game_actual A)=> //.
qed.
