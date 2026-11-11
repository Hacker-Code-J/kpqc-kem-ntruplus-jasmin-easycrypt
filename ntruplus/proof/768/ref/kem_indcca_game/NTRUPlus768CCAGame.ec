require import AllCore Distr DBool FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152 Array2336 Array13634 Array14466.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768EncapCompleteRNG.
require import NTRUPlus768EncapGuardSpec NTRUPlus768EncapGuardProof NTRUPlus768KEMFailureModel.
require import NTRUPlus768ROMOracles NTRUPlus768ROMCorrectness NTRUPlus768ROMDistributions.
require import NTRUPlus768FreshRetryLaw NTRUPlus768NumericalDFRModel.
require import NTRUPlus768StoppedKeygenModel NTRUPlus768StoppedKeygenPrefix.
require import NTRUPlus768CCAOraclePorts NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
require import NTRUPlus768CCADecapOracle NTRUPlus768CCAProbability.

(* The challenge is issued before the sole adversary phase. The oracle
   signatures expose queries, never initialization or private state. *)
module type CCAAdversary(H:CCAOraclePort,D:CCADecapPort) = {
 proc guess(pk:W8.t Array1152.t,ct:W8.t Array1152.t,key:W8.t Array32.t) : bool
   {H.e,H.f,H.g,H.h,D.decap}
}.
module type CCAExtendedAdversary(H:CCAExtendedOraclePort,D:CCADecapPort) = {
 proc guess(pk:W8.t Array1152.t,ct:W8.t Array1152.t,key:W8.t Array32.t) : bool
   {H.e,H.f,H.g,H.h,H.raw,D.decap}
}.
module CCATypedView(H:CCAExtendedOraclePort) : CCAOraclePort = {
 proc e=H.e
 proc f=H.f
 proc g=H.g
 proc h=H.h
}.
module TypedAdversaryLift(A:CCAAdversary,H:CCAExtendedOraclePort,D:CCADecapPort) = {
 proc guess=A(CCATypedView(H),D).guess
}.

type cca_encapsulation = (W8.t Array1152.t * W8.t Array32.t) option.
op cca_encap_result (r:encap_result) : cca_encapsulation =
 if r.`3=W32.zero then Some(r.`1,r.`2) else None.
module CCAEncapStatus = {
 proc run(pk:W8.t Array1152.t) : cca_encapsulation = {
  var result:encap_result;
  result <@ EncapRandom(SHAKEFROM,SHAKEGROM,SHAKEHROM,UniformCoins).run(pk,witness);
  return cca_encap_result result;
 }
}.

module CCAChallengeOriginal(A:CCAExtendedAdversary) = {
 module Adv=A(SharedCCAExtendedOracles,CCADecapOracle)
 proc run(pk:W8.t Array1152.t,sk:W8.t Array2336.t) : bool = {
  var real:encap_result; var random:W8.t Array32.t;
  var bit,guess:bool;
  real <@ EncapRandom(SHAKEFROM,SHAKEGROM,SHAKEHROM,UniformCoins).run(pk,witness);
  random <$ uniform32; bit <$ dbool;
  CCADecapOracle.init(sk,real.`1);
  guess <@ Adv.guess(pk,real.`1,if bit then random else real.`2);
  return guess=bit;
 }
}.
module CCAChallengeOption(A:CCAExtendedAdversary) = {
 module Adv=A(SharedCCAExtendedOracles,CCADecapOracle)
 proc run(pk:W8.t Array1152.t,sk:W8.t Array2336.t) : bool = {
  var encapsulated:cca_encapsulation; var random:W8.t Array32.t;
  var bit,guess,win:bool;
  encapsulated <@ CCAEncapStatus.run(pk);
  random <$ uniform32; bit <$ dbool;
  win <- false;
  if(encapsulated<>None){
   CCADecapOracle.init(sk,(oget encapsulated).`1);
   guess <@ Adv.guess(pk,(oget encapsulated).`1,
     if bit then random else (oget encapsulated).`2);
   win <- guess=bit;
  }
  return win;
 }
}.

(* This is a subdistribution game: actual unbounded KeyGen is retained,
   and no outcome is assigned to a nonreturning computation. *)
module CCAOriginalGame(A:CCAExtendedAdversary) = {
 proc run() : bool = {
  var pk:W8.t Array1152.t; var sk:W8.t Array2336.t; var win:bool;
  ROMInit.init(); RawXOFStreams.init(); CCADecapOracle.reset();
  (pk,sk) <@ Keygen(UniformSeedRNG,ExpandROM,SHAKEFROM).run();
  win <@ CCAChallengeOriginal(A).run(pk,sk);
  return win;
 }
}.
module CCAOptionGame(A:CCAExtendedAdversary) = {
 proc run() : bool = {
  var pk:W8.t Array1152.t; var sk:W8.t Array2336.t; var win:bool;
  ROMInit.init(); RawXOFStreams.init(); CCADecapOracle.reset();
  (pk,sk) <@ Keygen(UniformSeedRNG,ExpandROM,SHAKEFROM).run();
  win <@ CCAChallengeOption(A).run(pk,sk);
  return win;
 }
}.

(* Stopping is confined to analysis setup. A returned None means that
   setup exhausted its attempt budget, and the adversary was not called. *)
module CCAStoppedBody(A:CCAExtendedAdversary) = {
 proc run(qf:int,qg:int) : bool option = {
  var setup:stopped_output; var out:keygen_output;
  var result:bool option; var win:bool;
  ROMInit.init(); RawXOFStreams.init(); CCADecapOracle.reset();
  setup <@ StoppedKeygen(UniformSeedRNG,ExpandROM).run(qf,qg,witness);
  result <- None;
  if(setup.`1<>None){
   out <- oget setup.`1;
   win <@ CCAChallengeOption(A).run(out.`1.`kg_pk,out.`1.`kg_sk);
   result <- Some win;
  }
  return result;
 }
}.
module CCAFiniteGame(A:CCAExtendedAdversary) = CompleteFallback(CCAStoppedBody(A)).
module CCATypedOriginalGame(A:CCAAdversary) = CCAOriginalGame(TypedAdversaryLift(A)).
module CCATypedOptionGame(A:CCAAdversary) = CCAOptionGame(TypedAdversaryLift(A)).
module CCATypedFiniteGame(A:CCAAdversary) = CCAFiniteGame(TypedAdversaryLift(A)).

lemma cca_encap_status_lossless : islossless CCAEncapStatus.run.
proof.
 proc; call(encap_random_lossless UniformCoins SHAKEFROM SHAKEGROM SHAKEHROM
   uniform_coins_ll ro_f_shake_ll ro_g_shake_ll ro_h_shake_ll); auto.
qed.

lemma cca_challenge_original_lossless
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams}) :
 islossless A(SharedCCAExtendedOracles,CCADecapOracle).guess =>
 islossless CCAChallengeOriginal(A).run.
proof.
 move=>hA; proc; call hA; call cca_decap_init_lossless.
 rnd; rnd; call(encap_random_lossless UniformCoins SHAKEFROM SHAKEGROM SHAKEHROM
   uniform_coins_ll ro_f_shake_ll ro_g_shake_ll ro_h_shake_ll).
 auto; smt(dbool_ll uniform32_ll).
qed.
lemma cca_challenge_option_lossless
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams}) :
 islossless A(SharedCCAExtendedOracles,CCADecapOracle).guess =>
 islossless CCAChallengeOption(A).run.
proof.
 move=>hA; proc; seq 4:true; 1,4,5:by auto.
 + wp; rnd; rnd; call cca_encap_status_lossless; auto; smt(dbool_ll uniform32_ll).
 if; last by auto.
 wp; call hA; call cca_decap_init_lossless; auto.
qed.
lemma cca_stopped_body_lossless
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams}) :
 islossless A(SharedCCAExtendedOracles,CCADecapOracle).guess =>
 islossless CCAStoppedBody(A).run.
proof.
 move=>hA; proc; seq 5:true; 1,4,5:by auto.
 + wp; call(stopped_keygen_lossless UniformSeedRNG ExpandROM uniform_seed_rng_ll ro_e_shake_ll).
   call cca_decap_reset_lossless; call raw_stream_init_ll; call rom_init_ll; auto.
 if; last by auto.
 wp; call(cca_challenge_option_lossless A hA); auto.
qed.
lemma cca_finite_game_lossless
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams}) :
 islossless A(SharedCCAExtendedOracles,CCADecapOracle).guess =>
 islossless CCAFiniteGame(A).run.
proof. move=>hA; exact(cca_fallback_lossless (CCAStoppedBody(A)) (cca_stopped_body_lossless A hA)). qed.

lemma cca_finite_game_win
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams}) &m qf qg :
 Pr[CCAFiniteGame(A).run(qf,qg) @ &m:res]=
 Pr[CCAStoppedBody(A).run(qf,qg) @ &m:res=Some true]+
 Pr[CCAStoppedBody(A).run(qf,qg) @ &m:res=None]/2%r.
proof. exact(cca_fallback_win (CCAStoppedBody(A)) &m qf qg). qed.

lemma cca_original_partial_normalization
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams}) &m :
 Pr[CCAOriginalGame(A).run() @ &m:res]-1%r/2%r =
 (Pr[CCAOriginalGame(A).run() @ &m:res]-Pr[CCAOriginalGame(A).run() @ &m:!res])/2%r-
 (1%r-Pr[CCAOriginalGame(A).run() @ &m:true])/2%r.
proof. exact(cca_partial_signed_identity (CCAOriginalGame(A)) &m). qed.

require import NTRUPlus768CCASetup.

lemma cca_encap_same_valid :
 equiv[EncapRandom(SHAKEFROM,SHAKEGROM,SHAKEHROM,UniformCoins).run ~
       EncapRandom(SHAKEFROM,SHAKEGROM,SHAKEHROM,UniformCoins).run :
 ={pk,workspace,glob ROF,glob ROG,glob ROH} /\ encap_key_canonical pk{1} ==>
 ={res,glob ROF,glob ROG,glob ROH} /\ res.`3{1}=W32.zero].
proof.
 conseq (_: _ ==> ={res,glob ROF,glob ROG,glob ROH})
   (cca_encap_random_status_any UniformCoins SHAKEFROM SHAKEGROM SHAKEHROM) _ => />.
 sim.
qed.
lemma cca_challenge_original_option
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams}) :
 equiv[CCAChallengeOriginal(A).run ~ CCAChallengeOption(A).run :
 ={pk,sk,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob CCADecapOracle,glob RawXOFStreams} /\
 encap_key_canonical pk{1} ==>
 ={res,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob CCADecapOracle,glob RawXOFStreams}].
proof.
 proc; inline{2} CCAEncapStatus.run.
 seq 1 3 : (={pk,sk,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob CCADecapOracle,glob RawXOFStreams} /\
   encapsulated{2}=Some(real.`1,real.`2){1}).
 + wp; call cca_encap_same_valid.
   auto=> />.
   move=> &hr hk result hs; by rewrite /cca_encap_result hs.
 seq 2 3 : (={pk,sk,random,bit,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob CCADecapOracle,glob RawXOFStreams} /\
   encapsulated{2}=Some(real.`1,real.`2){1}).
 + wp; rnd; rnd; auto.
 rcondt{2} 1; first by auto.
 wp; call (_: ={glob ROE,glob ROF,glob ROG,glob ROH,glob CCADecapOracle,glob RawXOFStreams}); 1..6: by sim.
 inline CCADecapOracle.init; auto.
qed.
lemma cca_original_option_equiv
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams}) :
 equiv[CCAOriginalGame(A).run ~ CCAOptionGame(A).run : ={glob A} ==>
 ={res,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob CCADecapOracle,glob RawXOFStreams}].
proof.
 proc; call(cca_challenge_original_option A).
 call (_: ={glob ROE,glob ROF} ==> ={res,glob ROE,glob ROF} /\ encap_key_canonical res.`1{1}).
 + conseq (_: _ ==> ={res,glob ROE,glob ROF})
     (cca_keygen_public_canonical UniformSeedRNG ExpandROM) _ => />.
   sim.
 inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init CCADecapOracle.reset.
 auto.
qed.
lemma cca_original_option_event
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams}) &m (event:bool->bool) :
 Pr[CCAOriginalGame(A).run() @ &m:event res]=
 Pr[CCAOptionGame(A).run() @ &m:event res].
proof. byequiv(cca_original_option_equiv A)=> //. qed.

module CCAStoppedOriginalBody(A:CCAExtendedAdversary) = {
 proc run(qf:int,qg:int) : bool option = {
  var setup:stopped_output; var out:keygen_output;
  var result:bool option; var win:bool;
  ROMInit.init(); RawXOFStreams.init(); CCADecapOracle.reset();
  setup <@ StoppedKeygen(UniformSeedRNG,ExpandROM).run(qf,qg,witness);
  result <- None;
  if(setup.`1<>None){
   out <- oget setup.`1;
   win <@ CCAChallengeOriginal(A).run(out.`1.`kg_pk,out.`1.`kg_sk);
   result <- Some win;
  }
  return result;
 }
}.
lemma cca_stopped_same_valid :
 equiv[StoppedKeygen(UniformSeedRNG,ExpandROM).run ~ StoppedKeygen(UniformSeedRNG,ExpandROM).run :
 ={qf,qg,workspace,glob ROE,glob ROF} ==>
 ={res,glob ROE,glob ROF} /\ (res.`1{1}<>None => encap_key_canonical (oget res.`1{1}).`1.`kg_pk)].
proof.
 conseq (_: _ ==> ={res,glob ROE,glob ROF})
   (cca_stopped_keygen_valid UniformSeedRNG ExpandROM) _ => />.
 + move=> &m1 &m2 hqf hqg hws result fm hvalid hn; have [hk hc]:=hvalid hn.
   exact(cca_rom_key_canonical _ _ hk).
 sim.
qed.
lemma cca_stopped_original_option
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams}) :
 equiv[CCAStoppedOriginalBody(A).run ~ CCAStoppedBody(A).run : ={qf,qg,glob A} ==>
 ={res,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob CCADecapOracle,glob RawXOFStreams}].
proof.
 proc; seq 5 5 : (={setup,result,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob CCADecapOracle,glob RawXOFStreams} /\
 (setup.`1{1}<>None => encap_key_canonical (oget setup.`1{1}).`1.`kg_pk)).
 + wp; call cca_stopped_same_valid.
   inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init CCADecapOracle.reset; auto.
 if; auto.
 wp; call(cca_challenge_original_option A); auto.
qed.

lemma cca_typed_original_option
 (A<:CCAAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams}) :
 equiv[CCATypedOriginalGame(A).run ~ CCATypedOptionGame(A).run : ={glob A} ==>
 ={res,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob CCADecapOracle,glob RawXOFStreams}].
proof. exact(cca_original_option_equiv (TypedAdversaryLift(A))). qed.
lemma cca_typed_finite_lossless
 (A<:CCAAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams}) :
 islossless A(CCATypedView(SharedCCAExtendedOracles),CCADecapOracle).guess =>
 islossless CCATypedFiniteGame(A).run.
proof. move=>hA; exact(cca_finite_game_lossless (TypedAdversaryLift(A)) hA). qed.

module CCAFiniteOriginalGame(A:CCAExtendedAdversary) = CompleteFallback(CCAStoppedOriginalBody(A)).
lemma cca_finite_original_option
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams}) :
 equiv[CCAFiniteOriginalGame(A).run ~ CCAFiniteGame(A).run : ={qf,qg,glob A} ==>
 ={res,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob CCADecapOracle,glob RawXOFStreams}].
proof.
 proc; inline CompleteFallback(CCAStoppedOriginalBody(A)).sample CompleteFallback(CCAStoppedBody(A)).sample.
 wp; rnd; call(cca_stopped_original_option A); auto.
qed.

(* With no f-attempt budget, setup returns before encapsulation and before
   the adversary phase. No adversary losslessness premise is needed. *)
lemma cca_stopped_nonpositive_setup
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams}) &m :
 phoare[CCAStoppedBody(A).run : qf<=0 /\ (glob A)=(glob A){m} ==>
 res=None /\ (glob A)=(glob A){m} /\
 CCADecapOracle.cstar=None /\ CCADecapOracle.count=0]=1%r.
proof.
 proc; inline ROMInit.init ROE.init ROF.init ROG.init ROH.init
   RawXOFStreams.init CCADecapOracle.reset
   StoppedKeygen(UniformSeedRNG,ExpandROM).run
   BoundedRetry(UniformSeedRNG,ExpandROM).f BoundedRetry(UniformSeedRNG,ExpandROM).f_from.
 sp; rcondf 1; first by auto=> />; rewrite /retry_initial /=; smt().
 sp; rcondf 1; first by auto=> />; rewrite /retry_initial /=; smt(W64.to_uint0 W64.to_uint1).
 sp; rcondf 1; auto.
qed.
lemma cca_finite_zero_setup_fair
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams}) &m qg :
 Pr[CCAFiniteGame(A).run(0,qg) @ &m:res]=1%r/2%r.
proof.
 apply(cca_fallback_always_none (CCAStoppedBody(A)) &m 0 qg).
 have hj:Pr[CCAStoppedBody(A).run(0,qg) @ &m:
   res=None /\ (glob A)=(glob A){m} /\ CCADecapOracle.cstar=None /\ CCADecapOracle.count=0]=1%r.
 + byphoare(cca_stopped_nonpositive_setup A &m)=> //.
 have hsub:Pr[CCAStoppedBody(A).run(0,qg) @ &m:
   res=None /\ (glob A)=(glob A){m} /\ CCADecapOracle.cstar=None /\ CCADecapOracle.count=0]
   <=Pr[CCAStoppedBody(A).run(0,qg) @ &m:res=None] by rewrite Pr[mu_sub].
 have hu:Pr[CCAStoppedBody(A).run(0,qg) @ &m:res=None]<=1%r by smt(mu_bounded).
 smt().
qed.

(* Exact challenge exclusion also frames every raw-XOF suffix cache and
   every typed table included in RawXOFStreams' global state. *)
lemma cca_challenge_blocked_raw_state c0 sk0 n0 &m :
 phoare[CCADecapOracle.decap : ct=c0 /\ CCADecapOracle.cstar=Some c0 /\
 CCADecapOracle.sk=sk0 /\ CCADecapOracle.count=n0 /\
 (glob RawXOFStreams)=(glob RawXOFStreams){m} ==>
 res=None /\ CCADecapOracle.cstar=Some c0 /\ CCADecapOracle.sk=sk0 /\
 CCADecapOracle.count=n0+1 /\
 (glob RawXOFStreams)=(glob RawXOFStreams){m}]=1%r.
proof. proc; rcondt 2; auto. qed.
