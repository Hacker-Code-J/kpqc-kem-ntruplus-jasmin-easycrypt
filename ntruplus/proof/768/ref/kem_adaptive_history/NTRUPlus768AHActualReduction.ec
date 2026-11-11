require import AllCore List Distr FMap StdOrder.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152.
require import NTRUPlus768AHState NTRUPlus768AHAdapter NTRUPlus768AHReduction.
require import NTRUPlus768FOModel NTRUPlus768FOEagerG NTRUPlus768FOGAdapters.
require import NTRUPlus768CCAOraclePorts NTRUPlus768CCAGame NTRUPlus768CCADecapOracle NTRUPlus768CCAStatusAdapter.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
require import NTRUPlus768SimModel NTRUPlus768SimOracles NTRUPlus768SimLookup NTRUPlus768SimSampling.
require import NTRUPlus768SecModel NTRUPlus768SecGames NTRUPlus768SecReduction NTRUPlus768SecGOracles.
require import NTRUPlus768SecExtractModel NTRUPlus768SecExtract NTRUPlus768SecBaseGames.
require import NTRUPlus768PKEModel NTRUPlus768PKEKeyDistribution.
require import NTRUPlus768CPAModel NTRUPlus768CPAReduction.
require import NTRUPlus768OWGames NTRUPlus768INJGames NTRUPlus768OWKeyConditioning.
import RealOrder RField.

(* H responses are recorded only by AHWrapper's concrete store.
   The existing FOGRaw port preserves typed and untyped behavior without
   any SimHistory access, including in its own H branch. *)
module AHActualOracles(G:FOGPort) : CCAExtendedOraclePort = {
 proc e=SharedCCAOracles.e
 proc f=SharedCCAOracles.f
 proc g=SimOracles(G,SimHActual).g
 proc h=ROH.get
 proc raw=FOGRaw(G).get
}.
module AHRejectD : CCADecapPort = {
 proc decap(ct:W8.t Array1152.t):cca_reply = {return None;}
}.
module AHActualPhase(S:AHStore,A:CCAExtendedAdversary,G:FOGPort) = {
 proc run(pk ct:W8.t Array1152.t,key:W8.t Array32.t):bool = {
  var suffix:W8.t Array32.t;var answer:bool;
  suffix<@ROF.get(pk);
  answer<@AHWrapper(S,A,AHActualOracles(G),AHRejectD).guess(pk,ct,key);
  return answer;
 }
}.
module AHActualTranscript(S:AHStore,A:CCAExtendedAdversary) = {
 proc run(pk ct:W8.t Array1152.t):W8.t Array1152.t list = {
  var key:W8.t Array32.t;var ignored:bool;
  SecGHistory.init();key<$uniform32;
  ignored<@AHActualPhase(S,A,SecGLogged(FOGActual)).run(pk,ct,key);
  return SecGHistory.queries;
 }
}.
module AHActualINJReducer(S:AHStore,A:CCAExtendedAdversary) : SecINJAdversary = {
 proc run(pk:W8.t Array1152.t):sec_collision = {
  var code,r:pke_poly;var ct:W8.t Array1152.t;var queries:W8.t Array1152.t list;
  var out:(pke_poly*pke_poly) option;
  code<$pke_psi1;r<$pke_psi1;ct<-pke_ciphertext pk code r;
  queries<@AHActualTranscript(S,A).run(pk,ct);
  out<@SecExtract.run(pk,ct,Some r,queries);
  return if out=None then (code,code,r,r) else (code,(oget out).`1,r,(oget out).`2);
 }
}.
module AHActualOWReducer(S:AHStore,A:CCAExtendedAdversary) : SecOWAdversary = {
 proc run(pk ct:W8.t Array1152.t):pke_poly = {
  var queries:W8.t Array1152.t list;var out:(pke_poly*pke_poly) option;
  queries<@AHActualTranscript(S,A).run(pk,ct);out<@SecExtract.run(pk,ct,None,queries);
  return if out=None then sec_zero else (oget out).`1;
 }
}.
module AHActual_DI(S:AHStore,A:CCAExtendedAdversary) =
 INJNTRUReduction(SecINJAuxAdapter(AHActualINJReducer(S,A))).
module AHActual_DO(S:AHStore,A:CCAExtendedAdversary) =
 OWNTRUReduction(SecOWAuxAdapter(AHActualOWReducer(S,A))).
module AHActual_CO(S:AHStore,A:CCAExtendedAdversary) =
 OWRLWESolver(SecOWAuxAdapter(AHActualOWReducer(S,A))).

lemma ah_actual_h_projection
 (S<:AHStore {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[AHRecordH(S,AHActualOracles(SecGLogged(FOGActual))).get ~
 AHRecordH(S,SimOracles(SecGLogged(FOGActual),SimHActual)).get:
 ={arg,glob S,ROH.m} ==> ={res,glob S,ROH.m}].
proof.
 proc;call(_: ={arg,glob S} ==> ={glob S});first by proc true;auto.
 inline{2} SimOracles(SecGLogged(FOGActual),SimHActual).h SimHistory.record;wp.
 call(_: ={arg,ROH.m} ==> ={res,ROH.m});first by sim.
 auto.
qed.
lemma ah_actual_raw_projection :
 equiv[FOGRaw(SecGLogged(FOGActual)).get ~ SimRaw(SecGLogged(FOGActual),SimHActual).get:
 ={arg,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} ==>
 ={res,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries}].
proof.
 proc;inline SimRaw(SecGLogged(FOGActual),SimHActual).full
 FOGRaw(SecGLogged(FOGActual)).full FOGRawStreams(SecGLogged(FOGActual)).h
 SimLoggedH(SimHActual).get SimHistory.record;sim.
qed.

(* Only redundant map bookkeeping is erased. Both sides execute the
   same list scan and preserve its entire actual G-call transcript. *)
lemma ah_actual_adversary_projection
 (S<:AHStore {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[
 A(AHOracles(S,AHActualOracles(SecGLogged(FOGActual))),
   AHDecap(S,AHActualOracles(SecGLogged(FOGActual)))).guess ~
 A(AHOracles(S,SimOracles(SecGLogged(FOGActual),SimHActual)),
   AHDecap(S,SimOracles(SecGLogged(FOGActual),SimHActual))).guess:
 ={arg,glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} ==>
 ={res,glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries}].
proof.
 proc(={glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries})=> //.
 + by sim.
 + by sim.
 + by sim.
 + conseq(ah_actual_h_projection S)=> /#.
 + proc;inline AHRecordH(S,AHActualOracles(SecGLogged(FOGActual))).get
    AHRecordH(S,SimOracles(SecGLogged(FOGActual),SimHActual)).get
    AHActualOracles(SecGLogged(FOGActual)).raw
    SimOracles(SecGLogged(FOGActual),SimHActual).raw
    FOGRaw(SecGLogged(FOGActual)).full SimRaw(SecGLogged(FOGActual),SimHActual).full
    FOGRawStreams(SecGLogged(FOGActual)).h
    SimOracles(SecGLogged(FOGActual),SimHActual).h
    SimLoggedH(SimHActual).get SimHistory.record;
   sim.
 by sim.
qed.

lemma ah_actual_phase_projection
 (S<:AHStore {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[AHActualPhase(S,A,SecGLogged(FOGActual)).run ~
 SecPhase(AHWrapper(S,A),SecGLogged(FOGActual)).run:
 ={arg,glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} ==>
 ={res,glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries}].
proof.
 proc;inline AHWrapper(S,A,AHActualOracles(SecGLogged(FOGActual)),AHRejectD).guess
  AHWrapper(S,A,SimOracles(SecGLogged(FOGActual),SimHActual),SimLookup(SecGLogged(FOGActual))).guess;
 wp;call(ah_actual_adversary_projection S A).
 call(_: ={arg,glob S} ==> ={glob S});first by proc true;auto.
 call(_: ={arg,ROF.m} ==> ={res,ROF.m});first by sim.
 inline SimPublic.init SimHistory.init;wp.
 call(_: ={arg,ROF.m} ==> ={res,ROF.m});first by sim.
 auto.
qed.
lemma ah_actual_transcript_projection
 (S<:AHStore {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[AHActualTranscript(S,A).run ~ SecTranscript(AHWrapper(S,A)).run:
 ={arg,glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} ==>
 ={res,glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries}].
proof.
 proc;call(ah_actual_phase_projection S A);rnd;inline SecGHistory.init;auto.
qed.

(* Exact same-list transcript refinement through extraction and hardness games. *)
lemma ah_actual_inj_reducer_projection
 (S<:AHStore {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[AHActualINJReducer(S,A).run ~ SecINJReducer(AHWrapper(S,A)).run:
 ={arg,glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} ==> ={res,glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries}].
proof.
 proc;wp;call(_: ={arg} ==> ={res});first by sim.
 call(ah_actual_transcript_projection S A);wp;rnd;rnd;auto.
qed.
lemma ah_actual_ow_reducer_projection
 (S<:AHStore {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[AHActualOWReducer(S,A).run ~ SecOWReducer(AHWrapper(S,A)).run:
 ={arg,glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} ==> ={res,glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries}].
proof.
 proc;wp;call(_: ={arg} ==> ={res});first by sim.
 call(ah_actual_transcript_projection S A);auto.
qed.
lemma ah_actual_inj_aux_projection
 (S<:AHStore {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[SecINJAuxAdapter(AHActualINJReducer(S,A)).run ~ SecINJAuxAdapter(SecINJReducer(AHWrapper(S,A))).run:
 ={arg,glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} ==> ={res,glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries}].
proof.
 proc;call(ah_actual_inj_reducer_projection S A).
 call(_: ={arg,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams} ==>
 ={glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams});first by sim.
 auto.
qed.
lemma ah_actual_ow_aux_projection
 (S<:AHStore {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[SecOWAuxAdapter(AHActualOWReducer(S,A)).run ~ SecOWAuxAdapter(SecOWReducer(AHWrapper(S,A))).run:
 ={arg,glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} ==> ={res,glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries}].
proof.
 proc;call(ah_actual_ow_reducer_projection S A).
 call(_: ={arg,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams} ==>
 ={glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams});first by sim.
 auto.
qed.
lemma ah_actual_inj_ntru_projection
 (S<:AHStore {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[AHActual_DI(S,A).run ~ AH_DI(S,A).run:
 ={arg,glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} ==> ={res,glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries}].
proof.
 proc;inline INJFieldKernel(SecINJAuxAdapter(AHActualINJReducer(S,A))).guess
 INJFieldKernel(SecINJAuxAdapter(SecINJReducer(AHWrapper(S,A)))).guess;wp;sp.
 if;first by auto.
 + inline INJKernel(SecINJAuxAdapter(AHActualINJReducer(S,A))).run
   INJKernel(SecINJAuxAdapter(SecINJReducer(AHWrapper(S,A)))).run;wp;
   call(ah_actual_inj_aux_projection S A);auto.
 auto.
qed.
lemma ah_actual_ow_ntru_projection
 (S<:AHStore {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[AHActual_DO(S,A).run ~ AH_DO(S,A).run:
 ={arg,glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} ==> ={res,glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries}].
proof.
 proc;inline OWFieldKernel(SecOWAuxAdapter(AHActualOWReducer(S,A))).guess
 OWFieldKernel(SecOWAuxAdapter(SecOWReducer(AHWrapper(S,A)))).guess;wp;sp.
 if;first by auto.
 + inline OWKernel(SecOWAuxAdapter(AHActualOWReducer(S,A))).run
   OWKernel(SecOWAuxAdapter(SecOWReducer(AHWrapper(S,A)))).run;wp;
   call(ah_actual_ow_aux_projection S A);wp;rnd;rnd;auto.
 auto.
qed.
lemma ah_actual_rlwe_projection
 (S<:AHStore {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[AHActual_CO(S,A).run ~ AH_CO(S,A).run:
 ={arg,glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} ==> ={res,glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries}].
proof.
 proc;sp;if;first by auto.
 + wp;call(ah_actual_ow_aux_projection S A);auto.
 auto.
qed.
lemma ah_actual_inj_ntru_real_probability
 (S<:AHStore {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) &m :
 Pr[OWNTRURealGame(AHActual_DI(S,A)).run()@&m:res]=
 Pr[OWNTRURealGame(AH_DI(S,A)).run()@&m:res].
proof.
 byequiv(_: ={glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} ==> ={res})=> //.
 proc;call(ah_actual_inj_ntru_projection S A);rnd;auto.
qed.
lemma ah_actual_inj_ntru_uniform_probability
 (S<:AHStore {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) &m :
 Pr[OWNTRUUniformGame(AHActual_DI(S,A)).run()@&m:res]=
 Pr[OWNTRUUniformGame(AH_DI(S,A)).run()@&m:res].
proof.
 byequiv(_: ={glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} ==> ={res})=> //.
 proc;call(ah_actual_inj_ntru_projection S A);rnd;auto.
qed.
lemma ah_actual_ow_ntru_real_probability
 (S<:AHStore {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) &m :
 Pr[OWNTRURealGame(AHActual_DO(S,A)).run()@&m:res]=
 Pr[OWNTRURealGame(AH_DO(S,A)).run()@&m:res].
proof.
 byequiv(_: ={glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} ==> ={res})=> //.
 proc;call(ah_actual_ow_ntru_projection S A);rnd;auto.
qed.
lemma ah_actual_ow_ntru_uniform_probability
 (S<:AHStore {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) &m :
 Pr[OWNTRUUniformGame(AHActual_DO(S,A)).run()@&m:res]=
 Pr[OWNTRUUniformGame(AH_DO(S,A)).run()@&m:res].
proof.
 byequiv(_: ={glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} ==> ={res})=> //.
 proc;call(ah_actual_ow_ntru_projection S A);rnd;auto.
qed.
lemma ah_actual_rlwe_probability
 (S<:AHStore {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) &m :
 Pr[OWRLWEGame(AHActual_CO(S,A)).run()@&m:res]=
 Pr[OWRLWEGame(AH_CO(S,A)).run()@&m:res].
proof.
 byequiv(_: ={glob A,glob S,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,SecGHistory.queries} ==> ={res})=> //.
 proc;wp;call(ah_actual_rlwe_projection S A);wp;rnd;rnd;rnd;auto.
qed.

(* Neither public map bookkeeping state is accessed by the actual
   transcript. Ideal ROH/ROG caches remain the existing oracle model. *)
lemma ah_actual_transcript_private_frame
 (S<:AHStore {-SimPublic,-SimHistory})
 (A<:CCAExtendedAdversary {-S,-SimPublic,-SimHistory}) log0 public0 :
 hoare[AHActualTranscript(S,A).run:
 SimHistory.h=log0 /\ glob SimPublic=public0 ==>
 SimHistory.h=log0 /\ glob SimPublic=public0].
proof.
 proc;call(_:true ==>true);first by trivial.
 rnd;inline SecGHistory.init;auto.
qed.

lemma ah_actual_cpa_hardness
 (S<:AHStore {-CPAReduction,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,
 -SimPublic,-SimHistory,-SecGHistory,-SecGMark})
 (A<:CCAExtendedAdversary {-S,-CPAReduction,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,
 -SimPublic,-SimHistory,-SecGHistory,-SecGMark}) &m :
 islossless S.init=>islossless S.snapshot=>islossless S.record=>
 (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
 islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
 islossless D.decap=>islossless A(H,D).guess)=>
 `|Pr[CPAGame(CPAReduction(AHWrapper(S,A))).run()@&m:res]-1%r/2%r|<=
 (Pr[OWNTRURealGame(AHActual_DI(S,A)).run()@&m:res]-
  Pr[OWNTRUUniformGame(AHActual_DI(S,A)).run()@&m:res]+1%r/(2%r^244))/ow_alpha_g+
 (Pr[OWNTRURealGame(AHActual_DO(S,A)).run()@&m:res]-
  Pr[OWNTRUUniformGame(AHActual_DO(S,A)).run()@&m:res]+
  Pr[OWRLWEGame(AHActual_CO(S,A)).run()@&m:res])/ow_alpha_g.
proof.
 move=>hi hs hr all.
 rewrite (ah_actual_inj_ntru_real_probability S A &m)
 (ah_actual_inj_ntru_uniform_probability S A &m)
 (ah_actual_ow_ntru_real_probability S A &m)
 (ah_actual_ow_ntru_uniform_probability S A &m)
 (ah_actual_rlwe_probability S A &m).
 exact(ah_cpa_hardness S A &m hi hs hr all).
qed.
