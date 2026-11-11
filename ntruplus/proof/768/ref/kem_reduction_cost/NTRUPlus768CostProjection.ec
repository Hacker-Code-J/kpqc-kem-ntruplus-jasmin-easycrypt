require import AllCore List Distr FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array768 Array1152.
require import NTRUPlus768SecModel NTRUPlus768SecGames NTRUPlus768SecGOracles.
require import NTRUPlus768SecExtractModel NTRUPlus768SecExtract NTRUPlus768SecReduction NTRUPlus768SecBaseGames.
require import NTRUPlus768SimModel NTRUPlus768SimSampling NTRUPlus768SimOracles NTRUPlus768SimLookup.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
require import NTRUPlus768FOEagerG NTRUPlus768FOGAdapters NTRUPlus768CCAOraclePorts NTRUPlus768CCAGame NTRUPlus768CCADecapOracle.
require import NTRUPlus768PKEModel NTRUPlus768PKEKeyDistribution.
require import NTRUPlus768OWGames NTRUPlus768OWCodec NTRUPlus768OWUniform NTRUPlus768OWKeyConditioning NTRUPlus768INJGames.
require import NTRUPlus768CostExtract NTRUPlus768CostLookup NTRUPlus768CostRaw.

(* These ports discard only local resource results. There is no added
   global accumulator, no accumulated running-time result and no PPT claim. *)
module CostExtractPort = {
 proc run(pk ct:W8.t Array1152.t,excluded:pke_poly option,queries:W8.t Array1152.t list)
 : (pke_poly*pke_poly) option = {
  var out:((pke_poly*pke_poly) option)*int;
  out<@CostExtract.run(pk,ct,excluded,queries);return out.`1;
 }
}.
module CostRawReply(G:FOGPort,H:SimHPort) = {
 proc get(input:W8.t list,outlen:int):W8.t list option = {
  var out:W8.t list option*int*int;
  out<@CostRaw(G,H).get(input,outlen);return out.`1;
 }
}.
module CostOracles(G:FOGPort,H:SimHPort) : CCAExtendedOraclePort = {
 proc e=SharedCCAOracles.e
 proc f=SharedCCAOracles.f
 proc g=SimOracles(G,H).g
 proc h=SimLoggedH(H).get
 proc raw=CostRawReply(G,H).get
}.
module CostSecPhase(A:CCAExtendedAdversary,G:FOGPort) = {
 proc run(pk ct:W8.t Array1152.t,key:W8.t Array32.t):bool = {
  var suffix:W8.t Array32.t;var answer:bool;
  suffix<@ROF.get(pk);SimPublic.init(pk,suffix,ct);SimHistory.init();
  answer<@A(CostOracles(G,SimHActual),CostLookupReply(G)).guess(pk,ct,key);
  return answer;
 }
}.
module CostSecTranscript(A:CCAExtendedAdversary) = {
 proc run(pk ct:W8.t Array1152.t):W8.t Array1152.t list = {
  var key:W8.t Array32.t;var ignored:bool;
  SecGHistory.init();key<$uniform32;
  ignored<@CostSecPhase(A,SecGLogged(FOGActual)).run(pk,ct,key);
  return SecGHistory.queries;
 }
}.
module CostINJReducer(A:CCAExtendedAdversary) : SecINJAdversary = {
 proc run(pk:W8.t Array1152.t):sec_collision = {
  var code,r:pke_poly;var ct:W8.t Array1152.t;var queries:W8.t Array1152.t list;
  var out:(pke_poly*pke_poly) option;
  code<$pke_psi1;r<$pke_psi1;ct<-pke_ciphertext pk code r;
  queries<@CostSecTranscript(A).run(pk,ct);
  out<@CostExtractPort.run(pk,ct,Some r,queries);
  return if out=None then (code,code,r,r) else (code,(oget out).`1,r,(oget out).`2);
 }
}.
module CostOWReducer(A:CCAExtendedAdversary) : SecOWAdversary = {
 proc run(pk ct:W8.t Array1152.t):pke_poly = {
  var queries:W8.t Array1152.t list;var out:(pke_poly*pke_poly) option;
  queries<@CostSecTranscript(A).run(pk,ct);
  out<@CostExtractPort.run(pk,ct,None,queries);
  return if out=None then sec_zero else (oget out).`1;
 }
}.
module CostINJNTRU(A:CCAExtendedAdversary) = INJNTRUReduction(SecINJAuxAdapter(CostINJReducer(A))).
module CostOWNTRU(A:CCAExtendedAdversary) = OWNTRUReduction(SecOWAuxAdapter(CostOWReducer(A))).
module CostRLWE(A:CCAExtendedAdversary) = OWRLWESolver(SecOWAuxAdapter(CostOWReducer(A))).

lemma cost_extract_port_projection :
 equiv[CostExtractPort.run ~ SecExtract.run: ={arg} ==> ={res}].
proof.
 proc*;inline{1} CostExtractPort.run;wp;call cost_extract_projection;auto.
qed.
lemma cost_raw_reply_projection :
 equiv[CostRawReply(SecGLogged(FOGActual),SimHActual).get ~ SimRaw(SecGLogged(FOGActual),SimHActual).get:
 ={input,outlen,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob SimHistory,glob SecGHistory} ==>
 ={res,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob SimHistory,glob SecGHistory}].
proof.
 proc*;inline{1} CostRawReply(SecGLogged(FOGActual),SimHActual).get;wp;
 call cost_raw_logged_projection;auto.
qed.

(* The exclusion list is exactly the one used by the original SecTranscript
   and INJ/OW reductions. The local annotations require no new exclusion. *)
lemma cost_adversary_projection (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[A(CostOracles(SecGLogged(FOGActual),SimHActual),CostLookupReply(SecGLogged(FOGActual))).guess ~
 A(SimOracles(SecGLogged(FOGActual),SimHActual),SimLookup(SecGLogged(FOGActual))).guess:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,SecGHistory.queries} ==> ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,SecGHistory.queries}].
proof.
 proc(={ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,SecGHistory.queries})=> //.
 + by sim.
 + by sim.
 + by sim.
 + by sim.
 + conseq cost_raw_reply_projection=> /#.
 conseq cost_lookup_logged_reply_projection=> /#.
qed.
lemma cost_sec_phase_projection (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[CostSecPhase(A,SecGLogged(FOGActual)).run ~ SecPhase(A,SecGLogged(FOGActual)).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,SecGHistory.queries} ==> ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,SecGHistory.queries}].
proof.
 proc;call(cost_adversary_projection A).
 inline SimPublic.init SimHistory.init;wp.
 call(_: ={arg,glob ROF} ==> ={res,glob ROF});first by sim.
 auto.
qed.
lemma cost_sec_transcript_projection (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[CostSecTranscript(A).run ~ SecTranscript(A).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,SecGHistory.queries} ==> ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,SecGHistory.queries}].
proof.
 proc;call(cost_sec_phase_projection A);rnd;inline SecGHistory.init;auto.
qed.
lemma cost_inj_reducer_projection (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[CostINJReducer(A).run ~ SecINJReducer(A).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,SecGHistory.queries} ==> ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,SecGHistory.queries}].
proof.
 proc;wp;call cost_extract_port_projection;
 call(cost_sec_transcript_projection A);wp;rnd;rnd;auto.
qed.
lemma cost_ow_reducer_projection (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[CostOWReducer(A).run ~ SecOWReducer(A).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,SecGHistory.queries} ==> ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,SecGHistory.queries}].
proof.
 proc;wp;call cost_extract_port_projection;call(cost_sec_transcript_projection A);auto.
qed.
lemma cost_inj_aux_projection (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[SecINJAuxAdapter(CostINJReducer(A)).run ~ SecINJAuxAdapter(SecINJReducer(A)).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,SecGHistory.queries} ==> ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,SecGHistory.queries}].
proof.
 proc;call(cost_inj_reducer_projection A).
 call(_: ={arg,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams} ==>
 ={glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams});first by sim.
 auto.
qed.
lemma cost_ow_aux_projection (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[SecOWAuxAdapter(CostOWReducer(A)).run ~ SecOWAuxAdapter(SecOWReducer(A)).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,SecGHistory.queries} ==> ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,SecGHistory.queries}].
proof.
 proc;call(cost_ow_reducer_projection A).
 call(_: ={arg,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams} ==>
 ={glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams});first by sim.
 auto.
qed.

(* Three actual hardness-side algorithms, with the same public challenges,
   unit guards and auxiliary simulation as the original reductions. *)
lemma cost_inj_ntru_projection (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[CostINJNTRU(A).run ~ INJNTRUReduction(SecINJAuxAdapter(SecINJReducer(A))).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,SecGHistory.queries} ==> ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,SecGHistory.queries}].
proof.
 proc;inline INJFieldKernel(SecINJAuxAdapter(CostINJReducer(A))).guess INJFieldKernel(SecINJAuxAdapter(SecINJReducer(A))).guess;wp;sp.
 if;first by auto.
 + inline INJKernel(SecINJAuxAdapter(CostINJReducer(A))).run INJKernel(SecINJAuxAdapter(SecINJReducer(A))).run;wp;
   call(cost_inj_aux_projection A);auto.
 auto.
qed.
lemma cost_ow_ntru_projection (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[CostOWNTRU(A).run ~ OWNTRUReduction(SecOWAuxAdapter(SecOWReducer(A))).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,SecGHistory.queries} ==> ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,SecGHistory.queries}].
proof.
 proc;inline OWFieldKernel(SecOWAuxAdapter(CostOWReducer(A))).guess OWFieldKernel(SecOWAuxAdapter(SecOWReducer(A))).guess;wp;sp.
 if;first by auto.
 + inline OWKernel(SecOWAuxAdapter(CostOWReducer(A))).run OWKernel(SecOWAuxAdapter(SecOWReducer(A))).run;wp;
   call(cost_ow_aux_projection A);wp;rnd;rnd;auto.
 auto.
qed.
lemma cost_rlwe_projection (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[CostRLWE(A).run ~ OWRLWESolver(SecOWAuxAdapter(SecOWReducer(A))).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,SecGHistory.queries} ==> ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,SecGHistory.queries}].
proof.
 proc;sp;if;first by auto.
 + wp;call(cost_ow_aux_projection A);auto.
 auto.
qed.

lemma cost_inj_ntru_real_probability (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) &m :
 Pr[OWNTRURealGame(CostINJNTRU(A)).run()@&m:res]=
 Pr[OWNTRURealGame(INJNTRUReduction(SecINJAuxAdapter(SecINJReducer(A)))).run()@&m:res].
proof.
 byequiv(_: ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,SecGHistory.queries} ==> ={res})=> //.
 proc;call(cost_inj_ntru_projection A);rnd;auto.
qed.
lemma cost_inj_ntru_uniform_probability (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) &m :
 Pr[OWNTRUUniformGame(CostINJNTRU(A)).run()@&m:res]=
 Pr[OWNTRUUniformGame(INJNTRUReduction(SecINJAuxAdapter(SecINJReducer(A)))).run()@&m:res].
proof.
 byequiv(_: ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,SecGHistory.queries} ==> ={res})=> //.
 proc;call(cost_inj_ntru_projection A);rnd;auto.
qed.
lemma cost_ow_ntru_real_probability (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) &m :
 Pr[OWNTRURealGame(CostOWNTRU(A)).run()@&m:res]=
 Pr[OWNTRURealGame(OWNTRUReduction(SecOWAuxAdapter(SecOWReducer(A)))).run()@&m:res].
proof.
 byequiv(_: ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,SecGHistory.queries} ==> ={res})=> //.
 proc;call(cost_ow_ntru_projection A);rnd;auto.
qed.
lemma cost_ow_ntru_uniform_probability (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) &m :
 Pr[OWNTRUUniformGame(CostOWNTRU(A)).run()@&m:res]=
 Pr[OWNTRUUniformGame(OWNTRUReduction(SecOWAuxAdapter(SecOWReducer(A)))).run()@&m:res].
proof.
 byequiv(_: ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,SecGHistory.queries} ==> ={res})=> //.
 proc;call(cost_ow_ntru_projection A);rnd;auto.
qed.
lemma cost_rlwe_probability (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) &m :
 Pr[OWRLWEGame(CostRLWE(A)).run()@&m:res]=
 Pr[OWRLWEGame(OWRLWESolver(SecOWAuxAdapter(SecOWReducer(A)))).run()@&m:res].
proof.
 byequiv(_: ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,SecGHistory.queries} ==> ={res})=> //.
 proc;wp;call(cost_rlwe_projection A);wp;rnd;rnd;rnd;auto.
qed.
