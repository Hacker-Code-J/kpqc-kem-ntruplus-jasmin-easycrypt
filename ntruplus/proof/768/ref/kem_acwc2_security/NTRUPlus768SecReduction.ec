require import AllCore List Distr DBool FMap StdOrder.
from Jasmin require import JWord.
require import Array32 Array96 Array768 Array1152 Array2336.
require import NTRUPlus768SecModel NTRUPlus768SecGames NTRUPlus768SecGOracles.
require import NTRUPlus768SecExtractModel NTRUPlus768SecExtract.
require import NTRUPlus768CPAReduction NTRUPlus768CPAChallengeBridge.
require import NTRUPlus768PKEModel NTRUPlus768PKEAlgebra NTRUPlus768PKEKeyDistribution NTRUPlus768ACWC2Domains.
require import NTRUPlus768EncapGuardSpec NTRUPlus768RRecCodec.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
require import NTRUPlus768SimModel NTRUPlus768FOGAdapters NTRUPlus768FOEagerG NTRUPlus768CCAGame.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768FreshRetryLaw.
import RealOrder.

(* Both reductions inspect only the actual finite public G transcript.
   They neither enumerate the ternary space nor receive a secret key. *)
module SecINJReducer(A:CCAExtendedAdversary) : SecINJAdversary = {
 proc run(pk:W8.t Array1152.t):sec_collision = {
  var code,r:pke_poly;var ct:W8.t Array1152.t;var queries:W8.t Array1152.t list;
  var out:(pke_poly*pke_poly) option;
  code<$pke_psi1;r<$pke_psi1;ct<-pke_ciphertext pk code r;
  queries<@SecTranscript(A).run(pk,ct);
  out<@SecExtract.run(pk,ct,Some r,queries);
  return if out=None then (code,code,r,r) else (code,(oget out).`1,r,(oget out).`2);
 }
}.
module SecOWReducer(A:CCAExtendedAdversary) : SecOWAdversary = {
 proc run(pk ct:W8.t Array1152.t):pke_poly = {
  var queries:W8.t Array1152.t list;var out:(pke_poly*pke_poly) option;
  queries<@SecTranscript(A).run(pk,ct);out<@SecExtract.run(pk,ct,None,queries);
  return if out=None then sec_zero else (oget out).`1;
 }
}.
module SecSource(A:CCAExtendedAdversary) = {
 proc run():sec_observation = {
  var pk,ct:W8.t Array1152.t;var sk:W8.t Array2336.t;
  var code,r:pke_poly;var queries:W8.t Array1152.t list;
  ROMInit.init();RawXOFStreams.init();
  (pk,sk)<@Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run();
  code<$pke_psi1;r<$pke_psi1;ct<-pke_ciphertext pk code r;
  queries<@SecTranscript(A).run(pk,ct);
  return {|so_win=false;so_pk=pk;so_ct=ct;so_code=code;so_r=r;so_queries=queries|};
 }
}.
op sec_data(s:sec_observation) = (s.`so_pk,s.`so_ct,s.`so_code,s.`so_r,s.`so_queries).
lemma sec_data_hit s t:sec_data s=sec_data t=>sec_hit s=sec_hit t.
proof. rewrite /sec_data /sec_hit;smt(). qed.
module type SecTranscriptPort = {proc run(pk ct:W8.t Array1152.t):W8.t Array1152.t list}.
module type SecSourcePort = {proc run():sec_observation}.
lemma sec_transcript_same(M<:SecTranscriptPort):equiv[M.run ~ M.run: ={arg,glob M} ==> ={res,glob M}].
proof. proc true;auto. qed.
lemma sec_source_same(M<:SecSourcePort):equiv[M.run ~ M.run: ={glob M} ==> ={res,glob M}].
proof. proc true;auto. qed.

lemma sec_run_transcript
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[SecRun(A,SecGLogged(FOGActual)).run ~ SecTranscript(A).run:
 ={pk,ct,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h} /\
 SecGHistory.queries{1}=[] ==>
 SecGHistory.queries{1}=res{2} /\
 ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,SecGHistory.queries}].
proof.
 proc;wp;call(cpa_phase_same (SecPhase(A,SecGLogged(FOGActual))));rnd;
 inline{2} SecGHistory.init;auto.
qed.
lemma sec_source_projection
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[SecRandomGame(A).run ~ SecSource(A).run:
 ={glob A,glob SimPublic,SimHistory.h} ==> sec_data res{1}=sec_data res{2}].
proof.
 proc;wp;call(sec_run_transcript A).
 inline{1} SecGHistory.init;wp;swap{1} 7 1;rnd;rnd.
 rnd{1};rnd{1};rnd{1}.
 call(cpa_gen_same (Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM))).
 inline ROMInit.init RawXOFStreams.init ROE.init ROF.init ROG.init ROH.init;auto=> />;
 smt(dbool_ll uniform96_ll).
qed.
lemma sec_source_hit
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) &m :
 Pr[SecRandomGame(A).run()@&m:sec_hit res]=Pr[SecSource(A).run()@&m:sec_hit res].
proof.
 byequiv(_: ={glob A,glob SimPublic,SimHistory.h} ==>sec_hit res{1}=sec_hit res{2})=> //.
 conseq(sec_source_projection A)=> //.
 + move=> &1 &2 _ s t h;exact(sec_data_hit s t h).
 smt().
qed.

lemma sec_source_valid(A<:CCAExtendedAdversary) :
 hoare[SecSource(A).run:true ==>sec_valid res].
proof.
 proc;call(_:true ==>true);first by trivial.
 wp;rnd;rnd;call cpa_keygen_canonical.
 call(_:true ==>true);first by trivial.
 call(_:true ==>true);first by trivial.
 auto=> />.
 move=>result hp code hc r hr.
 split;first by move:hc;rewrite acwc2_psi1_support.
 split;first by move:hr;rewrite acwc2_psi1_support.
 exact(pke_enc_accept result.`1 code r hp).
qed.
lemma sec_source_inj
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) &m :
 Pr[SecSource(A).run()@&m:sec_inj_win res.`so_pk (sec_inj_output res)]=
 Pr[SecINJGame(SecINJReducer(A)).run()@&m:res].
proof.
 byequiv(_: ={glob A,glob SimPublic,SimHistory.h,SecGHistory.queries} ==>
 sec_inj_win res.`so_pk{1} (sec_inj_output res{1})=res{2})=> //.
 proc;inline{2} SecINJReducer(A).run;wp.
 ecall{2}(sec_extract_correct pk{1} ct{1} (Some r{1}) queries{1}).
 call(sec_transcript_same (SecTranscript(A)));wp;rnd;rnd;wp;
 call(cpa_gen_same (Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM))).
 inline ROMInit.init RawXOFStreams.init ROE.init ROF.init ROG.init ROH.init;
 auto=> />.
qed.
lemma sec_source_ow
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) &m :
 Pr[SecSource(A).run()@&m:sec_ow_output res=res.`so_code]=
 Pr[SecOWGame(SecOWReducer(A)).run()@&m:res].
proof.
 byequiv(_: ={glob A,glob SimPublic,SimHistory.h,SecGHistory.queries} ==> (sec_ow_output res{1}=res.`so_code{1})=res{2})=> //.
 proc;inline{2} SecOWReducer(A).run;wp.
 ecall{2}(sec_extract_correct pk{1} ct{1} None queries{1}).
 call(sec_transcript_same (SecTranscript(A)));wp;rnd;rnd;
 call(cpa_gen_same (Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM))).
 inline ROMInit.init RawXOFStreams.init ROE.init ROF.init ROG.init ROH.init;
 auto=> />.
qed.
lemma sec_hit_cover s : sec_valid s=>sec_hit s=>
 sec_inj_win s.`so_pk (sec_inj_output s) \/ sec_ow_output s=s.`so_code.
proof.
 move=>hv hh;case(sec_bad2 s)=>hb.
 + left;exact(sec_bad2_inj s hv hb).
 right;exact(sec_hit_good_ow s hv hh hb).
qed.

lemma sec_hit_reduction
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) &m :
 Pr[SecRandomGame(A).run()@&m:sec_hit res]<=
 Pr[SecINJGame(SecINJReducer(A)).run()@&m:res]+Pr[SecOWGame(SecOWReducer(A)).run()@&m:res].
proof.
 rewrite(sec_source_hit A &m) -(sec_source_inj A &m) -(sec_source_ow A &m).
 have hs:Pr[SecSource(A).run()@&m:sec_hit res]<=
 Pr[SecSource(A).run()@&m:sec_inj_win res.`so_pk (sec_inj_output res) \/ sec_ow_output res=res.`so_code].
 + byequiv(_: ={glob SecSource(A)} ==> sec_hit res{1}=>
   sec_inj_win res.`so_pk{2} (sec_inj_output res{2}) \/ sec_ow_output res{2}=res.`so_code{2})=> //.
   conseq(sec_source_same (SecSource(A))) (sec_source_valid A) _=> //;smt(sec_hit_cover).
 move:hs;rewrite Pr[mu_or];smt(mu_bounded).
qed.
