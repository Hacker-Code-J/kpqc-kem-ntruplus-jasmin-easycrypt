require import AllCore Distr FMap.
from Jasmin require import JWord.
require import Array32 Array768 Array1152.
require import NTRUPlus768SecModel NTRUPlus768SecKeygen.
require import NTRUPlus768SecReduction NTRUPlus768SecGOracles NTRUPlus768SecGames.
require import NTRUPlus768SimModel NTRUPlus768CCAGame.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768FreshRetryLaw.
require import NTRUPlus768ROMOracles NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
require import NTRUPlus768PKEModel NTRUPlus768PKEKeyDistribution NTRUPlus768CPAReduction.

(* Auxiliary random oracles are implemented inside each concrete attacker.
   The base challengers below call neither ROMInit nor any oracle. *)
module SecAuxSetup = {
 proc run(pk:W8.t Array1152.t) : unit = {
  var ignored:W8.t Array32.t;
  ROMInit.init();RawXOFStreams.init();ignored<@ROF.get(pk);
 }
}.
module SecINJAuxAdapter(B:SecINJAdversary) : SecINJAdversary = {
 proc run(pk:W8.t Array1152.t) : sec_collision = {
  var out:sec_collision;
  SecAuxSetup.run(pk);out<@B.run(pk);return out;
 }
}.
module SecOWAuxAdapter(B:SecOWAdversary) : SecOWAdversary = {
 proc run(pk ct:W8.t Array1152.t) : pke_poly = {
  var out:pke_poly;
  SecAuxSetup.run(pk);out<@B.run(pk,ct);return out;
 }
}.
module SecBaseINJGame(B:SecINJAdversary) = {
 proc run() : bool = {
  var pk:W8.t Array1152.t;var out:sec_collision;
  pk<@SecBaseKeygen.run();out<@B.run(pk);
  return sec_inj_win pk out;
 }
}.
module SecBaseOWGame(B:SecOWAdversary) = {
 proc run() : bool = {
  var pk,ct:W8.t Array1152.t;var code,r,answer:pke_poly;
  pk<@SecBaseKeygen.run();code<$pke_psi1;r<$pke_psi1;
  ct<-pke_ciphertext pk code r;
  answer<@B.run(pk,ct);return answer=code;
 }
}.

(* Intermediate setup views expose only pk and preserve the entire
   auxiliary state. No secret-key projection is passed to an attacker. *)
module SecAuxKeygen = {
 proc run() : W8.t Array1152.t = {
  var pk:W8.t Array1152.t;
  ROMInit.init();RawXOFStreams.init();pk<@SecPublicROMKeygen.run();return pk;
 }
}.
module SecAuxLateKeygen = {
 proc run() : W8.t Array1152.t = {
  var pk:W8.t Array1152.t;
  ROMInit.init();RawXOFStreams.init();pk<@SecBaseLateF.run();return pk;
 }
}.
module SecBaseSetup = {
 proc run() : W8.t Array1152.t = {
  var pk:W8.t Array1152.t;
  pk<@SecBaseKeygen.run();SecAuxSetup.run(pk);return pk;
 }
}.
module type SecPKPort = {proc run():W8.t Array1152.t}.
lemma sec_pk_same (M<:SecPKPort) :
 equiv[M.run ~ M.run : ={glob M} ==> ={res,glob M}].
proof. proc true;auto. qed.

lemma sec_aux_keygen_late :
 equiv[SecAuxKeygen.run ~ SecAuxLateKeygen.run:true ==>
 ={res,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams}].
proof.
 proc;call sec_keygen_hoist.
 inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init;auto.
qed.

lemma sec_aux_late_base_setup :
 equiv[SecAuxLateKeygen.run ~ SecBaseSetup.run:true ==>
 ={res,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams}].
proof.
 proc;inline{1} SecBaseLateF.run;inline{2} SecAuxSetup.run.
 swap{2} [1..2] 2.
 wp;call(_: ={arg,ROF.m} ==> ={res,ROF.m});first by sim.
 wp;call(sec_pk_same SecBaseKeygen).
 inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init;auto.
qed.

lemma sec_aux_keygen_base_setup :
 equiv[SecAuxKeygen.run ~ SecBaseSetup.run:true ==>
 ={res,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams}].
proof.
 transitivity SecAuxLateKeygen.run
  (true ==> ={res,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams})
  (true ==> ={res,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams})=> //.
 + exact sec_aux_keygen_late.
 exact sec_aux_late_base_setup.
qed.

module SecAuxINJView(B:SecINJAdversary) = {
 proc run():bool = {
  var pk:W8.t Array1152.t;var out:sec_collision;
  pk<@SecAuxKeygen.run();out<@B.run(pk);return sec_inj_win pk out;
 }
}.
module SecReadyINJView(B:SecINJAdversary) = {
 proc run():bool = {
  var pk:W8.t Array1152.t;var out:sec_collision;
  pk<@SecBaseSetup.run();out<@B.run(pk);return sec_inj_win pk out;
 }
}.
module SecAuxOWView(B:SecOWAdversary) = {
 proc run():bool = {
  var pk,ct:W8.t Array1152.t;var code,r,answer:pke_poly;
  pk<@SecAuxKeygen.run();code<$pke_psi1;r<$pke_psi1;ct<-pke_ciphertext pk code r;
  answer<@B.run(pk,ct);return answer=code;
 }
}.
module SecReadyOWView(B:SecOWAdversary) = {
 proc run():bool = {
  var pk,ct:W8.t Array1152.t;var code,r,answer:pke_poly;
  pk<@SecBaseSetup.run();code<$pke_psi1;r<$pke_psi1;ct<-pke_ciphertext pk code r;
  answer<@B.run(pk,ct);return answer=code;
 }
}.

lemma sec_inj_same (M<:SecINJAdversary) : equiv[M.run ~ M.run: ={arg,glob M} ==> ={res,glob M}].
proof. proc true;auto. qed.
lemma sec_ow_same (M<:SecOWAdversary) : equiv[M.run ~ M.run: ={arg,glob M} ==> ={res,glob M}].
proof. proc true;auto. qed.

lemma sec_inj_aux_view (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[SecINJGame(SecINJReducer(A)).run ~ SecAuxINJView(SecINJReducer(A)).run:
 ={glob SecINJReducer(A)} ==> ={res,glob SecINJReducer(A)}].
proof.
 proc;inline{2} SecAuxKeygen.run SecPublicROMKeygen.run;wp.
 call(sec_inj_same (SecINJReducer(A))).
 wp;call(cpa_gen_same (Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM))).
 inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init;auto.
qed.

lemma sec_inj_aux_ready (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[SecAuxINJView(SecINJReducer(A)).run ~ SecReadyINJView(SecINJReducer(A)).run:
 ={glob SecINJReducer(A)} ==> ={res,glob SecINJReducer(A)}].
proof.
 proc;call(sec_inj_same (SecINJReducer(A))).
 call sec_aux_keygen_base_setup;auto.
qed.

lemma sec_inj_base_ready (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[SecBaseINJGame(SecINJAuxAdapter(SecINJReducer(A))).run ~ SecReadyINJView(SecINJReducer(A)).run:
 ={glob SecINJReducer(A)} ==> ={res,glob SecINJReducer(A)}].
proof.
 proc;inline{1} SecINJAuxAdapter(SecINJReducer(A)).run;inline{2} SecBaseSetup.run;wp.
 call(sec_inj_same (SecINJReducer(A))).
 wp;call(_: ={arg} ==>
 ={ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams});first by sim.
 wp;call(sec_pk_same SecBaseKeygen);auto.
qed.

lemma sec_ow_aux_view (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[SecOWGame(SecOWReducer(A)).run ~ SecAuxOWView(SecOWReducer(A)).run:
 ={glob SecOWReducer(A)} ==> ={res,glob SecOWReducer(A)}].
proof.
 proc;inline{2} SecAuxKeygen.run SecPublicROMKeygen.run;wp.
 call(sec_ow_same (SecOWReducer(A))).
 wp;rnd;rnd;wp;call(cpa_gen_same (Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM))).
 inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init;auto.
qed.

lemma sec_ow_aux_ready (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[SecAuxOWView(SecOWReducer(A)).run ~ SecReadyOWView(SecOWReducer(A)).run:
 ={glob SecOWReducer(A)} ==> ={res,glob SecOWReducer(A)}].
proof.
 proc;call(sec_ow_same (SecOWReducer(A))).
 wp;rnd;rnd;call sec_aux_keygen_base_setup;auto.
qed.

lemma sec_ow_base_ready (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) :
 equiv[SecBaseOWGame(SecOWAuxAdapter(SecOWReducer(A))).run ~ SecReadyOWView(SecOWReducer(A)).run:
 ={glob SecOWReducer(A)} ==> ={res,glob SecOWReducer(A)}].
proof.
 proc;inline{1} SecOWAuxAdapter(SecOWReducer(A)).run;inline{2} SecBaseSetup.run.
 swap{1} 5 -3;swap{1} 7 -4.
 wp;call(sec_ow_same (SecOWReducer(A))).
 wp;rnd;rnd.
 wp;call(_: ={arg} ==>
 ={ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams});first by sim.
 wp;call(sec_pk_same SecBaseKeygen);auto.
qed.

lemma sec_inj_base_probability (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) &m :
 Pr[SecINJGame(SecINJReducer(A)).run()@&m:res]=Pr[SecBaseINJGame(SecINJAuxAdapter(SecINJReducer(A))).run()@&m:res].
proof.
 have h1:Pr[SecINJGame(SecINJReducer(A)).run()@&m:res]=Pr[SecAuxINJView(SecINJReducer(A)).run()@&m:res]
  by byequiv(sec_inj_aux_view A)=> //.
 have h2:Pr[SecAuxINJView(SecINJReducer(A)).run()@&m:res]=Pr[SecReadyINJView(SecINJReducer(A)).run()@&m:res]
  by byequiv(sec_inj_aux_ready A)=> //.
 have h3:Pr[SecBaseINJGame(SecINJAuxAdapter(SecINJReducer(A))).run()@&m:res]=Pr[SecReadyINJView(SecINJReducer(A)).run()@&m:res]
  by byequiv(sec_inj_base_ready A)=> //.
 by rewrite h1 h2 h3.
qed.

lemma sec_ow_base_probability (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark}) &m :
 Pr[SecOWGame(SecOWReducer(A)).run()@&m:res]=Pr[SecBaseOWGame(SecOWAuxAdapter(SecOWReducer(A))).run()@&m:res].
proof.
 have h1:Pr[SecOWGame(SecOWReducer(A)).run()@&m:res]=Pr[SecAuxOWView(SecOWReducer(A)).run()@&m:res]
  by byequiv(sec_ow_aux_view A)=> //.
 have h2:Pr[SecAuxOWView(SecOWReducer(A)).run()@&m:res]=Pr[SecReadyOWView(SecOWReducer(A)).run()@&m:res]
  by byequiv(sec_ow_aux_ready A)=> //.
 have h3:Pr[SecBaseOWGame(SecOWAuxAdapter(SecOWReducer(A))).run()@&m:res]=Pr[SecReadyOWView(SecOWReducer(A)).run()@&m:res]
  by byequiv(sec_ow_base_ready A)=> //.
 by rewrite h1 h2 h3.
qed.
