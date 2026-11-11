require import AllCore Distr FMap.
from Jasmin require import JWord.
require import Array32 Array1152 Array2336 Array13506.
require import NTRUPlus768SimModel NTRUPlus768SimSampling NTRUPlus768SimAnswer NTRUPlus768SimPrefix NTRUPlus768SimOracles NTRUPlus768SimPorts NTRUPlus768SimGames.
require import NTRUPlus768FOModel NTRUPlus768FOEagerG NTRUPlus768FOGAdapters NTRUPlus768FOProcedures NTRUPlus768FOKEMGame.
require import NTRUPlus768ROMOracles NTRUPlus768RawXOF NTRUPlus768RawXOFStreams.
require import NTRUPlus768CCAGame NTRUPlus768CCAOraclePorts NTRUPlus768CCADecapOracle NTRUPlus768CCAStatusAdapter.

module SimRealDecap(G:FOGPort,H:SimHPort) : CCADecapPort = {
 proc decap(ct:W8.t Array1152.t) : cca_reply = {
  var answer:cca_reply;
  SimPublic.count<-SimPublic.count+1;
  answer<-None;
  if(SimPublic.cstar<>Some ct){answer<@SimCore(G,SimAnswerReal(G,H)).run(SimPublic.pk,ct,CCADecapOracle.sk);}
  return answer;
 }
}.

lemma sim_leak_e_projection :
 equiv[SimLeakHashes(SimLeaksBackend(FOGActual,SimHActual)).e ~ SimOracles(FOGActual,SimHActual).e:
 ={arg,glob ROE} ==> ={res,glob ROE}].
proof.
 proc*.
 inline{1} SimLeakHashes(SimLeaksBackend(FOGActual,SimHActual)).e SimLeaksBackend(FOGActual,SimHActual).leaks.
 sp;wp.
 match{1};2,3,4,5,6:by exfalso=> />;smt().
 wp;call(_: ={arg,glob ROE} ==> ={res,glob ROE});first by sim.
 auto=> />;rewrite /sim_out192;smt().
qed.
lemma sim_leak_f_projection :
 equiv[SimLeakHashes(SimLeaksBackend(FOGActual,SimHActual)).f ~ SimOracles(FOGActual,SimHActual).f:
 ={arg,glob ROF} ==> ={res,glob ROF}].
proof.
 proc*.
 inline{1} SimLeakHashes(SimLeaksBackend(FOGActual,SimHActual)).f SimLeaksBackend(FOGActual,SimHActual).leaks.
 sp;wp.
 match{1};1,3,4,5,6:by exfalso=> />;smt().
 wp;call(_: ={arg,glob ROF} ==> ={res,glob ROF});first by sim.
 auto=> />;rewrite /sim_out32;smt().
qed.
lemma sim_leak_g_projection :
 equiv[SimLeakHashes(SimLeaksBackend(FOGActual,SimHActual)).g ~ SimOracles(FOGActual,SimHActual).g:
 ={arg,glob ROG} ==> ={res,glob ROG}].
proof.
 proc*.
 inline{1} SimLeakHashes(SimLeaksBackend(FOGActual,SimHActual)).g SimLeaksBackend(FOGActual,SimHActual).leaks.
 sp;wp.
 match{1};1,2,4,5,6:by exfalso=> />;smt().
 wp;call(_: ={arg,glob ROG} ==> ={res,glob ROG});first by sim.
 auto=> />;rewrite /sim_out192;smt().
qed.
lemma sim_leak_h_projection :
 equiv[SimLeakHashes(SimLeaksBackend(FOGActual,SimHActual)).h ~ SimOracles(FOGActual,SimHActual).h:
 ={arg,glob ROH,SimHistory.h} ==> ={res,glob ROH,SimHistory.h}].
proof.
 proc*.
 inline{1} SimLeakHashes(SimLeaksBackend(FOGActual,SimHActual)).h SimLeaksBackend(FOGActual,SimHActual).leaks.
 sp;wp.
 match{1};1,2,3,5,6:by exfalso=> />;smt().
 wp;call(_: ={arg,glob ROH,SimHistory.h} ==> ={res,glob ROH,SimHistory.h});first by sim.
 auto=> />;rewrite /sim_out224;smt().
qed.
lemma sim_leak_raw_projection :
 equiv[SimLeakHashes(SimLeaksBackend(FOGActual,SimHActual)).raw ~ SimOracles(FOGActual,SimHActual).raw:
 ={arg,ROG.m,ROH.m,ROE.m,ROF.m,glob RawXOFStreams,SimHistory.h} ==> ={res,ROG.m,ROH.m,ROE.m,ROF.m,glob RawXOFStreams,SimHistory.h}].
proof.
 proc*.
 inline{1} SimLeakHashes(SimLeaksBackend(FOGActual,SimHActual)).raw SimLeaksBackend(FOGActual,SimHActual).leaks.
 sp;wp.
 match{1};1,2,3,4,6:by exfalso=> />;smt().
 wp;call(_: ={arg,ROG.m,ROH.m,ROE.m,ROF.m,glob RawXOFStreams,SimHistory.h} ==> ={res,ROG.m,ROH.m,ROE.m,ROF.m,glob RawXOFStreams,SimHistory.h});first by sim.
 auto=> />;rewrite /sim_out_raw;smt().
qed.

lemma sim_real_decap_ll (G<:FOGPort)(H<:SimHPort):
 islossless G.get=>islossless H.get=>islossless SimRealDecap(G,H).decap.
proof.
 move=>hg hh;proc;sp;if;last by auto.
 call(sim_core_ll G (SimAnswerReal(G,H)) hg (sim_answer_real_ll G H hg hh));auto.
qed.

lemma sim_leak_real_decap :
 equiv[SimLeakDecaps(SimLeaksBackend(FOGActual,SimHActual),SimAnswerReal(FOGActual,SimHActual)).decap ~
 SimRealDecap(FOGActual,SimHActual).decap:
 ={ct,ROG.m,ROH.m,glob SimPublic,SimHistory.h,glob FOContext,CCADecapOracle.sk} ==>
 ={res,ROG.m,ROH.m,glob SimPublic,SimHistory.h,glob FOContext,CCADecapOracle.sk}].
proof.
 proc;inline{1} SimLeaksBackend(FOGActual,SimHActual).leaks;sp.
 match{1};1..5:by exfalso=> />;smt().
 inline{1} SimPrepare(FOGActual,SimHActual).run.
 inline{2} SimCore(FOGActual,SimAnswerReal(FOGActual,SimHActual)).run.
 sp;if;first by auto=> />;smt().
 + sp 0 3.
   seq 1 2:(request0{1}=request{2} /\ result{1}=None /\ result{2}=None /\
    ={ROG.m,ROH.m,glob SimPublic,SimHistory.h,glob FOContext,CCADecapOracle.sk}).
   - wp;call(_: ={arg,ROG.m} ==> ={res,ROG.m});first by sim.
     auto=> />;smt().
   if;first by auto.
   - sp 1 0;if{1}.
     + rcondf{1} 7.
       - move=> &m;wp;call(_:true ==>true);first by trivial. auto=> />;rewrite /sim_out_decap;done.
       wp;call(_: ={arg,ROG.m,ROH.m} ==> ={res,ROG.m,ROH.m});first by sim.
       auto=> />;rewrite /sim_out_decap;auto.
     rcondt{1} 5;first by auto=> />;rewrite /sim_out_decap;auto.
     wp;call(_: ={arg,ROG.m,ROH.m} ==> ={res,ROG.m,ROH.m});first by sim.
     auto=> />;rewrite /sim_out_decap;auto.
   rcondf{1} 5;first by auto=> />;rewrite /sim_out_decap;auto.
   auto=> />;rewrite /sim_out_decap;auto.
 rcondf{1} 5;first by auto=> />;rewrite /sim_out_decap;auto.
 auto=> />;rewrite /sim_out_decap;auto.
qed.

lemma sim_original_decaps_core :
 equiv[FODecaps(SHAKEGROM,SHAKEHROM).run ~ SimCore(FOGActual,SimAnswerReal(FOGActual,SimHActual)).run:
 ={pk,ct,sk,ROG.m,ROH.m} ==>
 cca_status_result res{1}.`1 res{1}.`2=res{2} /\ ={ROG.m,ROH.m}].
proof.
 transitivity FODecaps(FOGHash(FOGActual),SimHShake(SimHActual)).run
  (={arg,ROG.m,ROH.m} ==> ={res,ROG.m,ROH.m})
  (={pk,ct,sk,ROG.m,ROH.m} ==>
    cca_status_result res{1}.`1 res{1}.`2=res{2} /\ ={ROG.m,ROH.m}).
 + smt().
 + smt().
 + by sim.
 conseq(sim_decaps_actual FOGActual SimHActual);smt().
qed.

lemma sim_real_decap_original :
 equiv[SimRealDecap(FOGActual,SimHActual).decap ~ FOReencryptDecap(SHAKEGROM,SHAKEHROM).decap:
 ={ct,ROG.m,ROH.m,CCADecapOracle.sk} /\ SimPublic.pk{1}=FOPublicKey.pk{2} /\
 SimPublic.cstar{1}=CCADecapOracle.cstar{2} ==>
 ={res,ROG.m,ROH.m,CCADecapOracle.sk}].
proof.
 proc;sp;if{1}.
 + rcondf{2} 1;first by auto.
   wp;symmetry.
   call sim_original_decaps_core;auto=> />;smt().
 rcondt{2} 1;first by auto.
 auto.
qed.
