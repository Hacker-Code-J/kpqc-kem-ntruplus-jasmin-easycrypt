require import AllCore Distr DBool TotalProb.
require import NTRUPlus768CPAModel NTRUPlus768AcceptanceProbability.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions NTRUPlus768FreshRetryLaw NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
require import NTRUPlus768SimModel NTRUPlus768SimOracles NTRUPlus768SimLookup NTRUPlus768FOGAdapters.
require import NTRUPlus768FOEagerG NTRUPlus768SimSampling NTRUPlus768KeygenCompleteProof.
require import NTRUPlus768CCAGame NTRUPlus768CCAOraclePorts NTRUPlus768CCADecapOracle.
from Jasmin require import JWord.
require import Array32 Array96 Array1152 Array2336.
import RField.

clone TotalProb.TotalBool as CPATotalBool with type input <- unit proof *.
module CPAOutcome(A:CCAExtendedAdversary) = {
 proc main(i:unit,b:bool):bool = {var hit;hit<@CPAHybrid(A).run(b);return (!hit)=b;}
}.
module CPACoin(A:CCAExtendedAdversary) = {
 proc run():bool = {var b,r;b<$dbool;r<@CPAOutcome(A).main((),b);return r;}
}.

module type CPAInitPort = {proc init():unit}.
module type CPAGenPort = {proc run():W8.t Array1152.t * W8.t Array2336.t}.
module type CPACipherPort = {proc run(pk:W8.t Array1152.t,msg:W8.t Array96.t):W8.t Array1152.t}.
module type CPAPhasePort = {proc run(pk ct:W8.t Array1152.t,key:W8.t Array32.t):bool}.
module type CPABranchPort = {proc run(branch:bool):bool}.
module type CPAOutcomePort = {proc main(i:unit,b:bool):bool}.
lemma cpa_init_same (M<:CPAInitPort) : equiv[M.init ~ M.init: ={glob M} ==> ={glob M}].
proof. proc true;auto. qed.
lemma cpa_gen_same (M<:CPAGenPort) : equiv[M.run ~ M.run: ={glob M} ==> ={res,glob M}].
proof. proc true;auto. qed.
lemma cpa_cipher_same (M<:CPACipherPort) : equiv[M.run ~ M.run: ={arg,glob M} ==> ={res,glob M}].
proof. proc true;auto. qed.
lemma cpa_phase_same (M<:CPAPhasePort) : equiv[M.run ~ M.run: ={arg,glob M} ==> ={res,glob M}].
proof. proc true;auto. qed.
lemma cpa_branch_same (M<:CPABranchPort) : equiv[M.run ~ M.run: ={arg,glob M} ==> ={res,glob M}].
proof. proc true;auto. qed.
lemma cpa_outcome_same (M<:CPAOutcomePort) : equiv[M.main ~ M.main: ={arg,glob M} ==> ={res,glob M}].
proof. proc true;auto. qed.

lemma cpa_phase_ll (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory}) :
 (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
 islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
 islossless D.decap=>islossless A(H,D).guess)=>islossless CPAPhase(A).run.
proof.
 move=>all;proc;call(all (SimOracles(FOGActual,SimHActual)) (SimLookup(FOGActual)) _ _ _ _ _ _).
 + exact cca_e_ll.
 + exact cca_f_ll.
 + proc;call rog_get_ll;auto.
 + exact(sim_logged_h_ll SimHActual roh_get_ll).
 + exact(sim_raw_get_ll FOGActual SimHActual rog_get_ll roh_get_ll).
 + exact(sim_lookup_lossless FOGActual rog_get_ll).
 call sim_history_init_ll;call sim_public_init_ll;call rof_get_ll;auto.
qed.
lemma cpa_hybrid_ll (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory}) :
 (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
 islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
 islossless D.decap=>islossless A(H,D).guess)=>islossless CPAHybrid(A).run.
proof.
 move=>all;proc;call(cpa_phase_ll A all);rnd;call cpa_cipher_ll;rnd;rnd;
 call fresh_keygen_lossless_unconditional;call raw_stream_init_ll;call rom_init_ll;
 auto;smt(uniform96_ll uniform32_ll).
qed.

lemma cpa_game_coin (A<:CCAExtendedAdversary {-CPAReduction,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory}) &m :
 Pr[CPAGame(CPAReduction(A)).run()@&m:res]=Pr[CPACoin(A).run()@&m:res].
proof.
 byequiv(_: ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h} ==> ={res})=> //.
 proc;inline{1} CPAReduction(A).choose CPAReduction(A).guess.
 inline{2} CPAOutcome(A).main CPAHybrid(A).run.
 swap{1} 9 -8.
 wp;call(cpa_phase_same (CPAPhase(A))).
 wp;rnd;wp;call(cpa_cipher_same CPACipher).
 wp;rnd;rnd;wp;call(cpa_gen_same (Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM))).
 call(cpa_init_same RawXOFStreams).
 call(cpa_init_same ROMInit).
 wp;rnd;auto;smt().
qed.

lemma cpa_outcome_false (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory}) &m :
 Pr[CPAOutcome(A).main((),false)@&m:res]=Pr[CPAHybrid(A).run(false)@&m:res].
proof.
 byequiv(_: b{1}=branch{2} /\ b{1}=false /\ ={glob CPAHybrid(A)} ==> ={res})=> //.
 proc*;inline{1} CPAOutcome(A).main;wp.
 call(cpa_branch_same (CPAHybrid(A))).
 auto;smt().
qed.
lemma cpa_outcome_true (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory}) &m :
 Pr[CPAOutcome(A).main((),true)@&m:res]=Pr[CPAHybrid(A).run(true)@&m:!res].
proof.
 byequiv(_: b{1}=branch{2} /\ b{1}=true /\ ={glob CPAHybrid(A)} ==> res{1}=!res{2})=> //.
 proc*;inline{1} CPAOutcome(A).main;wp.
 call(cpa_branch_same (CPAHybrid(A))).
 auto;smt().
qed.
lemma cpa_coin_formula (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory}) &m : islossless CPAHybrid(A).run=>
 Pr[CPACoin(A).run()@&m:res]=
 (1%r+Pr[CPAHybrid(A).run(false)@&m:res]-Pr[CPAHybrid(A).run(true)@&m:res])/2%r.
proof.
 move=>hll.
 have he:Pr[CPACoin(A).run()@&m:res]=Pr[CPATotalBool.Rand(CPAOutcome(A)).f(dbool,())@&m:res].
 + byequiv(_:dt{2}=dbool /\ i{2}=() /\ ={glob CPAOutcome(A)} ==> ={res})=> //.
   proc;call(cpa_outcome_same (CPAOutcome(A))).
   auto.
 rewrite he (CPATotalBool.total_prob_bool (CPAOutcome(A)) () &m) (cpa_outcome_true A &m) (cpa_outcome_false A &m).
 have hl:Pr[CPAHybrid(A).run(true)@&m:true]=1%r by byphoare hll.
 rewrite Pr[mu_not] hl;ring.
qed.

lemma cpa_unprogrammed_false (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory}) &m :
 Pr[CPAUnprogrammed(A).run()@&m:res]=Pr[CPAHybrid(A).run(false)@&m:res].
proof.
 byequiv(_:branch{2}=false /\ ={glob CPAHybrid(A)} ==> ={res})=> //.
 proc;wp;call(cpa_phase_same (CPAPhase(A))).
 wp;rnd;wp;call(cpa_cipher_same CPACipher).
 rnd{2};rnd;call(cpa_gen_same (Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM))).
 call(cpa_init_same RawXOFStreams).
 call(cpa_init_same ROMInit).
 auto;smt(uniform96_ll).
qed.

lemma cpa_reduction_success (A<:CCAExtendedAdversary {-CPAReduction,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory}) &m :
 (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
 islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
 islossless D.decap=>islossless A(H,D).guess)=>
 Pr[CPAGame(CPAReduction(A)).run()@&m:res]=
 (1%r+Pr[CPAUnprogrammed(A).run()@&m:res]-Pr[CPAHybrid(A).run(true)@&m:res])/2%r.
proof.
 move=>all;by rewrite(cpa_game_coin A &m)(cpa_coin_formula A &m (cpa_hybrid_ll A all)) -(cpa_unprogrammed_false A &m).
qed.
