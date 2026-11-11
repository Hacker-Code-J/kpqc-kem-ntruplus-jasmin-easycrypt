require import AllCore FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array224 Array1152.
require import NTRUPlus768CPAReduction NTRUPlus768CPAProgramming NTRUPlus768CPAChallenge NTRUPlus768CPAHitHistory NTRUPlus768CPAHitOracles.
require import NTRUPlus768CPAModel NTRUPlus768SimModel NTRUPlus768SimOracles NTRUPlus768SimLookup NTRUPlus768SimSampling.
require import NTRUPlus768ROMOracles NTRUPlus768FOGAdapters NTRUPlus768FOEagerG NTRUPlus768RawXOFStreams NTRUPlus768CCAGame NTRUPlus768CCADecapOracle.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768FreshRetryLaw.

module type CPAEncryptSamePort = {
 proc run(pk:W8.t Array1152.t,msg:W8.t Array96.t,hout:W8.t Array224.t):W8.t Array1152.t option
}.
lemma cpa_encrypt_same (M<:CPAEncryptSamePort) :
 equiv[M.run ~ M.run: ={arg,glob M} ==> ={res,glob M}].
proof. proc true;auto. qed.

lemma cpa_hit_phase_projection
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-CPAHitState}) :
 equiv[CPAPhaseH(A,CPAHitH).run ~ CPAPhase(A).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h} ==>
 ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h}].
proof.
 transitivity CPAPhaseH(A,SimHActual).run
 (={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h} ==>
 ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h})
 (={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h} ==>
 ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h}).
 + smt().
 + smt().
 + conseq(cpa_hit_context_projection (CPAPhaseH(A)))=> //.
 conseq(cpa_phase_actual A)=> //.
qed.

lemma cpa_hit_phase_history
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-CPAHitState,-CCADecapOracle}) x :
 hoare[CPAPhaseH(A,CPAHitH).run:
 !CPAHitState.hit /\ CPAHitState.target=x /\ ROF.m.[pk]=Some x.`2 ==>
 CPAHitState.target=x /\ CPAHitState.hit=(x \in SimHistory.h) /\ SimPublic.suffix=x.`2].
proof.
 proc;call(cpa_hit_adversary_history A).
 inline SimHistory.init SimPublic.init;wp.
 inline ROF.get;sp;if;auto=> />;smt(domE emptyE).
qed.

lemma cpa_hit_phase_recorded
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-CPAHitState,-CCADecapOracle}) x :
 equiv[CPAPhaseH(A,CPAHitH).run ~ CPAPhase(A).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h} /\
 !CPAHitState.hit{1} /\ CPAHitState.target{1}=x /\ ROF.m{1}.[pk{1}]=Some x.`2 ==>
 ={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h} /\
 CPAHitState.hit{1}=((x.`1,SimPublic.suffix{2}) \in SimHistory.h{2})].
proof. conseq(cpa_hit_phase_projection A)(cpa_hit_phase_history A x) _=> //;smt(). qed.

lemma cpa_f_get_result x0 : hoare[ROF.get:input=x0 ==>ROF.m.[x0]=Some res].
proof.
 proc*;exists* ROF.m;elim*=>m0.
 call(rof_get_value m0 x0);auto.
qed.
lemma cpa_f_get_same_value x0 :
 equiv[ROF.get ~ ROF.get: ={arg,ROF.m} /\ input{1}=x0 ==>
 ={res,ROF.m} /\ ROF.m{1}.[x0]=Some res{1}].
proof. conseq(_: ={arg,ROF.m} ==> ={res,ROF.m}) (cpa_f_get_result x0) _=> //;by sim. qed.

lemma cpa_programming_programmed
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-CPAHitState}) :
 equiv[CPAProgrammingGame(A).run ~ CPAProgrammed(A).run:
 program{1} /\ ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h} ==>
 res{1}.`1=res{2}].
proof.
 proc;inline{1} CPAProgrammingKernel(A).run;wp.
 call(cpa_hit_phase_projection A).
 inline CPAHitState.init;wp;rnd;rnd;wp.
 call(cpa_encrypt_same (SimEncrypt(FOGActual))).
 call(_: ={arg,ROF.m} ==> ={res,ROF.m});first by sim.
 rnd;rnd.
 call(cpa_gen_same (Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM))).
 call(cpa_init_same RawXOFStreams).
 call(cpa_init_same ROMInit).
 auto=> />;smt().
qed.

require import NTRUPlus768CPAUnbiased.

lemma cpa_programming_erased
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-CPAHitState,-CCADecapOracle}) :
 equiv[CPAProgrammingGame(A).run ~ CPAErased(A).run:
 !program{1} /\ ={glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h} ==>
 ={res}].
proof.
 proc;seq 7 7:(={pk,msg,hout,suffix,ct,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h} /\
 !program{1} /\ ROH.m{1}=empty /\ ROF.m{1}.[pk{1}]=Some suffix{1}).
 + call(cpa_encrypt_same (SimEncrypt(FOGActual))).
   ecall(cpa_f_get_same_value pk{1}).
   rnd;rnd.
   call(cpa_gen_same (Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM))).
   inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init;auto=> />;smt().
 inline{1} CPAProgrammingKernel(A).run;wp.
 exists* msg{1},suffix{1};elim*=>m0 s0.
 call(cpa_hit_phase_recorded A (m0,s0)).
 inline CPAHitState.init;auto=> />;smt().

qed.

lemma cpa_programming_programmed_probability
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-CPAHitState}) &m :
 Pr[CPAProgrammingGame(A).run(true)@&m:res.`1]=Pr[CPAProgrammed(A).run()@&m:res].
proof. by byequiv(cpa_programming_programmed A)=> //. qed.
lemma cpa_programming_erased_probability
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-CPAHitState,-CCADecapOracle}) &m (event:bool*bool->bool) :
 Pr[CPAProgrammingGame(A).run(false)@&m:event res]=Pr[CPAErased(A).run()@&m:event res].
proof. by byequiv(cpa_programming_erased A)=> //. qed.
