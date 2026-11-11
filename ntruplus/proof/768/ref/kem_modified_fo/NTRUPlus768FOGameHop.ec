require import AllCore List Distr FMap DBool StdOrder.
from Jasmin require import JWord.
require import Array32 Array224 Array1152 Array2336.
require import NTRUPlus768FOModel NTRUPlus768FOFixedGames NTRUPlus768FOAdversaryCoupling.
require import NTRUPlus768FOSetupDistribution NTRUPlus768FOSetupExpectation.
require import NTRUPlus768FOChallengeBridge NTRUPlus768FOChallenge NTRUPlus768FOBackendContracts.
require import NTRUPlus768FOKEMGame NTRUPlus768FOHMonitor NTRUPlus768FOBadBound.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions NTRUPlus768RawXOFStreams.
require import NTRUPlus768CCADecapOracle NTRUPlus768CCAGame NTRUPlus768PKEModel NTRUPlus768PKEAlgebra.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768KEMFailureModel NTRUPlus768ACWC2Oracle.
require import NTRUPlus768ROMKeygen NTRUPlus768CCAOraclePorts NTRUPlus768FOQueryBudget.
require import NTRUPlus768RawXOF.
import RealOrder.

lemma fo_challenge_encap_self w g fm gm :
 rom_key_relation w fm=>acwc2_cache_matches g gm=>
 equiv[FOChallengeEncap.run ~ FOChallengeEncap.run:
 ={arg,ROF.m,ROG.m,ROH.m,glob FOContext} /\
 pk{1}=w.`kg_pk /\ FOContext.w{1}=w /\ FOContext.g{1}=g /\
 ROF.m{1}=fm /\ ROG.m{1}=gm /\ ROH.m{1}=empty ==>
 ={res,ROF.m,ROG.m,ROH.m,glob FOContext} /\
 FOContext.w{1}=w /\ FOContext.g{1}=g /\ ROG.m{1}=gm /\
 fo_challenge_invariant w g FOContext.challenge_h{1} FOContext.challenge_hash{1}
  FOContext.challenge_ct{1} ROH.m{1} /\
 fo_hcache_good w g FOContext.challenge_h{1} ROH.m{1} /\
 FOContext.challenge_ct{1}=res{1}.`1].
proof.
 move=>hk hg.
 conseq(_: ={arg,ROF.m,ROG.m,ROH.m,glob FOContext} ==>
   ={res,ROF.m,ROG.m,ROH.m,glob FOContext})
   (fo_challenge_encap_state w g fm gm hk hg) _=> />.
 by sim.
qed.

lemma fo_observed_challenge_upto
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOContext,-FOBadState,-FOBudgetState}) w g fm gm :
 rom_key_relation w fm=>acwc2_cache_matches g gm=>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
 islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
 islossless D.decap=>islossless A(H,D).guess) =>
 equiv[FOObservedChallenge(A,FONativeBackend).run ~ FOObservedChallenge(A,FOFullBackend).run:
 ={arg,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob CCADecapOracle,FOPublicKey.pk,glob FOContext,glob FOBadState,glob FOBudgetState} /\
 pk{1}=w.`kg_pk /\ sk{1}=w.`kg_sk /\ FOContext.w{1}=w /\ FOContext.g{1}=g /\
 ROF.m{1}=fm /\ ROG.m{1}=gm /\ ROH.m{1}=empty ==>
 ={FOBadState.bad} /\ (!FOBadState.bad{2}=> ={res})].
proof.
 move=>hk hg all; have hp:=pke_key_from_rom w fm hk; proc.
 seq 6 6:(={real,random,bit,q,pk,sk,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob CCADecapOracle,FOPublicKey.pk,glob FOContext,glob FOBadState,glob FOBudgetState} /\
 pk{1}=w.`kg_pk /\ sk{1}=w.`kg_sk /\
 FOPublicKey.pk{1}=w.`kg_pk /\ CCADecapOracle.sk{1}=w.`kg_sk /\ CCADecapOracle.cstar{1}=Some FOContext.challenge_ct{1} /\
 FOContext.w{1}=w /\ FOContext.g{1}=g /\ ROG.m{1}=gm /\
 fo_challenge_invariant w g FOContext.challenge_h{1} FOContext.challenge_hash{1}
   FOContext.challenge_ct{1} ROH.m{1} /\ fo_hcache_good w g FOContext.challenge_h{1} ROH.m{1}).
 + inline FOPublicKey.init CCADecapOracle.init; wp; rnd; rnd.
   call(fo_challenge_encap_self w g fm gm hk hg); auto.
 exists* FOContext.challenge_h{1},FOContext.challenge_hash{1},FOContext.challenge_ct{1}.
 elim*=>ex hs cs.
 call(fo_observed_phase_upto A w g ex hs cs hp all); auto=> />; smt().
qed.

lemma fo_observed_kernel_upto
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOContext,-FOBadState,-FOBudgetState}) s0 :
 fo_setup_valid s0=>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
 islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
 islossless D.decap=>islossless A(H,D).guess) =>
 equiv[FOObservedNativeKernel(A).guess ~ FOObservedFullKernel(A).guess:
 s{1}=s0 /\ s{2}=s0 /\ ={glob A,glob FOBadState,glob FOBudgetState,FOPublicKey.pk} ==>
 ={FOBadState.bad} /\ (!FOBadState.bad{2}=> ={res})].
proof.
 move=>hv all; have [hk [_ [_ [_ hg]]]]:=hv; proc.
 call(fo_observed_challenge_upto A s0.`1.`1 (acwc2_gfun s0.`3) s0.`2 (acwc2_g_cache s0.`3) hk hg all).
 inline FOContext.init CCADecapOracle.reset RawXOFStreams.init ROH.init ROG.init ROE.init;
 auto.
qed.

lemma fo_observed_kernel_good
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOContext,-FOBadState,-FOBudgetState}) s &m :
 fo_setup_valid s=>(forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
 islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
 islossless D.decap=>islossless A(H,D).guess)=>
 Pr[FOObservedNativeKernel(A).guess(s) @ &m:res=true /\ !FOBadState.bad]=
 Pr[FOObservedFullKernel(A).guess(s) @ &m:res=true /\ !FOBadState.bad].
proof. move=>hv all; byequiv(fo_observed_kernel_upto A s hv all)=> //; clear hv all; smt(). qed.

lemma fo_observed_kernel_distance_bad
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOContext,-FOBadState,-FOBudgetState}) s &m :
 fo_setup_valid s=>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
 islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
 islossless D.decap=>islossless A(H,D).guess) =>
 `|Pr[FOObservedNativeKernel(A).guess(s) @ &m:res=true]-
   Pr[FOObservedFullKernel(A).guess(s) @ &m:res=true]|<=
 Pr[FOObservedFullKernel(A).guess(s) @ &m:FOBadState.bad].
proof.
 move=>hv all.
 have good:=fo_observed_kernel_good A s &m hv all.
 have bad:Pr[FOObservedNativeKernel(A).guess(s) @ &m:FOBadState.bad]=
   Pr[FOObservedFullKernel(A).guess(s) @ &m:FOBadState.bad]
   by byequiv(fo_observed_kernel_upto A s hv all)=> //; clear hv all; smt().
 have hn:Pr[FOObservedNativeKernel(A).guess(s) @ &m:res=true /\ FOBadState.bad]<=
   Pr[FOObservedNativeKernel(A).guess(s) @ &m:FOBadState.bad] by rewrite Pr[mu_sub].
 have hf:Pr[FOObservedFullKernel(A).guess(s) @ &m:res=true /\ FOBadState.bad]<=
   Pr[FOObservedFullKernel(A).guess(s) @ &m:FOBadState.bad] by rewrite Pr[mu_sub].
 rewrite Pr[mu_split FOBadState.bad].
 have ->:Pr[FOObservedFullKernel(A).guess(s) @ &m:res=true]=
   Pr[FOObservedFullKernel(A).guess(s) @ &m:res=true /\ FOBadState.bad]+
   Pr[FOObservedFullKernel(A).guess(s) @ &m:res=true /\ !FOBadState.bad]
   by rewrite Pr[mu_split FOBadState.bad].
 clear hv all.
 smt(mu_bounded).
qed.

lemma fo_observed_kernel_bad
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOContext,-FOBadState,-FOBudgetState}) s &m :
 fo_setup_valid s=>(forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
 islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
 islossless D.decap=>islossless A(H,D).guess)=>
 Pr[FOObservedNativeKernel(A).guess(s) @ &m:FOBadState.bad]=
 Pr[FOObservedFullKernel(A).guess(s) @ &m:FOBadState.bad].
proof. move=>hv all; byequiv(fo_observed_kernel_upto A s hv all)=> //; clear hv all; smt(). qed.

require import NTRUPlus768FOKernelBound.

lemma fo_observed_kernel_distance
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,-FOPublicKey,-FOContext,-FOBadState,-FOBudgetState}) s Q &m :
 fo_setup_valid s=>0<=Q=>FOBudgetState.limit{m}=Q=>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
 islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
 islossless D.decap=>islossless A(H,D).guess) =>
 `|Pr[FOObservedNativeKernel(A).guess(s) @ &m:res=true]-
   Pr[FOObservedFullKernel(A).guess(s) @ &m:res=true]|<=Q%r*fo_setup_error s.
proof.
 move=>hv hq hi all.
 exact(ler_trans _ _ _ (fo_observed_kernel_distance_bad A s &m hv all)
   (fo_observed_full_kernel_bad A s Q &m hq hi)).
qed.

