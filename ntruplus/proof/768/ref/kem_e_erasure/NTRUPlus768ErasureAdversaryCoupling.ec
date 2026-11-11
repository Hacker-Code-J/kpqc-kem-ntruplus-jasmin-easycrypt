require import AllCore List Distr DBool FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152 Array2336.
require import NTRUPlus768ROMDistributions NTRUPlus768ROMOracles.
require import NTRUPlus768CCAOraclePorts NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
require import NTRUPlus768CCADecapOracle NTRUPlus768CCAGame.
require import NTRUPlus768EncapCompleteRNG NTRUPlus768NumericalDFRModel.
require import NTRUPlus768ErasureModel NTRUPlus768ErasureBudget NTRUPlus768ErasureOracleCoupling.

lemma erasure_f_identity :
 equiv[SharedCCAExtendedOracles.f ~ SharedCCAExtendedOracles.f:
 ={arg,ROF.m} ==> ={res,ROF.m}].
proof. by sim. qed.
lemma erasure_g_identity :
 equiv[SharedCCAExtendedOracles.g ~ SharedCCAExtendedOracles.g:
 ={arg,ROG.m} ==> ={res,ROG.m}].
proof. by sim. qed.
lemma erasure_h_identity :
 equiv[SharedCCAExtendedOracles.h ~ SharedCCAExtendedOracles.h:
 ={arg,ROH.m} ==> ={res,ROH.m}].
proof. by sim. qed.
lemma erasure_decap_identity :
 equiv[CCADecapOracle.decap ~ CCADecapOracle.decap:
 ={arg,ROG.m,ROH.m,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count} ==>
 ={res,ROG.m,ROH.m,CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count}].
proof. by sim. qed.

(* Robust losslessness concerns the adversary phase only. No termination
   hypothesis is placed on the actual, unbounded ROM KeyGen. *)
lemma erasure_capped_adversary_upto
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
   -EBudgetState,-ErasureSeedLog,-ErasureHit,-ErasureSeedPool}) s :
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e =>islossless H.f =>islossless H.g =>islossless H.h =>
  islossless H.raw =>islossless D.decap =>islossless A(H,D).guess) =>
 equiv[CappedA(A,SharedCCAExtendedOracles,CCADecapOracle).guess ~
       CappedA(A,SharedCCAExtendedOracles,CCADecapOracle).guess:
  ={pk,ct,key,glob A,glob EBudgetState,ROF.m,ROG.m,ROH.m,
    RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,
    CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count} /\
  ErasureSeedLog.used{1}=s /\ ErasureSeedLog.used{2}=s /\
  !ErasureHit.bad{1} /\ !ErasureHit.bad{2} /\
  erasure_tables_agree s ROE.m{1} ROE.m{2} ==>
  ={ErasureHit.bad} /\ (!ErasureHit.bad{2} =>
  ={res,glob A,glob EBudgetState,ROF.m,ROG.m,ROH.m,
    RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,
    CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count} /\
  erasure_tables_agree s ROE.m{1} ROE.m{2})].
proof.
 move=>all; proc*.
 call (_: ErasureHit.bad,
  ={glob EBudgetState,ROF.m,ROG.m,ROH.m,ErasureHit.bad,
    RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,
    CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count} /\
  ErasureSeedLog.used{1}=s /\ ErasureSeedLog.used{2}=s /\
  erasure_tables_agree s ROE.m{1} ROE.m{2},
  ={ErasureHit.bad}).
 + conseq(erasure_cap_e_upto s); smt().
 + move=> &2 h; conseq erasure_cap_e_bad; smt().
 + move=> &1; conseq erasure_cap_e_bad; smt().
 + conseq erasure_f_identity; smt().
 + move=> &2 h; conseq cca_extended_f_ll; smt().
 + move=> &1; conseq cca_extended_f_ll; smt().
 + conseq erasure_g_identity; smt().
 + move=> &2 h; conseq cca_extended_g_ll; smt().
 + move=> &1; conseq cca_extended_g_ll; smt().
 + conseq erasure_h_identity; smt().
 + move=> &2 h; conseq cca_extended_h_ll; smt().
 + move=> &1; conseq cca_extended_h_ll; smt().
 + conseq(erasure_cap_raw_upto s); smt().
 + move=> &2 h; conseq erasure_cap_raw_bad; smt().
 + move=> &1; conseq erasure_cap_raw_bad; smt().
 + conseq erasure_decap_identity; smt().
 + move=> &2 h; conseq cca_decap_lossless; smt().
 + move=> &1; conseq cca_decap_lossless; smt().
 auto=> />; smt().
qed.

lemma erasure_capped_adversary_ll
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
   -EBudgetState,-ErasureSeedLog,-ErasureHit,-ErasureSeedPool}) :
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e =>islossless H.f =>islossless H.g =>islossless H.h =>
  islossless H.raw =>islossless D.decap =>islossless A(H,D).guess) =>
 islossless CappedA(A,SharedCCAExtendedOracles,CCADecapOracle).guess.
proof.
 move=>all; exact(all (CapEPort(SharedCCAExtendedOracles)) CCADecapOracle
  cap_shared_e_ll cca_extended_f_ll cca_extended_g_ll cca_extended_h_ll
  cap_shared_raw_ll cca_decap_lossless).
qed.

lemma erasure_challenge_upto
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
   -EBudgetState,-ErasureSeedLog,-ErasureHit,-ErasureSeedPool}) s :
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e =>islossless H.f =>islossless H.g =>islossless H.h =>
  islossless H.raw =>islossless D.decap =>islossless A(H,D).guess) =>
 equiv[CCAChallengeOriginal(CappedA(A)).run ~ CCAChallengeOriginal(CappedA(A)).run:
  ={pk,sk,glob A,glob EBudgetState,ROF.m,ROG.m,ROH.m,
    RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other} /\
  ErasureSeedLog.used{1}=s /\ ErasureSeedLog.used{2}=s /\
  !ErasureHit.bad{1} /\ !ErasureHit.bad{2} /\
  erasure_tables_agree s ROE.m{1} ROE.m{2} ==>
  ={ErasureHit.bad} /\ (!ErasureHit.bad{2} =>
  ={res,glob A,glob EBudgetState,ROF.m,ROG.m,ROH.m,
    RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other,
    CCADecapOracle.sk,CCADecapOracle.cstar,CCADecapOracle.count} /\
  erasure_tables_agree s ROE.m{1} ROE.m{2})].
proof.
 move=>all; proc.
 call(erasure_capped_adversary_upto A s all).
 inline CCADecapOracle.init; wp; rnd; rnd.
 call (_: ={pk,workspace,ROF.m,ROG.m,ROH.m} ==> ={res,ROF.m,ROG.m,ROH.m}).
 + by sim.
 auto=> />; smt().
qed.

lemma erasure_challenge_ll
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
   -EBudgetState,-ErasureSeedLog,-ErasureHit,-ErasureSeedPool}) :
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
  islossless H.e =>islossless H.f =>islossless H.g =>islossless H.h =>
  islossless H.raw =>islossless D.decap =>islossless A(H,D).guess) =>
 islossless CCAChallengeOriginal(CappedA(A)).run.
proof.
 move=>all; apply(cca_challenge_original_lossless (CappedA(A))).
 exact(erasure_capped_adversary_ll A all).
qed.
