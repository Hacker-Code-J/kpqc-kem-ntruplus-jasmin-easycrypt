"""Only the game-hop layer assumes robust attacker termination; cap removal is explicit."""
BASE='ntruplus/proof/768/ref/kem_e_erasure/'
ADVERSARY=BASE+'NTRUPlus768ErasureAdversaryCoupling.ec'
REMOVAL=BASE+'NTRUPlus768ErasureCapRemoval.ec'
ORACLE=BASE+'NTRUPlus768ErasureOracleCoupling.ec'
ROBUST=r'''(forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
 islossless H.e =>islossless H.f =>islossless H.g =>islossless H.h =>
 islossless H.raw =>islossless D.decap =>islossless A(H,D).guess)'''
CHALLENGE=r'''lemma erasure_challenge_ll
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
 -EBudgetState,-ErasureSeedLog,-ErasureHit,-ErasureSeedPool}) :'''
CAP_HEADER=r'''lemma capped_original_event
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
 -EBudgetState,-ErasureHit,-ErasureSeedLog,-ErasureSeedPool}) &m q0 (event:bool->bool) :
 0<=q0 =>'''
QUERY_CONTRACT=r'''hoare[CountedA(A,SharedCCAExtendedOracles,CCADecapOracle).guess:
 EBudgetState.requests=0 /\ EBudgetState.forwarded=0 /\ EBudgetState.limit=q0 /\
 !EBudgetState.overflow /\ EBudgetState.queries=[] ==> EBudgetState.requests<=q0] =>'''
INITIAL=r'''EBudgetState.requests{m}=0 =>EBudgetState.forwarded{m}=0 =>EBudgetState.limit{m}=q0 =>
 !EBudgetState.overflow{m} =>EBudgetState.queries{m}=[] =>'''
CONCLUSION=r'''Pr[CCAOriginalGame(CappedA(A)).run() @ &m:event res]=
 Pr[CCAOriginalGame(A).run() @ &m:event res].'''
RAW_UPTO=r'''lemma erasure_cap_raw_upto s :
 equiv[CapEPort(SharedCCAExtendedOracles).raw ~ CapEPort(SharedCCAExtendedOracles).raw:
 ={input,outlen,glob EBudgetState,ROF.m,ROG.m,ROH.m,
 RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other} /\
 ErasureSeedLog.used{1}=s /\ ErasureSeedLog.used{2}=s /\
 !ErasureHit.bad{1} /\ !ErasureHit.bad{2} /\
 erasure_tables_agree s ROE.m{1} ROE.m{2} ==>
 ={ErasureHit.bad} /\ (!ErasureHit.bad{2} =>
 ={res,glob EBudgetState,ROF.m,ROG.m,ROH.m,
 RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other} /\
 erasure_tables_agree s ROE.m{1} ROE.m{2})].'''
RULES=(
 (ADVERSARY,'actual capped challenge LL requires robust termination against all lossless interfaces',CHALLENGE+ROBUST+'=> islossless CCAChallengeOriginal(CappedA(A)).run.'),
 (REMOVAL,'removing the cap needs robust termination, a universal-state counted-query contract, and initial budget state',CAP_HEADER+ROBUST+'=>'+QUERY_CONTRACT+INITIAL+CONCLUSION),
 (ORACLE,'actual raw oracle coupling preserves all stream state only before a forwarded seed hit',RAW_UPTO),
)
MUTATIONS=(
 ('cap-is-falsely-treated-as-an-attacker-termination-proof',ADVERSARY,CHALLENGE+ROBUST+'=>',CHALLENGE),
 ('robust-termination-is-weakened-to-one-uncapped-backend',ADVERSARY,CHALLENGE+ROBUST+'=>',CHALLENGE+'islossless A(SharedCCAExtendedOracles,CCADecapOracle).guess =>'),
 ('cap-removal-omits-robust-attacker-termination',REMOVAL,CAP_HEADER+ROBUST+'=>',CAP_HEADER),
 ('cap-removal-omits-the-counted-query-contract',REMOVAL,CAP_HEADER+ROBUST+'=>'+QUERY_CONTRACT,CAP_HEADER+ROBUST+'=> true =>'),
 ('cap-removal-checks-only-one-memory-and-witness-input',REMOVAL,CAP_HEADER+ROBUST+'=>'+QUERY_CONTRACT,CAP_HEADER+ROBUST+'=> Pr[CountedA(A,SharedCCAExtendedOracles,CCADecapOracle).guess(witness,witness,witness) @ &m:EBudgetState.requests<=q0]=1%r =>'),
 ('cap-removal-starts-with-an-unaccounted-query-offset',REMOVAL,CAP_HEADER+ROBUST+'=>'+QUERY_CONTRACT+INITIAL,CAP_HEADER+ROBUST+'=>'+QUERY_CONTRACT+INITIAL.replace('EBudgetState.requests{m}=0 =>','')),
 ('challenge-allows-direct-hidden-pool-access',ADVERSARY,CHALLENGE,CHALLENGE.replace(',-ErasureSeedPool','')),
 ('raw-oracle-equality-is-claimed-after-a-hit',ORACLE,RAW_UPTO,RAW_UPTO.replace('(!ErasureHit.bad{2} =>','(true =>')),
)
