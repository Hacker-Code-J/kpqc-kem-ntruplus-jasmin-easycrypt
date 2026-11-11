"""Actual setup/challenge calls and explicit partial-game boundaries."""
BASE='ntruplus/proof/768/ref/kem_indcca_game/'
GAME=BASE+'NTRUPlus768CCAGame.ec'
RULES=(
 (GAME,'adversary receives only typed and decap query capabilities',r'module type CCAAdversary(H:CCAOraclePort,D:CCADecapPort) = { proc guess(pk:W8.t Array1152.t,ct:W8.t Array1152.t,key:W8.t Array32.t) : bool {H.e,H.f,H.g,H.h,D.decap} }.'),
 (GAME,'extended adversary receives raw query but no setup capability',r'module type CCAExtendedAdversary(H:CCAExtendedOraclePort,D:CCADecapPort) = { proc guess(pk:W8.t Array1152.t,ct:W8.t Array1152.t,key:W8.t Array32.t) : bool {H.e,H.f,H.g,H.h,H.raw,D.decap} }.'),
 (GAME,'Encaps option uses actual return status',r'op cca_encap_result (r:encap_result) : cca_encapsulation = if r.`3=W32.zero then Some(r.`1,r.`2) else None.'),
 (GAME,'Encaps status adapter retains original RNG and hash calls',r'result <@ EncapRandom(SHAKEFROM,SHAKEGROM,SHAKEHROM,UniformCoins).run(pk,witness); return cca_encap_result result;'),
 (GAME,'original challenge retains independent key/bit and exact ciphertext',r'module CCAChallengeOriginal(A:CCAExtendedAdversary) = { module Adv=A(SharedCCAExtendedOracles,CCADecapOracle) proc run(pk:W8.t Array1152.t,sk:W8.t Array2336.t) : bool = { var real:encap_result; var random:W8.t Array32.t; var bit,guess:bool; real <@ EncapRandom(SHAKEFROM,SHAKEGROM,SHAKEHROM,UniformCoins).run(pk,witness); random <$ uniform32; bit <$ dbool; CCADecapOracle.init(sk,real.`1); guess <@ Adv.guess(pk,real.`1,if bit then random else real.`2); return guess=bit; } }.'),
 (GAME,'stopping remains analysis setup with returned exhaustion',r'module CCAStoppedBody(A:CCAExtendedAdversary) = { proc run(qf:int,qg:int) : bool option = { var setup:stopped_output; var out:keygen_output; var result:bool option; var win:bool; ROMInit.init(); RawXOFStreams.init(); CCADecapOracle.reset(); setup <@ StoppedKeygen(UniformSeedRNG,ExpandROM).run(qf,qg,witness); result <- None; if(setup.`1<>None){ out <- oget setup.`1; win <@ CCAChallengeOption(A).run(out.`1.`kg_pk,out.`1.`kg_sk); result <- Some win; } return result; } }.'),
 (GAME,'finite setup completion explicit fallback wrapper',r'module CCAFiniteGame(A:CCAExtendedAdversary) = CompleteFallback(CCAStoppedBody(A)).'),
)
for variant in ('Original','Option'):
 RULES+=((GAME,'actual unbounded public Keygen in '+variant+' game',
  'module CCA'+variant+'Game(A:CCAExtendedAdversary) = { proc run() : bool = { var pk:W8.t Array1152.t; var sk:W8.t Array2336.t; var win:bool; ROMInit.init(); RawXOFStreams.init(); CCADecapOracle.reset(); (pk,sk) <@ Keygen(UniformSeedRNG,ExpandROM,SHAKEFROM).run(); win <@ CCAChallenge'+variant+'(A).run(pk,sk); return win; } }.'),)
MUTATIONS=(
 ('adversary-port-exposes-decap-init',GAME,'{H.e,H.f,H.g,H.h,D.decap}','{H.e,H.f,H.g,H.h,D.decap,D.init}'),
 ('extended-adversary-port-exposes-hash-init',GAME,'{H.e,H.f,H.g,H.h,H.raw,D.decap}','{H.e,H.f,H.g,H.h,H.raw,H.init,D.decap}'),
 ('challenge-key-coins-frozen',GAME,'random <$ uniform32; bit <$ dbool;','random <- witness; bit <$ dbool;'),
 ('challenge-bit-frozen',GAME,'random <$ uniform32; bit <$ dbool;','random <$ uniform32; bit <- false;'),
 ('challenge-compares-wrong-status-field',GAME,'if r.`3=W32.zero then Some(r.`1,r.`2)','if r.`2=witness then Some(r.`1,r.`2)'),
 ('challenge-actual-Encaps-RNG-substituted',GAME,'real <@ EncapRandom(SHAKEFROM,SHAKEGROM,SHAKEHROM,UniformCoins).run(pk,witness);','real <@ ReferenceEncap.run(pk,witness);'),
 ('challenge-installs-random-ciphertext',GAME,'CCADecapOracle.init(sk,real.`1);','CCADecapOracle.init(sk,witness);'),
 ('challenge-always-gives-real-key',GAME,'if bit then random else real.`2','real.`2'),
 ('original-game-truncates-real-Keygen',GAME,'(pk,sk) <@ Keygen(UniformSeedRNG,ExpandROM,SHAKEFROM).run();','(pk,sk) <@ CappedKeygen.run();'),
 ('game-clears-shared-table-after-Keygen',GAME,'win <@ CCAChallengeOriginal(A).run(pk,sk);','ROF.init(); win <@ CCAChallengeOriginal(A).run(pk,sk);'),
 ('stopped-body-turns-exhaustion-into-returned-false',GAME,'result <- None;','result <- Some false;'),
 ('adversary-can-read-ROE-global',GAME,'{-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams}','{-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams}'),
)


def check_extra(read, require):
 import re
 code=read(GAME)
 binders=re.findall(r'\(A<:CCA(?:Extended)?Adversary([^)]*)\)',code)
 require(bool(binders),'no adversary semantic theorem binders')
 for binder in binders:
  exclusions=set(re.findall(r'-([A-Za-z0-9_]+)',binder))
  for forbidden in ('ROE','ROF','ROG','ROH','CCADecapOracle','RawXOFStreams'):
   require(forbidden in exclusions,'adversary direct access to '+forbidden)
 require('islosslessKeygen(UniformSeedRNG,ExpandROM,SHAKEFROM).run' not in code,
         'unsupported actual unbounded ROM Keygen losslessness')

SETUP=BASE+'NTRUPlus768CCASetup.ec'
RULES+=(
 (SETUP,'actual public Keygen canonical law without totality premise',r'lemma cca_keygen_public_canonical (R<:KeygenSeedRNG {-ROF}) (E<:KeygenExpand {-ROF}) : hoare[Keygen(R,E,SHAKEFROM).run : true ==> encap_key_canonical res.`1].'),
 (SETUP,'actual Encaps status only under canonical public key',r'lemma cca_encap_random_status_any (R<:EncapRNG) (F<:EncapSHAKEF) (G<:MessageSHAKE) (H<:CompleteSHAKEH) : hoare[EncapRandom(F,G,H,R).run : encap_key_canonical pk ==> res.`3=W32.zero].'),
)
MUTATIONS+=(
 ('setup-canonical-law-assumes-real-keygen-lossless',SETUP,'lemma cca_keygen_public_canonical (R<:KeygenSeedRNG {-ROF}) (E<:KeygenExpand {-ROF}) :','lemma cca_keygen_public_canonical (R<:KeygenSeedRNG {-ROF}) (E<:KeygenExpand {-ROF}) : islossless Keygen(R,E,SHAKEFROM).run =>'),
 ('encap-success-status-assumed-for-noncanonical-keys',SETUP,'hoare[EncapRandom(F,G,H,R).run : encap_key_canonical pk ==> res.`3=W32.zero]','hoare[EncapRandom(F,G,H,R).run : true ==> res.`3=W32.zero]'),
)

_stopped=next(expected for _,label,expected in RULES if label=='stopping remains analysis setup with returned exhaustion')
RULES+=((GAME,'stopped original retains the same setup and challenge',
         _stopped.replace('CCAStoppedBody','CCAStoppedOriginalBody').replace('CCAChallengeOption','CCAChallengeOriginal')),)

RULES+=((GAME,'zero setup budget returns fair completion without adversary totality',
 r'lemma cca_finite_zero_setup_fair (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams}) &m qg : Pr[CCAFiniteGame(A).run(0,qg) @ &m:res]=1%r/2%r.'),)

FRAME=BASE+'NTRUPlus768CCARawStateFrame.ec'
KNOWN='raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other'
RULES+=(
 (FRAME,'original Decaps preserves all previously stored raw streams',
  'lemma cca_actual_decaps_preserves_raw_known x0 s0 : hoare[CompleteDecaps(SHAKEGROM,SHAKEHROM).run : '+KNOWN+' ==> '+KNOWN+'].'),
 (FRAME,'mixed hash and Decaps adversary invariant requires no termination premise',
  'lemma cca_adversary_preserves_raw_known (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams}) x0 s0 : hoare[A(SharedCCAExtendedOracles,CCADecapOracle).guess : '+KNOWN+' ==> '+KNOWN+'].'),
)
MUTATIONS+=(
 ('raw-state-frame-substitutes-reference-Decaps',FRAME,'hoare[CompleteDecaps(SHAKEGROM,SHAKEHROM).run :','hoare[ReferenceDecaps.run :'),
 ('raw-state-frame-omits-Decaps-capability',FRAME,'hoare[A(SharedCCAExtendedOracles,CCADecapOracle).guess :','hoare[A(SharedCCAExtendedOracles).run :'),
 ('raw-state-frame-assumes-adversary-totality',FRAME,'}) x0 s0 : hoare[A(SharedCCAExtendedOracles,CCADecapOracle).guess :','}) x0 s0 : islossless A(SharedCCAExtendedOracles,CCADecapOracle).guess => hoare[A(SharedCCAExtendedOracles,CCADecapOracle).guess :'),
)
