require import AllCore Distr FMap StdOrder.
from Jasmin require import JWord.
require import Array14466.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteProof.
require import NTRUPlus768StoppedKeygenModel NTRUPlus768StoppedKeygenPrefix.
require import NTRUPlus768FreshRetryLaw NTRUPlus768ROMOracles.
require import NTRUPlus768CCAGame NTRUPlus768CCADecapOracle NTRUPlus768RawXOFStreams.
require import NTRUPlus768CCASetupPrefix.
require import NTRUPlus768ErasureModel NTRUPlus768ErasureBudget.
require import NTRUPlus768ErasureSetup NTRUPlus768ErasurePrefix NTRUPlus768ErasureGames.
import RealOrder.

(* Both full games extend their stopped returned-win masses by a number
   in [0,tau]. Their residuals need not be equal or independent. *)
lemma erasure_common_tail_interval p1 p2 s1 s2 tau :
 0%r<=p1-s1<=tau =>0%r<=p2-s2<=tau =>
 `|p1-p2|<=`|s1-s2|+tau.
proof. rewrite !ler_norml; smt(). qed.

(* Reify only the successful setup observation. The None branch carries
   no key, oracle table or private log; both setup procedures are lossless. *)
lemma erasure_counted_stopped_coupling
 (E<:KeygenExpand {-ROF,-UniformSeedRNG,-PrefixBad}) qf0 qg0 :
 islossless E.shake =>
 islossless CountedKeygen(UniformSeedRNG,E).run =>
 equiv[CountedKeygen(UniformSeedRNG,E).run ~ StoppedKeygen(UniformSeedRNG,E).run:
 ={workspace,glob E,glob ROF} /\ qf{2}=qf0 /\ qg{2}=qg0 ==>
 counted_within qf0 qg0 res{1}=stopped_success res{2} /\
 (counted_within qf0 qg0 res{1} =>
  res.`1{1}=oget res.`1{2} /\ ={glob E,glob ROF})].
proof.
 move=>hE hfull.
 conseq (_: _ ==>
  (if counted_within qf0 qg0 res{1} then Some(res.`1{1},(glob E){1},ROF.m{1}) else None)=
  (if stopped_success res{2} then Some(oget res.`1{2},(glob E){2},ROF.m{2}) else None)) => //.
 + smt().
 bypr
  (if counted_within qf0 qg0 res{1} then Some(res.`1{1},(glob E){1},ROF.m{1}) else None)
  (if stopped_success res{2} then Some(oget res.`1{2},(glob E){2},ROF.m{2}) else None).
 + smt().
 move=> &1 &2 z [[hw [hEeq hFeq]] [hqf hqg]].
 rewrite hqf hqg.
 have hs : Pr[StoppedKeygen(UniformSeedRNG,E).run(qf0,qg0,workspace{2}) @ &2:
  (if stopped_success res then Some(oget res.`1,(glob E),ROF.m) else None)=z]=
  Pr[StoppedKeygen(UniformSeedRNG,E).run(qf0,qg0,workspace{1}) @ &1:
  (if stopped_success res then Some(oget res.`1,(glob E),ROF.m) else None)=z].
 + byequiv (_: ={qf,qg,workspace,glob E,glob ROF} ==> ={res,glob E,glob ROF}) => //.
   proc; sim.
   smt().
 rewrite hs.
 clear hs.
 case z=>[|v].
 + have hp:=cca_counted_stopped_state_prefix UniformSeedRNG E qf0 qg0 workspace{1}
    (fun _ _ _=>true) &1 uniform_seed_rng_ll hE.
   have hf:Pr[CountedKeygen(UniformSeedRNG,E).run(workspace{1}) @ &1:true]=1%r
    by byphoare hfull.
   have ht:Pr[StoppedKeygen(UniformSeedRNG,E).run(qf0,qg0,workspace{1}) @ &1:true]=1%r
    by byphoare(stopped_keygen_lossless UniformSeedRNG E uniform_seed_rng_ll hE).
   have e1:Pr[CountedKeygen(UniformSeedRNG,E).run(workspace{1}) @ &1:
     (if counted_within qf0 qg0 res then Some(res.`1,(glob E),ROF.m) else None)=None]=
    Pr[CountedKeygen(UniformSeedRNG,E).run(workspace{1}) @ &1:!counted_within qf0 qg0 res]
    by rewrite Pr[mu_eq]; smt().
   have e2:Pr[StoppedKeygen(UniformSeedRNG,E).run(qf0,qg0,workspace{1}) @ &1:
     (if stopped_success res then Some(oget res.`1,(glob E),ROF.m) else None)=None]=
    Pr[StoppedKeygen(UniformSeedRNG,E).run(qf0,qg0,workspace{1}) @ &1:!stopped_success res]
    by rewrite Pr[mu_eq]; smt().
   rewrite e1 e2 Pr[mu_not] Pr[mu_not] hf ht.
   have ->:Pr[CountedKeygen(UniformSeedRNG,E).run(workspace{1}) @ &1:counted_within qf0 qg0 res]=
    Pr[StoppedKeygen(UniformSeedRNG,E).run(qf0,qg0,workspace{1}) @ &1:stopped_success res]
    by move:hp; rewrite /=.
   done.
 have hp:=cca_counted_stopped_state_prefix UniformSeedRNG E qf0 qg0 workspace{1}
   (fun out ge fm=>(out,ge,fm)=v) &1 uniform_seed_rng_ll hE.
 have e1:Pr[CountedKeygen(UniformSeedRNG,E).run(workspace{1}) @ &1:
   (if counted_within qf0 qg0 res then Some(res.`1,(glob E),ROF.m) else None)=Some v]=
  Pr[CountedKeygen(UniformSeedRNG,E).run(workspace{1}) @ &1:
   counted_within qf0 qg0 res /\ (res.`1,(glob E),ROF.m)=v]
  by rewrite Pr[mu_eq]; smt().
 have e2:Pr[StoppedKeygen(UniformSeedRNG,E).run(qf0,qg0,workspace{1}) @ &1:
   (if stopped_success res then Some(oget res.`1,(glob E),ROF.m) else None)=Some v]=
  Pr[StoppedKeygen(UniformSeedRNG,E).run(qf0,qg0,workspace{1}) @ &1:
   stopped_success res /\ (oget res.`1,(glob E),ROF.m)=v]
  by rewrite Pr[mu_eq]; smt().
 by rewrite e1 e2 hp.
qed.

op erasure_game_within (qf qg:int) (r:bool*int*int) =
 r.`2<=max 0 qf /\ r.`3<=max 0 qg.

lemma erasure_programmed_game_counted
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState}) :
 equiv[ErasureCountedGame(LoggedProgrammedExpand,A).run ~ ErasureLoggedProgrammedGame(A).run:
 ={glob A,glob EBudgetState} ==> res.`1{1}=res{2}].
proof.
 proc; inline{2} Keygen(UniformSeedRNG,LoggedProgrammedExpand,SHAKEFROM).run; wp.
 call(erasure_capped_challenge_ghost_independent A).
 wp.
 call(counted_keygen_erasure UniformSeedRNG LoggedProgrammedExpand).
 inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init
  CCADecapOracle.reset ErasureSeedLog.init ErasureHit.init.
 auto.
qed.

lemma erasure_programmed_game_prefix
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState}) qf0 qg0 :
 islossless CCAChallengeOriginal(CappedA(A)).run =>
 equiv[ErasureCountedGame(LoggedProgrammedExpand,A).run ~ ErasureStoppedProgrammedGame(A).run:
 ={glob A,glob EBudgetState} /\ qf{2}=qf0 /\ qg{2}=qg0 ==>
 (res.`1{1} /\ erasure_game_within qf0 qg0 res{1})=(res{2}=Some true)].
proof.
 move=>hA; proc.
 seq 6 6 : (qf{2}=qf0 /\ qg{2}=qg0 /\
  counted_within qf0 qg0 setup{1}=stopped_success setup{2} /\
  (counted_within qf0 qg0 setup{1} =>
   setup.`1{1}=oget setup.`1{2} /\
   ={glob A,glob EBudgetState,glob ROE,glob ROF,glob ROG,glob ROH,
     glob RawXOFStreams,glob CCADecapOracle})).
 + call(erasure_counted_stopped_coupling LoggedProgrammedExpand qf0 qg0
     logged_programmed_expand_ll erasure_programmed_counted_ll).
   inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init
    CCADecapOracle.reset ErasureSeedLog.init ErasureHit.init.
   auto; smt().
 sp 0 1; if{2}.
 + wp; call(erasure_capped_challenge_ghost_independent A).
   auto=> />; rewrite /erasure_game_within /counted_within /stopped_success; smt().
 wp; call{1} hA; auto=> />; rewrite /erasure_game_within /counted_within /stopped_success; smt().
qed.

lemma erasure_programmed_game_prefix_probability
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState}) &m qf qg :
 islossless CCAChallengeOriginal(CappedA(A)).run =>
 Pr[ErasureCountedGame(LoggedProgrammedExpand,A).run() @ &m:
   res.`1 /\ erasure_game_within qf qg res]=
 Pr[ErasureStoppedProgrammedGame(A).run(qf,qg) @ &m:res=Some true].
proof. move=>hA; byequiv(erasure_programmed_game_prefix A qf qg hA)=> //; smt(). qed.

lemma erasure_programmed_game_tail
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState}) &m qf qg :
 0<=qf=>0<=qg=>
 Pr[ErasureCountedGame(LoggedProgrammedExpand,A).run() @ &m:!erasure_game_within qf qg res]
 <=fresh_retry_tail qf qg.
proof.
 move=>hf hg.
 have hT:phoare[CountedKeygen(UniformSeedRNG,LoggedProgrammedExpand).run:
  true ==> !counted_within qf qg res] <=(fresh_retry_tail qf qg).
 + bypr=> &mm _; exact(erasure_programmed_counted_tail &mm qf qg workspace{mm} hf hg).
 byphoare (_:true ==> _) => //.
 proc; rewrite /erasure_game_within.
 seq 6 : (!counted_within qf qg setup) (fresh_retry_tail qf qg) 1%r 1%r 0%r true => //.
 + call hT.
   inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init
    CCADecapOracle.reset ErasureSeedLog.init ErasureHit.init; auto.
 hoare; call (_:true ==>true); first by trivial.
 auto=> />; rewrite /counted_within; smt().
qed.

lemma erasure_programmed_tail_interval
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState}) &m qf qg :
 islossless CCAChallengeOriginal(CappedA(A)).run =>
 0<=qf=>0<=qg=>
 0%r<=Pr[ErasureProgrammedGame(A).run() @ &m:res]-
       Pr[ErasureStoppedProgrammedGame(A).run(qf,qg) @ &m:res=Some true]
 <=fresh_retry_tail qf qg.
proof.
 move=>hA hf hg.
 have hc:Pr[ErasureCountedGame(LoggedProgrammedExpand,A).run() @ &m:res.`1]=
   Pr[ErasureLoggedProgrammedGame(A).run() @ &m:res]
   by byequiv(erasure_programmed_game_counted A)=> //.
 have he:Pr[ErasureLoggedProgrammedGame(A).run() @ &m:res]=
   Pr[ErasureProgrammedGame(A).run() @ &m:res]
   by byequiv(erasure_programmed_game_projection A)=> //.
 have hp:=erasure_programmed_game_prefix_probability A &m qf qg hA.
 have ht:=erasure_programmed_game_tail A &m qf qg hf hg.
 have hs:Pr[ErasureCountedGame(LoggedProgrammedExpand,A).run() @ &m:res.`1]=
   Pr[ErasureCountedGame(LoggedProgrammedExpand,A).run() @ &m:res.`1 /\ erasure_game_within qf qg res]+
   Pr[ErasureCountedGame(LoggedProgrammedExpand,A).run() @ &m:res.`1 /\ !erasure_game_within qf qg res]
   by rewrite Pr[mu_split (erasure_game_within qf qg res)].
 have hb:Pr[ErasureCountedGame(LoggedProgrammedExpand,A).run() @ &m:res.`1 /\ !erasure_game_within qf qg res]<=
   Pr[ErasureCountedGame(LoggedProgrammedExpand,A).run() @ &m:!erasure_game_within qf qg res]
   by rewrite Pr[mu_sub].
 have hn:0%r<=Pr[ErasureCountedGame(LoggedProgrammedExpand,A).run() @ &m:res.`1 /\ !erasure_game_within qf qg res]
   by smt(mu_bounded).
 have hd:Pr[ErasureProgrammedGame(A).run() @ &m:res]-
   Pr[ErasureStoppedProgrammedGame(A).run(qf,qg) @ &m:res=Some true]=
   Pr[ErasureCountedGame(LoggedProgrammedExpand,A).run() @ &m:res.`1 /\ !erasure_game_within qf qg res].
 + rewrite -he -hc -hp hs; ring.
 rewrite hd; split; first exact hn.
 move=>_.
 exact(ler_trans _ _ _ hb ht).
qed.

lemma erasure_independent_game_counted
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState}) :
 equiv[ErasureCountedGame(LoggedErasedExpand,A).run ~ ErasureLoggedIndependentGame(A).run:
 ={glob A,glob EBudgetState} ==> res.`1{1}=res{2}].
proof.
 proc; inline{2} Keygen(UniformSeedRNG,LoggedErasedExpand,SHAKEFROM).run; wp.
 call(erasure_capped_challenge_ghost_independent A).
 wp.
 call(counted_keygen_erasure UniformSeedRNG LoggedErasedExpand).
 inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init
  CCADecapOracle.reset ErasureSeedLog.init ErasureHit.init.
 auto.
qed.

lemma erasure_independent_game_prefix
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState}) qf0 qg0 :
 islossless CCAChallengeOriginal(CappedA(A)).run =>
 equiv[ErasureCountedGame(LoggedErasedExpand,A).run ~ ErasureStoppedIndependentGame(A).run:
 ={glob A,glob EBudgetState} /\ qf{2}=qf0 /\ qg{2}=qg0 ==>
 (res.`1{1} /\ erasure_game_within qf0 qg0 res{1})=(res{2}=Some true)].
proof.
 move=>hA; proc.
 seq 6 6 : (qf{2}=qf0 /\ qg{2}=qg0 /\
  counted_within qf0 qg0 setup{1}=stopped_success setup{2} /\
  (counted_within qf0 qg0 setup{1} =>
   setup.`1{1}=oget setup.`1{2} /\
   ={glob A,glob EBudgetState,glob ROE,glob ROF,glob ROG,glob ROH,
     glob RawXOFStreams,glob CCADecapOracle})).
 + call(erasure_counted_stopped_coupling LoggedErasedExpand qf0 qg0
     logged_erased_expand_ll erasure_erased_counted_ll).
   inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init
    CCADecapOracle.reset ErasureSeedLog.init ErasureHit.init.
   auto; smt().
 sp 0 1; if{2}.
 + wp; call(erasure_capped_challenge_ghost_independent A).
   auto=> />; rewrite /erasure_game_within /counted_within /stopped_success; smt().
 wp; call{1} hA; auto=> />; rewrite /erasure_game_within /counted_within /stopped_success; smt().
qed.

lemma erasure_independent_game_prefix_probability
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState}) &m qf qg :
 islossless CCAChallengeOriginal(CappedA(A)).run =>
 Pr[ErasureCountedGame(LoggedErasedExpand,A).run() @ &m:
   res.`1 /\ erasure_game_within qf qg res]=
 Pr[ErasureStoppedIndependentGame(A).run(qf,qg) @ &m:res=Some true].
proof. move=>hA; byequiv(erasure_independent_game_prefix A qf qg hA)=> //; smt(). qed.

lemma erasure_independent_game_tail
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState}) &m qf qg :
 0<=qf=>0<=qg=>
 Pr[ErasureCountedGame(LoggedErasedExpand,A).run() @ &m:!erasure_game_within qf qg res]
 <=fresh_retry_tail qf qg.
proof.
 move=>hf hg.
 have hT:phoare[CountedKeygen(UniformSeedRNG,LoggedErasedExpand).run:
  true ==> !counted_within qf qg res] <=(fresh_retry_tail qf qg).
 + bypr=> &mm _; exact(erasure_erased_counted_tail &mm qf qg workspace{mm} hf hg).
 byphoare (_:true ==> _) => //.
 proc; rewrite /erasure_game_within.
 seq 6 : (!counted_within qf qg setup) (fresh_retry_tail qf qg) 1%r 1%r 0%r true => //.
 + call hT.
   inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init
    CCADecapOracle.reset ErasureSeedLog.init ErasureHit.init; auto.
 hoare; call (_:true ==>true); first by trivial.
 auto=> />; rewrite /counted_within; smt().
qed.

lemma erasure_independent_tail_interval
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState}) &m qf qg :
 islossless CCAChallengeOriginal(CappedA(A)).run =>
 0<=qf=>0<=qg=>
 0%r<=Pr[ErasureIndependentGame(A).run() @ &m:res]-
       Pr[ErasureStoppedIndependentGame(A).run(qf,qg) @ &m:res=Some true]
 <=fresh_retry_tail qf qg.
proof.
 move=>hA hf hg.
 have hc:Pr[ErasureCountedGame(LoggedErasedExpand,A).run() @ &m:res.`1]=
   Pr[ErasureLoggedIndependentGame(A).run() @ &m:res]
   by byequiv(erasure_independent_game_counted A)=> //.
 have he:Pr[ErasureLoggedIndependentGame(A).run() @ &m:res]=
   Pr[ErasureIndependentGame(A).run() @ &m:res]
   by byequiv(erasure_independent_game_projection A)=> //.
 have hp:=erasure_independent_game_prefix_probability A &m qf qg hA.
 have ht:=erasure_independent_game_tail A &m qf qg hf hg.
 have hs:Pr[ErasureCountedGame(LoggedErasedExpand,A).run() @ &m:res.`1]=
   Pr[ErasureCountedGame(LoggedErasedExpand,A).run() @ &m:res.`1 /\ erasure_game_within qf qg res]+
   Pr[ErasureCountedGame(LoggedErasedExpand,A).run() @ &m:res.`1 /\ !erasure_game_within qf qg res]
   by rewrite Pr[mu_split (erasure_game_within qf qg res)].
 have hb:Pr[ErasureCountedGame(LoggedErasedExpand,A).run() @ &m:res.`1 /\ !erasure_game_within qf qg res]<=
   Pr[ErasureCountedGame(LoggedErasedExpand,A).run() @ &m:!erasure_game_within qf qg res]
   by rewrite Pr[mu_sub].
 have hn:0%r<=Pr[ErasureCountedGame(LoggedErasedExpand,A).run() @ &m:res.`1 /\ !erasure_game_within qf qg res]
   by smt(mu_bounded).
 have hd:Pr[ErasureIndependentGame(A).run() @ &m:res]-
   Pr[ErasureStoppedIndependentGame(A).run(qf,qg) @ &m:res=Some true]=
   Pr[ErasureCountedGame(LoggedErasedExpand,A).run() @ &m:res.`1 /\ !erasure_game_within qf qg res].
 + rewrite -he -hc -hp hs; ring.
 rewrite hd; split; first exact hn.
 move=>_.
 exact(ler_trans _ _ _ hb ht).
qed.

lemma erasure_games_common_tail
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams,
  -ErasureSeedLog,-ErasureHit,-ErasureSeedPool,-EBudgetState}) &m qf qg :
 islossless CCAChallengeOriginal(CappedA(A)).run =>
 0<=qf=>0<=qg=>
 `|Pr[ErasureProgrammedGame(A).run() @ &m:res]-
    Pr[ErasureIndependentGame(A).run() @ &m:res]| <=
 `|Pr[ErasureStoppedProgrammedGame(A).run(qf,qg) @ &m:res=Some true]-
    Pr[ErasureStoppedIndependentGame(A).run(qf,qg) @ &m:res=Some true]|+
 fresh_retry_tail qf qg.
proof.
 move=>hA hf hg.
 exact(erasure_common_tail_interval _ _ _ _ _
   (erasure_programmed_tail_interval A &m qf qg hA hf hg)
   (erasure_independent_tail_interval A &m qf qg hA hf hg)).
qed.

