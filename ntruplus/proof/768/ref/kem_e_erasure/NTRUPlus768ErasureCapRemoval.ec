require import AllCore List Distr FMap.
from Jasmin require import JWord.
require import Array32 Array1152.
require import NTRUPlus768ROMOracles NTRUPlus768CCAOraclePorts.
require import NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
require import NTRUPlus768CCADecapOracle NTRUPlus768CCAGame.
require import NTRUPlus768ErasureModel NTRUPlus768ErasureBudget.

(* The original setup, challenge, clearing, and Decaps calls are reused.
   The new limit is an explicit argument of this restricted experiment. *)
module CountedOriginalGame(A:CCAExtendedAdversary) = {
 proc run(q:int) : bool = {
  var win:bool;
  EBudgetState.configure(q);
  win <@ CCAOriginalGame(CountedA(A)).run();
  return win;
 }
}.
module CappedOriginalGame(A:CCAExtendedAdversary) = {
 proc run(q:int) : bool = {
  var win:bool;
  EBudgetState.configure(q);
  win <@ CCAOriginalGame(CappedA(A)).run();
  return win;
 }
}.

(* These phase wrappers are total only under an explicit adversary
   termination contract. The physical unbounded KeyGen is outside them. *)
module CountedEPhase(A:CCAExtendedAdversary) = {
 proc run(q:int,pk:W8.t Array1152.t,ct:W8.t Array1152.t,key:W8.t Array32.t) : bool = {
  var answer:bool;
  EBudgetState.configure(q);
  answer <@ CountedA(A,SharedCCAExtendedOracles,CCADecapOracle).guess(pk,ct,key);
  return answer;
 }
}.
module CappedEPhase(A:CCAExtendedAdversary) = {
 proc run(q:int,pk:W8.t Array1152.t,ct:W8.t Array1152.t,key:W8.t Array32.t) : bool = {
  var answer:bool;
  EBudgetState.configure(q);
  answer <@ CappedA(A,SharedCCAExtendedOracles,CCADecapOracle).guess(pk,ct,key);
  return answer;
 }
}.

lemma counted_adversary_erasure
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
   -EBudgetState,-ErasureHit,-ErasureSeedLog,-ErasureSeedPool}) :
 equiv[CountedA(A,SharedCCAExtendedOracles,CCADecapOracle).guess ~
       A(SharedCCAExtendedOracles,CCADecapOracle).guess:
 ={pk,ct,key,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle} ==>
 ={res,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle}].
proof.
 proc(={glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle}); 1,2:by auto.
 + proc*; call count_shared_e_backend; auto.
 + by sim.
 + by sim.
 + by sim.
 + proc*; call count_shared_raw_backend; auto.
 by sim.
qed.

require import NTRUPlus768KeygenCompleteProof NTRUPlus768FreshRetryLaw.
require import NTRUPlus768EncapCompleteRNG NTRUPlus768NumericalDFRModel.

lemma counted_challenge_erasure
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
   -EBudgetState,-ErasureHit,-ErasureSeedLog,-ErasureSeedPool}) :
 equiv[CCAChallengeOriginal(CountedA(A)).run ~ CCAChallengeOriginal(A).run:
 ={pk,sk,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle} ==>
 ={res,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle}].
proof.
 proc; call(counted_adversary_erasure A).
 inline CCADecapOracle.init; wp; rnd; rnd.
 call(_: ={pk,workspace,glob ROF,glob ROG,glob ROH} ==> ={res,glob ROF,glob ROG,glob ROH}); first by sim.
 auto.
qed.

lemma counted_original_erasure
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
   -EBudgetState,-ErasureHit,-ErasureSeedLog,-ErasureSeedPool}) :
 equiv[CountedOriginalGame(A).run ~ CCAOriginalGame(A).run: ={glob A} ==>
 ={res,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle}].
proof.
 proc; inline CCAOriginalGame(CountedA(A)).run; wp.
 call(counted_challenge_erasure A).
 call(_: ={glob ROE,glob ROF} ==> ={res,glob ROE,glob ROF}); first by sim.
 inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init CCADecapOracle.reset EBudgetState.configure.
 auto.
qed.

lemma counted_original_event
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
   -EBudgetState,-ErasureHit,-ErasureSeedLog,-ErasureSeedPool}) &m q (event:bool->bool) :
 Pr[CountedOriginalGame(A).run(q) @ &m:event res]=
 Pr[CCAOriginalGame(A).run() @ &m:event res].
proof. byequiv(counted_original_erasure A)=> //. qed.

lemma count_e_overflow_exact (H<:CCAExtendedOraclePort {-EBudgetState,-ErasureHit,-ErasureSeedLog}) :
 hoare[CountEPort(H).e:EBudgetState.overflow=(EBudgetState.limit<EBudgetState.requests) ==>
 EBudgetState.overflow=(EBudgetState.limit<EBudgetState.requests)].
proof.
 proc; call(_:true ==>true); first by trivial.
 inline ErasureBudgetMonitor.request ErasureBudgetMonitor.forward ErasureHit.mark; auto; smt().
qed.
lemma count_raw_overflow_exact (H<:CCAExtendedOraclePort {-EBudgetState,-ErasureHit,-ErasureSeedLog}) :
 hoare[CountEPort(H).raw:EBudgetState.overflow=(EBudgetState.limit<EBudgetState.requests) ==>
 EBudgetState.overflow=(EBudgetState.limit<EBudgetState.requests)].
proof.
 proc; call(_:true ==>true); first by trivial.
 inline ErasureBudgetMonitor.request ErasureBudgetMonitor.forward ErasureHit.mark; auto; smt().
qed.
lemma counted_adversary_overflow_exact
 (A<:CCAExtendedAdversary {-EBudgetState,-ErasureHit,-ErasureSeedLog,-ErasureSeedPool})
 (H<:CCAExtendedOraclePort {-A,-EBudgetState,-ErasureHit,-ErasureSeedLog})
 (D<:CCADecapPort {-A,-EBudgetState,-ErasureHit,-ErasureSeedLog}) :
 hoare[CountedA(A,H,D).guess:EBudgetState.overflow=(EBudgetState.limit<EBudgetState.requests) ==>
 EBudgetState.overflow=(EBudgetState.limit<EBudgetState.requests)].
proof.
 proc(EBudgetState.overflow=(EBudgetState.limit<EBudgetState.requests)); 1,2:by auto.
 + exact(count_e_overflow_exact H).
 + proc*; call(_:true ==>true); first by trivial. auto.
 + proc*; call(_:true ==>true); first by trivial. auto.
 + proc*; call(_:true ==>true); first by trivial. auto.
 + exact(count_raw_overflow_exact H).
 proc*; call(_:true ==>true); first by trivial. auto.
qed.

lemma counted_phase_overflow_exact
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
   -EBudgetState,-ErasureHit,-ErasureSeedLog,-ErasureSeedPool}) q0 :
 hoare[CountedEPhase(A).run:q=q0 ==>
 EBudgetState.limit=max 0 q0 /\ EBudgetState.overflow=(EBudgetState.limit<EBudgetState.requests)].
proof.
 proc; call(counted_adversary_overflow_exact A SharedCCAExtendedOracles CCADecapOracle).
 inline EBudgetState.configure; auto; smt().
qed.

lemma count_e_overflow_sticky (H<:CCAExtendedOraclePort {-EBudgetState,-ErasureHit,-ErasureSeedLog}) :
 hoare[CountEPort(H).e:EBudgetState.overflow ==> EBudgetState.overflow].
proof.
 proc; call(_:true ==>true); first by trivial.
 inline ErasureBudgetMonitor.request ErasureBudgetMonitor.forward ErasureHit.mark; auto; smt().
qed.
lemma count_raw_overflow_sticky (H<:CCAExtendedOraclePort {-EBudgetState,-ErasureHit,-ErasureSeedLog}) :
 hoare[CountEPort(H).raw:EBudgetState.overflow ==> EBudgetState.overflow].
proof.
 proc; call(_:true ==>true); first by trivial.
 inline ErasureBudgetMonitor.request ErasureBudgetMonitor.forward ErasureHit.mark; auto; smt().
qed.
lemma cap_e_overflow_sticky (H<:CCAExtendedOraclePort {-EBudgetState,-ErasureHit,-ErasureSeedLog}) :
 hoare[CapEPort(H).e:EBudgetState.overflow ==> EBudgetState.overflow].
proof.
 proc; inline ErasureBudgetMonitor.request; sp; if; last by auto; smt().
 call(_:true ==>true); first by trivial.
 inline ErasureBudgetMonitor.forward ErasureHit.mark; auto; smt().
qed.
lemma cap_raw_overflow_sticky (H<:CCAExtendedOraclePort {-EBudgetState,-ErasureHit,-ErasureSeedLog}) :
 hoare[CapEPort(H).raw:EBudgetState.overflow ==> EBudgetState.overflow].
proof.
 proc; inline ErasureBudgetMonitor.request ErasureBudgetMonitor.forward ErasureHit.mark; sp; if; last by auto; smt().
 call(_:true ==>true); first by trivial.
 auto; smt().
qed.

lemma count_cap_e_step :
 equiv[CountEPort(SharedCCAExtendedOracles).e ~ CapEPort(SharedCCAExtendedOracles).e:
 ={input,glob EBudgetState,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle} /\
 !EBudgetState.overflow{2} ==>
 EBudgetState.overflow{1}=EBudgetState.overflow{2} /\
 (!EBudgetState.overflow{2} =>
  ={res,glob EBudgetState,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle})].
proof.
 proc; seq 1 1:(={input,allowed,glob EBudgetState,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle} /\
   EBudgetState.overflow{1}=!allowed{1}).
 + inline ErasureBudgetMonitor.request; auto; smt().
 sp 0 1; if{2}.
 + wp; call(_: ={arg,glob ROE} ==> ={res,glob ROE}); first by sim.
   inline ErasureBudgetMonitor.forward ErasureHit.mark; auto; smt().
 wp; call{1} cca_extended_e_ll.
 inline ErasureBudgetMonitor.forward ErasureHit.mark; auto; smt().
qed.

lemma count_cap_raw_step :
 equiv[CountEPort(SharedCCAExtendedOracles).raw ~ CapEPort(SharedCCAExtendedOracles).raw:
 ={input,outlen,glob EBudgetState,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle} /\
 !EBudgetState.overflow{2} ==>
 EBudgetState.overflow{1}=EBudgetState.overflow{2} /\
 (!EBudgetState.overflow{2} =>
  ={res,glob EBudgetState,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle})].
proof.
 proc; inline ErasureBudgetMonitor.request ErasureBudgetMonitor.forward ErasureHit.mark; sp; if{2}.
 + wp; call(_: ={arg,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams} ==>
     ={res,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams}); first by sim.
   auto; smt().
 wp; call{1} cca_extended_raw_ll; auto; smt().
qed.

lemma count_cap_f_step :
 equiv[CountEPort(SharedCCAExtendedOracles).f ~ CapEPort(SharedCCAExtendedOracles).f:
 ={arg,glob EBudgetState,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle} ==> ={res,glob EBudgetState,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle}].
proof. by sim. qed.

lemma count_cap_g_step :
 equiv[CountEPort(SharedCCAExtendedOracles).g ~ CapEPort(SharedCCAExtendedOracles).g:
 ={arg,glob EBudgetState,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle} ==> ={res,glob EBudgetState,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle}].
proof. by sim. qed.

lemma count_cap_h_step :
 equiv[CountEPort(SharedCCAExtendedOracles).h ~ CapEPort(SharedCCAExtendedOracles).h:
 ={arg,glob EBudgetState,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle} ==> ={res,glob EBudgetState,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle}].
proof. by sim. qed.

lemma count_cap_decap_step :
 equiv[CCADecapOracle.decap ~ CCADecapOracle.decap:
 ={arg,glob EBudgetState,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle} ==> ={res,glob EBudgetState,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle}].
proof. by sim. qed.

lemma counted_adversary_lossless
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
   -EBudgetState,-ErasureHit,-ErasureSeedLog,-ErasureSeedPool}) :
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
   islossless H.e =>islossless H.f =>islossless H.g =>islossless H.h =>islossless H.raw =>
   islossless D.decap =>islossless A(H,D).guess) =>
 islossless CountedA(A,SharedCCAExtendedOracles,CCADecapOracle).guess.
proof.
 move=>all; exact(all (CountEPort(SharedCCAExtendedOracles)) CCADecapOracle
   (count_e_ll SharedCCAExtendedOracles cca_extended_e_ll) cca_extended_f_ll
   cca_extended_g_ll cca_extended_h_ll
   (count_raw_ll SharedCCAExtendedOracles cca_extended_raw_ll) cca_decap_lossless).
qed.

lemma capped_adversary_lossless
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
   -EBudgetState,-ErasureHit,-ErasureSeedLog,-ErasureSeedPool}) :
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
   islossless H.e =>islossless H.f =>islossless H.g =>islossless H.h =>islossless H.raw =>
   islossless D.decap =>islossless A(H,D).guess) =>
 islossless CappedA(A,SharedCCAExtendedOracles,CCADecapOracle).guess.
proof.
 move=>all; exact(all (CapEPort(SharedCCAExtendedOracles)) CCADecapOracle
   (cap_e_ll SharedCCAExtendedOracles cca_extended_e_ll) cca_extended_f_ll
   cca_extended_g_ll cca_extended_h_ll
   (cap_raw_ll SharedCCAExtendedOracles cca_extended_raw_ll) cca_decap_lossless).
qed.

lemma count_cap_adversary_upto
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
   -EBudgetState,-ErasureHit,-ErasureSeedLog,-ErasureSeedPool}) :
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
   islossless H.e =>islossless H.f =>islossless H.g =>islossless H.h =>islossless H.raw =>
   islossless D.decap =>islossless A(H,D).guess) =>
 equiv[CountedA(A,SharedCCAExtendedOracles,CCADecapOracle).guess ~
       CappedA(A,SharedCCAExtendedOracles,CCADecapOracle).guess:
 ={pk,ct,key,glob A,glob EBudgetState,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle} /\
 !EBudgetState.overflow{2} ==>
 EBudgetState.overflow{1}=EBudgetState.overflow{2} /\
 (!EBudgetState.overflow{2} =>
  ={res,glob A,glob EBudgetState,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle})].
proof.
 move=>all.
 have al:=counted_adversary_lossless A all.
 have ar:=capped_adversary_lossless A all.
 proc*;
 call(_:EBudgetState.overflow,
   ={glob EBudgetState,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle},
   EBudgetState.overflow{1}=EBudgetState.overflow{2}).
 + conseq count_cap_e_step; smt().
 + move=> &2 h; conseq(count_e_ll SharedCCAExtendedOracles cca_extended_e_ll)
     (count_e_overflow_sticky SharedCCAExtendedOracles); smt().
 + move=> &1; conseq(cap_e_ll SharedCCAExtendedOracles cca_extended_e_ll)
     (cap_e_overflow_sticky SharedCCAExtendedOracles); smt().
 + conseq count_cap_f_step; smt().
 + move=> &2 h; proc*; call cca_extended_f_ll; auto; smt().
 + move=> &1; proc*; call cca_extended_f_ll; auto; smt().
 + conseq count_cap_g_step; smt().
 + move=> &2 h; proc*; call cca_extended_g_ll; auto; smt().
 + move=> &1; proc*; call cca_extended_g_ll; auto; smt().
 + conseq count_cap_h_step; smt().
 + move=> &2 h; proc*; call cca_extended_h_ll; auto; smt().
 + move=> &1; proc*; call cca_extended_h_ll; auto; smt().
 + conseq count_cap_raw_step; smt().
 + move=> &2 h; conseq(count_raw_ll SharedCCAExtendedOracles cca_extended_raw_ll)
     (count_raw_overflow_sticky SharedCCAExtendedOracles); smt().
 + move=> &1; conseq(cap_raw_ll SharedCCAExtendedOracles cca_extended_raw_ll)
     (cap_raw_overflow_sticky SharedCCAExtendedOracles); smt().
 + conseq count_cap_decap_step; smt().
 + move=> &2 h; proc*; call cca_decap_lossless; auto; smt().
 + move=> &1; proc*; call cca_decap_lossless; auto; smt().
 auto; smt().
qed.

lemma counted_adversary_overflow_fixed
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
   -EBudgetState,-ErasureHit,-ErasureSeedLog,-ErasureSeedPool}) q0 :
 hoare[CountedA(A,SharedCCAExtendedOracles,CCADecapOracle).guess:
 EBudgetState.limit=q0 /\ EBudgetState.overflow=(q0<EBudgetState.requests) ==>
 EBudgetState.limit=q0 /\ EBudgetState.overflow=(q0<EBudgetState.requests)].
proof.
 proc*; call(counted_adversary_overflow_exact A SharedCCAExtendedOracles CCADecapOracle).
 auto.
qed.

lemma counted_adversary_no_overflow
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
   -EBudgetState,-ErasureHit,-ErasureSeedLog,-ErasureSeedPool}) q0 :
 0<=q0 =>
 hoare[CountedA(A,SharedCCAExtendedOracles,CCADecapOracle).guess:
 EBudgetState.requests=0 /\ EBudgetState.forwarded=0 /\ EBudgetState.limit=q0 /\
 !EBudgetState.overflow /\ EBudgetState.queries=[] ==> EBudgetState.requests<=q0] =>
 hoare[CountedA(A,SharedCCAExtendedOracles,CCADecapOracle).guess:
 EBudgetState.requests=0 /\ EBudgetState.forwarded=0 /\ EBudgetState.limit=q0 /\
 !EBudgetState.overflow /\ EBudgetState.queries=[] ==> !EBudgetState.overflow].
proof.
 move=>hq bounded.
 conseq bounded (counted_adversary_overflow_fixed A q0); smt().
qed.

lemma count_cap_adversary_equiv
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
   -EBudgetState,-ErasureHit,-ErasureSeedLog,-ErasureSeedPool}) q0 :
 0<=q0 =>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
   islossless H.e =>islossless H.f =>islossless H.g =>islossless H.h =>islossless H.raw =>
   islossless D.decap =>islossless A(H,D).guess) =>
 hoare[CountedA(A,SharedCCAExtendedOracles,CCADecapOracle).guess:
 EBudgetState.requests=0 /\ EBudgetState.forwarded=0 /\ EBudgetState.limit=q0 /\
 !EBudgetState.overflow /\ EBudgetState.queries=[] ==> EBudgetState.requests<=q0] =>
 equiv[CountedA(A,SharedCCAExtendedOracles,CCADecapOracle).guess ~
       CappedA(A,SharedCCAExtendedOracles,CCADecapOracle).guess:
 ={pk,ct,key,glob A,glob EBudgetState,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle} /\
 EBudgetState.requests{1}=0 /\ EBudgetState.forwarded{1}=0 /\ EBudgetState.limit{1}=q0 /\
 !EBudgetState.overflow{1} /\ EBudgetState.queries{1}=[] ==>
 ={res,glob A,glob EBudgetState,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle}].
proof.
 move=>hq all bounded.
 conseq(count_cap_adversary_upto A all)
   (counted_adversary_no_overflow A q0 hq bounded) _; smt().
qed.

lemma count_cap_challenge_equiv
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
   -EBudgetState,-ErasureHit,-ErasureSeedLog,-ErasureSeedPool}) q0 :
 0<=q0 =>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
   islossless H.e =>islossless H.f =>islossless H.g =>islossless H.h =>islossless H.raw =>
   islossless D.decap =>islossless A(H,D).guess) =>
 hoare[CountedA(A,SharedCCAExtendedOracles,CCADecapOracle).guess:
 EBudgetState.requests=0 /\ EBudgetState.forwarded=0 /\ EBudgetState.limit=q0 /\
 !EBudgetState.overflow /\ EBudgetState.queries=[] ==> EBudgetState.requests<=q0] =>
 equiv[CCAChallengeOriginal(CountedA(A)).run ~ CCAChallengeOriginal(CappedA(A)).run:
 ={pk,sk,glob A,glob EBudgetState,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle} /\
 EBudgetState.requests{1}=0 /\ EBudgetState.forwarded{1}=0 /\ EBudgetState.limit{1}=q0 /\
 !EBudgetState.overflow{1} /\ EBudgetState.queries{1}=[] ==>
 ={res,glob A,glob EBudgetState,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle}].
proof.
 move=>hq all bounded; proc.
 call(count_cap_adversary_equiv A q0 hq all bounded).
 inline CCADecapOracle.init; wp; rnd; rnd.
 call(_: ={pk,workspace,glob ROF,glob ROG,glob ROH} ==> ={res,glob ROF,glob ROG,glob ROH}); first by sim.
 auto.
qed.

(* KeyGen remains the same partial procedure on both sides. Its physical
   E calls never pass through the adversarial counter. *)
lemma count_cap_original_equiv
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
   -EBudgetState,-ErasureHit,-ErasureSeedLog,-ErasureSeedPool}) q0 :
 0<=q0 =>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
   islossless H.e =>islossless H.f =>islossless H.g =>islossless H.h =>islossless H.raw =>
   islossless D.decap =>islossless A(H,D).guess) =>
 hoare[CountedA(A,SharedCCAExtendedOracles,CCADecapOracle).guess:
 EBudgetState.requests=0 /\ EBudgetState.forwarded=0 /\ EBudgetState.limit=q0 /\
 !EBudgetState.overflow /\ EBudgetState.queries=[] ==> EBudgetState.requests<=q0] =>
 equiv[CCAOriginalGame(CountedA(A)).run ~ CCAOriginalGame(CappedA(A)).run:
 ={glob A,glob EBudgetState} /\
 EBudgetState.requests{1}=0 /\ EBudgetState.forwarded{1}=0 /\ EBudgetState.limit{1}=q0 /\
 !EBudgetState.overflow{1} /\ EBudgetState.queries{1}=[] ==>
 ={res,glob A,glob EBudgetState,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle}].
proof.
 move=>hq all bounded; proc.
 call(count_cap_challenge_equiv A q0 hq all bounded).
 call(_: ={glob ROE,glob ROF} ==> ={res,glob ROE,glob ROF}); first by sim.
 inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init CCADecapOracle.reset.
 auto.
qed.

lemma counted_original_plain_erasure
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
   -EBudgetState,-ErasureHit,-ErasureSeedLog,-ErasureSeedPool}) :
 equiv[CCAOriginalGame(CountedA(A)).run ~ CCAOriginalGame(A).run: ={glob A} ==>
 ={res,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob RawXOFStreams,glob CCADecapOracle}].
proof.
 proc; call(counted_challenge_erasure A).
 call(_: ={glob ROE,glob ROF} ==> ={res,glob ROE,glob ROF}); first by sim.
 inline ROMInit.init ROE.init ROF.init ROG.init ROH.init RawXOFStreams.init CCADecapOracle.reset.
 auto.
qed.

(* Explicit robust adversary termination and the universal initial-state
   query bound are separate premises. No ROM KeyGen termination is assumed,
   and event predT retains the original experiment's missing mass. *)
lemma capped_original_event
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
   -EBudgetState,-ErasureHit,-ErasureSeedLog,-ErasureSeedPool}) &m q0 (event:bool->bool) :
 0<=q0 =>
 (forall (H<:CCAExtendedOraclePort {-A}) (D<:CCADecapPort {-A}),
   islossless H.e =>islossless H.f =>islossless H.g =>islossless H.h =>islossless H.raw =>
   islossless D.decap =>islossless A(H,D).guess) =>
 hoare[CountedA(A,SharedCCAExtendedOracles,CCADecapOracle).guess:
 EBudgetState.requests=0 /\ EBudgetState.forwarded=0 /\ EBudgetState.limit=q0 /\
 !EBudgetState.overflow /\ EBudgetState.queries=[] ==> EBudgetState.requests<=q0] =>
 EBudgetState.requests{m}=0 =>EBudgetState.forwarded{m}=0 =>EBudgetState.limit{m}=q0 =>
 !EBudgetState.overflow{m} =>EBudgetState.queries{m}=[] =>
 Pr[CCAOriginalGame(CappedA(A)).run() @ &m:event res]=
 Pr[CCAOriginalGame(A).run() @ &m:event res].
proof.
 move=>hq all bounded hn hf hl hb hx.
 have hc:Pr[CCAOriginalGame(CountedA(A)).run() @ &m:event res]=
   Pr[CCAOriginalGame(CappedA(A)).run() @ &m:event res].
 + byequiv(count_cap_original_equiv A q0 hq all bounded)=> //; smt().
 rewrite -hc.
 byequiv(counted_original_plain_erasure A)=> //.
qed.
