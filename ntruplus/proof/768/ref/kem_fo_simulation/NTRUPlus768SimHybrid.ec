require import AllCore Distr Hybrid StdOrder.
from Jasmin require import JWord.
require import Array32.
require import NTRUPlus768SimModel NTRUPlus768FOSetupDistribution.
import RealOrder.

(* Static clone parameters, not section-local declared operators. The
   normalized query bound discharges Hybrid.q_ge0 without a new axiom.
   Shared callbacks must go through leaks: otherwise the standard
   Hybrid adversary/backend disjointness restriction would be violated. *)
abstract theory SimHybridBudget.
type leak_input.
type leak_output.
op budget : int.

clone import Hybrid as HB with
 type input <- sim_request,
 type output <- W8.t Array32.t option,
 type inleaks <- leak_input,
 type outleaks <- leak_output,
 type outputA <- bool,
 op q <- max 0 budget
 proof q_ge0 by smt()
 proof *.

module SimOracleOfAnswer(S:SimAnswer) : HB.Orcl = {
 proc orcl(q:sim_request) : W8.t Array32.t option = {
  var answer; answer<@S.answer(q); return answer;
 }
}.
module SimAnswerOfOracle(O:HB.Orcl) : SimAnswer = {
 proc answer(q:sim_request) : W8.t Array32.t option = {
  var result; result<@O.orcl(q); return result;
 }
}.

module type SimHybridContext(B:HB.Orclb,O:SimAnswer) = {
 proc distinguish(s:fo_setup_observation) : bool {B.leaks,O.answer}
}.
module SimHybridInput = {
 var setup:fo_setup_observation
 proc init(s:fo_setup_observation) = {setup<-s;}
}.
module SimHybridCaller(C:SimHybridContext,B:HB.Orclb,O:HB.Orcl) : HB.Adv = {
 proc main() : bool = {
  var result;
  result<@C(B,SimAnswerOfOracle(O)).distinguish(SimHybridInput.setup);
  return result;
 }
}.

(* Configured entry points expose the ordinary setup argument. The
   numerical Hybrid identity below is deliberately stated on the core
   games so every required count/losslessness premise remains explicit. *)
module SimHybridGames(C:SimHybridContext,B:HB.Orclb) = {
 proc left(s:fo_setup_observation) : bool = {
  var result; SimHybridInput.init(s);
  result<@HB.Ln(B,SimHybridCaller(C)).main(); return result;
 }
 proc right(s:fo_setup_observation) : bool = {
  var result; SimHybridInput.init(s);
  result<@HB.Rn(B,SimHybridCaller(C)).main(); return result;
 }
 proc selected_left(s:fo_setup_observation) : bool = {
  var result; SimHybridInput.init(s);
  result<@HB.HybGame(SimHybridCaller(C),B,HB.L(B)).main(); return result;
 }
 proc selected_right(s:fo_setup_observation) : bool = {
  var result; SimHybridInput.init(s);
  result<@HB.HybGame(SimHybridCaller(C),B,HB.R(B)).main(); return result;
 }
}.

lemma sim_hybrid_input_ll : islossless SimHybridInput.init.
proof. proc;auto. qed.
lemma sim_oracle_of_answer_ll (S<:SimAnswer) :
 islossless S.answer=>islossless SimOracleOfAnswer(S).orcl.
proof. move=>h;proc;call h;auto. qed.
lemma sim_answer_of_oracle_ll (O<:HB.Orcl) :
 islossless O.orcl=>islossless SimAnswerOfOracle(O).answer.
proof. move=>h;proc;call h;auto. qed.

lemma sim_hybrid_difference
 (B<:HB.Orclb {-HB.Count,-HB.HybOrcl})
 (A<:HB.AdvOrclb {-HB.Count,-HB.HybOrcl,-B}) &m :
 (forall (O<:HB.Orcl {-HB.Count,-A}),
  hoare[HB.Orcln(A(B),O).main:true ==>HB.Count.c<=max 0 budget])=>
 islossless B.leaks=>islossless B.orclL=>islossless B.orclR=>
 (forall (B0<:HB.Orclb {-A})(O<:HB.Orcl {-A}),
  islossless O.orcl=>islossless B0.leaks=>islossless B0.orclL=>islossless B0.orclR=>
  islossless A(B0,O).main)=>
 Pr[HB.Ln(B,A).main() @ &m:res]-Pr[HB.Rn(B,A).main() @ &m:res]=
 (max 0 budget)%r*(
  Pr[HB.HybGame(A,B,HB.L(B)).main() @ &m:res]-
  Pr[HB.HybGame(A,B,HB.R(B)).main() @ &m:res]).
proof.
 move=>hc hl hL hR ha.
 exact(HB.Hybrid_restr B A hc hl hL hR ha &m (fun _ _ _ b=>b)).
qed.

(* This is a generic transport lemma. The selected-query bound is a
   premise to be discharged by the concrete fresh-H simulation proof;
   it is not an assumed whole-game security error. *)
lemma sim_hybrid_distance
 (B<:HB.Orclb {-HB.Count,-HB.HybOrcl})
 (A<:HB.AdvOrclb {-HB.Count,-HB.HybOrcl,-B}) &m gamma :
 (forall (O<:HB.Orcl {-HB.Count,-A}),
  hoare[HB.Orcln(A(B),O).main:true ==>HB.Count.c<=max 0 budget])=>
 islossless B.leaks=>islossless B.orclL=>islossless B.orclR=>
 (forall (B0<:HB.Orclb {-A})(O<:HB.Orcl {-A}),
  islossless O.orcl=>islossless B0.leaks=>islossless B0.orclL=>islossless B0.orclR=>
  islossless A(B0,O).main)=>
 `|Pr[HB.HybGame(A,B,HB.L(B)).main() @ &m:res]-
   Pr[HB.HybGame(A,B,HB.R(B)).main() @ &m:res]|<=gamma=>
 `|Pr[HB.Ln(B,A).main() @ &m:res]-Pr[HB.Rn(B,A).main() @ &m:res]|
 <=(max 0 budget)%r*gamma.
proof.
 move=>hc hl hL hR ha hg.
 rewrite(sim_hybrid_difference B A &m hc hl hL hR ha) normrM.
 have hq:0%r<=(max 0 budget)%r by smt().
 rewrite(ger0_norm _ hq).
 exact(ler_wpmul2l _ hq _ _ hg).
qed.

end SimHybridBudget.
