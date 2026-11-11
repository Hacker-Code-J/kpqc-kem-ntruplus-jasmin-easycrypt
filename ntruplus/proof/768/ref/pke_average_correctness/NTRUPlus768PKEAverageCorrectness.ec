require import AllCore Distr FMap StdOrder.
from Jasmin require import JWord.
require import Array192 Array768 Array1152.
require import NTRUPlus768ROMOracles NTRUPlus768ROMKeygen.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteProof.
require import NTRUPlus768FreshRetryLaw NTRUPlus768PolyCBD1Algebra.
require import NTRUPlus768PolyCBD1CheckedProof NTRUPlus768ValidKeyM1Recovery.
require import NTRUPlus768KEMProposalContext NTRUPlus768KEMIdealObservation.
require import NTRUPlus768NumericalDFRModel NTRUPlus768NumericalDFR.
require import NTRUPlus768PKEAverageModel NTRUPlus768PKEModel.
require import NTRUPlus768PKEAlgebra NTRUPlus768PKECallProof.
import RealOrder RField.

lemma pke_average_public_projection (E<:KeygenExpand {-ROF}) :
 equiv[PKEAverage(E).run ~ PKEAverageObserved(E).run :
  ={glob E,glob ROF} ==> res{1}=res.`1{2} /\ ={glob E,glob ROF}].
proof.
 proc; call (_: ={x} ==> ={res}); first by sim.
 call (_: ={glob E,glob ROF} ==> ={res,glob E,glob ROF}); first by sim.
 auto.
qed.

lemma pke_average_bad_projection (E<:KeygenExpand {-ROF}) :
 equiv[PKEAverageObserved(E).run ~ KeygenThenUniform(E).run :
  ={glob E,glob ROF} ==> res.`2{1}= !honest_no_wrap res{2} /\ ={glob E,glob ROF}].
proof.
 proc*; inline{1} PKEAverageObserved(E).run; wp.
 call{1} pke_average_trial_lossless.
 call (_: ={glob E,glob ROF} ==> ={res,glob E,glob ROF}); first by sim.
 auto.
qed.

lemma pke_average_failure_probability (E<:KeygenExpand {-ROF}) &m :
 Pr[PKEAverage(E).run() @ &m:res]=
 Pr[PKEAverageObserved(E).run() @ &m:res.`1].
proof. by byequiv(pke_average_public_projection E). qed.

lemma pke_average_bad_probability (E<:KeygenExpand {-ROF}) &m :
 Pr[PKEAverageObserved(E).run() @ &m:res.`2]=
 Pr[KeygenThenUniform(E).run() @ &m:!honest_no_wrap res].
proof. byequiv(pke_average_bad_projection E) => //; smt(). qed.

lemma pke_average_return_probability (E<:KeygenExpand {-ROF}) &m :
 Pr[PKEAverage(E).run() @ &m:true]=Pr[KeygenThenUniform(E).run() @ &m:true].
proof.
 have he:Pr[PKEAverage(E).run() @ &m:true]=Pr[PKEAverageObserved(E).run() @ &m:true]
   by byequiv(pke_average_public_projection E).
 rewrite he; by byequiv(pke_average_bad_projection E).
qed.

(* The observer retains the accepted whole buffers and independent fresh
   CBD message/randomness, rather than assuming iid accepted coefficients. *)
lemma pke_fresh_bad_probability &m :
 Pr[PKEAverageObserved(FreshExpand).run() @ &m:res.`2]=
 mu accepted_four_law four_buffers_bad.
proof.
 rewrite (pke_average_bad_probability FreshExpand &m).
 exact(fresh_keygen_no_wrap_ideal &m).
qed.

lemma pke_average_trial_correct (x0:kem_keygen_observation) :
 pke_key_relation x0.`1.`1 => honest_no_wrap x0 =>
 hoare[PKEAverageTrial.run : x=x0 ==> !res].
proof.
 move=>hk hn.
 have hm:=pke_domain_cbd x0.`3.
 have hr:=pke_domain_cbd x0.`2.
 have [he hd]:=pke_no_wrap_correct x0.`1.`1
   (poly_cbd1_spec x0.`3) (poly_cbd1_spec x0.`2) hk hm hr hn.
 proc; rcondt 5.
 + wp; call(pke_enc_functional x0.`1.`1.`kg_pk
       (poly_cbd1_spec x0.`3) (poly_cbd1_spec x0.`2) hm hr).
   call(poly_cbd1_functional witness x0.`3).
   call(poly_cbd1_functional witness x0.`2).
   auto=> />; by rewrite he.
 wp; call(pke_dec_functional
   (pke_ciphertext x0.`1.`1.`kg_pk (poly_cbd1_spec x0.`3) (poly_cbd1_spec x0.`2))
   (pke_secret_bytes x0.`1.`1)).
 wp; call(pke_enc_functional x0.`1.`1.`kg_pk
   (poly_cbd1_spec x0.`3) (poly_cbd1_spec x0.`2) hm hr).
 call(poly_cbd1_functional witness x0.`3).
 call(poly_cbd1_functional witness x0.`2).
 auto=> />; by rewrite ?he /= ?hd.
qed.

lemma pke_average_trial_failure (x0:kem_keygen_observation) :
 hoare[PKEAverageTrial.run : x=x0 /\ pke_key_relation x0.`1.`1 ==>
 res => !honest_no_wrap x0].
proof.
 case(pke_key_relation x0.`1.`1)=>hk; last first.
 + conseq (_:false ==>true)=> //; smt().
 case(honest_no_wrap x0)=>hn; last first.
 + conseq (_:true ==>true)=> //; smt().
 conseq(pke_average_trial_correct x0 hk hn)=> //; smt().
qed.

lemma pke_average_failure_implies_bad (E<:KeygenExpand {-ROF}) :
 hoare[PKEAverageObserved(E).run:true ==> res.`1 => res.`2].
proof.
 proc; ecall(pke_average_trial_failure x).
 call(keygen_then_uniform_rom_valid E).
 auto=> />; smt(pke_key_from_rom).
qed.

lemma pke_average_failure_bound (E<:KeygenExpand {-ROF}) &m :
 Pr[PKEAverage(E).run() @ &m:res] <=
 Pr[KeygenThenUniform(E).run() @ &m:!honest_no_wrap res].
proof.
 rewrite(pke_average_failure_probability E &m).
 have hz:Pr[PKEAverageObserved(E).run() @ &m:res.`1 /\ !res.`2]=0%r.
 + byphoare (_:true ==> res.`1 /\ !res.`2)=> //; hoare.
   conseq(pke_average_failure_implies_bad E)=> />; smt().
 rewrite Pr[mu_split res.`2] hz /= -(pke_average_bad_probability E &m).
 by byequiv (_: ={glob E,glob ROF} ==> ={res})=> //; sim.
qed.

(* This is average correctness for the actual acceptance-conditioned
   fresh implementation key law and independent CBD message/randomness. *)
lemma pke_fresh_average_correctness &m :
 Pr[PKEAverage(FreshExpand).run() @ &m:res] < 1%r/(2%r^354).
proof.
 have hb:=pke_average_failure_bound FreshExpand &m.
 rewrite(fresh_keygen_no_wrap_ideal &m) in hb.
 exact(ler_lt_trans _ _ _ hb conditioned_no_wrap_numerical).
qed.
