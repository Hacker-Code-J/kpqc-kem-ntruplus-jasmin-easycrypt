require import AllCore Distr FMap StdOrder.
require import NTRUPlus768ROMOracles NTRUPlus768ROMCorrectness.
require import NTRUPlus768FreshRetryLaw NTRUPlus768NumericalDFRModel.
require import NTRUPlus768KEMProposalContext NTRUPlus768KEMROMTransfer.
require import NTRUPlus768KEMIdealObservation NTRUPlus768ROMDFRObservation.
require import NTRUPlus768ConditionalBufferLaw NTRUPlus768NoiseTail.
import RealOrder RField.

(* Keep arithmetic automation over real scalars rather than expanding the
   cryptographic predicates inside probability expressions. *)
lemma ndfr_scaled_bound (x y z c:real) :
 0%r<=c => x<=c*y => y<=z => x<=c*z.
proof. smt(). qed.
lemma ndfr_sum_bound (x y a b t:real) : x<a => y<b => a+b<=t => x+y<t.
proof. smt(). qed.
lemma ndfr_good_lower (good bound:real) : 1%r-good<=bound => 1%r-bound<=good.
proof. smt(). qed.
lemma ndfr_bad_missing (good mass bound:real) :
 1%r-bound<=good => (mass-good)+(1%r-mass)<=bound.
proof. smt(). qed.
lemma ndfr_failure_transfer (failed bad mass observed_mass bound:real) :
 failed<=bad => mass=observed_mass => bad+(1%r-observed_mass)<=bound =>
 failed+(1%r-mass)<=bound.
proof. smt(). qed.
lemma ndfr_returned_bound (failed mass bound:real) :
 0%r<=failed => mass<=1%r => failed+(1%r-mass)<bound => 0%r<=failed<bound.
proof. smt(). qed.
lemma ndfr_missing_bound (failed mass bound:real) :
 0%r<=failed => mass<=1%r => failed+(1%r-mass)<bound => 0%r<=1%r-mass<bound.
proof. smt(). qed.
lemma ndfr_success_bound (failed mass bound:real) :
 failed+(1%r-mass)<bound => 1%r-bound<mass-failed.
proof. smt(). qed.

lemma conditioned_no_wrap_numerical :
 mu accepted_four_law four_buffers_bad < 1%r/(2%r^354).
proof.
 have hpos : 0%r<=64%r/25%r by smt().
 have hc:=accepted_bad_event_bound.
 have hr:=raw_four_bad_bound.
 have hn:=noise_accepted_numerical.
 have hu:=ndfr_scaled_bound _ _ _ _ hpos hc hr.
 exact(ler_lt_trans _ _ _ hu hn).
qed.

lemma numerical_error_scales :
 1%r/(2%r^354)+1%r/(2%r^239)<=1%r/(2%r^238).
proof.
 have h239 : 0%r<2%r^239 by apply expr_gt0; smt().
 have h354 : 0%r<2%r^354 by apply expr_gt0; smt().
 have hp : 2%r^239<=2%r^354 by apply ler_weexpn2l; smt().
 have hs : 1%r/(2%r^354)<=1%r/(2%r^239).
 + by rewrite !div1r (lef_pinv _ _ h239 h354).
 have h238 : 0%r<2%r^238 by apply expr_gt0; smt().
 have he : 2%r^239=2%r*(2%r^238).
 + rewrite (_:239=1+238) 1:// exprD_nneg 1,2://; ring.
 have hc : 1%r/(2%r^239)+1%r/(2%r^239)=1%r/(2%r^238).
 + rewrite he; field; smt().
 smt().
qed.
lemma numerical_total_error :
 mu accepted_four_law four_buffers_bad+keygen_observer_error < 1%r/(2%r^238).
proof.
 exact(ndfr_sum_bound _ _ _ _ _ conditioned_no_wrap_numerical
   keygen_observer_error_239 numerical_error_scales).
qed.

(* The initializer discharges the empty-E premise before the original
   unbounded KeyGen call. No losslessness premise is imposed on that call. *)
lemma initialized_uniform_good_lower :
 phoare[InitializedKeygenThenUniform(ExpandROM).run : true ==> honest_no_wrap res]
 >= (1%r-(mu accepted_four_law four_buffers_bad+keygen_observer_error)).
proof.
 have hraw : phoare[KeygenThenUniform(ExpandROM).run : ROE.m=empty ==> honest_no_wrap res]
   >= (1%r-(mu accepted_four_law four_buffers_bad+keygen_observer_error)).
 + bypr=> &m he.
   have h:=keygen_uniform_bad_or_missing &m he.
   rewrite (keygen_uniform_bad_missing_identity &m) (fresh_keygen_no_wrap_ideal &m) in h.
   exact(ndfr_good_lower _ _ h).
 proc; call hraw.
 inline ROE.init ROF.init ROG.init ROH.init; auto.
qed.

lemma initialized_uniform_bad_or_missing &m :
 Pr[InitializedKeygenThenUniform(ExpandROM).run() @ &m : !honest_no_wrap res] +
 (1%r-Pr[InitializedKeygenThenUniform(ExpandROM).run() @ &m : true]) <=
 mu accepted_four_law four_buffers_bad+keygen_observer_error.
proof.
 have hgood : 1%r-(mu accepted_four_law four_buffers_bad+keygen_observer_error) <=
   Pr[InitializedKeygenThenUniform(ExpandROM).run() @ &m : honest_no_wrap res]
   by byphoare initialized_uniform_good_lower.
 rewrite Pr[mu_not]; exact(ndfr_bad_missing _ _ _ hgood).
qed.

lemma numerical_rom_return_mass &m :
 Pr[KEMROMCorrectness(UniformKEMRNG).run() @ &m : true] =
 Pr[InitializedKeygenThenUniform(ExpandROM).run() @ &m : true].
proof.
 rewrite -(initialized_rom_return_mass &m).
 by byequiv(rom_public_projection UniformKEMRNG).
qed.

(* This is the original initialized three-caller API. Failure includes the
   returned KEM failure event and the mass of executions that do not return. *)
lemma numerical_rom_dfr_total &m :
 Pr[KEMROMCorrectness(UniformKEMRNG).run() @ &m : res] +
 (1%r-Pr[KEMROMCorrectness(UniformKEMRNG).run() @ &m : true]) <
 1%r/(2%r^238).
proof.
 have hf:=rom_failure_probability UniformKEMRNG &m.
 have hm:=numerical_rom_return_mass &m.
 have ho:=initialized_uniform_bad_or_missing &m.
 have hn:=numerical_total_error.
 rewrite (initialized_rom_bad_probability &m) in hf.
 have hu:=ndfr_failure_transfer _ _ _ _ _ hf hm ho.
 exact(ler_lt_trans _ _ _ hu hn).
qed.

lemma numerical_rom_dfr_returned &m :
 0%r<=Pr[KEMROMCorrectness(UniformKEMRNG).run() @ &m : res] < 1%r/(2%r^238).
proof.
 have h:=numerical_rom_dfr_total &m.
 have hf : 0%r<=Pr[KEMROMCorrectness(UniformKEMRNG).run() @ &m : res] by byphoare.
 have hm : Pr[KEMROMCorrectness(UniformKEMRNG).run() @ &m : true]<=1%r by byphoare.
 exact(ndfr_returned_bound _ _ _ hf hm h).
qed.

lemma numerical_rom_missing_mass &m :
 0%r<=1%r-Pr[KEMROMCorrectness(UniformKEMRNG).run() @ &m : true] < 1%r/(2%r^238).
proof.
 have h:=numerical_rom_dfr_total &m.
 have hf : 0%r<=Pr[KEMROMCorrectness(UniformKEMRNG).run() @ &m : res] by byphoare.
 have hm : Pr[KEMROMCorrectness(UniformKEMRNG).run() @ &m : true]<=1%r by byphoare.
 exact(ndfr_missing_bound _ _ _ hf hm h).
qed.

lemma numerical_rom_success_mass &m :
 1%r-1%r/(2%r^238) < Pr[KEMROMCorrectness(UniformKEMRNG).run() @ &m : !res].
proof.
 have h:=numerical_rom_dfr_total &m.
 rewrite Pr[mu_not]; exact(ndfr_success_bound _ _ _ h).
qed.
