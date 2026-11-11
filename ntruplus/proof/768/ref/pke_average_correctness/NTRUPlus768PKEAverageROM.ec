require import AllCore Distr FMap StdOrder.
require import NTRUPlus768ROMOracles NTRUPlus768FreshRetryLaw.
require import NTRUPlus768NumericalDFRModel NTRUPlus768NumericalDFR.
require import NTRUPlus768KEMProposalContext NTRUPlus768KEMIdealObservation.
require import NTRUPlus768KEMROMTransfer.
require import NTRUPlus768PKEAverageModel NTRUPlus768PKEAverageCorrectness.
import RealOrder RField.

(* This extension uses the stateless no-wrap observer transfer. It does
   not assert losslessness of unrestricted cached-ROM KeyGen. *)
lemma pke_rom_raw_bad_missing_identity &m :
 Pr[PKEAverage(ExpandROM).run() @ &m:res] +
 (1%r-Pr[PKEAverage(ExpandROM).run() @ &m:true]) =
 1%r-Pr[PKEAverage(ExpandROM).run() @ &m:!res].
proof. rewrite Pr[mu_not]; ring. qed.

lemma pke_rom_raw_bad_or_missing &m :
 ROE.m{m}=empty =>
 Pr[PKEAverage(ExpandROM).run() @ &m:res] +
 (1%r-Pr[PKEAverage(ExpandROM).run() @ &m:true]) <=
 mu accepted_four_law four_buffers_bad+keygen_observer_error.
proof.
 move=>he.
 have hf:=pke_average_failure_bound ExpandROM &m.
 have hm:=pke_average_return_probability ExpandROM &m.
 have ho:=keygen_uniform_bad_or_missing &m he.
 rewrite(fresh_keygen_no_wrap_ideal &m) in ho.
 exact(ndfr_failure_transfer _ _ _ _ _ hf hm ho).
qed.

lemma pke_rom_good_lower :
 phoare[PKEAverageROM.run:true ==> !res] >=
 (1%r-(mu accepted_four_law four_buffers_bad+keygen_observer_error)).
proof.
 have hraw:phoare[PKEAverage(ExpandROM).run:ROE.m=empty ==> !res] >=
   (1%r-(mu accepted_four_law four_buffers_bad+keygen_observer_error)).
 + bypr=> &m he.
   have h:=pke_rom_raw_bad_or_missing &m he.
   rewrite(pke_rom_raw_bad_missing_identity &m) in h.
   exact(ndfr_good_lower _ _ h).
 proc; call hraw; inline ROE.init ROF.init; auto.
qed.

(* Failure means a returned encryption/decryption failure or missing
   return mass, with fresh independent CBD message and randomness. *)
lemma pke_rom_average_total &m :
 Pr[PKEAverageROM.run() @ &m:res] +
 (1%r-Pr[PKEAverageROM.run() @ &m:true]) < 1%r/(2%r^238).
proof.
 have hgood:1%r-(mu accepted_four_law four_buffers_bad+keygen_observer_error) <=
   Pr[PKEAverageROM.run() @ &m:!res] by byphoare pke_rom_good_lower.
 have hi:Pr[PKEAverageROM.run() @ &m:res] +
   (1%r-Pr[PKEAverageROM.run() @ &m:true]) =
   1%r-Pr[PKEAverageROM.run() @ &m:!res] by rewrite Pr[mu_not]; ring.
 have hb:=ndfr_bad_missing _ 1%r _ hgood.
 move:hb; rewrite /= => hb.
 rewrite hi; exact(ler_lt_trans _ _ _ hb numerical_total_error).
qed.
