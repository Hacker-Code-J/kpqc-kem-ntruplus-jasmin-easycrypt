require import AllCore Distr FMap StdOrder.
from Jasmin require import JWord.
require import Array1152 Array2336.
require import NTRUPlus768StoppedROMBound NTRUPlus768AcceptanceBudget.
require import NTRUPlus768AcceptanceProbability.
require import NTRUPlus768FreshRetryLaw NTRUPlus768ProposalSwitch NTRUPlus768StoppedKeygenModel.
require import NTRUPlus768ROMOracles NTRUPlus768ROMKeygen NTRUPlus768KeygenCompleteProof.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KEMPayloadSpec.
import RealOrder RField.

(* The lower bounds are proved for fresh uniform buffers. They discharge
   the old positivity premises; no per-call ROM acceptance premise is used. *)
lemma certified_fresh_retry_tail qf qg :
 0<=qf => 0<=qg =>
 fresh_retry_tail qf qg <= (3%r/8%r)^qf+(3%r/8%r)^qg.
proof.
 move=> hf hg.
 have pf:=fresh_f_accept_lower; have pg:=fresh_g_accept_lower.
 have rf:=fresh_f_mass_range; have rg:=fresh_g_mass_range.
 have bf:0%r<=1%r-fresh_f_accept_mass<=3%r/8%r by smt().
 have bg:0%r<=1%r-fresh_g_accept_mass<=3%r/8%r by smt().
 have ef:=ler_pexp qf (1%r-fresh_f_accept_mass) (3%r/8%r) hf bf.
 have eg:=ler_pexp qg (1%r-fresh_g_accept_mass) (3%r/8%r) hg bg.
 rewrite /fresh_retry_tail; smt().
qed.

lemma certified_keygen_rom_distance &m qf qg a m0 (event:keygen_output -> bool) :
 0<=qf => 0<=qg => 0<=a => fsize m0<=a => ROE.m{m}=m0 =>
 `|Pr[KeygenInstrumented(UniformSeedRNG,ExpandROM,SHAKEFROM).run(witness) @ &m : event res] -
   Pr[KeygenInstrumented(UniformSeedRNG,FreshExpand,SHAKEFROM).run(witness) @ &m : event res]|
 <= proposal_delta a (qf+qg)+(3%r/8%r)^qf+(3%r/8%r)^qg.
proof.
 move=> hf hg ha hm he.
 have h:=keygen_rom_fresh_distance &m qf qg a m0 event hf hg ha hm he
  fresh_f_accept_positive fresh_g_accept_positive.
 have t:=certified_fresh_retry_tail qf qg hf hg; smt().
qed.

lemma certified_keygen_public_distance &m qf qg a m0
 (event:W8.t Array1152.t * W8.t Array2336.t -> bool) :
 0<=qf => 0<=qg => 0<=a => fsize m0<=a => ROE.m{m}=m0 =>
 `|Pr[Keygen(UniformSeedRNG,ExpandROM,SHAKEFROM).run() @ &m : event res] -
   Pr[Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run() @ &m : event res]|
 <= proposal_delta a (qf+qg)+(3%r/8%r)^qf+(3%r/8%r)^qg.
proof.
 move=> hf hg ha hm he.
 have h:=keygen_public_rom_fresh_distance &m qf qg a m0 event hf hg ha hm he
  fresh_f_accept_positive fresh_g_accept_positive.
 have t:=certified_fresh_retry_tail qf qg hf hg; smt().
qed.

lemma certified_keygen_error_256 a :
 proposal_delta a (256+256)+fresh_retry_tail 256 256
 <= (512%r*a%r+130818%r)/(2%r^256).
proof.
 have hf:=fresh_f_accept_lower; have hg:=fresh_g_accept_lower.
 have rf:=fresh_f_mass_range; have rg:=fresh_g_mass_range.
 have pf:5%r/8%r<=fresh_f_accept_mass<=1%r by smt().
 have pg:5%r/8%r<=fresh_g_accept_mass<=1%r by smt().
 exact (keygen_budget_error_256 a fresh_f_accept_mass fresh_g_accept_mass pf pg).
qed.

lemma certified_keygen_public_distance_256 &m a m0
 (event:W8.t Array1152.t * W8.t Array2336.t -> bool) :
 0<=a => fsize m0<=a => ROE.m{m}=m0 =>
 `|Pr[Keygen(UniformSeedRNG,ExpandROM,SHAKEFROM).run() @ &m : event res] -
   Pr[Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run() @ &m : event res]|
 <= (512%r*a%r+130818%r)/(2%r^256).
proof.
 move=> ha hm he.
 have h:=keygen_public_rom_fresh_distance &m 256 256 a m0 event _ _ ha hm he
  fresh_f_accept_positive fresh_g_accept_positive; first 2 smt().
 have b:=certified_keygen_error_256 a; smt().
qed.

lemma certified_keygen_late_or_missing_256 &m a m0 :
 0<=a => fsize m0<=a => ROE.m{m}=m0 =>
 (Pr[CountedKeygen(UniformSeedRNG,ExpandROM).run(witness) @ &m : !counted_within 256 256 res] +
  (1%r-Pr[CountedKeygen(UniformSeedRNG,ExpandROM).run(witness) @ &m : true]))
 <= (512%r*a%r+130818%r)/(2%r^256).
proof.
 move=> ha hm he.
 have h:=rom_counted_late_or_divergent &m 256 256 a m0 _ _ ha hm he
  fresh_f_accept_positive fresh_g_accept_positive; first 2 smt().
 have b:=certified_keygen_error_256 a; smt().
qed.

lemma certified_keygen_missing_mass_256 &m a m0 :
 0<=a => fsize m0<=a => ROE.m{m}=m0 =>
 0%r <= 1%r-Pr[KeygenInstrumented(UniformSeedRNG,ExpandROM,SHAKEFROM).run(witness) @ &m : true]
 <= (512%r*a%r+130818%r)/(2%r^256).
proof.
 move=> ha hm he.
 have h:=keygen_rom_missing_mass &m 256 256 a m0 _ _ ha hm he
  fresh_f_accept_positive fresh_g_accept_positive; first 2 smt().
 have b:=certified_keygen_error_256 a; smt().
qed.

(* Empty-cache specialization retains the original public API. This is a
   KeyGen approximation error, not a decryption-failure or IND-CCA bound. *)
lemma certified_keygen_empty_cache_distance &m
 (event:W8.t Array1152.t * W8.t Array2336.t -> bool) :
 ROE.m{m}=empty =>
 `|Pr[Keygen(UniformSeedRNG,ExpandROM,SHAKEFROM).run() @ &m : event res] -
   Pr[Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run() @ &m : event res]|
 < 1%r/(2%r^239).
proof.
 move=> he.
 have h:=certified_keygen_public_distance_256 &m 0 empty event _ _ he; first 2 smt(fsize_empty).
 have b:=keygen_empty_cache_error_239; smt().
qed.
