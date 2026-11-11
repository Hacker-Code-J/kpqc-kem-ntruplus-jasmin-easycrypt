require import AllCore Distr FMap StdOrder.
from Jasmin require import JWord.
require import Array1152 Array2336.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768FreshRetryLaw.
require import NTRUPlus768ROMOracles NTRUPlus768CyclotomicFactorization.
require import NTRUPlus768AcceptanceROMBound NTRUPlus768AcceptanceBudget.
require import NTRUPlus768ProposalSwitch.
require import NTRUPlus768GenModel NTRUPlus768GenKeyProjection.
require import NTRUPlus768GenDistribution.
import RealOrder.

(* This is only the core-key marginal of the actual ROM procedure. It
   neither erases its E table nor replaces a shared-state CCA continuation. *)
lemma gen_rom_public_key_law_budget &m qf qg
 (event:NTRUPoly.poly*NTRUPoly.poly->bool) :
 0<=qf => 0<=qg => ROE.m{m}=empty =>
 `|Pr[Keygen(UniformSeedRNG,ExpandROM,SHAKEFROM).run() @ &m:
    event(gen_serialized_core res.`1 res.`2)]-mu gen_key_law event| <=
 proposal_delta 0 (qf+qg)+(3%r/8%r)^qf+(3%r/8%r)^qg.
proof.
 move=>hf hg he.
 have h:=certified_keygen_public_distance &m qf qg 0 empty
  (fun (keys:W8.t Array1152.t*W8.t Array2336.t)=>event(gen_serialized_core keys.`1 keys.`2)) hf hg _ _ he;
  first 2 smt(fsize_empty).
 rewrite (gen_fresh_public_key_law &m event) in h.
 exact h.
qed.

lemma gen_rom_public_key_law_256 &m
 (event:NTRUPoly.poly*NTRUPoly.poly->bool) :
 ROE.m{m}=empty =>
 `|Pr[Keygen(UniformSeedRNG,ExpandROM,SHAKEFROM).run() @ &m:
    event(gen_serialized_core res.`1 res.`2)]-mu gen_key_law event| <=
 130818%r/(2%r^256).
proof.
 move=>he.
 have h:=certified_keygen_public_distance_256 &m 0 empty
  (fun (keys:W8.t Array1152.t*W8.t Array2336.t)=>event(gen_serialized_core keys.`1 keys.`2)) _ _ he;
  first 2 smt(fsize_empty).
 rewrite (gen_fresh_public_key_law &m event) /= in h.
 exact h.
qed.

lemma gen_rom_public_key_law_239 &m
 (event:NTRUPoly.poly*NTRUPoly.poly->bool) :
 ROE.m{m}=empty =>
 `|Pr[Keygen(UniformSeedRNG,ExpandROM,SHAKEFROM).run() @ &m:
    event(gen_serialized_core res.`1 res.`2)]-mu gen_key_law event| <
 1%r/(2%r^239).
proof.
 move=>he; have h:=gen_rom_public_key_law_256 &m event he.
 exact(ler_lt_trans _ _ _ h keygen_empty_cache_error_239).
qed.
