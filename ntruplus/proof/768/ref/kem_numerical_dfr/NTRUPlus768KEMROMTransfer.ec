require import AllCore Distr FMap SDist StdOrder.
from Jasmin require import JWord.
require import Array192 Array14466.
require import NTRUPlus768ROMOracles NTRUPlus768FreshRetryLaw.
require import NTRUPlus768StoppedKeygenModel NTRUPlus768StoppedROMBound.
require import NTRUPlus768AcceptanceProbability NTRUPlus768AcceptanceROMBound NTRUPlus768AcceptanceBudget.
require import NTRUPlus768KEMProposalContext.
import RealOrder.

lemma keygen_source_empty_distance &m (event:keygen_output -> bool) :
 ROE.m{m}=empty =>
 `|Pr[KeygenSource(ExpandROM).guess(witness) @ &m : event res] -
   Pr[KeygenSource(FreshExpand).guess(witness) @ &m : event res]|
 <= keygen_observer_error.
proof.
 move=> he.
 rewrite (keygen_source_probability ExpandROM &m witness event)
   (keygen_source_probability FreshExpand &m witness event).
 have h:=keygen_rom_fresh_distance &m 256 256 0 empty event _ _ _ _ he
   fresh_f_accept_positive fresh_g_accept_positive; first 4 smt(fsize_empty).
 have hb:=certified_keygen_error_256 0.
 rewrite /keygen_observer_error; smt().
qed.

lemma keygen_source_empty_sdist &m :
 ROE.m{m}=empty =>
 sdist (mk(fun z=>Pr[KeygenSource(ExpandROM).guess(witness) @ &m : res=z]))
       (mk(fun z=>Pr[KeygenSource(FreshExpand).guess(witness) @ &m : res=z]))
 <= keygen_observer_error.
proof.
 move=> he; apply sdist_le_ub=> event.
 rewrite -(keygen_source_mu ExpandROM &m witness event)
   -(keygen_source_mu FreshExpand &m witness event).
 exact(keygen_source_empty_distance &m event he).
qed.

(* Statistical-distance contraction is valid for subdistributions.  The
   observer is the explicit stateless two-buffer procedure in Context. *)
lemma keygen_uniform_no_wrap_transfer &m :
 ROE.m{m}=empty =>
 `|Pr[KeygenThenUniform(ExpandROM).run() @ &m : honest_no_wrap res] -
   Pr[KeygenThenUniform(FreshExpand).run() @ &m : honest_no_wrap res]|
 <= keygen_observer_error.
proof.
 move=> he.
 rewrite (keygen_then_uniform_reified ExpandROM &m honest_no_wrap)
   (keygen_then_uniform_reified FreshExpand &m honest_no_wrap).
 rewrite (reified_no_wrap_sample &m) (reified_no_wrap_sample &m).
 have hc:=NoWrapDist.adv_sdist NoWrapObserver &m
   (mk(fun z=>Pr[KeygenSource(ExpandROM).guess(witness) @ &m : res=z]))
   (mk(fun z=>Pr[KeygenSource(FreshExpand).guess(witness) @ &m : res=z])).
 exact (ler_trans _ _ _ hc (keygen_source_empty_sdist &m he)).
qed.

lemma keygen_uniform_good_lower &m :
 ROE.m{m}=empty =>
 Pr[KeygenThenUniform(FreshExpand).run() @ &m : honest_no_wrap res] - keygen_observer_error <=
 Pr[KeygenThenUniform(ExpandROM).run() @ &m : honest_no_wrap res].
proof.
 move=> he; have h:=keygen_uniform_no_wrap_transfer &m he.
 rewrite ler_norml in h; smt().
qed.

lemma keygen_uniform_bad_missing_identity &m :
 Pr[KeygenThenUniform(ExpandROM).run() @ &m : !honest_no_wrap res] +
 (1%r-Pr[KeygenThenUniform(ExpandROM).run() @ &m : true]) =
 1%r-Pr[KeygenThenUniform(ExpandROM).run() @ &m : honest_no_wrap res].
proof. rewrite Pr[mu_not]; smt(). qed.

lemma keygen_uniform_bad_or_missing &m :
 ROE.m{m}=empty =>
 Pr[KeygenThenUniform(ExpandROM).run() @ &m : !honest_no_wrap res] +
 (1%r-Pr[KeygenThenUniform(ExpandROM).run() @ &m : true]) <=
 Pr[KeygenThenUniform(FreshExpand).run() @ &m : !honest_no_wrap res] + keygen_observer_error.
proof.
 move=> he.
 have hg:=keygen_uniform_good_lower &m he.
 have ht : Pr[KeygenThenUniform(FreshExpand).run() @ &m : true]=1%r
   by byphoare fresh_keygen_then_uniform_lossless.
 rewrite keygen_uniform_bad_missing_identity Pr[mu_not] ht; smt().
qed.

lemma keygen_observer_error_239 : keygen_observer_error < 1%r/(2%r^239).
proof. exact keygen_empty_cache_error_239. qed.
