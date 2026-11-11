require import AllCore Distr FMap SDist StdOrder.
from Jasmin require import JWord.
require import NTRUPlus768ROMOracles NTRUPlus768CCAGame.
require import NTRUPlus768CCADecapOracle NTRUPlus768RawXOFStreams.
require import NTRUPlus768CCASetupState NTRUPlus768CCASetupDistribution.
require import NTRUPlus768CCASetupGame NTRUPlus768CCASetupBound.
require import NTRUPlus768FreshRetryLaw NTRUPlus768ProposalSwitch.
require import NTRUPlus768AcceptanceROMBound NTRUPlus768AcceptanceBudget.
import RealOrder.

lemma cca_setup_source_sdist &m qf qg :
 0<=qf => 0<=qg =>
 sdist (mk(fun z=>Pr[JointSetupSource(ExpandROM).guess(witness) @ &m:res=z]))
       (mk(fun z=>Pr[JointSetupSource(ProgrammedFreshExpand).guess(witness) @ &m:res=z])) <=
 proposal_delta 0 (qf+qg)+fresh_retry_tail qf qg.
proof.
 move=>hf hg; apply(cca_setup_event_sdist ExpandROM ProgrammedFreshExpand &m)=>event.
 exact(cca_setup_source_distance &m qf qg event hf hg).
qed.

lemma cca_setup_source_sdist_256 &m :
 sdist (mk(fun z=>Pr[JointSetupSource(ExpandROM).guess(witness) @ &m:res=z]))
       (mk(fun z=>Pr[JointSetupSource(ProgrammedFreshExpand).guess(witness) @ &m:res=z])) <=
 130818%r/(2%r^256).
proof.
 apply(cca_setup_event_sdist ExpandROM ProgrammedFreshExpand &m)=>event.
 exact(cca_setup_source_distance_256 &m event).
qed.

(* The observer may diverge. SDist contraction is for subdistribution
   kernels and therefore requires no attacker losslessness hypothesis. *)
lemma cca_original_programmed_setup_distance
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams})
 &m qf qg :
 0<=qf => 0<=qg =>
 `|Pr[CCAOriginalGame(A).run() @ &m:res]-
   Pr[CCAProgrammedFreshGame(A).run() @ &m:res]| <=
 proposal_delta 0 (qf+qg)+fresh_retry_tail qf qg.
proof.
 move=>hf hg.
 have hs:=cca_setup_source_sdist &m qf qg hf hg.
 have hc:=CCASetupObserverDist.adv_sdist (CCASetupObserver(A)) &m
  (mk(fun z=>Pr[JointSetupSource(ExpandROM).guess(witness) @ &m:res=z]))
  (mk(fun z=>Pr[JointSetupSource(ProgrammedFreshExpand).guess(witness) @ &m:res=z])).
 rewrite -(cca_setup_game_reified_rom A &m)
  -(cca_setup_game_reified_programmed A &m)
  -(cca_original_setup_probability A &m) in hc.
 exact(ler_trans _ _ _ hc hs).
qed.

lemma cca_original_programmed_setup_distance_256
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams}) &m :
 `|Pr[CCAOriginalGame(A).run() @ &m:res]-
   Pr[CCAProgrammedFreshGame(A).run() @ &m:res]| <= 130818%r/(2%r^256).
proof.
 have h:=cca_original_programmed_setup_distance A &m 256 256 _ _; first 2 smt().
 have hb:=certified_keygen_error_256 0; rewrite /= in hb.
 exact(ler_trans _ _ _ h hb).
qed.

lemma cca_original_programmed_setup_distance_239
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams}) &m :
 `|Pr[CCAOriginalGame(A).run() @ &m:res]-
   Pr[CCAProgrammedFreshGame(A).run() @ &m:res]| < 1%r/(2%r^239).
proof.
 have h:=cca_original_programmed_setup_distance_256 A &m.
 have hb:=keygen_empty_cache_error_239.
 exact(ler_lt_trans _ _ _ h hb).
qed.
