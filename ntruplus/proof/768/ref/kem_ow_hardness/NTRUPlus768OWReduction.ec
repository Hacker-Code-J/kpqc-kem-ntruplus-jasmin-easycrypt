require import AllCore Distr StdOrder.
require import NTRUPlus768OWGames NTRUPlus768OWReductionReal NTRUPlus768OWReductionUniform NTRUPlus768OWKeyConditioning.
require import NTRUPlus768SecModel NTRUPlus768SecBaseGames.
import RealOrder RField.

lemma ow_weighted_hardness (alpha p realprob uniformprob solved:real) :
 0%r<alpha=>realprob=alpha*p=>uniformprob<=solved=>
 p<=(realprob-uniformprob+solved)/alpha.
proof.
 move=>ha he hu;rewrite ler_pdivl_mulr 1:ha.
 have hp:p*alpha=realprob by smt().
 rewrite hp;smt().
qed.

(* This is the signed advantage of the concrete distinguisher. Replacing
   that difference by its absolute value gives the usual DNTRU advantage.
   All probabilities are returning events; no B-losslessness premise or
   unit-conditioning of the uniform RLWE challenge is introduced. *)
lemma ow_base_hardness(B<:SecOWAdversary) &m :
 Pr[SecBaseOWGame(B).run()@&m:res]<=
 (Pr[OWNTRURealGame(OWNTRUReduction(B)).run()@&m:res]-
  Pr[OWNTRUUniformGame(OWNTRUReduction(B)).run()@&m:res]+
  Pr[OWRLWEGame(OWRLWESolver(B)).run()@&m:res])/ow_alpha_g.
proof.
 exact(ow_weighted_hardness _ _ _ _ _ ow_alpha_g_positive
  (ow_ntru_real_identity B &m) (ow_uniform_rlwe_bound B &m)).
qed.
