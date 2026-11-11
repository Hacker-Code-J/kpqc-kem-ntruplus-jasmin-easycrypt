require import AllCore Distr.
require import NTRUPlus768INJGames NTRUPlus768INJReductionReal NTRUPlus768INJReductionUniform.
require import NTRUPlus768OWGames NTRUPlus768OWReduction NTRUPlus768OWKeyConditioning.
require import NTRUPlus768SecModel NTRUPlus768SecBaseGames.

(* The final target is the explicit uniform systematic short-relation
   experiment. No claim that it has an iid Ring-SIS law, or that its
   hardness is established by the collision bridge, is made here. *)
lemma inj_base_hardness(B<:SecINJAdversary) &m :
 Pr[SecBaseINJGame(B).run()@&m:res]<=
 (Pr[OWNTRURealGame(INJNTRUReduction(B)).run()@&m:res]-
  Pr[OWNTRUUniformGame(INJNTRUReduction(B)).run()@&m:res]+
  Pr[INJShortRelationGame(INJShortSolver(B)).run()@&m:res])/ow_alpha_g.
proof.
 exact(ow_weighted_hardness _ _ _ _ _ ow_alpha_g_positive
  (inj_ntru_real_identity B &m)(inj_uniform_short_bound B &m)).
qed.
