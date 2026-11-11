require import AllCore Distr.
from Jasmin require import JWord.
require import Array1152.
require import NTRUPlus768INJGames NTRUPlus768INJCollision NTRUPlus768INJCollisionProof.
require import NTRUPlus768OWGames NTRUPlus768OWUniform NTRUPlus768OWUniformScale NTRUPlus768OWCodec.
require import NTRUPlus768CyclotomicFactorization NTRUPlus768SecModel NTRUPlus768SecBaseGames.

module INJUniformScaled(B:SecINJAdversary) = {
 proc run():bool = {
  var a:NTRUPoly.poly;var win:bool;
  a<@OWUniformSampler.scale3();win<@INJFieldKernel(B).guess(a);return win;
 }
}.
lemma inj_uniform_scaled_view(B<:SecINJAdversary) :
 equiv[OWNTRUUniformGame(INJNTRUReduction(B)).run ~ INJUniformScaled(B).run:
 ={glob B} ==> ={res,glob B}].
proof.
 proc;inline{1} INJNTRUReduction(B).run;inline{2} OWUniformSampler.scale3.
 wp;call(ow_poly_same (INJFieldKernel(B)));wp;rnd;auto.
qed.
lemma inj_uniform_scaled_plain(B<:SecINJAdversary) :
 equiv[INJUniformScaled(B).run ~ INJUniformTest(B).run:
 ={glob B} ==> ={res,glob B}].
proof.
 proc;call(ow_poly_same (INJFieldKernel(B))).
 outline{2} 1 ~ OWUniformSampler.sample.
 call ow_uniform_sampler_scale3;auto.
qed.
lemma inj_uniform_probability(B<:SecINJAdversary) &m :
 Pr[OWNTRUUniformGame(INJNTRUReduction(B)).run()@&m:res]=
 Pr[INJUniformTest(B).run()@&m:res].
proof.
 have h:Pr[OWNTRUUniformGame(INJNTRUReduction(B)).run()@&m:res]=
 Pr[INJUniformScaled(B).run()@&m:res] by byequiv(inj_uniform_scaled_view B)=> //.
 rewrite h;byequiv(inj_uniform_scaled_plain B)=> //.
qed.

(* Validation is performed on the actual returned byte-level collision.
   The output is an integer lift, not a modular subtraction. *)
lemma inj_checked_success a z : ow_rq_domain a=>sec_inj_win(ow_encode a)z=>
 inj_short_win a (if sec_inj_win(ow_encode a)z then inj_difference_pair z else inj_zero_pair).
proof. move=>ha hz;rewrite hz;exact(inj_encoded_collision a z ha hz). qed.

lemma inj_uniform_short(B<:SecINJAdversary) :
 equiv[INJUniformTest(B).run ~ INJShortRelationGame(INJShortSolver(B)).run:
 ={glob B} ==>res{1}=>res{2}].
proof.
 proc;inline{1} INJFieldKernel(B).guess;inline{2} INJShortSolver(B).run.
 seq 1 1:(={a,glob B} /\ ow_rq_domain a{1}).
 + rnd;auto=> /> a ha;exact(iffLR _ _ (ow_uniform_support a) ha).
 wp;sp 2 2;if;first by auto.
 + inline{1} INJKernel(B).run;wp;call(sec_inj_same B);auto.
   move=> &1 &2 [[har [hz [hal [hw [[ha hb] hd]]]]] hu].
   have hd2:ow_rq_domain a{2} by move:hd;rewrite ha.
   rewrite har hal ha /=;split;first exact hb.
   move=>_ zL zR bL bR [he hg];subst zL.
   case(sec_inj_win(ow_encode a{2})zR)=>hc.
   - move=>_;exact(inj_encoded_collision a{2} zR hd2 hc).
   by trivial.
 auto.
qed.
lemma inj_uniform_short_bound(B<:SecINJAdversary) &m :
 Pr[OWNTRUUniformGame(INJNTRUReduction(B)).run()@&m:res]<=
 Pr[INJShortRelationGame(INJShortSolver(B)).run()@&m:res].
proof.
 rewrite(inj_uniform_probability B &m).
 byequiv(inj_uniform_short B)=> //.
qed.
