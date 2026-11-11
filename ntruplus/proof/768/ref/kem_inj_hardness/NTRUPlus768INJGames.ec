require import AllCore Distr.
from Jasmin require import JWord.
require import Array1152.
require import NTRUPlus768SecModel NTRUPlus768SecBaseGames.
require import NTRUPlus768OWGames NTRUPlus768OWUniform NTRUPlus768OWCodec.
require import NTRUPlus768CyclotomicFactorization NTRUPlus768INJCollision.

module INJKernel(B:SecINJAdversary) = {
 proc run(pk:W8.t Array1152.t):bool = {
  var collision:sec_collision;
  collision<@B.run(pk);return sec_inj_win pk collision;
 }
}.
module INJFieldKernel(B:SecINJAdversary) = {
 proc guess(a:NTRUPoly.poly):bool = {
  var win;win<-false;
  if(ow_unit_test a){win<@INJKernel(B).run(ow_encode a);}
  return win;
 }
}.
module INJNTRUReduction(B:SecINJAdversary) : OWNTRUAdversary = {
 proc run(h:NTRUPoly.poly):bool = {
  var win;win<@INJFieldKernel(B).guess(ow_scale3 h);return win;
 }
}.
module INJUniformTest(B:SecINJAdversary) = {
 proc run():bool = {
  var a:NTRUPoly.poly;var win;
  a<$ow_uniform_rq;win<@INJFieldKernel(B).guess(a);return win;
 }
}.
module type INJShortAdversary = {proc run(a:NTRUPoly.poly):inj_pair}.
module INJShortSolver(B:SecINJAdversary) : INJShortAdversary = {
 proc run(a:NTRUPoly.poly):inj_pair = {
  var pk:W8.t Array1152.t;var collision:sec_collision;var result:inj_pair;
  result<-inj_zero_pair;
  if(ow_unit_test a){
   pk<-ow_encode a;collision<@B.run(pk);
   if(sec_inj_win pk collision){result<-inj_difference_pair collision;}
  }
  return result;
 }
}.
(* This experiment is explicit: a is uniform in all R_q, and the row is
   [a,1]. It does not assert an iid Ring-SIS sampling law or hardness axiom. *)
module INJShortRelationGame(C:INJShortAdversary) = {
 proc run():bool = {
  var a:NTRUPoly.poly;var out:inj_pair;
  a<$ow_uniform_rq;out<@C.run(a);return inj_short_win a out;
 }
}.
lemma inj_field_reject_nonunit(B<:SecINJAdversary) :
 phoare[INJFieldKernel(B).guess:!ow_unit_test a ==>!res]=1%r.
proof. proc;rcondf 2;auto. qed.
