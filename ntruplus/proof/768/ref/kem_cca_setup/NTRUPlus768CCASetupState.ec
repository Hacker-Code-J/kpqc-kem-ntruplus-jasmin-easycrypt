require import AllCore Distr FMap.
from Jasmin require import JWord.
require import Array32 Array192 Array1152 Array14466.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions.
require import NTRUPlus768FreshRetryLaw NTRUPlus768StoppedKeygenModel.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteProof.

type cca_e_table = (W8.t Array32.t,W8.t Array192.t) fmap.
type cca_f_table = (W8.t Array1152.t,W8.t Array32.t) fmap.
type cca_setup_state = keygen_output * cca_e_table * cca_f_table.

(* Analysis-only fresh expansion. Repeated seeds receive fresh answers and
   overwrite E during setup; this discrepancy belongs to the collision event.
   Subsequent adversarial queries use the unchanged lazy shared oracles. *)
module ProgrammedFreshExpand = {
 proc shake(seed:W8.t Array32.t) : W8.t Array192.t = {
  var y:W8.t Array192.t;
  y <$ uniform192;
  ROE.m.[seed] <- y;
  return y;
 }
}.

module JointSetup(E:KeygenExpand) = {
 proc run(workspace:W8.t Array14466.t) : cca_setup_state = {
  var out:keygen_output;
  out <@ KeygenInstrumented(UniformSeedRNG,E,SHAKEFROM).run(workspace);
  return (out,ROE.m,ROF.m);
 }
}.

module JointSetupSource(E:KeygenExpand) = {
 proc guess(workspace:W8.t Array14466.t) : cca_setup_state = {
  var out:cca_setup_state;
  ROE.init(); ROF.init();
  out <@ JointSetup(E).run(workspace);
  return out;
 }
}.

lemma programmed_fresh_expand_ll : islossless ProgrammedFreshExpand.shake.
proof. proc; auto=> />; exact uniform192_ll. qed.

lemma programmed_fresh_expand_value seed0 :
 hoare[ProgrammedFreshExpand.shake : seed=seed0 ==>
  ROE.m.[seed0]=Some res].
proof. proc; auto=> />; smt(get_set_sameE). qed.

lemma programmed_fresh_expand_projection :
 equiv[ProgrammedFreshExpand.shake ~ FreshExpand.shake : ={seed} ==> ={res}].
proof. proc; auto. qed.
