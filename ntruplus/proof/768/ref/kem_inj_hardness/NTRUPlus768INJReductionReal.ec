require import AllCore Distr SDist RealSeries StdOrder.
from Jasmin require import JWord.
require import Array1152.
require import NTRUPlus768INJGames NTRUPlus768OWGames NTRUPlus768OWReductionReal.
require import NTRUPlus768OWCodec NTRUPlus768OWKeyAlgebra NTRUPlus768OWKeyLaw NTRUPlus768OWKeyConditioning.
require import NTRUPlus768GenModel NTRUPlus768GenDistribution NTRUPlus768PKEKeyDistribution.
require import NTRUPlus768CyclotomicFactorization NTRUPlus768SecModel NTRUPlus768SecBaseGames.
import RealOrder RField.

module INJPairKernel(B:SecINJAdversary) = {
 proc guess(fg:NTRUPoly.poly*NTRUPoly.poly):bool = {
  var win;win<@INJKernel(B).run(ow_encode(gen_public_key fg.`1 fg.`2));return win;
 }
}.
module INJGuardedPairKernel(B:SecINJAdversary) = {
 proc guess(fg:NTRUPoly.poly*NTRUPoly.poly):bool = {
  var win;win<-false;
  if(ow_g_unit fg){win<@INJPairKernel(B).guess(fg);}
  return win;
 }
}.
module INJAcceptedByteGame(B:SecINJAdversary) = {
 proc run():bool = {
  var pk:W8.t Array1152.t;var win:bool;
  pk<@OWKeySample.run();win<@INJKernel(B).run(pk);return win;
 }
}.
lemma inj_real_pair_kernel(B<:SecINJAdversary) :
 equiv[INJNTRUReduction(B).run ~ INJGuardedPairKernel(B).guess:
 h{1}=ow_ntru_key fg{2}.`1 fg{2}.`2 /\ fg{2} \in ow_raw_fg_law /\ ={glob B} ==>
 ={res,glob B}].
proof.
 proc;inline{1} INJFieldKernel(B).guess;wp;sp 2 1;if.
 + auto=> &1 &2 [hw [ha [hw0 [hh [hs hb]]]]].
   by rewrite ha hh (ow_raw_guard fg{2} hs).
 + inline{2} INJPairKernel(B).guess;wp;call(ow_kernel_same (INJKernel(B))).
   auto=> /> &2 _ _.
   by rewrite ow_ntru_scale3.
 auto.
qed.
lemma inj_real_pair_probability(B<:SecINJAdversary) &m :
 Pr[OWNTRURealGame(INJNTRUReduction(B)).run()@&m:res]=
 Pr[OWPairDist.Sample(INJGuardedPairKernel(B)).main(ow_raw_fg_law)@&m:res].
proof.
 byequiv(_:d{2}=ow_raw_fg_law /\ ={glob B} ==> ={res})=> //.
 proc;call(inj_real_pair_kernel B);rnd;auto.
qed.

lemma inj_base_accepted_bytes(B<:SecINJAdversary) &m :
 Pr[SecBaseINJGame(B).run()@&m:res]=Pr[INJAcceptedByteGame(B).run()@&m:res].
proof.
 byequiv(_: ={glob B} ==> ={res})=> //.
 proc;inline{2} INJKernel(B).run;wp;call(sec_inj_same B);wp;
 call ow_base_keygen_sample;auto.
qed.
lemma inj_accepted_pair_probability(B<:SecINJAdversary) &m :
 Pr[INJAcceptedByteGame(B).run()@&m:res]=
 Pr[OWPairDist.Sample(INJPairKernel(B)).main(gen_fg_law)@&m:res].
proof.
 byequiv(_:d{2}=gen_fg_law /\ ={glob B} ==> ={res})=> //.
 proc;inline{1} OWKeySample.run;inline{2} INJPairKernel(B).guess;wp;
 call(ow_kernel_same (INJKernel(B)));wp;rnd;auto.
qed.

lemma inj_guarded_pair_probability(B<:SecINJAdversary) &m fg :
 Pr[INJGuardedPairKernel(B).guess(fg)@&m:res]=
 if ow_g_unit fg then Pr[INJPairKernel(B).guess(fg)@&m:res] else 0%r.
proof.
 case(ow_g_unit fg)=>hu.
 + byequiv(_:arg{1}=fg /\ arg{2}=fg /\ ={glob B} ==> ={res})=> //.
   proc;rcondt{1} 2;first by auto.
   inline{1} INJPairKernel(B).guess;wp;call(ow_kernel_same (INJKernel(B)));auto.
 byphoare(_:arg=fg ==>res)=> //.
 hoare;proc;rcondf 2;auto.
qed.

lemma inj_ntru_real_identity(B<:SecINJAdversary) &m :
 Pr[OWNTRURealGame(INJNTRUReduction(B)).run()@&m:res]=
 ow_alpha_g*Pr[SecBaseINJGame(B).run()@&m:res].
proof.
 rewrite(inj_real_pair_probability B &m)(inj_base_accepted_bytes B &m)
 (inj_accepted_pair_probability B &m)
 (ow_pair_expectation (INJGuardedPairKernel(B)) &m ow_raw_fg_law)
 (ow_pair_expectation (INJPairKernel(B)) &m gen_fg_law)
 (ow_conditioned_expectation(fun fg=>Pr[INJPairKernel(B).guess(fg)@&m:res])).
 apply eq_exp=>fg _;exact(inj_guarded_pair_probability B &m fg).
qed.
