require import AllCore Distr DProd SDist RealSeries StdOrder.
from Jasmin require import JWord.
require import Array1152.
require import NTRUPlus768OWGames NTRUPlus768OWUniform NTRUPlus768OWUniformScale.
require import NTRUPlus768OWCodec NTRUPlus768OWCodecProof NTRUPlus768OWKeyAlgebra NTRUPlus768OWKeyLaw NTRUPlus768OWKeyConditioning.
require import NTRUPlus768GenModel NTRUPlus768GenDistribution NTRUPlus768PKEKeyDistribution.
require import NTRUPlus768CyclotomicFactorization NTRUPlus768SecModel NTRUPlus768SecBaseGames.
import RealOrder RField.

clone SDist.Dist as OWPairDist with type a <- NTRUPoly.poly*NTRUPoly.poly proof *.
module OWPairKernel(B:SecOWAdversary) = {
 proc guess(fg:NTRUPoly.poly*NTRUPoly.poly):bool = {
  var win;win<@OWKernel(B).run(ow_encode(gen_public_key fg.`1 fg.`2));return win;
 }
}.
module OWGuardedPairKernel(B:SecOWAdversary) = {
 proc guess(fg:NTRUPoly.poly*NTRUPoly.poly):bool = {
  var win;win<-false;
  if(ow_g_unit fg){win<@OWPairKernel(B).guess(fg);}
  return win;
 }
}.
module OWAcceptedByteGame(B:SecOWAdversary) = {
 proc run():bool = {
  var pk:W8.t Array1152.t;var win:bool;
  pk<@OWKeySample.run();win<@OWKernel(B).run(pk);return win;
 }
}.
lemma ow_pair_same(K<:OWPairDist.GenDist.Distinguisher):
 equiv[K.guess ~ K.guess: ={arg,glob K} ==> ={res,glob K}].
proof. proc true;auto. qed.

lemma ow_raw_support fg : fg \in ow_raw_fg_law <=>
 fg.`1 \in gen_f_law /\ fg.`2 \in pke_field_psi1.
proof. by rewrite /ow_raw_fg_law supp_dprod. qed.
lemma ow_raw_public_domain fg : fg \in ow_raw_fg_law=>ow_rq_domain(gen_public_key fg.`1 fg.`2).
proof.
 rewrite ow_raw_support;move=>[hf hg].
 have hd:=ow_ntru_degree fg.`1 fg.`2 hf hg.
 have hs:=ow_scale3_domain (ow_ntru_key fg.`1 fg.`2) hd.
 by move:hs;rewrite ow_ntru_scale3.
qed.
lemma ow_raw_guard fg : fg \in ow_raw_fg_law=>
 ow_unit_test(ow_scale3(ow_ntru_key fg.`1 fg.`2))=ow_g_unit fg.
proof.
 move=>hs;have [hf hg]:=iffLR _ _ (ow_raw_support fg) hs.
 rewrite ow_ntru_scale3 (ow_unit_test_iff _ (ow_raw_public_domain fg hs)) /ow_g_unit.
 apply eq_iff;exact(ow_gen_public_unit fg.`1 fg.`2 hf hg).
qed.

lemma ow_real_pair_kernel(B<:SecOWAdversary) :
 equiv[OWNTRUReduction(B).run ~ OWGuardedPairKernel(B).guess:
 h{1}=ow_ntru_key fg{2}.`1 fg{2}.`2 /\ fg{2} \in ow_raw_fg_law /\ ={glob B} ==>
 ={res,glob B}].
proof.
 proc;inline{1} OWFieldKernel(B).guess;wp;sp 2 1;if.
 + auto=> &1 &2 [hw [ha [hw0 [hh [hs hb]]]]].
   by rewrite ha hh (ow_raw_guard fg{2} hs).
 + inline{2} OWPairKernel(B).guess;wp;call(ow_kernel_same (OWKernel(B))).
   auto=> /> &2 _ _.
   by rewrite ow_ntru_scale3.
 auto.
qed.
lemma ow_real_pair_probability(B<:SecOWAdversary) &m :
 Pr[OWNTRURealGame(OWNTRUReduction(B)).run()@&m:res]=
 Pr[OWPairDist.Sample(OWGuardedPairKernel(B)).main(ow_raw_fg_law)@&m:res].
proof.
 byequiv(_:d{2}=ow_raw_fg_law /\ ={glob B} ==> ={res})=> //.
 proc;call(ow_real_pair_kernel B);rnd;auto.
qed.

lemma ow_base_accepted_bytes(B<:SecOWAdversary) &m :
 Pr[SecBaseOWGame(B).run()@&m:res]=Pr[OWAcceptedByteGame(B).run()@&m:res].
proof.
 byequiv(_: ={glob B} ==> ={res})=> //.
 proc;inline{2} OWKernel(B).run;wp;call(sec_ow_same B);wp;rnd;rnd;wp;
 call ow_base_keygen_sample;auto.
qed.
lemma ow_accepted_pair_probability(B<:SecOWAdversary) &m :
 Pr[OWAcceptedByteGame(B).run()@&m:res]=
 Pr[OWPairDist.Sample(OWPairKernel(B)).main(gen_fg_law)@&m:res].
proof.
 byequiv(_:d{2}=gen_fg_law /\ ={glob B} ==> ={res})=> //.
 proc;inline{1} OWKeySample.run;inline{2} OWPairKernel(B).guess;wp;
 call(ow_kernel_same (OWKernel(B)));wp;rnd;auto.
qed.

(* The library law represents returning probabilities, so divergence of
   B is retained in the kernel rather than normalized away. *)
lemma ow_pair_expectation(K<:OWPairDist.GenDist.Distinguisher) &m d :
 Pr[OWPairDist.Sample(K).main(d)@&m:res]=
 E d(fun fg=>Pr[K.guess(fg)@&m:res]).
proof.
 rewrite(OWPairDist.Sample_dlet K &m d) dletE /E.
 apply eq_sum=>fg /=.
 have hv:mu1(mk(fun b=>Pr[K.guess(fg)@&m:res=b]))true=Pr[K.guess(fg)@&m:res].
 + rewrite -(OWPairDist.GenDist.adv_mu1 K &m true fg).
   by rewrite Pr[mu_eq];smt().
 rewrite hv;ring.
qed.
lemma ow_guarded_pair_probability(B<:SecOWAdversary) &m fg :
 Pr[OWGuardedPairKernel(B).guess(fg)@&m:res]=
 if ow_g_unit fg then Pr[OWPairKernel(B).guess(fg)@&m:res] else 0%r.
proof.
 case(ow_g_unit fg)=>hu.
 + byequiv(_:arg{1}=fg /\ arg{2}=fg /\ ={glob B} ==> ={res})=> //.
   proc;rcondt{1} 2;first by auto.
   inline{1} OWPairKernel(B).guess;wp;call(ow_kernel_same (OWKernel(B)));auto.
 byphoare(_:arg=fg ==>res)=> //.
 hoare;proc;rcondf 2;auto.
qed.

lemma ow_ntru_real_identity(B<:SecOWAdversary) &m :
 Pr[OWNTRURealGame(OWNTRUReduction(B)).run()@&m:res]=
 ow_alpha_g*Pr[SecBaseOWGame(B).run()@&m:res].
proof.
 rewrite(ow_real_pair_probability B &m)(ow_base_accepted_bytes B &m)
 (ow_accepted_pair_probability B &m)
 (ow_pair_expectation (OWGuardedPairKernel(B)) &m ow_raw_fg_law)
 (ow_pair_expectation (OWPairKernel(B)) &m gen_fg_law)
 (ow_conditioned_expectation(fun fg=>Pr[OWPairKernel(B).guess(fg)@&m:res])).
 apply eq_exp=>fg _;exact(ow_guarded_pair_probability B &m fg).
qed.
