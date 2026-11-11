require import AllCore Distr.
from Jasmin require import JWord.
require import Array768 Array1152.
require import NTRUPlus768CyclotomicFactorization.
require import NTRUPlus768OWGames NTRUPlus768OWUniform NTRUPlus768OWUniformScale.
require import NTRUPlus768OWCodec NTRUPlus768OWCodecProof.
require import NTRUPlus768PKEModel NTRUPlus768PKEKeyDistribution NTRUPlus768ACWC2Domains.
require import NTRUPlus768SecModel NTRUPlus768SecBaseGames NTRUPlus768CoefficientRecovery.

module OWUniformScaled(B:SecOWAdversary) = {
 proc run():bool = {
  var a:NTRUPoly.poly;var win:bool;
  a<@OWUniformSampler.scale3();win<@OWFieldKernel(B).guess(a);return win;
 }
}.
lemma ow_uniform_scaled_view(B<:SecOWAdversary) :
 equiv[OWNTRUUniformGame(OWNTRUReduction(B)).run ~ OWUniformScaled(B).run:
 ={glob B} ==> ={res,glob B}].
proof.
 proc;inline{1} OWNTRUReduction(B).run;inline{2} OWUniformSampler.scale3.
 wp;call(ow_poly_same (OWFieldKernel(B)));wp;rnd;auto.
qed.
lemma ow_uniform_scaled_plain(B<:SecOWAdversary) :
 equiv[OWUniformScaled(B).run ~ OWUniformTest(B).run:
 ={glob B} ==> ={res,glob B}].
proof.
 proc;call(ow_poly_same (OWFieldKernel(B))).
 outline{2} 1 ~ OWUniformSampler.sample.
 call ow_uniform_sampler_scale3;auto.
qed.
lemma ow_uniform_probability(B<:SecOWAdversary) &m :
 Pr[OWNTRUUniformGame(OWNTRUReduction(B)).run()@&m:res]=
 Pr[OWUniformTest(B).run()@&m:res].
proof.
 have h:Pr[OWNTRUUniformGame(OWNTRUReduction(B)).run()@&m:res]=
 Pr[OWUniformScaled(B).run()@&m:res] by byequiv(ow_uniform_scaled_view B)=> //.
 rewrite h;byequiv(ow_uniform_scaled_plain B)=> //.
qed.

(* Sampling the independent noise even on the rejected branch preserves
   its false result. This uses psi1 losslessness, not attacker termination. *)
lemma ow_uniform_source(B<:SecOWAdversary) :
 equiv[OWUniformTest(B).run ~ OWUniformSource(B).run:
 ={glob B} ==> ={res,glob B}].
proof.
 proc;inline{1} OWFieldKernel(B).guess.
 seq 1 1:(={a,glob B});first by rnd;auto.
 case(ow_unit_test a{1}).
 + rcondt{1} 3;first by auto.
   rcondt{2} 4;first by auto.
   inline{1} OWKernel(B).run.
   wp;call(sec_ow_same B);wp;rnd;rnd;auto.
 rcondf{1} 3;first by auto.
 rcondf{2} 4;first by auto.
 wp;rnd{2};rnd{2};auto=> />;smt(pke_psi1_lossless).
qed.

(* Correctly guessing the error permits public recovery of the secret
   whenever a is a unit. The nonunit branch contributes zero on the left;
   the RLWE experiment remains uniform over all of R_q. *)
lemma ow_uniform_source_rlwe(B<:SecOWAdversary) :
 equiv[OWUniformSource(B).run ~ OWRLWEGame(OWRLWESolver(B)).run:
 ={glob B} ==> res{1}=>res{2}].
proof.
 proc;inline{2} OWRLWESolver(B).run.
 seq 3 3:(={a,glob B} /\ code{1}=error{2} /\ r{1}=secret{2} /\
 ow_rq_domain a{1} /\ pke_domain code{1} /\ pke_domain r{1}).
 + rnd;rnd;rnd;auto=> />.
   move=>a ha code hc r hr;split.
   + exact(iffLR _ _ (ow_uniform_support a) ha).
   split.
   + exact(iffLR _ _ (acwc2_psi1_support code) hc).
   exact(iffLR _ _ (acwc2_psi1_support r) hr).
 case(ow_unit_test a{1}).
 + rcondt{1} 2;first by auto.
   rcondt{2} 5;first by auto.
   wp;call(sec_ow_same B);auto=> />.
   move=> &2 ha he hs hu;split.
   + apply/eq_sym;exact(ow_encode_rlwe a{2} secret{2} error{2} ha hs he).
   move=>_;exact(ow_recover_rlwe a{2} secret{2} error{2} ha hs he hu).
 rcondf{1} 2;first by auto.
 rcondf{2} 5;first by auto.
 auto.
qed.
lemma ow_uniform_rlwe_bound(B<:SecOWAdversary) &m :
 Pr[OWNTRUUniformGame(OWNTRUReduction(B)).run()@&m:res]<=
 Pr[OWRLWEGame(OWRLWESolver(B)).run()@&m:res].
proof.
 rewrite(ow_uniform_probability B &m).
 have h:Pr[OWUniformTest(B).run()@&m:res]=Pr[OWUniformSource(B).run()@&m:res]
 by byequiv(ow_uniform_source B)=> //.
 rewrite h;byequiv(ow_uniform_source_rlwe B)=> //.
qed.
