require import AllCore Distr DProd Dexcepted.
require import NTRUPlus768CyclotomicFactorization NTRUPlus768PKEKeyDistribution.
require import NTRUPlus768GenModel NTRUPlus768GenDistribution.

(* This standard rejection sampler has polynomial-valued proposals. Its
   exact law also covers zero acceptance mass; positivity is used for LL. *)
clone import Dexcepted.WhileSampling as GenPolynomialSampling with
 type input <- NTRUPoly.poly distr,
 type t <- NTRUPoly.poly,
 op dt <- (fun d=>d).
op gen_polynomial_reject (accept:NTRUPoly.poly->bool)
 (_:NTRUPoly.poly distr) (p:NTRUPoly.poly) = !accept p.

module GenPolynomialRejection = {
 proc sample(d:NTRUPoly.poly distr,accept:NTRUPoly.poly->bool) : NTRUPoly.poly = {
  var p:NTRUPoly.poly;
  p <$ d;
  while(!accept p){p <$ d;}
  return p;
 }
 proc direct(d:NTRUPoly.poly distr,accept:NTRUPoly.poly->bool) : NTRUPoly.poly = {
  var p:NTRUPoly.poly; p <$ dcond d accept; return p;
 }
}.
lemma gen_excepted_conditional d accept :
 d \ gen_polynomial_reject accept d=dcond d accept.
proof.
 rewrite /gen_polynomial_reject /(\) /dcond; congr; congr.
 by apply fun_ext=>p; rewrite /predC.
qed.
lemma gen_polynomial_rejection_library :
 equiv[GenPolynomialRejection.sample ~ GenPolynomialSampling.SampleW.sample :
 d{1}=i{2} /\ test{2}=gen_polynomial_reject accept{1} ==> ={res}].
proof.
 proc; inline GenPolynomialSampling.SampleWi.sample.
 wp; while(p{1}=r0{2} /\ d{1}=i0{2} /\ test0{2}=gen_polynomial_reject accept{1});
 auto=> />; rewrite /gen_polynomial_reject; smt().
qed.
lemma gen_polynomial_rejection_probability &m d accept (event:NTRUPoly.poly->bool) :
 is_lossless d =>
 Pr[GenPolynomialRejection.sample(d,accept) @ &m:event res]=mu(dcond d accept)event.
proof.
 move=>hd; rewrite -gen_excepted_conditional.
 rewrite -(@GenPolynomialSampling.pr_sampleW &m d (gen_polynomial_reject accept) event hd).
 by byequiv gen_polynomial_rejection_library.
qed.
lemma gen_polynomial_rejection_direct :
 equiv[GenPolynomialRejection.sample ~ GenPolynomialRejection.direct :
 ={d,accept} /\ is_lossless d{1} ==> ={res}].
proof.
 bypr(res{1})(res{2})=> /> &1 &2 p <- <- hd.
 rewrite(gen_polynomial_rejection_probability &1 d{1} accept{1} (pred1 p) hd).
 by byphoare(_:d=d{1} /\ accept=accept{1} ==>res=p)=> //; proc; rnd; auto.
qed.

(* Figure 18: the first loop tests 1+3*f0, the second tests unscaled g.
   The public relation is mathematical quotient-ring division, not NTT code. *)
module Figure18Gen = {
 proc sample_fg() : NTRUPoly.poly*NTRUPoly.poly = {
  var f0,f,g:NTRUPoly.poly;
  f0 <@ GenPolynomialRejection.sample(pke_field_psi1,gen_f0_accept);
  f <- gen_shape_f f0;
  g <@ GenPolynomialRejection.sample(pke_field_psi1,pke_rq_unit);
  return(f,g);
 }
 proc run() : NTRUPoly.poly*NTRUPoly.poly = {
  var fg,key:NTRUPoly.poly*NTRUPoly.poly;
  fg <@ sample_fg();
  key <- gen_key_from_fg fg;
  return key;
 }
}.
module Figure18Conditional = {
 proc sample_fg() : NTRUPoly.poly*NTRUPoly.poly = {
  var f0,f,g:NTRUPoly.poly;
  f0 <$ dcond pke_field_psi1 gen_f0_accept;
  f <- gen_shape_f f0;
  g <$ dcond pke_field_psi1 pke_rq_unit;
  return(f,g);
 }
}.
module Figure18Law = {
 proc sample_fg() : NTRUPoly.poly*NTRUPoly.poly = {
  var fg:NTRUPoly.poly*NTRUPoly.poly;
  fg <$ gen_fg_law; return fg;
 }
 proc run() : NTRUPoly.poly*NTRUPoly.poly = {
  var key:NTRUPoly.poly*NTRUPoly.poly;
  key <$ gen_key_law; return key;
 }
}.

lemma figure18_repeat_conditional :
 equiv[Figure18Gen.sample_fg ~ Figure18Conditional.sample_fg:true ==> ={res}].
proof.
 proc.
 outline{2} 1 ~ GenPolynomialRejection.direct.
 outline{2} 3 ~ GenPolynomialRejection.direct.
 call gen_polynomial_rejection_direct; wp; call gen_polynomial_rejection_direct.
 auto=> />; exact gen_field_psi_lossless.
qed.

lemma gen_fg_law_dlet : gen_fg_law=
 dlet (dcond pke_field_psi1 gen_f0_accept) (fun f0=>
  dmap (dcond pke_field_psi1 pke_rq_unit) (fun g=>(gen_shape_f f0,g))).
proof.
 rewrite /gen_fg_law /gen_f_law /gen_f0_law /gen_g_law dprod_dlet /dmap dlet_dlet.
 apply eq_dlet=> // f0.
 by rewrite dlet_unit /(\o).
qed.

lemma figure18_conditional_product :
 equiv[Figure18Conditional.sample_fg ~ Figure18Law.sample_fg:true ==> ={res}].
proof.
 proc; rnd : *0 *0 => /=; auto=> />.
 rewrite dmap_id gen_fg_law_dlet.
 auto=> />.
 by move=>[f g] hs.
qed.
lemma figure18_fg_law :
 equiv[Figure18Gen.sample_fg ~ Figure18Law.sample_fg:true ==> ={res}].
proof.
 transitivity Figure18Conditional.sample_fg (true ==> ={res}) (true ==> ={res})=> //.
 + exact figure18_repeat_conditional.
 exact figure18_conditional_product.
qed.
lemma figure18_gen_law :
 equiv[Figure18Gen.run ~ Figure18Law.run:true ==> ={res}].
proof.
 proc; transitivity{1} {fg <@ Figure18Law.sample_fg(); key <- gen_key_from_fg fg;}
  (true ==> ={key}) (true ==> ={key})=> //.
 + wp; call figure18_fg_law; auto.
 inline Figure18Law.sample_fg; rnd : *0 *0 => /=; auto=> />.
 by rewrite dmap_id /gen_key_law.
qed.
lemma figure18_gen_probability &m (event:NTRUPoly.poly*NTRUPoly.poly->bool) :
 Pr[Figure18Gen.run() @ &m:event res]=mu gen_key_law event.
proof.
 have he:Pr[Figure18Law.run() @ &m:event res]=mu gen_key_law event
  by byphoare(_:true ==>event res)=> //; proc; rnd; auto.
 rewrite -he; by byequiv figure18_gen_law.
qed.
lemma figure18_gen_lossless : islossless Figure18Gen.run.
proof.
 have hl:islossless Figure18Law.run by proc; rnd; auto=> />; exact gen_key_lossless.
 conseq figure18_gen_law hl; smt().
qed.

require import NTRUPlus768KeygenCompleteProof NTRUPlus768FreshRetryLaw.
require import NTRUPlus768ROMOracles NTRUPlus768CCASetupState NTRUPlus768GenKeyProjection.

(* Literal public-API to Figure-18 probability identities. The observation
   is the core extracted from returned bytes; this forgets no table inside
   an adversarial experiment and claims no ROM equality. *)
lemma figure18_fresh_public_probability &m (event:NTRUPoly.poly*NTRUPoly.poly->bool) :
 Pr[Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run() @ &m:
  event(gen_serialized_core res.`1 res.`2)]=Pr[Figure18Gen.run() @ &m:event res].
proof. by rewrite gen_fresh_public_key_law figure18_gen_probability. qed.
lemma figure18_programmed_public_probability &m (event:NTRUPoly.poly*NTRUPoly.poly->bool) :
 Pr[Keygen(UniformSeedRNG,ProgrammedFreshExpand,SHAKEFROM).run() @ &m:
  event(gen_serialized_core res.`1 res.`2)]=Pr[Figure18Gen.run() @ &m:event res].
proof. by rewrite gen_programmed_public_key_law figure18_gen_probability. qed.

