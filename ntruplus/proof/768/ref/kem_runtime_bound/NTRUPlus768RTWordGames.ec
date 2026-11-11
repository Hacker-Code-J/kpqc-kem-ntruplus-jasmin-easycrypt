require import AllCore Distr.
from Jasmin require import JWord.
require import Array768.
require import NTRUPlus768PKEModel NTRUPlus768PKEKeyDistribution.
require import NTRUPlus768OWGames NTRUPlus768OWUniform NTRUPlus768OWCodec.
require import NTRUPlus768OWKeyAlgebra NTRUPlus768OWKeyConditioning NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768CyclotomicFactorization.

(* These games specify the ordinary fixed-coefficient representation of
   the same mathematical hardness challenges. Encoding/reification is
   challenger-side notation. The actual word adversary never computes
   a function-valued polynomial or enumerates an abstract polynomial. *)
module type RTWordNTRUAdversary = {proc run(h:pke_poly):bool}.
module type RTWordRLWEAdversary = {proc run(a b:pke_poly):pke_poly}.
module RTPolyNTRUAdapter(D:RTWordNTRUAdversary) : OWNTRUAdversary = {
 proc run(h:NTRUPoly.poly):bool = {
  var out:bool;out<@D.run(ow_coeff_words h);return out;
 }
}.
module RTPolyRLWEAdapter(C:RTWordRLWEAdversary) : OWRLWEAdversary = {
 proc run(a b:NTRUPoly.poly):NTRUPoly.poly = {
  var out:pke_poly;out<@C.run(ow_coeff_words a,ow_coeff_words b);return input_poly out;
 }
}.
module RTWordNTRURealGame(D:RTWordNTRUAdversary) = {
 proc run():bool = {
  var fg:NTRUPoly.poly*NTRUPoly.poly;var out:bool;
  fg<$ow_raw_fg_law;out<@D.run(ow_coeff_words(ow_ntru_key fg.`1 fg.`2));return out;
 }
}.
module RTWordNTRUUniformGame(D:RTWordNTRUAdversary) = {
 proc run():bool = {
  var h:NTRUPoly.poly;var out:bool;
  h<$ow_uniform_rq;out<@D.run(ow_coeff_words h);return out;
 }
}.
module RTWordRLWEGame(C:RTWordRLWEAdversary) = {
 proc run():bool = {
  var a,b:NTRUPoly.poly;var error,secret,out:pke_poly;
  a<$ow_uniform_rq;error<$pke_psi1;secret<$pke_psi1;
  b<-ow_rlwe_value a secret error;
  out<@C.run(ow_coeff_words a,ow_coeff_words b);
  return input_poly out=input_poly secret;
 }
}.
lemma rt_word_ntru_real_game (D<:RTWordNTRUAdversary) :
 equiv[RTWordNTRURealGame(D).run ~ OWNTRURealGame(RTPolyNTRUAdapter(D)).run:
 ={glob D} ==> ={res,glob D}].
proof.
 proc;inline{2} RTPolyNTRUAdapter(D).run;wp.
 call(_: ={arg,glob D} ==> ={res,glob D});first by proc true;auto.
 wp;rnd;auto.
qed.
lemma rt_word_ntru_uniform_game (D<:RTWordNTRUAdversary) :
 equiv[RTWordNTRUUniformGame(D).run ~ OWNTRUUniformGame(RTPolyNTRUAdapter(D)).run:
 ={glob D} ==> ={res,glob D}].
proof.
 proc;inline{2} RTPolyNTRUAdapter(D).run;wp.
 call(_: ={arg,glob D} ==> ={res,glob D});first by proc true;auto.
 wp;rnd;auto.
qed.
lemma rt_word_rlwe_game (C<:RTWordRLWEAdversary) :
 equiv[RTWordRLWEGame(C).run ~ OWRLWEGame(RTPolyRLWEAdapter(C)).run:
 ={glob C} ==> ={res,glob C}].
proof.
 proc;inline{2} RTPolyRLWEAdapter(C).run;wp.
 call(_: ={arg,glob C} ==> ={res,glob C});first by proc true;auto.
 wp;rnd;rnd;rnd;auto.
qed.
lemma rt_word_ntru_real_probability (D<:RTWordNTRUAdversary) &m :
 Pr[RTWordNTRURealGame(D).run()@&m:res]=Pr[OWNTRURealGame(RTPolyNTRUAdapter(D)).run()@&m:res].
proof. by byequiv(rt_word_ntru_real_game D)=> //. qed.
lemma rt_word_ntru_uniform_probability (D<:RTWordNTRUAdversary) &m :
 Pr[RTWordNTRUUniformGame(D).run()@&m:res]=Pr[OWNTRUUniformGame(RTPolyNTRUAdapter(D)).run()@&m:res].
proof. by byequiv(rt_word_ntru_uniform_game D)=> //. qed.
lemma rt_word_rlwe_probability (C<:RTWordRLWEAdversary) &m :
 Pr[RTWordRLWEGame(C).run()@&m:res]=Pr[OWRLWEGame(RTPolyRLWEAdapter(C)).run()@&m:res].
proof. by byequiv(rt_word_rlwe_game C)=> //. qed.
