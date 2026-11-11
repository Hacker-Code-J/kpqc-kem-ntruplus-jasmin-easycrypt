require import AllCore Distr DList.
from Jasmin require import JWord.
require import Array32 Array192 Array768.
require import NTRUPlus768ROMDistributions.
require import NTRUPlus768PKEModel NTRUPlus768PKEKeyDistribution.
require import NTRUPlus768PolyCBD1Algebra NTRUPlus768PolyCBD1Checked NTRUPlus768PolyCBD1CheckedProof.
require import NTRUPlus768RTFixedCBD.

(* The reference module is used only to state distribution equality.
   The concrete sampler calls the existing extracted CBD implementation. *)
module RTPsiLaw = {
 proc run():pke_poly = {
  var p:pke_poly;p<$pke_psi1;return p;
 }
 proc bytes():pke_poly = {
  var buf:W8.t Array192.t;var p:pke_poly;
  buf<$uniform192;p<-poly_cbd1_spec buf;return p;
 }
 proc key32():W8.t Array32.t = {
  var key:W8.t Array32.t;key<$uniform32;return key;
 }
}.
module RTPsiSampler = {
 proc run():pke_poly = {
  var buf:W8.t Array192.t;var scratch,p:pke_poly;
  buf<$uniform192;scratch<-witness;
  p<@NTRUPlus768PolyCBD1Checked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(scratch,buf);
  return p;
 }
 (* The second result counts nonrandom primitive operations; the third
    counts sampled bytes. The fixed lowering of uniform192 allocates and
    writes 192 cells and transfers the buffer once (385 nonrandom steps).
    Calls and returns use owned buffers, including the 3N copy rule.
    Instrumentation fields and their own arithmetic are erased. *)
 proc measure():pke_poly*int*int = {
  var buf:W8.t Array192.t;var scratch:pke_poly;var out:pke_poly*int;
  var work,random_bytes:int;
  work<-0;random_bytes<-0;
  buf<$uniform192;work<-work+385;random_bytes<-random_bytes+192;
  scratch<-witness;work<-work+769;
  out<@RTFixedCBD.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(scratch,buf);
  work<-work+out.`2+2308;
  work<-work+2305;
  return(out.`1,work,random_bytes);
 }
}.
module RTKey32Sampler = {
 proc run():W8.t Array32.t = {
  var key:W8.t Array32.t;key<$uniform32;return key;
 }
 proc measure():W8.t Array32.t*int*int = {
  var key:W8.t Array32.t;var work,random_bytes:int;
  work<-0;random_bytes<-0;
  key<$uniform32;work<-work+65;random_bytes<-random_bytes+32;
  work<-work+97;
  return(key,work,random_bytes);
 }
}.

(* Only these fixed byte-product distributions are authorized for the
   bulk-sampling price expansion. This is not a rule for arbitrary
   distributions or a unit-cost polynomial sample. *)
lemma rt_uniform192_byte_product :
 uniform192=dmap(dlist W8.dword 192)(Array192.of_list W8.zero).
proof. by rewrite /uniform192. qed.
lemma rt_uniform32_byte_product :
 uniform32=dmap(dlist W8.dword 32)(Array32.of_list W8.zero).
proof. by rewrite /uniform32. qed.
lemma rt_psi_cbd_law : dmap uniform192 poly_cbd1_spec=pke_psi1.
proof. exact pke_cbd1_uniform. qed.

lemma rt_psi_law_ll : islossless RTPsiLaw.run.
proof. proc;rnd;auto=> />;exact pke_psi1_lossless. qed.
lemma rt_psi_sampler_ll : islossless RTPsiSampler.run.
proof. proc;call poly_cbd1_lossless;wp;rnd;auto=> />;exact uniform192_ll. qed.
lemma rt_psi_sampler_bytes :
 equiv[RTPsiSampler.run ~ RTPsiLaw.bytes:true ==> ={res}].
proof.
 proc;seq 2 1:(scratch{1}=witness /\ ={buf}).
 + wp;rnd;auto.
 wp;ecall{1}(poly_cbd1_correct witness buf{2});auto.
qed.
lemma rt_psi_bytes_law :
 equiv[RTPsiLaw.bytes ~ RTPsiLaw.run:true ==> ={res}].
proof.
 proc;rndsem*{1} 0;rnd;auto=> />;by rewrite pke_cbd1_uniform.
qed.
lemma rt_psi_sampler_law :
 equiv[RTPsiSampler.run ~ RTPsiLaw.run:true ==> ={res}].
proof.
 transitivity RTPsiLaw.bytes (true ==> ={res})(true ==> ={res}).
 + smt().
 + smt().
 exact rt_psi_sampler_bytes.
 exact rt_psi_bytes_law.
qed.

lemma rt_psi_sampler_measure_projection :
 equiv[RTPsiSampler.measure ~ RTPsiSampler.run:true ==>res{1}.`1=res{2}].
proof.
 proc;wp;call rt_fixed_cbd_jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1_projection.
 wp;rnd;auto.
qed.
lemma rt_fixed_cbd_sampler_ll :
 islossless RTFixedCBD.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1.
proof.
 conseq rt_fixed_cbd_jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1_projection poly_cbd1_lossless;smt().
qed.
lemma rt_psi_sampler_measure_ll : islossless RTPsiSampler.measure.
proof. proc;wp;call rt_fixed_cbd_sampler_ll;wp;rnd;auto=> />;exact uniform192_ll. qed.
lemma rt_psi_sampler_measure_cost :
 hoare[RTPsiSampler.measure:true ==>
 0<=res.`2<=rt_fixed_cbd_bound+5767 /\ res.`3=192].
proof. proc;wp;call rt_fixed_cbd_bound_cost;wp;rnd;auto=> />;smt(). qed.
lemma rt_psi_sampler_measure_total :
 hoare[RTPsiSampler.measure:true ==>0<=res.`2+res.`3<=42636].
proof. conseq rt_psi_sampler_measure_cost=> />;rewrite /rt_fixed_cbd_bound;smt(). qed.

lemma rt_key32_sampler_ll : islossless RTKey32Sampler.run.
proof. proc;rnd;auto=> />;exact uniform32_ll. qed.
lemma rt_key32_sampler_law :
 equiv[RTKey32Sampler.run ~ RTPsiLaw.key32:true ==> ={res}].
proof. proc;rnd;auto. qed.
lemma rt_key32_sampler_measure_projection :
 equiv[RTKey32Sampler.measure ~ RTKey32Sampler.run:true ==>res{1}.`1=res{2}].
proof. proc;wp;rnd;auto. qed.
lemma rt_key32_sampler_measure_ll : islossless RTKey32Sampler.measure.
proof. proc;wp;rnd;auto=> />;exact uniform32_ll. qed.
lemma rt_key32_sampler_measure_cost :
 hoare[RTKey32Sampler.measure:true ==>res.`2=162 /\ res.`3=32 /\ res.`2+res.`3=194].
proof. proc;wp;rnd;auto. qed.
