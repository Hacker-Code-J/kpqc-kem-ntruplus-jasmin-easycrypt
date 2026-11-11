require import AllCore Distr DProd.
from Jasmin require import JWord.
require import Array192 Array768 Array14466.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteProof.
require import NTRUPlus768KeygenCompleteRetry NTRUPlus768KeygenCompleteFinish NTRUPlus768KeygenClearProof.
require import NTRUPlus768ROMDistributions NTRUPlus768ROMOracles NTRUPlus768FreshRetryLaw.
require import NTRUPlus768StoppedKeygenModel NTRUPlus768KEMProposalContext NTRUPlus768NumericalDFRModel.

op observation_four_buffers (x:kem_keygen_observation) : four_buffers =
 ((x.`1.`1.`kg_fbuf,x.`1.`1.`kg_gbuf),(x.`2,x.`3)).
lemma observation_bad_projection x :
 four_buffers_bad(observation_four_buffers x)= !honest_no_wrap x.
proof. by rewrite /four_buffers_bad /dfr_bad /observation_four_buffers /honest_no_wrap. qed.

module AcceptedBufferSampling = {
 proc f() : W8.t Array192.t = {
  var buf; buf <$ dcond uniform192 keygen_f_accept; return buf;
 }
 proc g() : W8.t Array192.t = {
  var buf; buf <$ dcond uniform192 keygen_g_accept; return buf;
 }
}.
lemma fresh_retry_f_accepted_buffer :
 equiv[KeygenRetry(UniformSeedRNG,FreshExpand).f ~ AcceptedBufferSampling.f : true ==>
 res.`1{1}=res{2}].
proof.
 bypr(res.`1{1})(res{2}) => // &1 &2 b.
 have hl : Pr[KeygenRetry(UniformSeedRNG,FreshExpand).f() @ &1 : res.`1=b] =
   mu(dcond uniform192 keygen_f_accept)(fun x=>x=b)
   by byphoare(fresh_retry_f_buffer_law (fun x=>x=b)).
 have hr : Pr[AcceptedBufferSampling.f() @ &2 : res=b] =
   mu(dcond uniform192 keygen_f_accept)(fun x=>x=b).
 + byphoare (_: true ==> _) => //; proc; rnd; auto.
 by rewrite hl hr.
qed.
lemma fresh_retry_g_accepted_buffer :
 equiv[KeygenRetry(UniformSeedRNG,FreshExpand).g ~ AcceptedBufferSampling.g : true ==>
 res.`1{1}=res{2}].
proof.
 bypr(res.`1{1})(res{2}) => // &1 &2 b.
 have hl : Pr[KeygenRetry(UniformSeedRNG,FreshExpand).g() @ &1 : res.`1=b] =
   mu(dcond uniform192 keygen_g_accept)(fun x=>x=b)
   by byphoare(fresh_retry_g_buffer_law (fun x=>x=b)).
 have hr : Pr[AcceptedBufferSampling.g() @ &2 : res=b] =
   mu(dcond uniform192 keygen_g_accept)(fun x=>x=b).
 + byphoare (_: true ==> _) => //; proc; rnd; auto.
 by rewrite hl hr.
qed.

lemma fresh_keygen_four_buffers :
 equiv[KeygenThenUniform(FreshExpand).run ~ AcceptedFourBuffers.sample : true ==>
 observation_four_buffers res{1}=res{2}].
proof.
 proc; inline KeygenInstrumented(UniformSeedRNG,FreshExpand,SHAKEFROM).run.
 outline{2} 1 ~ AcceptedBufferSampling.f.
 outline{2} 2 ~ AcceptedBufferSampling.g.
 rewrite /observation_four_buffers.
 rnd; rnd; wp.
 call{1} keygen_clear_lossless.
 call{1}(keygen_finish_lossless SHAKEFROM ro_f_shake_ll).
 call fresh_retry_g_accepted_buffer; call fresh_retry_f_accepted_buffer; auto.
qed.

type flat_four_buffers = W8.t Array192.t * W8.t Array192.t * W8.t Array192.t * W8.t Array192.t.
op pack_four_buffers (v:flat_four_buffers) : four_buffers = ((v.`1,v.`2),(v.`3,v.`4)).
op accepted_flat_law : flat_four_buffers distr =
 dlet (dcond uniform192 keygen_f_accept) (fun f=>
 dlet (dcond uniform192 keygen_g_accept) (fun g=>
 dlet uniform192 (fun r=>dmap uniform192 (fun m=>(f,g,r,m))))).
lemma four_dlet_product ['a 'b 'c 'd]
 (da:'a distr) (db:'b distr) (dc:'c distr) (dd:'d distr) :
 dmap (dlet da (fun a=>dlet db (fun b=>dlet dc (fun c=>dmap dd (fun d=>(a,b,c,d))))))
   (fun (v:'a * 'b * 'c * 'd)=>((v.`1,v.`2),(v.`3,v.`4))) = (da `*` db) `*` (dc `*` dd).
proof.
 rewrite !dprod_dlet /dmap /(\o).
 rewrite !dlet_dlet /=.
 apply eq_dlet => // a.
 rewrite !dlet_dlet /=.
 apply eq_dlet => // b.
 rewrite dlet_unit /= !dlet_dlet /=.
 apply eq_dlet => // c.
 rewrite !dlet_dlet /=.
 apply eq_dlet => // d.
 by rewrite !dlet_unit /=.
qed.
lemma accepted_flat_lawE : dmap accepted_flat_law pack_four_buffers=accepted_four_law.
proof.
 exact(four_dlet_product (dcond uniform192 keygen_f_accept)
   (dcond uniform192 keygen_g_accept) uniform192 uniform192).
qed.
module AcceptedFourLawSampling = {
 proc sample() : four_buffers = {
  var bs; bs <$ accepted_flat_law; return pack_four_buffers bs;
 }
}.
lemma accepted_four_sampling :
 equiv[AcceptedFourBuffers.sample ~ AcceptedFourLawSampling.sample : true ==> ={res}].
proof.
 proc; rewrite /pack_four_buffers.
 rnd : *0 *0 => /=; auto => />.
 by rewrite dmap_id /accepted_flat_law.
qed.
lemma accepted_four_sample_law &m (event:four_buffers -> bool) :
 Pr[AcceptedFourBuffers.sample() @ &m : event res]=mu accepted_four_law event.
proof.
 have he : Pr[AcceptedFourLawSampling.sample() @ &m : event res]=mu accepted_four_law event.
 + rewrite -accepted_flat_lawE dmapE.
   byphoare (_: true ==> _) => //; proc; rnd; auto.
 rewrite -he; by byequiv accepted_four_sampling.
qed.
lemma fresh_keygen_no_wrap_ideal &m :
 Pr[KeygenThenUniform(FreshExpand).run() @ &m : !honest_no_wrap res]=
 mu accepted_four_law four_buffers_bad.
proof.
 rewrite -(accepted_four_sample_law &m four_buffers_bad).
 byequiv fresh_keygen_four_buffers => //.
 move=> &1 &2 <-.
 by rewrite observation_bad_projection.
qed.
