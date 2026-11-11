require import AllCore Distr DProd.
from Jasmin require import JWord.
require import Array192 Array14466.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteRetry.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768KeygenCompleteFinish.
require import NTRUPlus768KeygenClearProof NTRUPlus768ROMOracles.
require import NTRUPlus768ROMDistributions NTRUPlus768BufferRejection NTRUPlus768FreshRetryLaw.

clone import DProd.ProdSampling as BufferProduct with
 type t1 <- W8.t Array192.t,
 type t2 <- W8.t Array192.t.

op fresh_accepted_pair_law =
 ((dcond uniform192 keygen_f_accept) `*` (dcond uniform192 keygen_g_accept)).

lemma buffer_rejection_direct_equiv :
 equiv[BufferRejection.sample ~ BufferRejection.direct :
 ={d,accept} /\ is_lossless d{1} ==> ={res}].
proof.
 bypr (res{1}) (res{2}) => /> &1 &2 buf <- <- dll.
 rewrite (buffer_rejection_probability &1 d{1} accept{1} (pred1 buf) dll).
 by byphoare (_:d=d{1} /\ accept=accept{1} ==> res=buf) => //; proc; rnd; auto.
qed.
lemma buffer_flagged_direct_equiv :
 equiv[BufferRejection.flagged ~ BufferRejection.direct :
 ={d,accept} /\ is_lossless d{1} ==> ={res}].
proof.
 transitivity BufferRejection.sample
 (={d,accept} ==> ={res}) (={d,accept} /\ is_lossless d{1} ==> ={res}) => //.
 + smt().
 + exact buffer_rejection_flagged.
 exact buffer_rejection_direct_equiv.
qed.

lemma fresh_retry_f_direct_buffer :
 equiv[KeygenRetry(UniformSeedRNG,FreshExpand).f ~ BufferRejection.direct :
 d{2}=uniform192 /\ accept{2}=keygen_f_accept ==> res.`1{1}=res{2}].
proof.
 transitivity FreshRetrySpec.f
 (true ==> ={res})
 (d{2}=uniform192 /\ accept{2}=keygen_f_accept ==> res.`1{1}=res{2}) => //.
 + exact fresh_retry_f_equiv.
 proc*; inline{1} FreshRetrySpec.f; wp; call buffer_flagged_direct_equiv; auto=> />; exact uniform192_ll.
qed.
lemma fresh_retry_g_direct_buffer :
 equiv[KeygenRetry(UniformSeedRNG,FreshExpand).g ~ BufferRejection.direct :
 d{2}=uniform192 /\ accept{2}=keygen_g_accept ==> res.`1{1}=res{2}].
proof.
 transitivity FreshRetrySpec.g
 (true ==> ={res})
 (d{2}=uniform192 /\ accept{2}=keygen_g_accept ==> res.`1{1}=res{2}) => //.
 + exact fresh_retry_g_equiv.
 proc*; inline{1} FreshRetrySpec.g; wp; call buffer_flagged_direct_equiv; auto=> />; exact uniform192_ll.
qed.

module FreshAcceptedPair = {
 proc sequential() : W8.t Array192.t * W8.t Array192.t = {
  var fbuf,gbuf;
  fbuf <@ BufferRejection.direct(uniform192,keygen_f_accept);
  gbuf <@ BufferRejection.direct(uniform192,keygen_g_accept);
  return(fbuf,gbuf);
 }
 proc product() : W8.t Array192.t * W8.t Array192.t = {
  var pair; pair <$ fresh_accepted_pair_law; return pair;
 }
}.

(* This retains the actual f-then-g retries and discharges the exact old
   Finish and workspace-clear calls using their losslessness contracts. *)
lemma fresh_keygen_pair_sequential :
 equiv[KeygenInstrumented(UniformSeedRNG,FreshExpand,SHAKEFROM).run ~ FreshAcceptedPair.sequential :
 true ==> (res.`1.`kg_fbuf,res.`1.`kg_gbuf){1}=res{2}].
proof.
 proc.
 call{1} keygen_clear_lossless.
 call{1}(keygen_finish_lossless SHAKEFROM ro_f_shake_ll).
 call fresh_retry_g_direct_buffer.
 call fresh_retry_f_direct_buffer.
 auto.
qed.

lemma fresh_pair_sequential_product :
 equiv[FreshAcceptedPair.sequential ~ FreshAcceptedPair.product : true ==> ={res}].
proof.
 transitivity BufferProduct.S.sample2
 (d1{2}=dcond uniform192 keygen_f_accept /\ d2{2}=dcond uniform192 keygen_g_accept ==> ={res})
 (d1{1}=dcond uniform192 keygen_f_accept /\ d2{1}=dcond uniform192 keygen_g_accept ==> ={res}) => //.
 + move=> *; exists (dcond uniform192 keygen_f_accept,dcond uniform192 keygen_g_accept); auto.
 + proc; inline BufferRejection.direct; auto.
 transitivity BufferProduct.S.sample
 (={d1,d2} ==> ={res})
 (d1{1}=dcond uniform192 keygen_f_accept /\ d2{1}=dcond uniform192 keygen_g_accept ==> ={res}) => //.
 + move=> &1 &2 h; exists arg{1}; auto.
 + symmetry; conseq BufferProduct.sample_sample2; smt().
 proc; auto=> />; rewrite /fresh_accepted_pair_law; auto.
qed.

(* The two accepted buffers have this product law. Each factor conditions
   its entire buffer; this is not independence of its accepted coefficients. *)
lemma fresh_keygen_buffer_pair_law
 (event:(W8.t Array192.t * W8.t Array192.t) -> bool) :
 phoare[KeygenInstrumented(UniformSeedRNG,FreshExpand,SHAKEFROM).run : true ==>
 event(res.`1.`kg_fbuf,res.`1.`kg_gbuf)] = (mu fresh_accepted_pair_law event).
proof.
 have hp: phoare[FreshAcceptedPair.product:true ==> event res] =
  (mu fresh_accepted_pair_law event).
 + proc; rnd; auto.
 have hs: phoare[FreshAcceptedPair.sequential:true ==> event res] =
  (mu fresh_accepted_pair_law event).
 + by conseq fresh_pair_sequential_product hp.
 by conseq fresh_keygen_pair_sequential hs.
qed.

lemma fresh_keygen_buffer_pair_probability &m workspace
 (event:(W8.t Array192.t * W8.t Array192.t) -> bool) :
 Pr[KeygenInstrumented(UniformSeedRNG,FreshExpand,SHAKEFROM).run(workspace) @ &m :
 event(res.`1.`kg_fbuf,res.`1.`kg_gbuf)] =
 mu (((dcond uniform192 keygen_f_accept) `*` (dcond uniform192 keygen_g_accept))) event.
proof. by byphoare (fresh_keygen_buffer_pair_law event). qed.
