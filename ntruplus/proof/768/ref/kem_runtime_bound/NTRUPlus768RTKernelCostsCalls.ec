require import AllCore Distr.
require import NTRUPlus768RTKernelCosts NTRUPlus768RTWordCodec.
require import NTRUPlus768PKEProcedures NTRUPlus768RRecPublicInverse NTRUPlus768RRecProcedures.
require import NTRUPlus768RRecLinearProcedures NTRUPlus768MRecCalls NTRUPlus768MRecDecode NTRUPlus768SecExtract.

(* Termination and almost-sure cost are derived from exact execution
   projections and existing actual-procedure losslessness. *)
lemma rt_kernel_encode_ll : islossless RTKernelEncode.run.
proof. conseq rt_kernel_encode_projection rt_word_encode_ll;smt(). qed.
lemma rt_kernel_encode_cost_correct :
 phoare[RTKernelEncode.run:true ==>0<=res.`2<=rt_kernel_encode_bound]=1%r.
proof. by conseq rt_kernel_encode_ll rt_kernel_encode_cost. qed.

lemma rt_kernel_publicinverse_ll : islossless RTKernelPublicInverse.run.
proof. conseq rt_kernel_publicinverse_projection rrec_public_inverse_lossless;smt(). qed.
lemma rt_kernel_publicinverse_cost_correct :
 phoare[RTKernelPublicInverse.run:true ==>0<=res.`2<=rt_kernel_publicinverse_bound]=1%r.
proof. by conseq rt_kernel_publicinverse_ll rt_kernel_publicinverse_cost. qed.

lemma rt_kernel_pkeencbody_ll : islossless RTKernelPKEEncBody.run.
proof. conseq rt_kernel_pkeencbody_projection pke_enc_body_lossless;smt(). qed.
lemma rt_kernel_pkeencbody_cost_correct :
 phoare[RTKernelPKEEncBody.run:true ==>0<=res.`2<=rt_kernel_pkeencbody_bound]=1%r.
proof. by conseq rt_kernel_pkeencbody_ll rt_kernel_pkeencbody_cost. qed.

lemma rt_kernel_pkeenc_ll : islossless RTKernelPKEEnc.run.
proof. conseq rt_kernel_pkeenc_projection pke_enc_lossless;smt(). qed.
lemma rt_kernel_pkeenc_cost_correct :
 phoare[RTKernelPKEEnc.run:true ==>0<=res.`2<=rt_kernel_pkeenc_bound]=1%r.
proof. by conseq rt_kernel_pkeenc_ll rt_kernel_pkeenc_cost. qed.

lemma rt_kernel_rreccore_ll : islossless RTKernelRRecCore.run.
proof. conseq rt_kernel_rreccore_projection rrec_core_lossless;smt(). qed.
lemma rt_kernel_rreccore_cost_correct :
 phoare[RTKernelRRecCore.run:true ==>0<=res.`2<=rt_kernel_rreccore_bound]=1%r.
proof. by conseq rt_kernel_rreccore_ll rt_kernel_rreccore_cost. qed.

lemma rt_kernel_rrecfinish_ll : islossless RTKernelRRecFinish.run.
proof. conseq rt_kernel_rrecfinish_projection rrec_finish_lossless;smt(). qed.
lemma rt_kernel_rrecfinish_cost_correct :
 phoare[RTKernelRRecFinish.run:true ==>0<=res.`2<=rt_kernel_rrecfinish_bound]=1%r.
proof. by conseq rt_kernel_rrecfinish_ll rt_kernel_rrecfinish_cost. qed.

lemma rt_kernel_linearusinginverse_ll : islossless RTKernelLinearUsingInverse.run.
proof. conseq rt_kernel_linearusinginverse_projection linear_rrec_using_inverse_lossless;smt(). qed.
lemma rt_kernel_linearusinginverse_cost_correct :
 phoare[RTKernelLinearUsingInverse.run:true ==>0<=res.`2<=rt_kernel_linearusinginverse_bound]=1%r.
proof. by conseq rt_kernel_linearusinginverse_ll rt_kernel_linearusinginverse_cost. qed.

lemma rt_kernel_linearrrec_ll : islossless RTKernelLinearRRec.run.
proof. conseq rt_kernel_linearrrec_projection linear_rrec_lossless;smt(). qed.
lemma rt_kernel_linearrrec_cost_correct :
 phoare[RTKernelLinearRRec.run:true ==>0<=res.`2<=rt_kernel_linearrrec_bound]=1%r.
proof. by conseq rt_kernel_linearrrec_ll rt_kernel_linearrrec_cost. qed.

lemma rt_kernel_unit_ll : islossless RTKernelUnit.run.
proof. conseq rt_kernel_unit_projection rt_word_unit_ll;smt(). qed.
lemma rt_kernel_unit_cost_correct :
 phoare[RTKernelUnit.run:true ==>0<=res.`2<=rt_kernel_unit_bound]=1%r.
proof. by conseq rt_kernel_unit_ll rt_kernel_unit_cost. qed.

lemma rt_kernel_recover_ll : islossless RTKernelRecover.run.
proof. conseq rt_kernel_recover_projection rt_word_recover_ll;smt(). qed.
lemma rt_kernel_recover_cost_correct :
 phoare[RTKernelRecover.run:true ==>0<=res.`2<=rt_kernel_recover_bound]=1%r.
proof. by conseq rt_kernel_recover_ll rt_kernel_recover_cost. qed.

lemma rt_kernel_mreccandidate_ll : islossless RTKernelMRecCandidate.run.
proof. conseq rt_kernel_mreccandidate_projection mrec_candidate_lossless;smt(). qed.
lemma rt_kernel_mreccandidate_cost_correct :
 phoare[RTKernelMRecCandidate.run:true ==>0<=res.`2<=rt_kernel_mreccandidate_bound]=1%r.
proof. by conseq rt_kernel_mreccandidate_ll rt_kernel_mreccandidate_cost. qed.

lemma rt_kernel_mrec_ll : islossless RTKernelMRec.run.
proof. conseq rt_kernel_mrec_projection mrec_lossless;smt(). qed.
lemma rt_kernel_mrec_cost_correct :
 phoare[RTKernelMRec.run:true ==>0<=res.`2<=rt_kernel_mrec_bound]=1%r.
proof. by conseq rt_kernel_mrec_ll rt_kernel_mrec_cost. qed.

lemma rt_kernel_decodecandidate_ll : islossless RTKernelDecodeCandidate.run.
proof. conseq rt_kernel_decodecandidate_projection mrec_decode_candidate_ll;smt(). qed.
lemma rt_kernel_decodecandidate_cost_correct :
 phoare[RTKernelDecodeCandidate.run:true ==>0<=res.`2<=rt_kernel_decodecandidate_bound]=1%r.
proof. by conseq rt_kernel_decodecandidate_ll rt_kernel_decodecandidate_cost. qed.

lemma rt_kernel_decode_ll : islossless RTKernelDecode.run.
proof. conseq rt_kernel_decode_projection mrec_decode_ll;smt(). qed.
lemma rt_kernel_decode_cost_correct :
 phoare[RTKernelDecode.run:true ==>0<=res.`2<=rt_kernel_decode_bound]=1%r.
proof. by conseq rt_kernel_decode_ll rt_kernel_decode_cost. qed.

lemma rt_kernel_candidate_ll : islossless RTKernelCandidate.run.
proof. conseq rt_kernel_candidate_projection sec_candidate_ll;smt(). qed.
lemma rt_kernel_candidate_cost_correct :
 phoare[RTKernelCandidate.run:true ==>0<=res.`2<=rt_kernel_candidate_bound]=1%r.
proof. by conseq rt_kernel_candidate_ll rt_kernel_candidate_cost. qed.

