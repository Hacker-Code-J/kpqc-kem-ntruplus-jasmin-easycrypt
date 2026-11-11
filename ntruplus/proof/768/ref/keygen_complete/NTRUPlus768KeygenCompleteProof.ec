require import AllCore Distr.
from Jasmin require import JWord.
require import Array192 Array768 Array1152 Array2336 Array14466.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteRetry NTRUPlus768KeygenCompleteFinish.
require import NTRUPlus768KeygenClear NTRUPlus768KeygenClearProof NTRUPlus768EncapCompleteHash.
require import NTRUPlus768KEMAgreementContext.

(* Proof instrumentation retains the accepted sampling buffers and inverse
   witnesses. They are private and projected away by the public API below.
   The explicit auxiliary array is not an embedding of the native C struct. *)
type keygen_witness = {
 kg_pk : W8.t Array1152.t;
 kg_sk : W8.t Array2336.t;
 kg_fbuf : W8.t Array192.t;
 kg_gbuf : W8.t Array192.t;
 kg_finv : W16.t Array768.t;
 kg_ginv : W16.t Array768.t;
 kg_h : W16.t Array768.t;
 kg_hinv : W16.t Array768.t;
}.
op [opaque] keygen_witness_valid (w:keygen_witness) = agreement_key_relation
 w.`kg_fbuf w.`kg_gbuf w.`kg_finv w.`kg_ginv w.`kg_h w.`kg_hinv w.`kg_pk w.`kg_sk.

lemma keygen_witness_build_valid fbuf gbuf finv ginv
 (r:W8.t Array1152.t * W8.t Array2336.t * W16.t Array768.t * W16.t Array768.t) :
 keygen_finish_output_valid fbuf gbuf finv ginv r =>
 keygen_witness_valid {|kg_pk=r.`1;kg_sk=r.`2;kg_fbuf=fbuf;kg_gbuf=gbuf;
 kg_finv=finv;kg_ginv=ginv;kg_h=r.`3;kg_hinv=r.`4|}.
proof. by rewrite /keygen_finish_output_valid /keygen_witness_valid /=. qed.

module KeygenInstrumented(R:KeygenSeedRNG,E:KeygenExpand,F:EncapSHAKEF) = {
 proc run(workspace:W8.t Array14466.t) : keygen_witness * W8.t Array14466.t = {
  var fbuf,gbuf:W8.t Array192.t;
  var f,finv,g,ginv,h,hinv:W16.t Array768.t;
  var pk:W8.t Array1152.t; var sk:W8.t Array2336.t;
  (fbuf,f,finv) <@ KeygenRetry(R,E).f();
  (gbuf,g,ginv) <@ KeygenRetry(R,E).g();
  (pk,sk,h,hinv) <@ KeygenFinish(F).run(f,finv,g,ginv);
  workspace <@ NTRUPlus768KeygenClear.M.jade_ntruplus_ntruplus768_amd64_ref_keygen_clear(workspace);
  return ({|kg_pk=pk;kg_sk=sk;kg_fbuf=fbuf;kg_gbuf=gbuf;kg_finv=finv;kg_ginv=ginv;kg_h=h;kg_hinv=hinv|},workspace);
 }
}.
module Keygen(R:KeygenSeedRNG,E:KeygenExpand,F:EncapSHAKEF) = {
 proc run() : W8.t Array1152.t * W8.t Array2336.t = {
  var w:keygen_witness; var cleared:W8.t Array14466.t;
  (w,cleared) <@ KeygenInstrumented(R,E,F).run(witness);
  return(w.`kg_pk,w.`kg_sk);
 }
}.
lemma keygen_instrumented_functional (R<:KeygenSeedRNG) (E<:KeygenExpand) (F<:EncapSHAKEF) :
 (forall x, hoare [F.shake : input=x ==> res=encap_shake_f_spec x]) =>
 hoare [KeygenInstrumented(R,E,F).run : true ==>
 keygen_witness_valid res.`1 /\ res.`2=keygen_clear_zero_spec].
proof.
 move=> hF; proc.
 ecall(keygen_clear_functional workspace).
 seq 2 : (keygen_f_accepted fbuf f finv /\ keygen_g_accepted gbuf g ginv).
 + call(keygen_retry_g_accepted R E); call(keygen_retry_f_accepted R E); auto.
 ecall(keygen_finish_from_accepted F fbuf gbuf f finv g ginv hF).
 auto => /> &hr hf hg result hout.
 exact(keygen_witness_build_valid fbuf{hr} gbuf{hr} finv{hr} ginv{hr} result hout).
qed.
lemma keygen_public_functional (R<:KeygenSeedRNG) (E<:KeygenExpand) (F<:EncapSHAKEF) :
 (forall x, hoare [F.shake : input=x ==> res=encap_shake_f_spec x]) =>
 hoare [Keygen(R,E,F).run : true ==>
 exists (w:keygen_witness), keygen_witness_valid w /\ res=(w.`kg_pk,w.`kg_sk)].
proof.
 move=> hF; proc; call(keygen_instrumented_functional R E F hF).
 auto => /> result hv hc; exists (result.`1); done.
qed.
lemma keygen_instrumented_lossless (R<:KeygenSeedRNG) (E<:KeygenExpand) (F<:EncapSHAKEF) :
 islossless KeygenRetry(R,E).f => islossless KeygenRetry(R,E).g => islossless F.shake =>
 islossless KeygenInstrumented(R,E,F).run.
proof.
 move=> hf hg hF; proc; call keygen_clear_lossless; call(keygen_finish_lossless F hF);
 call hg; call hf; auto.
qed.
lemma keygen_public_lossless (R<:KeygenSeedRNG) (E<:KeygenExpand) (F<:EncapSHAKEF) :
 islossless KeygenRetry(R,E).f => islossless KeygenRetry(R,E).g => islossless F.shake =>
 islossless Keygen(R,E,F).run.
proof. move=> hf hg hF; proc; call(keygen_instrumented_lossless R E F hf hg hF); auto. qed.
lemma keygen_public_correct (R<:KeygenSeedRNG) (E<:KeygenExpand) (F<:EncapSHAKEF) :
 (forall x, hoare [F.shake : input=x ==> res=encap_shake_f_spec x]) =>
 islossless KeygenRetry(R,E).f => islossless KeygenRetry(R,E).g => islossless F.shake =>
 phoare [Keygen(R,E,F).run : true ==>
 exists (w:keygen_witness), keygen_witness_valid w /\ res=(w.`kg_pk,w.`kg_sk)]=1%r.
proof.
 move=> hF hf hg hl; conseq(keygen_public_lossless R E F hf hg hl)(keygen_public_functional R E F hF).
 by move=> &hr _ result; rewrite andbb.
qed.
