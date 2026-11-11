require import AllCore List Distr.
from Jasmin require import JWord.
require import Array32 Array192 Array14466.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteRetry.
require import NTRUPlus768KeygenCompleteFinish NTRUPlus768KeygenCompleteProof.
require import NTRUPlus768KeygenRetryLaw NTRUPlus768KeygenClearProof.
require import NTRUPlus768EncapCompleteHash Keccak1600_Spec EclibExtra.

op keygen_seed_expansion (seed:W8.t Array32.t) : W8.t Array192.t =
  Array192.of_list W8.zero (SHAKE256 (Array32.to_list seed) 192).
module MathematicalKeygenExpand = {
  proc shake(seed:W8.t Array32.t) : W8.t Array192.t = {
    var output; output <@ Keccak1600Bytes.shake256(Array32.to_list seed,192);
    return Array192.of_list W8.zero output;
  }
}.
lemma mathematical_keygen_expand_functional seed0 :
  hoare [MathematicalKeygenExpand.shake : seed=seed0 ==> res=keygen_seed_expansion seed0].
proof. proc; ecall(SHAKE256_h (Array32.to_list seed0) 192); by auto => />. qed.
lemma mathematical_keygen_expand_lossless : islossless MathematicalKeygenExpand.shake.
proof. proc; call SHAKE256_ll; by auto. qed.

(* The proposal law is fixed through both loops. Positivity is required
   separately for f and g under that law and the fixed expansion function;
   neither SHAKE nor lossless random-byte generation implies it alone. *)
lemma keygen_iid_instrumented_terminates
    (E<:KeygenExpand {-IIDSeedRNG}) (F<:EncapSHAKEF {-IIDSeedRNG}) d expand0 :
  (forall x, hoare [E.shake:seed=x ==> res=expand0 x]) =>
  islossless E.shake => islossless F.shake => is_lossless d =>
  0%r < mu d (keygen_f_seed_accept expand0) =>
  0%r < mu d (keygen_g_seed_accept expand0) =>
  phoare [KeygenInstrumented(IIDSeedRNG,E,F).run : IIDSeedRNG.law=d ==> true]=1%r.
proof.
  move=> he el fl dll pf pg; proc.
  call keygen_clear_lossless; call(keygen_finish_lossless F fl).
  call(keygen_retry_g_terminates E d expand0 he el dll pg).
  call(keygen_retry_f_terminates E d expand0 he el dll pf).
  by auto.
qed.

lemma keygen_iid_public_terminates
    (E<:KeygenExpand {-IIDSeedRNG}) (F<:EncapSHAKEF {-IIDSeedRNG}) d expand0 :
  (forall x, hoare [E.shake:seed=x ==> res=expand0 x]) =>
  islossless E.shake => islossless F.shake => is_lossless d =>
  0%r < mu d (keygen_f_seed_accept expand0) =>
  0%r < mu d (keygen_g_seed_accept expand0) =>
  phoare [Keygen(IIDSeedRNG,E,F).run : IIDSeedRNG.law=d ==> true]=1%r.
proof.
  move=> he el fl dll pf pg; proc.
  call(keygen_iid_instrumented_terminates E F d expand0 he el fl dll pf pg); by auto.
qed.

lemma keygen_iid_instrumented_correct
    (E<:KeygenExpand {-IIDSeedRNG}) (F<:EncapSHAKEF {-IIDSeedRNG}) d expand0 :
  (forall x, hoare [E.shake:seed=x ==> res=expand0 x]) =>
  (forall x, hoare [F.shake:input=x ==> res=encap_shake_f_spec x]) =>
  islossless E.shake => islossless F.shake => is_lossless d =>
  0%r < mu d (keygen_f_seed_accept expand0) =>
  0%r < mu d (keygen_g_seed_accept expand0) =>
  phoare [KeygenInstrumented(IIDSeedRNG,E,F).run : IIDSeedRNG.law=d ==>
    keygen_witness_valid res.`1 /\ res.`2=keygen_clear_zero_spec]=1%r.
proof.
  move=> he hf el fl dll pf pg.
  by conseq (keygen_iid_instrumented_terminates E F d expand0 he el fl dll pf pg)
    (keygen_instrumented_functional IIDSeedRNG E F hf).
qed.

lemma keygen_iid_public_correct
    (E<:KeygenExpand {-IIDSeedRNG}) (F<:EncapSHAKEF {-IIDSeedRNG}) d expand0 :
  (forall x, hoare [E.shake:seed=x ==> res=expand0 x]) =>
  (forall x, hoare [F.shake:input=x ==> res=encap_shake_f_spec x]) =>
  islossless E.shake => islossless F.shake => is_lossless d =>
  0%r < mu d (keygen_f_seed_accept expand0) =>
  0%r < mu d (keygen_g_seed_accept expand0) =>
  phoare [Keygen(IIDSeedRNG,E,F).run : IIDSeedRNG.law=d ==>
    exists (w:keygen_witness), keygen_witness_valid w /\ res=(w.`kg_pk,w.`kg_sk)]=1%r.
proof.
  move=> he hf el fl dll pf pg.
  conseq (keygen_iid_public_terminates E F d expand0 he el fl dll pf pg)
    (keygen_public_functional IIDSeedRNG E F hf).
  by move=> &hr _ result; rewrite andbb.
qed.

lemma keygen_mathematical_iid_correct d :
  is_lossless d =>
  0%r < mu d (keygen_f_seed_accept keygen_seed_expansion) =>
  0%r < mu d (keygen_g_seed_accept keygen_seed_expansion) =>
  phoare [Keygen(IIDSeedRNG,MathematicalKeygenExpand,MathematicalSHAKEF).run : IIDSeedRNG.law=d ==>
    exists (w:keygen_witness), keygen_witness_valid w /\ res=(w.`kg_pk,w.`kg_sk)]=1%r.
proof.
  move=> dll pf pg.
  exact(keygen_iid_public_correct MathematicalKeygenExpand MathematicalSHAKEF d keygen_seed_expansion
    mathematical_keygen_expand_functional encap_mathematical_f_functional
    mathematical_keygen_expand_lossless encap_mathematical_f_lossless dll pf pg).
qed.
