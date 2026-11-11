"""Reviewed semantic EOF references, with explicit module parameters."""

SENTINELS = {
    'NTRUPlus768KEMFailureModel.ec': r'''
lemma __failure_eof_characterization (er:encap_result) (dr:decap_result) :
  kem_failure er dr = (er.`3 <> W32.zero \/ dr.`2 <> W32.zero \/ er.`2 <> dr.`1).
proof. exact kem_failure_characterization. qed.
''',
    'NTRUPlus768KEMFailureSpec.ec': r'''
lemma __failure_eof_generated_key_bad (w:keygen_witness) coins
    (er:encap_result) (dr:decap_result) :
  keygen_witness_valid w =>
  (er.`1,er.`2,er.`3)=encap_derand_spec w.`kg_pk coins =>
  (dr.`1,dr.`2)=complete_spec er.`1 w.`kg_sk =>
  kem_failure er dr => !keygen_coins_no_wrap w coins.
proof. exact generated_key_failure_implies_bad. qed.
''',
    'NTRUPlus768KEMFailureProof.ec': r'''
lemma __failure_eof_actual_randomized_bound
    (B<:KEMRNG) (E<:KeygenExpand {-B}) (F<:EncapSHAKEF {-B,-E})
    (G<:MessageSHAKE {-B,-E,-F}) (H<:CompleteSHAKEH {-B,-E,-F,-G}) &m :
  (forall x,hoare[F.shake:input=x ==> res=encap_shake_f_spec x]) =>
  (forall x,hoare[G.shake:input=x ==> res=message_shake_spec x]) =>
  (forall x,hoare[H.shake:input=x ==> res=complete_shake_h_spec x]) =>
  Pr[KEMCorrectness(KeygenRNGPort(B),E,F,G,H,EncapRNGPort(B)).run() @ &m:res] <=
  Pr[KEMCorrectnessInstrumented(KeygenRNGPort(B),E,F,G,H,EncapRNGPort(B)).run() @ &m:res.`2].
proof. exact (correctness_failure_bound B E F G H). qed.
''',
    'NTRUPlus768KEMFailureIID.ec': r'''
lemma __failure_eof_iid_epsilon (d:W8.t Array32.t distr)
    (coinslaw:W8.t Array96.t distr) epsilon &m :
  is_lossless d => is_lossless coinslaw =>
  0%r < mu d (keygen_f_seed_accept keygen_seed_expansion) =>
  0%r < mu d (keygen_g_seed_accept keygen_seed_expansion) =>
  IIDSeedRNG.law{m}=d => DistributionRNG.law{m}=coinslaw =>
  Pr[MathematicalCorrectnessInstrumented.run() @ &m:res.`2] <= epsilon =>
  Pr[MathematicalCorrectness.run() @ &m:res] <= epsilon /\
  Pr[MathematicalCorrectness.run() @ &m:true]=1%r.
proof. exact mathematical_correctness_epsilon. qed.
''',
}

NEGATIVE_PROOFS = tuple(SENTINELS)
