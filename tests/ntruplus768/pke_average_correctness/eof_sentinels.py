"""Reviewed literal semantic EOF declarations for eight PKE average mains."""
SENTINELS = {
    'pke_average_correctness/NTRUPlus768PKEModel.ec': r'''

lemma __pke_average_eof_6 ct fbytes :
 pke_dec_spec ct fbytes=None <=> !(encap_key_canonical ct /\ encap_key_canonical fbytes).
proof. exact (pke_dec_none ct fbytes). qed.
''',
    'pke_average_correctness/NTRUPlus768PKEProcedures.ec': r'''

lemma __pke_average_eof_0 : islossless PKEDec.run.
proof. exact (pke_dec_lossless). qed.
''',
    'pke_average_correctness/NTRUPlus768PKEAlgebra.ec': r'''

lemma __pke_average_eof_7 w m r :
 pke_key_relation w => pke_domain m => pke_domain r =>
 pke_ring_decodes
  ((polyC(lift_int 3)*input_poly(poly_cbd1_spec w.`kg_gbuf))*input_poly r +
   input_poly m*(poly1+polyC(lift_int 3)*input_poly(poly_cbd1_spec w.`kg_fbuf)))
  (decap_candidate_spec(decoded_poly(pke_ciphertext w.`kg_pk m r))
    (decoded_poly(pke_secret_bytes w))).
proof. exact (pke_valid_key_cf_shape w m r). qed.
''',
    'pke_average_correctness/NTRUPlus768PKECallProof.ec': r'''

lemma __pke_average_eof_5 w m0 r0 :
 pke_key_relation w => pke_domain m0 => pke_domain r0 =>
 sampled_m1_no_wrap w.`kg_fbuf w.`kg_gbuf r0 m0 =>
 phoare[PKEDec.run : ct=pke_ciphertext w.`kg_pk m0 r0 /\ fbytes=pke_secret_bytes w ==>
 res=Some m0]=1%r.
proof. exact (pke_dec_no_wrap w m0 r0). qed.
''',
    'pke_average_correctness/NTRUPlus768PKEKeyDistribution.ec': r'''

lemma __pke_average_eof_1 &m workspace
 (event:(NTRUPoly.poly*NTRUPoly.poly)->bool) :
 Pr[KeygenInstrumented(UniformSeedRNG,FreshExpand,SHAKEFROM).run(workspace) @ &m :
 event(input_poly(keygen_f_pre_ntt_spec res.`1.`kg_fbuf),pke_cbd_field res.`1.`kg_gbuf)]=
 mu pke_accepted_field_pair event.
proof. exact (pke_actual_keygen_field_pair_law &m workspace event). qed.
''',
    'pke_average_correctness/NTRUPlus768PKEAverageModel.ec': r'''

lemma __pke_average_eof_2 : islossless PKEAverageObserved(FreshExpand).run.
proof. exact (pke_average_observed_fresh_lossless). qed.
''',
    'pke_average_correctness/NTRUPlus768PKEAverageCorrectness.ec': r'''

lemma __pke_average_eof_3 &m :
 Pr[PKEAverage(FreshExpand).run() @ &m:res] < 1%r/(2%r^354).
proof. exact (pke_fresh_average_correctness &m). qed.
''',
    'pke_average_correctness/NTRUPlus768PKEAverageROM.ec': r'''

lemma __pke_average_eof_4 &m :
 Pr[PKEAverageROM.run() @ &m:res] +
 (1%r-Pr[PKEAverageROM.run() @ &m:true]) < 1%r/(2%r^238).
proof. exact (pke_rom_average_total &m). qed.
''',
}
SEMANTIC_TARGETS = {
    'pke_average_correctness/NTRUPlus768PKEModel.ec': 'pke_dec_none',
    'pke_average_correctness/NTRUPlus768PKEProcedures.ec': 'pke_dec_lossless',
    'pke_average_correctness/NTRUPlus768PKEAlgebra.ec': 'pke_valid_key_cf_shape',
    'pke_average_correctness/NTRUPlus768PKECallProof.ec': 'pke_dec_no_wrap',
    'pke_average_correctness/NTRUPlus768PKEKeyDistribution.ec': 'pke_actual_keygen_field_pair_law',
    'pke_average_correctness/NTRUPlus768PKEAverageModel.ec': 'pke_average_observed_fresh_lossless',
    'pke_average_correctness/NTRUPlus768PKEAverageCorrectness.ec': 'pke_fresh_average_correctness',
    'pke_average_correctness/NTRUPlus768PKEAverageROM.ec': 'pke_rom_average_total',
}
MODULE_BINDERS = {
    'pke_average_correctness/NTRUPlus768PKEModel.ec': (),
    'pke_average_correctness/NTRUPlus768PKEProcedures.ec': (),
    'pke_average_correctness/NTRUPlus768PKEAlgebra.ec': (),
    'pke_average_correctness/NTRUPlus768PKECallProof.ec': (),
    'pke_average_correctness/NTRUPlus768PKEKeyDistribution.ec': (),
    'pke_average_correctness/NTRUPlus768PKEAverageModel.ec': (),
    'pke_average_correctness/NTRUPlus768PKEAverageCorrectness.ec': (),
    'pke_average_correctness/NTRUPlus768PKEAverageROM.ec': (),
}
NEGATIVE_PROOFS = (
    'pke_average_correctness/NTRUPlus768PKEModel.ec',
    'pke_average_correctness/NTRUPlus768PKEProcedures.ec',
    'pke_average_correctness/NTRUPlus768PKEAlgebra.ec',
    'pke_average_correctness/NTRUPlus768PKECallProof.ec',
    'pke_average_correctness/NTRUPlus768PKEKeyDistribution.ec',
    'pke_average_correctness/NTRUPlus768PKEAverageModel.ec',
    'pke_average_correctness/NTRUPlus768PKEAverageCorrectness.ec',
    'pke_average_correctness/NTRUPlus768PKEAverageROM.ec',
)
