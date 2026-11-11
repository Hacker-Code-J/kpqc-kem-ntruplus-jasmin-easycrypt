"""Full serialization and public versus stored inverse comparison contracts."""
BASE='ntruplus/proof/768/ref/linear_rrec/'
SERIALIZATION=BASE+'NTRUPlus768RRecSerialization.ec'
ALGEBRA=BASE+'NTRUPlus768RRecLinearAlgebra.ec'
RULES=(
 (SERIALIZATION,'arithmetic unpack/repack preserves the entire byte array including noncanonical encodings',r'lemma rrec_reencode_all ct : NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec(decoded_poly ct)=ct.'),
 (SERIALIZATION,'injectivity concerns the arithmetic decoder rather than the rejecting option decoder',r'lemma rrec_decoded_poly_injective ct1 ct2 : decoded_poly ct1=decoded_poly ct2 =>ct1=ct2.'),
 (ALGEBRA,'full byte equality implies mod-q equality under both serializer range preconditions',r'lemma rrec_serialized_equal_mod_q a b : NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange a => NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange b => NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec a=NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec b => poly_coeff_eq_mod_q a b.'),
 (ALGEBRA,'public and stored inverses coincide as canonical arrays for a valid generated key',r'lemma rrec_generated_public_inverse_stored w : pke_key_relation w => rrec_public_inverse(decoded_poly w.`kg_pk)= Some(decoded_poly(decap_hbytes(complete_sk_poly w.`kg_sk))).'),
 (ALGEBRA,'full terminal comparison uses NTT randomness and the same decoded message on both sides',r'lemma rrec_r2_serialized_iff pk m ct r : encap_key_canonical pk => rrec_public_inverse(decoded_poly pk)<>None => encap_key_canonical ct => pke_domain m => pke_domain r => (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec (decap_r2_spec (decoded_poly ct) m (oget(rrec_public_inverse(decoded_poly pk))))= NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec(pke_rhat r) <=> pke_enc_spec pk m r=Some ct).'),
 (ALGEBRA,'linear candidate soundness requires only the existing guards and candidate domain',r'lemma rrec_linear_candidate_reencrypt pk m ct : encap_key_canonical pk => rrec_public_inverse(decoded_poly pk)<>None => encap_key_canonical ct => pke_domain m => pke_domain(rrec_candidate (decoded_poly ct) m (oget(rrec_public_inverse(decoded_poly pk)))) => pke_enc_spec pk m (rrec_candidate (decoded_poly ct) m (oget(rrec_public_inverse(decoded_poly pk))))=Some ct.'),
)
MUTATIONS=(
 ('raw-decoder-injectivity-falsely-applied-to-rejecting-decoder',SERIALIZATION,'decoded_poly ct1=decoded_poly ct2 =>ct1=ct2.','checked_decode ct1=checked_decode ct2 =>ct1=ct2.'),
 ('serializer-equality-uses-only-a-prefix',ALGEBRA,'NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec a=NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec b => poly_coeff_eq_mod_q a b.','(NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec a).[0]=(NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec b).[0] => poly_coeff_eq_mod_q a b.'),
 ('serializer-equality-falsely-claims-word-array-equality',ALGEBRA,'NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec a=NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec b => poly_coeff_eq_mod_q a b.','NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec a=NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec b => a=b.'),
 ('stored-public-inverse-agreement-drops-valid-key-condition',ALGEBRA,'lemma rrec_generated_public_inverse_stored w : pke_key_relation w =>','lemma rrec_generated_public_inverse_stored w :'),
 ('native-comparison-serializes-raw-randomness-instead-of-its-NTT',ALGEBRA,'NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec(pke_rhat r) <=>','NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec r <=>'),
 ('same-message-comparison-changes-the-reencryption-message',ALGEBRA,'pke_enc_spec pk m r=Some ct).','pke_enc_spec pk witness r=Some ct).'),
 ('candidate-soundness-assumes-honest-ciphertext',ALGEBRA,'lemma rrec_linear_candidate_reencrypt pk m ct :',r'lemma rrec_linear_candidate_reencrypt pk m ct : (exists r,pke_domain r /\ ct=pke_ciphertext pk m r) =>'),
 ('candidate-soundness-assumes-the-reencryption-result',ALGEBRA,'lemma rrec_linear_candidate_reencrypt pk m ct :','lemma rrec_linear_candidate_reencrypt pk m ct : pke_enc_spec pk m (rrec_candidate (decoded_poly ct) m (oget(rrec_public_inverse(decoded_poly pk))))=Some ct =>'),
)
