"""Both RR directions retain their distinct quantifiers and public call endpoint."""
BASE='ntruplus/proof/768/ref/acwc2_contracts/'
MODEL=BASE+'NTRUPlus768RRecModel.ec'
ALGEBRA=BASE+'NTRUPlus768RRecAlgebra.ec'
CALLS=BASE+'NTRUPlus768RRecCallProof.ec'
CODEC=BASE+'NTRUPlus768RRecCodec.ec'
RULES=(
 (MODEL,'specification performs the explicit public consistency check',r'op rrec_verify_spec (pk:W8.t Array1152.t) (m:pke_poly) (ct:W8.t Array1152.t) (candidate:pke_poly option) : pke_poly option = if candidate=None then None else if pke_enc_spec pk m (oget candidate)=Some ct then candidate else None.'),
 (MODEL,'reverse soundness covers arbitrary key/message/ciphertext on success',r'lemma rrec_spec_sound pk m ct r : rrec_spec pk m ct=Some r => pke_domain m /\ pke_domain r /\ pke_enc_spec pk m r=Some ct.'),
 (ALGEBRA,'forward recovery for all trit randomness and messages needs no no-wrap',r'lemma rrec_keyed_forward w m r : pke_key_relation w => pke_domain m => pke_domain r => rrec_spec w.`kg_pk m (pke_ciphertext w.`kg_pk m r)=Some r.'),
 (CALLS,'actual reverse contract is not conditioned on an honest ciphertext',r'lemma rrec_sound_correct pk0 m0 ct0 : phoare[RRec.run : pk=pk0 /\ m=m0 /\ ct=ct0 ==> forall r, res=Some r => pke_domain m0 /\ pke_domain r /\ pke_enc_spec pk0 m0 r=Some ct0]=1%r.'),
 (CALLS,'actual re-encryption call returns the accepted ciphertext',r'lemma rrec_reencrypt_correct pk0 m0 ct0 r0 : rrec_spec pk0 m0 ct0=Some r0 => phoare[PKEEnc.run : pk=pk0 /\ m=m0 /\ r=r0 ==>res=Some ct0]=1%r.'),
 (CALLS,'actual forward contract keeps its public RR interface and no-wrap-free premises',r'lemma rrec_keyed_forward_correct w m0 r0 : pke_key_relation w => pke_domain m0 => pke_domain r0 => phoare[RRec.run : pk=w.`kg_pk /\ m=m0 /\ ct=pke_ciphertext w.`kg_pk m0 r0 ==> res=Some r0]=1%r.'),
 (CODEC,'G input serializes the transform rather than the coefficient array',r'op rr_G_input (r:pke_poly) : W8.t Array1152.t = NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec(pke_rhat r).'),
 (CODEC,'G encoding injection keeps both trit-domain premises',r'lemma rr_G_input_injective r s : pke_domain r => pke_domain s => rr_G_input r=rr_G_input s => r=s.'),
)
MUTATIONS=(
 ('RR-specification-omits-candidate-consistency',MODEL,'if pke_enc_spec pk m (oget candidate)=Some ct then candidate else None','candidate'),
 ('RR-reverse-soundness-weakened-to-honest-ciphertexts',MODEL,'lemma rrec_spec_sound pk m ct r : rrec_spec pk m ct=Some r =>','lemma rrec_spec_sound pk m ct r : ct=pke_ciphertext pk m r => rrec_spec pk m ct=Some r =>'),
 ('RR-forward-adds-forbidden-no-wrap-premise',ALGEBRA,'lemma rrec_keyed_forward w m r : pke_key_relation w =>','lemma rrec_keyed_forward w m r : sampled_m1_no_wrap w.`kg_fbuf w.`kg_gbuf r m => pke_key_relation w =>'),
 ('actual-RR-soundness-assumes-generated-key',CALLS,'lemma rrec_sound_correct pk0 m0 ct0 :',r'lemma rrec_sound_correct pk0 m0 ct0 : exists w,pke_key_relation w /\ pk0=w.`kg_pk =>'),
 ('actual-RR-reencrypt-contract-substitutes-reference',CALLS,r'phoare[PKEEnc.run : pk=pk0 /\ m=m0 /\ r=r0 ==>res=Some ct0]',r'phoare[ReferenceEnc.run : pk=pk0 /\ m=m0 /\ r=r0 ==>res=Some ct0]'),
 ('actual-RR-forward-adds-forbidden-no-wrap-premise',CALLS,'lemma rrec_keyed_forward_correct w m0 r0 : pke_key_relation w =>','lemma rrec_keyed_forward_correct w m0 r0 : sampled_m1_no_wrap w.`kg_fbuf w.`kg_gbuf r0 m0 => pke_key_relation w =>'),
 ('G-input-serializes-coefficients-instead-of-NTT',CODEC,'NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec(pke_rhat r).','NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec(r).'),
 ('G-input-injectivity-omits-second-domain',CODEC,'lemma rr_G_input_injective r s : pke_domain r => pke_domain s =>','lemma rr_G_input_injective r s : pke_domain r =>'),
)
