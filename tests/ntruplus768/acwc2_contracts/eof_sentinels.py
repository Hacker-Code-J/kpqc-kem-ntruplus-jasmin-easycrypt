"""Reviewed literal semantic EOF declarations for the eleven RR/SOTP mains."""
SENTINELS = {
    'acwc2_contracts/NTRUPlus768RRecWordChecks.ec': r'''

lemma __acwc2_eof_0 a0 : hoare[RRecTrit.check : ap=a0 ==>res=pke_domain a0].
proof. exact (rrec_trit_functional a0). qed.
''',
    'acwc2_contracts/NTRUPlus768RRecPublicInverse.ec': r'''

lemma __acwc2_eof_1 hp : in_qrange768 hp =>
 rrec_public_inverse hp<>None =>
 poly_basemul_qring hp (oget(rrec_public_inverse hp)) ntt_block_identity 192.
proof. exact (rrec_public_inverse_product hp). qed.
''',
    'acwc2_contracts/NTRUPlus768RRecInverseAlgebra.ec': r'''

lemma __acwc2_eof_2 hp inverse :
 in_qrange768 hp => in_canonical_range768 inverse =>
 poly_basemul_qring hp inverse ntt_block_identity 192 =>
 rrec_public_inverse hp=Some inverse.
proof. exact (rrec_public_inverse_known_canonical hp inverse). qed.
''',
    'acwc2_contracts/NTRUPlus768RRecModel.ec': r'''

lemma __acwc2_eof_4 pk m ct r : rrec_spec pk m ct=Some r =>
 pke_domain m /\ pke_domain r /\ pke_enc_spec pk m r=Some ct.
proof. exact (rrec_spec_sound pk m ct r). qed.
''',
    'acwc2_contracts/NTRUPlus768RRecProcedures.ec': r'''

lemma __acwc2_eof_3 : islossless RRec.run.
proof. exact (rrec_lossless). qed.
''',
    'acwc2_contracts/NTRUPlus768RRecCodec.ec': r'''

lemma __acwc2_eof_7 r s : pke_domain r => pke_domain s => rr_G_input r=rr_G_input s => r=s.
proof. exact (rr_G_input_injective r s). qed.
''',
    'acwc2_contracts/NTRUPlus768RRecAlgebra.ec': r'''

lemma __acwc2_eof_9 w m r :
 pke_key_relation w => pke_domain m => pke_domain r =>
 rrec_spec w.`kg_pk m (pke_ciphertext w.`kg_pk m r)=Some r.
proof. exact (rrec_keyed_forward w m r). qed.
''',
    'acwc2_contracts/NTRUPlus768RRecCallProof.ec': r'''

lemma __acwc2_eof_8 w m0 r0 :
 pke_key_relation w => pke_domain m0 => pke_domain r0 =>
 phoare[RRec.run : pk=w.`kg_pk /\ m=m0 /\ ct=pke_ciphertext w.`kg_pk m0 r0 ==>
 res=Some r0]=1%r.
proof. exact (rrec_keyed_forward_correct w m0 r0). qed.
''',
    'acwc2_contracts/NTRUPlus768SOTPRigidity.ec': r'''

lemma __acwc2_eof_5 a pad :
 !poly_sotp_decode_fail_spec a pad =>
 poly_sotp_encode_spec (poly_sotp_decode_msg_spec a pad) pad = a.
proof. exact (sotp_decode_encode_rigidity a pad). qed.
''',
    'acwc2_contracts/NTRUPlus768SOTPContracts.ec': r'''

lemma __acwc2_eof_6 &m msg0 event :
 Pr[SOTPUniformEncode.run(msg0) @ &m:event res]=mu pke_psi1 event.
proof. exact (sotp_uniform_encode_law &m msg0 event). qed.
''',
    'acwc2_contracts/NTRUPlus768ACWC2HashG.ec': r'''

lemma __acwc2_eof_10 &m r0 event :
 pke_domain r0 => rr_G_input r0 \notin ROG.m{m} =>
 Pr[ACWC2HashG.run(r0) @ &m:event res]=mu uniform192 event.
proof. exact (acwc2_hash_g_fresh_law &m r0 event). qed.
''',
}
SEMANTIC_TARGETS = {
    'acwc2_contracts/NTRUPlus768RRecWordChecks.ec': 'rrec_trit_functional',
    'acwc2_contracts/NTRUPlus768RRecPublicInverse.ec': 'rrec_public_inverse_product',
    'acwc2_contracts/NTRUPlus768RRecInverseAlgebra.ec': 'rrec_public_inverse_known_canonical',
    'acwc2_contracts/NTRUPlus768RRecModel.ec': 'rrec_spec_sound',
    'acwc2_contracts/NTRUPlus768RRecProcedures.ec': 'rrec_lossless',
    'acwc2_contracts/NTRUPlus768RRecCodec.ec': 'rr_G_input_injective',
    'acwc2_contracts/NTRUPlus768RRecAlgebra.ec': 'rrec_keyed_forward',
    'acwc2_contracts/NTRUPlus768RRecCallProof.ec': 'rrec_keyed_forward_correct',
    'acwc2_contracts/NTRUPlus768SOTPRigidity.ec': 'sotp_decode_encode_rigidity',
    'acwc2_contracts/NTRUPlus768SOTPContracts.ec': 'sotp_uniform_encode_law',
    'acwc2_contracts/NTRUPlus768ACWC2HashG.ec': 'acwc2_hash_g_fresh_law',
}
MODULE_BINDERS = {
    'acwc2_contracts/NTRUPlus768RRecWordChecks.ec': (),
    'acwc2_contracts/NTRUPlus768RRecPublicInverse.ec': (),
    'acwc2_contracts/NTRUPlus768RRecInverseAlgebra.ec': (),
    'acwc2_contracts/NTRUPlus768RRecModel.ec': (),
    'acwc2_contracts/NTRUPlus768RRecProcedures.ec': (),
    'acwc2_contracts/NTRUPlus768RRecCodec.ec': (),
    'acwc2_contracts/NTRUPlus768RRecAlgebra.ec': (),
    'acwc2_contracts/NTRUPlus768RRecCallProof.ec': (),
    'acwc2_contracts/NTRUPlus768SOTPRigidity.ec': (),
    'acwc2_contracts/NTRUPlus768SOTPContracts.ec': (),
    'acwc2_contracts/NTRUPlus768ACWC2HashG.ec': (),
}
NEGATIVE_PROOFS = (
    'acwc2_contracts/NTRUPlus768RRecWordChecks.ec',
    'acwc2_contracts/NTRUPlus768RRecPublicInverse.ec',
    'acwc2_contracts/NTRUPlus768RRecInverseAlgebra.ec',
    'acwc2_contracts/NTRUPlus768RRecModel.ec',
    'acwc2_contracts/NTRUPlus768RRecProcedures.ec',
    'acwc2_contracts/NTRUPlus768RRecCodec.ec',
    'acwc2_contracts/NTRUPlus768RRecAlgebra.ec',
    'acwc2_contracts/NTRUPlus768RRecCallProof.ec',
    'acwc2_contracts/NTRUPlus768SOTPRigidity.ec',
    'acwc2_contracts/NTRUPlus768SOTPContracts.ec',
    'acwc2_contracts/NTRUPlus768ACWC2HashG.ec',
)
