"""Actual linear recovery contracts keep arbitrary ciphertexts and all ternary inputs."""
BASE='ntruplus/proof/768/ref/linear_rrec/'
PROOF=BASE+'NTRUPlus768RRecLinearProof.ec'
RULES=(
 (PROOF,'actual functional result holds for arbitrary public inputs',r'lemma linear_rrec_correct pk0 m0 ct0 : phoare[LinearRRec.run:pk=pk0 /\ m=m0 /\ ct=ct0 ==>res=rrec_linear_spec pk0 m0 ct0]=1%r.'),
 (PROOF,'forward correctness retains all ternary messages and coins without no-wrap',r'lemma linear_rrec_keyed_forward w m0 r0 : pke_key_relation w =>pke_domain m0 =>pke_domain r0 => phoare[LinearRRec.run:pk=w.`kg_pk /\ m=m0 /\ ct=pke_ciphertext w.`kg_pk m0 r0 ==>res=Some r0]=1%r.'),
 (PROOF,'actual checked and linear procedures agree as options for all public inputs',r'lemma linear_rrec_actual_equiv : equiv[LinearRRec.run ~ RRec.run: ={pk,m,ct} ==> ={res}].'),
 (PROOF,'actual successful linear recovery implies same-ciphertext encryption without an external input premise',r'lemma linear_rrec_sound pk0 m0 ct0 : hoare[LinearRRec.run:pk=pk0 /\ m=m0 /\ ct=ct0 ==> forall r,res=Some r =>pke_domain m0 /\ pke_domain r /\ pke_enc_spec pk0 m0 r=Some ct0].'),
)
MUTATIONS=(
 ('actual-functional-contract-adds-an-honest-ciphertext-premise',PROOF,'lemma linear_rrec_correct pk0 m0 ct0 :',r'lemma linear_rrec_correct pk0 m0 ct0 : (exists r,pke_domain r /\ ct0=pke_ciphertext pk0 m0 r) =>'),
 ('actual-forward-contract-adds-a-no-wrap-premise',PROOF,'lemma linear_rrec_keyed_forward w m0 r0 :','lemma linear_rrec_keyed_forward w m0 r0 : honest_no_wrap (w,m0,r0) =>'),
 ('all-input-actual-equivalence-restricted-to-canonical-ciphertexts',PROOF,'equiv[LinearRRec.run ~ RRec.run: ={pk,m,ct} ==> ={res}].',r'equiv[LinearRRec.run ~ RRec.run: ={pk,m,ct} /\ encap_key_canonical ct{1} ==> ={res}].'),
 ('all-input-actual-equivalence-forgets-option-status',PROOF,'equiv[LinearRRec.run ~ RRec.run: ={pk,m,ct} ==> ={res}].','equiv[LinearRRec.run ~ RRec.run: ={pk,m,ct} ==> oget res{1}=oget res{2}].'),
)
