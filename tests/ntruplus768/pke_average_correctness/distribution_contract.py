"""Fresh whole-key conditioning is distinct from the actual ROM key law."""
BASE='ntruplus/proof/768/ref/pke_average_correctness/'
MODEL=BASE+'NTRUPlus768PKEModel.ec'
KEYS=BASE+'NTRUPlus768PKEKeyDistribution.ec'
CALLS=BASE+'NTRUPlus768PKECallProof.ec'
RULES=(
 (MODEL,'underlying PKE secret is only serialized f',r'op pke_secret_bytes (w:keygen_witness) = decap_fbytes (complete_sk_poly w.`kg_sk).'),
 (MODEL,'PKE decryption specification computes c times f without an input message',r'op pke_dec_spec (ct fbytes:W8.t Array1152.t) : pke_poly option = if encap_key_canonical ct /\ encap_key_canonical fbytes then Some(decap_candidate_spec (decoded_poly ct) (decoded_poly fbytes)) else None.'),
 (MODEL,'PKE key relation does not require an unrelated F hash cache',r'op pke_key_relation (w:keygen_witness) = payload_key_relation w.`kg_fbuf w.`kg_gbuf w.`kg_finv w.`kg_ginv w.`kg_h w.`kg_hinv w.`kg_pk w.`kg_sk.'),
 (KEYS,'unconditioned CBD polynomial has 768 independent trits',r'op pke_psi1 : W16.t Array768.t distr = dmap (dlist dcbd 768) cbd_word_array.'),
 (KEYS,'accepted f/g laws condition whole polynomials separately',r'op pke_accepted_cbd_pair = (dcond pke_psi1 pke_f_accept_array) `*` (dcond pke_psi1 pke_g_accept_array).'),
 (KEYS,'actual f acceptance uses shaped NTT/baseinv predicate',r'op pke_f_accept_array (p:W16.t Array768.t) = poly_blocks_succeed (forward_ntt_spec(keygen_shape_f_spec p)) 192.'),
 (KEYS,'actual g acceptance uses scaled shape NTT/baseinv predicate',r'op pke_g_accept_array (p:W16.t Array768.t) = poly_blocks_succeed (forward_ntt_spec(keygen_shape_g_spec p)) 192.'),
 (KEYS,'fresh actual retry law is not an iid law for the ROM',r'lemma pke_actual_keygen_cbd_pair_law &m workspace (event:(W16.t Array768.t*W16.t Array768.t)->bool) : Pr[KeygenInstrumented(UniformSeedRNG,FreshExpand,SHAKEFROM).run(workspace) @ &m : event(poly_cbd1_spec res.`1.`kg_fbuf,poly_cbd1_spec res.`1.`kg_gbuf)]= mu pke_accepted_cbd_pair event.'),
 (KEYS,'key conditioning leaves independent new r and m',r'lemma pke_independent_key_randomness_message : dmap accepted_four_law pke_four_cbd= pke_accepted_cbd_pair `*` (pke_psi1 `*` pke_psi1).'),
 (KEYS,'g polynomial retains its factor three',r'lemma pke_g_field_shape buf : input_poly(keygen_g_pre_ntt_spec buf)=NTRUPoly.polyC(lift_int 3)*pke_cbd_field buf.'),
 (KEYS,'scalar invertibility is required for the quotient-ring unit equivalence',r'lemma pke_rq_unit_scale (c:CycloFq.cyclocoeff) (p:NTRUPoly.poly) : c<>CycloFq.zero => (pke_rq_unit(NTRUPoly.polyC c*p) <=> pke_rq_unit p).'),
 (CALLS,'functional encryption preserves both ternary-domain premises',r'lemma pke_enc_functional pk0 m0 r0 : pke_domain m0 => pke_domain r0 => hoare[PKEEnc.run : pk=pk0 /\ m=m0 /\ r=r0 ==> res=pke_enc_spec pk0 m0 r0].'),
 (CALLS,'actual decryption endpoint is its own recovered message',r'lemma pke_dec_functional ct0 fbytes0 : hoare[PKEDec.run : ct=ct0 /\ fbytes=fbytes0 ==> res=pke_dec_spec ct0 fbytes0].'),
)
MUTATIONS=(
 ('PKE-secret-substitutes-KEM-hash-suffix',MODEL,'decap_fbytes (complete_sk_poly w.`kg_sk)','complete_sk_suffix w.`kg_sk'),
 ('PKE-spec-decrypts-with-ciphertext-as-secret',MODEL,'decap_candidate_spec (decoded_poly ct) (decoded_poly fbytes)','decap_candidate_spec (decoded_poly ct) (decoded_poly ct)'),
 ('PKE-spec-omits-secret-canonicality',MODEL,r'if encap_key_canonical ct /\ encap_key_canonical fbytes then',r'if encap_key_canonical ct then'),
 ('PKE-key-relation-adds-unrelated-hash-state',MODEL,'op pke_key_relation (w:keygen_witness) = payload_key_relation',r'op pke_key_relation (w:keygen_witness) = ROF.m=empty /\ payload_key_relation'),
 ('accepted-key-coefficients-asserted-iid',KEYS,'op pke_accepted_cbd_pair = (dcond pke_psi1 pke_f_accept_array) `*` (dcond pke_psi1 pke_g_accept_array).','op pke_accepted_cbd_pair = pke_psi1 `*` pke_psi1.'),
 ('g-acceptance-tests-f-shape',KEYS,'op pke_g_accept_array (p:W16.t Array768.t) = poly_blocks_succeed (forward_ntt_spec(keygen_shape_g_spec p)) 192.','op pke_g_accept_array (p:W16.t Array768.t) = poly_blocks_succeed (forward_ntt_spec(keygen_shape_f_spec p)) 192.'),
 ('fresh-retry-law-misapplied-to-real-ROM',KEYS,'KeygenInstrumented(UniformSeedRNG,FreshExpand,SHAKEFROM).run(workspace)','KeygenInstrumented(UniformSeedRNG,ExpandROM,SHAKEFROM).run(workspace)'),
 ('g-scalar-three-dropped',KEYS,'input_poly(keygen_g_pre_ntt_spec buf)=NTRUPoly.polyC(lift_int 3)*pke_cbd_field buf.','input_poly(keygen_g_pre_ntt_spec buf)=pke_cbd_field buf.'),
 ('scalar-unit-law-allows-zero',KEYS,'lemma pke_rq_unit_scale (c:CycloFq.cyclocoeff) (p:NTRUPoly.poly) : c<>CycloFq.zero =>','lemma pke_rq_unit_scale (c:CycloFq.cyclocoeff) (p:NTRUPoly.poly) :'),
 ('actual-Enc-functional-law-omits-message-domain',CALLS,'lemma pke_enc_functional pk0 m0 r0 : pke_domain m0 => pke_domain r0 =>','lemma pke_enc_functional pk0 m0 r0 : pke_domain r0 =>'),
 ('actual-Dec-functional-law-substitutes-reference-call',CALLS,r'hoare[PKEDec.run : ct=ct0 /\ fbytes=fbytes0',r'hoare[ReferenceDec.run : ct=ct0 /\ fbytes=fbytes0'),
)

ALGEBRA=BASE+'NTRUPlus768PKEAlgebra.ec'
RULES+=(
 (ALGEBRA,'no-wrap recovery retains valid key and both ternary-domain premises',r'lemma pke_no_wrap_recovery w m r : pke_key_relation w => pke_domain m => pke_domain r => sampled_m1_no_wrap w.`kg_fbuf w.`kg_gbuf r m => pke_dec_spec (pke_ciphertext w.`kg_pk m r) (pke_secret_bytes w)=Some m.'),
 (ALGEBRA,'actual inverses match f and the implemented scaled-g transform',r'lemma pke_actual_inverse_predicates w : pke_key_relation w => poly_baseinv_success (keygen_f_ntt_spec w.`kg_fbuf) w.`kg_finv /\ poly_baseinv_success (keygen_g_ntt_spec w.`kg_gbuf) w.`kg_ginv.'),
 (CALLS,'conditional recovery targets actual Dec with the derived ciphertext and secret',r'lemma pke_dec_no_wrap w m0 r0 : pke_key_relation w => pke_domain m0 => pke_domain r0 => sampled_m1_no_wrap w.`kg_fbuf w.`kg_gbuf r0 m0 => phoare[PKEDec.run : ct=pke_ciphertext w.`kg_pk m0 r0 /\ fbytes=pke_secret_bytes w ==> res=Some m0]=1%r.'),
)
MUTATIONS+=(
 ('no-wrap-recovery-omits-valid-key-premise',ALGEBRA,'lemma pke_no_wrap_recovery w m r : pke_key_relation w =>','lemma pke_no_wrap_recovery w m r :'),
 ('no-wrap-recovery-becomes-unconditional',ALGEBRA,'sampled_m1_no_wrap w.`kg_fbuf w.`kg_gbuf r m => pke_dec_spec','pke_dec_spec'),
 ('no-wrap-recovery-swaps-message-and-randomness',ALGEBRA,'sampled_m1_no_wrap w.`kg_fbuf w.`kg_gbuf r m => pke_dec_spec','sampled_m1_no_wrap w.`kg_fbuf w.`kg_gbuf m r => pke_dec_spec'),
 ('scaled-g-inverse-replaced-with-f-inverse',ALGEBRA,'poly_baseinv_success (keygen_g_ntt_spec w.`kg_gbuf) w.`kg_ginv.','poly_baseinv_success (keygen_g_ntt_spec w.`kg_gbuf) w.`kg_finv.'),
 ('actual-Dec-no-wrap-returns-randomness',CALLS,'fbytes=pke_secret_bytes w ==> res=Some m0]=1%r.','fbytes=pke_secret_bytes w ==> res=Some r0]=1%r.'),
)

RULES+=((ALGEBRA,'independent ring decoding links the input residue to its centered lift and recovered trits',r'op pke_ring_decodes (P:poly) (candidate:pke_poly) = exists (v:int Array768.t), (forall j,0<=j<768 => -1728<=v.[j]<=1728) /\ eqm_global P (int_poly v) /\ message_mod3_witness v candidate.'),)
MUTATIONS+=(
 ('ring-decoding-relation-forgets-input-polynomial',ALGEBRA,r'eqm_global P (int_poly v) /\ message_mod3_witness v candidate',r'message_mod3_witness v candidate'),
 ('ring-decoding-relation-loses-unique-centered-lift',ALGEBRA,r'(forall j,0<=j<768 => -1728<=v.[j]<=1728) /\ eqm_global P (int_poly v)',r'eqm_global P (int_poly v)'),
)
