"""Frozen complete semantic EOF declarations and isolated unfinished-proof inventory."""
SENTINELS = {
    'linear_rrec/NTRUPlus768RRecCanonical.ec': r"""

lemma __linear_rrec_eof_0 : is_finite rrec_canonical_domain.
proof. exact rrec_canonical_domain_finite. qed.
""",
    'linear_rrec/NTRUPlus768RRecTerminal.ec': r"""

lemma __linear_rrec_eof_7 (a b:W16.t Array768.t) (p:poly) :
 terminal_represents a p=>terminal_represents b p=>poly_coeff_eq_mod_q a b.
proof. exact (rrec_terminal_same_poly_mod_q a b p). qed.
""",
    'linear_rrec/NTRUPlus768RRecTransform.ec': r"""

lemma __linear_rrec_eof_1 y r :
 qrange_input_shape y =>pke_domain r =>rrec_normalize(inverse_invntt_spec y)=r =>
 poly_coeff_eq_mod_q (pke_rhat r) y.
proof. exact (rrec_inverse_forward_trit y r). qed.
""",
    'linear_rrec/NTRUPlus768RRecSerialization.ec': r"""

lemma __linear_rrec_eof_4 ct : encap_key_canonical ct =>
 NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec(decoded_poly ct)=ct.
proof. exact (rrec_canonical_reencode ct). qed.
""",
    'linear_rrec/NTRUPlus768RRecLinearModel.ec': r"""

lemma __linear_rrec_eof_2 pk m ct r : rrec_spec pk m ct=Some r =>rrec_linear_spec pk m ct=Some r.
proof. exact (rrec_linear_from_checked pk m ct r). qed.
""",
    'linear_rrec/NTRUPlus768RRecLinearProcedures.ec': r"""

lemma __linear_rrec_eof_3 : islossless LinearRRec.run.
proof. exact (linear_rrec_lossless). qed.
""",
    'linear_rrec/NTRUPlus768RRecLinearAlgebra.ec': r"""

lemma __linear_rrec_eof_5 pk m ct :
 encap_key_canonical pk => rrec_public_inverse(decoded_poly pk)<>None =>
 encap_key_canonical ct => pke_domain m =>
 pke_domain(rrec_candidate (decoded_poly ct) m (oget(rrec_public_inverse(decoded_poly pk)))) =>
 pke_enc_spec pk m (rrec_candidate (decoded_poly ct) m
   (oget(rrec_public_inverse(decoded_poly pk))))=Some ct.
proof. exact (rrec_linear_candidate_reencrypt pk m ct). qed.
""",
    'linear_rrec/NTRUPlus768RRecLinearProof.ec': r"""

lemma __linear_rrec_eof_6 :
 equiv[LinearRRec.run ~ RRec.run: ={pk,m,ct} ==> ={res}].
proof. exact linear_rrec_actual_equiv. qed.
""",
    'linear_rrec/NTRUPlus768RRecNativeComparison.ec': r"""

lemma __linear_rrec_eof_8 w ct : pke_key_relation w=>
 complete_entry_accepts ct w.`kg_sk=>
 rrec_compare_relation w.`kg_pk ct (message_candidate ct(complete_sk_poly w.`kg_sk))
   (NTRUPlus768PolyToBytesProof.poly_tobytes_spec(message_r2 ct(complete_sk_poly w.`kg_sk))).
proof. exact (rrec_native_compare_relation_procedure w ct). qed.
""",
    'linear_rrec/NTRUPlus768RRecNativeProcedures.ec': r"""

lemma __linear_rrec_eof_10 (G<:MessageSHAKE) (H<:CompleteSHAKEH) :
 islossless G.shake => islossless H.shake => islossless ReencryptDecaps(G,H).run.
proof. exact (reencrypt_decaps_lossless G H). qed.
""",
    'linear_rrec/NTRUPlus768RRecNativeProof.ec': r"""

lemma __linear_rrec_eof_11 w ct0 : pke_key_relation w =>
 equiv[CompleteDecaps(SHAKEGROM,SHAKEHROM).run ~ ReencryptDecaps(SHAKEGROM,SHAKEHROM).run:
 ct{1}=ct0 /\ ct{2}=ct0 /\ sk{1}=w.`kg_sk /\ sk{2}=w.`kg_sk /\ pk{2}=w.`kg_pk /\
 ={workspace,ROG.m,ROH.m} ==>
 ={res,ROG.m,ROH.m} /\ res.`3{1}=clear_zero_spec].
proof. exact (native_reencrypt_rom_decaps w ct0). qed.
""",
    'linear_rrec/NTRUPlus768RRecACWC2Bridge.ec': r"""

lemma __linear_rrec_eof_9 &m :
 E (mk(fun z=>Pr[KeygenSource(FreshExpand).guess(witness) @ &m:res=z]))
  (fun (out:keygen_output)=>E acwc2_gpads_law
   (fun (pads:W8.t Array192.t list)=>acwc2_finite_max acwc2_message_enum
    (fun (msg:W8.t Array96.t)=>
      Pr[LinearACWC2FixedOracleTrial.run(pads,out.`1.`kg_pk,out.`1.`kg_sk,msg) @ &m:res])))
 <1%r/(2%r^353).
proof. exact (linear_acwc2_fresh_worst_actual_calls &m). qed.
""",
}

SEMANTIC_TARGETS = {'linear_rrec/NTRUPlus768RRecACWC2Bridge.ec': 'linear_acwc2_fresh_worst_actual_calls',
 'linear_rrec/NTRUPlus768RRecCanonical.ec': 'rrec_canonical_domain_finite',
 'linear_rrec/NTRUPlus768RRecLinearAlgebra.ec': 'rrec_linear_candidate_reencrypt',
 'linear_rrec/NTRUPlus768RRecLinearModel.ec': 'rrec_linear_from_checked',
 'linear_rrec/NTRUPlus768RRecLinearProcedures.ec': 'linear_rrec_lossless',
 'linear_rrec/NTRUPlus768RRecLinearProof.ec': 'linear_rrec_actual_equiv',
 'linear_rrec/NTRUPlus768RRecNativeComparison.ec': 'rrec_native_compare_relation_procedure',
 'linear_rrec/NTRUPlus768RRecNativeProcedures.ec': 'reencrypt_decaps_lossless',
 'linear_rrec/NTRUPlus768RRecNativeProof.ec': 'native_reencrypt_rom_decaps',
 'linear_rrec/NTRUPlus768RRecSerialization.ec': 'rrec_canonical_reencode',
 'linear_rrec/NTRUPlus768RRecTerminal.ec': 'rrec_terminal_same_poly_mod_q',
 'linear_rrec/NTRUPlus768RRecTransform.ec': 'rrec_inverse_forward_trit'}

MODULE_BINDERS = {'linear_rrec/NTRUPlus768RRecACWC2Bridge.ec': (),
 'linear_rrec/NTRUPlus768RRecCanonical.ec': (),
 'linear_rrec/NTRUPlus768RRecLinearAlgebra.ec': (),
 'linear_rrec/NTRUPlus768RRecLinearModel.ec': (),
 'linear_rrec/NTRUPlus768RRecLinearProcedures.ec': (),
 'linear_rrec/NTRUPlus768RRecLinearProof.ec': (),
 'linear_rrec/NTRUPlus768RRecNativeComparison.ec': (),
 'linear_rrec/NTRUPlus768RRecNativeProcedures.ec': ('G', 'H'),
 'linear_rrec/NTRUPlus768RRecNativeProof.ec': (),
 'linear_rrec/NTRUPlus768RRecSerialization.ec': (),
 'linear_rrec/NTRUPlus768RRecTerminal.ec': (),
 'linear_rrec/NTRUPlus768RRecTransform.ec': ()}

NEGATIVE_PROOFS = ('linear_rrec/NTRUPlus768RRecCanonical.ec',
 'linear_rrec/NTRUPlus768RRecTerminal.ec',
 'linear_rrec/NTRUPlus768RRecTransform.ec',
 'linear_rrec/NTRUPlus768RRecSerialization.ec',
 'linear_rrec/NTRUPlus768RRecLinearModel.ec',
 'linear_rrec/NTRUPlus768RRecLinearProcedures.ec',
 'linear_rrec/NTRUPlus768RRecLinearAlgebra.ec',
 'linear_rrec/NTRUPlus768RRecLinearProof.ec',
 'linear_rrec/NTRUPlus768RRecNativeComparison.ec',
 'linear_rrec/NTRUPlus768RRecNativeProcedures.ec',
 'linear_rrec/NTRUPlus768RRecNativeProof.ec',
 'linear_rrec/NTRUPlus768RRecACWC2Bridge.ec')
