

lemma __spreadness_eof w m :
 pke_key_relation w=>pke_domain m=>
 mu pke_psi1 (fun r=>pke_enc_spec w.`kg_pk m r=
   Some(pke_ciphertext w.`kg_pk m spread_cbd_zero))=1%r/(2%r^768).
proof. exact (spread_base_zero_tight w m). qed.
