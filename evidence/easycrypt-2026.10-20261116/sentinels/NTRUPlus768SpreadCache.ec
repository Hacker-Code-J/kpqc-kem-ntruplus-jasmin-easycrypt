

lemma __spreadness_eof w msg g gm ct &m :
 acwc2_cache_matches g gm=>ROG.m{m}=gm=>
 Pr[SpreadEncodedValue.run(w.`kg_pk,msg) @ &m:res=Some ct]=spread_cipher_mass w msg g ct.
proof. exact (spread_encoded_prepared_probability w msg g gm ct &m). qed.
