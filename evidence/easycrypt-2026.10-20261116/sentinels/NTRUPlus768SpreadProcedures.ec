

lemma __spreadness_eof pk0 m0 event &m : pke_domain m0=>
 Pr[SpreadPKE.run(pk0,m0) @ &m:event res]=
 mu pke_psi1(fun r=>event(pke_enc_spec pk0 m0 r)).
proof. exact (spread_pke_probability pk0 m0 event &m). qed.
