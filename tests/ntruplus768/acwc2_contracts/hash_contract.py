"""Actual tag-1 G preparation and cache-dependent laws keep their real call boundary."""
HASH='ntruplus/proof/768/ref/acwc2_contracts/NTRUPlus768ACWC2HashG.ec'
RULES=(
 (HASH,'typed G query uses the actual serialized transform payload',r'op rr_G_query (r:pke_poly) : W8.t Array1153.t = encode_g(rr_G_input r).'),
 (HASH,'actual NTT and message-preparation kernels produce the G query',r'module ACWC2GPrepare = { proc run(r:pke_poly) : W8.t Array1152.t * W8.t Array1153.t = { var rhat:pke_poly; var serialized:W8.t Array1152.t; var input:W8.t Array1153.t; rhat <@ NTRUPlus768NTT.M.jade_ntruplus_ntruplus768_amd64_ref_ntt(witness,r); (serialized,input) <@ NTRUPlus768DecapMessagePrepare.M.jade_ntruplus_ntruplus768_amd64_ref_decap_message_prepare(witness,witness,rhat); return(serialized,input); } }.'),
 (HASH,'actual G hash uses the shared ROM wrapper without table reset',r'module ACWC2HashG = { proc run(r:pke_poly) : W8.t Array192.t = { var serialized:W8.t Array1152.t; var input:W8.t Array1153.t; var pad:W8.t Array192.t; (serialized,input) <@ ACWC2GPrepare.run(r); pad <@ SHAKEGROM.shake(input); return pad; } }.'),
 (HASH,'actual G preparation has the declared typed payload and raw tag',r'lemma acwc2_g_prepare_correct r0 : phoare[ACWC2GPrepare.run:r=r0 /\ pke_domain r0 ==> res=(rr_G_input r0,rr_G_query r0)]=1%r.'),
 (HASH,'raw byte query equals the typed G encoding',r'lemma acwc2_g_query_raw r : Array1153.to_list(rr_G_query r)=raw_query(G(rr_G_input r)).'),
 (HASH,'cached G call returns its stored answer and preserves the table',r'lemma acwc2_hash_g_cached r0 gm0 pad0 : hoare[ACWC2HashG.run:r=r0 /\ pke_domain r0 /\ ROG.m=gm0 /\ gm0.[rr_G_input r0]=Some pad0 ==> res=pad0 /\ ROG.m=gm0].'),
 (HASH,'uniform G law requires an absent current-table input',r'lemma acwc2_hash_g_fresh_law &m r0 event : pke_domain r0 => rr_G_input r0 \notin ROG.m{m} => Pr[ACWC2HashG.run(r0) @ &m:event res]=mu uniform192 event.'),
)
MUTATIONS=(
 ('G-query-uses-F-domain-tag',HASH,'= encode_g(rr_G_input r).','= encode_f(rr_G_input r).'),
 ('G-prepare-skips-NTT',HASH,'rhat <@ NTRUPlus768NTT.M.jade_ntruplus_ntruplus768_amd64_ref_ntt(witness,r);','rhat<-r;'),
 ('G-prepare-serializes-untransformed-randomness',HASH,'decap_message_prepare(witness,witness,rhat);','decap_message_prepare(witness,witness,r);'),
 ('G-call-resamples-instead-of-using-shared-cache',HASH,'pad <@ SHAKEGROM.shake(input);','pad <$ uniform192;'),
 ('G-call-resets-table-before-query',HASH,'pad <@ SHAKEGROM.shake(input);','ROG.init(); pad <@ SHAKEGROM.shake(input);'),
 ('G-fresh-law-omits-absence-premise',HASH,r'pke_domain r0 => rr_G_input r0 \notin ROG.m{m} =>',r'pke_domain r0 =>'),
 ('G-fresh-law-uses-coefficients-as-cache-key',HASH,r'rr_G_input r0 \notin ROG.m{m} =>',r'raw_coeff_bytes r0 \notin ROG.m{m} =>'),
)

RULES+=((HASH,'actual G wire query is accepted by the shared typed/raw decoder',r'lemma acwc2_g_query_typed r : decode_typed(Array1153.to_list(rr_G_query r))=Some(G(rr_G_input r)).'),)
