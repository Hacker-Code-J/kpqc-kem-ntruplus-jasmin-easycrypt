
lemma __stopped_actual_fresh_pair_eof &m workspace
 (event:(W8.t Array192.t * W8.t Array192.t) -> bool) :
 Pr[KeygenInstrumented(UniformSeedRNG,FreshExpand,SHAKEFROM).run(workspace) @ &m :
 event(res.`1.`kg_fbuf,res.`1.`kg_gbuf)] =
 mu (((dcond uniform192 keygen_f_accept) `*` (dcond uniform192 keygen_g_accept))) event.
proof. exact (fresh_keygen_buffer_pair_probability &m workspace event). qed.
