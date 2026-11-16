
lemma __stopped_fresh_buffer_eof (event:W8.t Array192.t -> bool) :
 phoare[KeygenRetry(UniformSeedRNG,FreshExpand).g : true ==> event res.`1] =
 (mu (dcond uniform192 keygen_g_accept) event).
proof. exact (fresh_retry_g_buffer_law event). qed.
