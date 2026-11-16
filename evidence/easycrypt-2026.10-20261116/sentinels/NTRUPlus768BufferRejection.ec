
lemma __stopped_buffer_eof &m d accept (event:W8.t Array192.t -> bool) :
 is_lossless d =>
 Pr[BufferRejection.sample(d,accept) @ &m:event res] =
 mu d (fun buffer => accept buffer /\ event buffer) / mu d accept.
proof. exact (buffer_rejection_exact_conditional &m d accept event). qed.
