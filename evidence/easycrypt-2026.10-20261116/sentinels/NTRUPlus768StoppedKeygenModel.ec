
lemma __stopped_model_eof (event:keygen_output -> bool) nf ng :
 stopped_event event (None,nf,ng)=false.
proof. exact (stopped_event_none event nf ng). qed.
