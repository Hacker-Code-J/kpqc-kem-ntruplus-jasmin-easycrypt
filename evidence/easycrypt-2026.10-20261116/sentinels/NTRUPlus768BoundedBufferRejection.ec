
lemma __stopped_bounded_buffer_eof &m d0 accept0 q0 :
 is_lossless d0 => 0<=q0 =>
 Pr[BoundedBufferRejection.run(d0,accept0,q0) @ &m:res=None] =
 (1%r-mu d0 accept0)^q0.
proof. exact (bounded_buffer_rejection_tail &m d0 accept0 q0). qed.
