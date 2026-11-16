
lemma __stopped_attempt_eof (E <: KeygenExpand) :
 islossless E.shake =>
 phoare[KeygenAttempt(E).g : true ==> res=keygen_g_attempt_result res.`1]=1%r.
proof. exact (keygen_attempt_g_realized_total E). qed.
