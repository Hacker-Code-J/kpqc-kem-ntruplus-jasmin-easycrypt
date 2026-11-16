
lemma __stopped_subdistribution_eof (mass good epsilon:real) :
 mass<=1%r => good<=mass => 1%r-epsilon<=good => 0%r<=1%r-mass<=epsilon.
proof. exact (subdistribution_missing_mass mass good epsilon). qed.
