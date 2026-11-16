
lemma __stopped_pair_ports_eof (P <: ProposalPort) :
 hoare[PairPorts(P).shake : true ==> res=PairPorts.pending].
proof. exact (pair_ports_shake_value P). qed.
