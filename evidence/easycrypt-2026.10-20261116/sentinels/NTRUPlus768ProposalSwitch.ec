
lemma __stopped_proposal_switch_eof
 (A <: ProposalContext {-FreshProposal,-ROMProposal,-ROE})
 &mem qf qg qb ab m0 :
 (forall (P <: ProposalPort {-A}),
  islossless P.draw => islossless A(P).run) =>
 0<=qb => 0<=ab => fsize m0<=ab =>
 `|Pr[ROMProposalExperiment(A).run(qf,qg,qb,m0) @ &mem : res] -
   Pr[FreshProposalExperiment(A).run(qf,qg,qb,m0) @ &mem : res]| <= proposal_delta ab qb.
proof. exact (proposal_switch_distance A &mem qf qg qb ab m0). qed.
