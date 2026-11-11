require import AllCore Distr FMap.
from Jasmin require import JWord.
require import Array32 Array192 Array768 Array14466.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteAttempt.
require import NTRUPlus768StoppedKeygenModel NTRUPlus768StoppedKeygenPrefix.
require import NTRUPlus768ProposalModel NTRUPlus768ProposalSwitch.
require import NTRUPlus768AttemptRealized NTRUPlus768FreshRetryLaw.
require import NTRUPlus768ROMDistributions NTRUPlus768ROMOracles.

module StoppedKeygenContext(P:ProposalPort) = {
 var event:stopped_output -> bool
 proc run(qf:int,qg:int) : bool = {
  var result;
  result <@ StoppedKeygen(PairPorts(P),PairPorts(P)).run(qf,qg,witness);
  return event result;
 }
}.

lemma stopped_keygen_context_ll (P <:ProposalPort {-StoppedKeygenContext}) :
 islossless P.draw => islossless StoppedKeygenContext(P).run.
proof.
 move=> pl; proc.
 call (stopped_keygen_lossless (PairPorts(P)) (PairPorts(P))
   (pair_ports_sample_lossless P pl) (pair_ports_shake_lossless P)); auto.
qed.

(* The sole change is the previously proved realized-attempt contract.
   Seed, expansion, count, and stopping order are retained. *)
module ResultRetry(R:KeygenSeedRNG,E:KeygenExpand) = {
 proc f(limit:int) : retry_state = {
  var seed:W8.t Array32.t; var buf:W8.t Array192.t;
  var ntt,inverse:W16.t Array768.t; var status:W64.t; var count:int;
  buf <- witness; ntt <- witness; inverse <- witness; status <- W64.one; count <- 0;
  while (status <> W64.zero /\ count < max 0 limit) {
   seed <@ R.sample();
   (buf,ntt,inverse,status) <@ AttemptResult(E).f(seed);
   count <- count+1;
  }
  return {|rs_buf=buf;rs_ntt=ntt;rs_inv=inverse;rs_ok=status=W64.zero;rs_count=count|};
 }
 proc g(limit:int) : retry_state = {
  var seed:W8.t Array32.t; var buf:W8.t Array192.t;
  var ntt,inverse:W16.t Array768.t; var status:W64.t; var count:int;
  buf <- witness; ntt <- witness; inverse <- witness; status <- W64.one; count <- 0;
  while (status <> W64.zero /\ count < max 0 limit) {
   seed <@ R.sample();
   (buf,ntt,inverse,status) <@ AttemptResult(E).g(seed);
   count <- count+1;
  }
  return {|rs_buf=buf;rs_ntt=ntt;rs_inv=inverse;rs_ok=status=W64.zero;rs_count=count|};
 }
}.
lemma bounded_f_result_equiv (R <:KeygenSeedRNG) (E <:KeygenExpand {-R}) :
 equiv[BoundedRetry(R,E).f ~ ResultRetry(R,E).f :
 ={limit,glob R,glob E} ==> ={res,glob R,glob E}].
proof.
 proc; inline BoundedRetry(R,E).f_from; wp.
 while(={buf,ntt,inverse,status,count,glob R,glob E} /\ limit0{1}=limit{2}).
 + wp; call(keygen_attempt_f_realized_equiv E).
   call (_: ={glob R} ==> ={res,glob R}); first by sim.
   auto.
 by auto=> />; rewrite /retry_initial /=.
qed.
lemma bounded_g_result_equiv (R <:KeygenSeedRNG) (E <:KeygenExpand {-R}) :
 equiv[BoundedRetry(R,E).g ~ ResultRetry(R,E).g :
 ={limit,glob R,glob E} ==> ={res,glob R,glob E}].
proof.
 proc; inline BoundedRetry(R,E).g_from; wp.
 while(={buf,ntt,inverse,status,count,glob R,glob E} /\ limit0{1}=limit{2}).
 + wp; call(keygen_attempt_g_realized_equiv E).
   call (_: ={glob R} ==> ={res,glob R}); first by sim.
   auto.
 by auto=> />; rewrite /retry_initial /=.
qed.

lemma bounded_paired_f_result_equiv (P <:ProposalPort {-PairPorts}) :
 equiv[BoundedRetry(PairPorts(P),PairPorts(P)).f ~ ResultRetry(PairPorts(P),PairPorts(P)).f :
 ={limit,glob P,PairPorts.pending} ==> ={res,glob P,PairPorts.pending}].
proof.
 proc; inline BoundedRetry(PairPorts(P),PairPorts(P)).f_from; wp.
 while(={buf,ntt,inverse,status,count,glob P,PairPorts.pending} /\ limit0{1}=limit{2}).
 + wp; call(keygen_attempt_f_realized_equiv (PairPorts(P))).
   call (_: ={glob P,PairPorts.pending} ==> ={res,glob P,PairPorts.pending}); first by sim.
   auto.
 by auto=> />; rewrite /retry_initial /=.
qed.
lemma bounded_paired_g_result_equiv (P <:ProposalPort {-PairPorts}) :
 equiv[BoundedRetry(PairPorts(P),PairPorts(P)).g ~ ResultRetry(PairPorts(P),PairPorts(P)).g :
 ={limit,glob P,PairPorts.pending} ==> ={res,glob P,PairPorts.pending}].
proof.
 proc; inline BoundedRetry(PairPorts(P),PairPorts(P)).g_from; wp.
 while(={buf,ntt,inverse,status,count,glob P,PairPorts.pending} /\ limit0{1}=limit{2}).
 + wp; call(keygen_attempt_g_realized_equiv (PairPorts(P))).
   call (_: ={glob P,PairPorts.pending} ==> ={res,glob P,PairPorts.pending}); first by sim.
   auto.
 by auto=> />; rewrite /retry_initial /=.
qed.

lemma result_rom_f_bridge c qb q0 :
 equiv[ResultRetry(UniformSeedRNG,ExpandROM).f ~
       ResultRetry(PairPorts(ROMProposal),PairPorts(ROMProposal)).f :
 0<=q0 /\ c+q0<=qb /\ limit{1}=q0 /\ ={limit,glob ROE} /\ ROMProposal.n{2}=c /\ ROMProposal.q{2}=qb ==>
 ={res,glob ROE} /\ ROMProposal.n{2}=c+res.`rs_count{2} /\
 ROMProposal.q{2}=qb /\ 0<=res.`rs_count{2}<=q0].
proof.
 proc.
 while(0<=q0 /\ c+q0<=qb /\ ={limit,buf,ntt,inverse,status,count,glob ROE} /\ limit{1}=q0 /\
  ROMProposal.n{2}=c+count{2} /\ ROMProposal.q{2}=qb /\ 0<=count{2}<=q0).
 + inline AttemptResult(ExpandROM).f AttemptResult(PairPorts(ROMProposal)).f.
   inline UniformSeedRNG.sample ExpandROM.shake PairPorts(ROMProposal).sample PairPorts(ROMProposal).shake ROMProposal.draw.
   rcondt{2} 3; first by auto=> />; smt().
   wp; call (_: ={input,glob ROE} ==> ={res,glob ROE}); first by sim.
   by auto=> />; smt().
 by auto=> />; smt().
qed.

lemma result_rom_g_bridge c qb q0 :
 equiv[ResultRetry(UniformSeedRNG,ExpandROM).g ~
       ResultRetry(PairPorts(ROMProposal),PairPorts(ROMProposal)).g :
 0<=q0 /\ c+q0<=qb /\ limit{1}=q0 /\ ={limit,glob ROE} /\ ROMProposal.n{2}=c /\ ROMProposal.q{2}=qb ==>
 ={res,glob ROE} /\ ROMProposal.n{2}=c+res.`rs_count{2} /\
 ROMProposal.q{2}=qb /\ 0<=res.`rs_count{2}<=q0].
proof.
 proc.
 while(0<=q0 /\ c+q0<=qb /\ ={limit,buf,ntt,inverse,status,count,glob ROE} /\ limit{1}=q0 /\
  ROMProposal.n{2}=c+count{2} /\ ROMProposal.q{2}=qb /\ 0<=count{2}<=q0).
 + inline AttemptResult(ExpandROM).g AttemptResult(PairPorts(ROMProposal)).g.
   inline UniformSeedRNG.sample ExpandROM.shake PairPorts(ROMProposal).sample PairPorts(ROMProposal).shake ROMProposal.draw.
   rcondt{2} 3; first by auto=> />; smt().
   wp; call (_: ={input,glob ROE} ==> ={res,glob ROE}); first by sim.
   by auto=> />; smt().
 by auto=> />; smt().
qed.

lemma result_fresh_f_bridge c qb q0 :
 equiv[ResultRetry(UniformSeedRNG,FreshExpand).f ~
       ResultRetry(PairPorts(FreshProposal),PairPorts(FreshProposal)).f :
 0<=q0 /\ c+q0<=qb /\ limit{1}=q0 /\ ={limit} /\ FreshProposal.n{2}=c /\ FreshProposal.q{2}=qb ==>
 ={res} /\ FreshProposal.n{2}=c+res.`rs_count{2} /\
 FreshProposal.q{2}=qb /\ 0<=res.`rs_count{2}<=q0].
proof.
 proc.
 while(0<=q0 /\ c+q0<=qb /\ ={limit,buf,ntt,inverse,status,count} /\ limit{1}=q0 /\
  FreshProposal.n{2}=c+count{2} /\ FreshProposal.q{2}=qb /\ 0<=count{2}<=q0).
 + inline AttemptResult(FreshExpand).f AttemptResult(PairPorts(FreshProposal)).f.
   inline UniformSeedRNG.sample FreshExpand.shake PairPorts(FreshProposal).sample PairPorts(FreshProposal).shake FreshProposal.draw.
   rcondt{2} 3; first by auto=> />; smt().
   by auto=> />; smt().
 by auto=> />; smt().
qed.

lemma result_fresh_g_bridge c qb q0 :
 equiv[ResultRetry(UniformSeedRNG,FreshExpand).g ~
       ResultRetry(PairPorts(FreshProposal),PairPorts(FreshProposal)).g :
 0<=q0 /\ c+q0<=qb /\ limit{1}=q0 /\ ={limit} /\ FreshProposal.n{2}=c /\ FreshProposal.q{2}=qb ==>
 ={res} /\ FreshProposal.n{2}=c+res.`rs_count{2} /\
 FreshProposal.q{2}=qb /\ 0<=res.`rs_count{2}<=q0].
proof.
 proc.
 while(0<=q0 /\ c+q0<=qb /\ ={limit,buf,ntt,inverse,status,count} /\ limit{1}=q0 /\
  FreshProposal.n{2}=c+count{2} /\ FreshProposal.q{2}=qb /\ 0<=count{2}<=q0).
 + inline AttemptResult(FreshExpand).g AttemptResult(PairPorts(FreshProposal)).g.
   inline UniformSeedRNG.sample FreshExpand.shake PairPorts(FreshProposal).sample PairPorts(FreshProposal).shake FreshProposal.draw.
   rcondt{2} 3; first by auto=> />; smt().
   by auto=> />; smt().
 by auto=> />; smt().
qed.

module ResultStoppedKeygen(R:KeygenSeedRNG,E:KeygenExpand) = {
 proc run(qf:int,qg:int,workspace:W8.t Array14466.t) : stopped_output = {
  var fv,gv:retry_state; var result:keygen_output option; var out:keygen_output;
  result <- None; gv <- retry_initial;
  fv <@ ResultRetry(R,E).f(qf);
  if (fv.`rs_ok) {
   gv <@ ResultRetry(R,E).g(qg);
   if (gv.`rs_ok) {
    out <@ ObservedFinish.run(fv,gv,workspace); result <- Some out;
   }
  }
  return(result,fv.`rs_count,gv.`rs_count);
 }
}.
lemma stopped_result_equiv (R <:KeygenSeedRNG {-ROF}) (E <:KeygenExpand {-R,-ROF}) :
 equiv[StoppedKeygen(R,E).run ~ ResultStoppedKeygen(R,E).run :
 ={qf,qg,workspace,glob R,glob E,glob ROF} ==> ={res,glob R,glob E,glob ROF}].
proof.
 proc.
 seq 3 3 : (={qg,workspace,fv,gv,result,glob R,glob E,glob ROF}).
 + call(bounded_f_result_equiv R E); auto.
 if; 1,3: by auto.
 seq 1 1 : (={workspace,fv,gv,result,glob R,glob E,glob ROF}).
 + call(bounded_g_result_equiv R E); auto.
 if; 1,3: by auto.
 wp; call (_: ={fv,gv,workspace,glob ROF} ==> ={res,glob ROF}); first by sim.
 auto.
qed.
lemma stopped_paired_result_equiv (P <:ProposalPort {-PairPorts,-ROF}) :
 equiv[StoppedKeygen(PairPorts(P),PairPorts(P)).run ~ ResultStoppedKeygen(PairPorts(P),PairPorts(P)).run :
 ={qf,qg,workspace,glob P,PairPorts.pending,glob ROF} ==>
 ={res,glob P,PairPorts.pending,glob ROF}].
proof.
 proc.
 seq 3 3 : (={qg,workspace,fv,gv,result,glob P,PairPorts.pending,glob ROF}).
 + call(bounded_paired_f_result_equiv P); auto.
 if; 1,3: by auto.
 seq 1 1 : (={workspace,fv,gv,result,glob P,PairPorts.pending,glob ROF}).
 + call(bounded_paired_g_result_equiv P); auto.
 if; 1,3: by auto.
 wp; call (_: ={fv,gv,workspace,glob ROF} ==> ={res,glob ROF}); first by sim.
 auto.
qed.

lemma result_stopped_rom_bridge :
 equiv[ResultStoppedKeygen(UniformSeedRNG,ExpandROM).run ~
       ResultStoppedKeygen(PairPorts(ROMProposal),PairPorts(ROMProposal)).run :
 ={qf,qg,workspace,glob ROE,glob ROF} /\ 0<=qf{1} /\ 0<=qg{1} /\
 ROMProposal.n{2}=0 /\ ROMProposal.q{2}=qf{1}+qg{1} ==>
 ={res,glob ROE,glob ROF}].
proof.
 proc.
 seq 3 3 : (={qf,qg,workspace,fv,gv,result,glob ROE,glob ROF} /\
  0<=qf{1} /\ 0<=qg{1} /\ ROMProposal.n{2}=fv.`rs_count{2} /\
  ROMProposal.q{2}=qf{1}+qg{1} /\ 0<=fv.`rs_count{2}<=qf{1}).
 + ecall(result_rom_f_bridge 0 (qf{1}+qg{1}) qf{1}); auto=> />; smt().
 if; 1,3: by auto.
 seq 1 1 : (={workspace,fv,gv,result,glob ROE,glob ROF}).
 + ecall(result_rom_g_bridge fv.`rs_count{2} (qf{1}+qg{1}) qg{1}); auto=> />; smt().
 if; 1,3: by auto.
 wp; call (_: ={fv,gv,workspace,glob ROF} ==> ={res,glob ROF}); first by sim.
 auto.
qed.

lemma result_stopped_fresh_bridge :
 equiv[ResultStoppedKeygen(UniformSeedRNG,FreshExpand).run ~
       ResultStoppedKeygen(PairPorts(FreshProposal),PairPorts(FreshProposal)).run :
 ={qf,qg,workspace,glob ROF} /\ 0<=qf{1} /\ 0<=qg{1} /\
 FreshProposal.n{2}=0 /\ FreshProposal.q{2}=qf{1}+qg{1} ==>
 ={res,glob ROF}].
proof.
 proc.
 seq 3 3 : (={qf,qg,workspace,fv,gv,result,glob ROF} /\
  0<=qf{1} /\ 0<=qg{1} /\ FreshProposal.n{2}=fv.`rs_count{2} /\
  FreshProposal.q{2}=qf{1}+qg{1} /\ 0<=fv.`rs_count{2}<=qf{1}).
 + ecall(result_fresh_f_bridge 0 (qf{1}+qg{1}) qf{1}); auto=> />; smt().
 if; 1,3: by auto.
 seq 1 1 : (={workspace,fv,gv,result,glob ROF}).
 + ecall(result_fresh_g_bridge fv.`rs_count{2} (qf{1}+qg{1}) qg{1}); auto=> />; smt().
 if; 1,3: by auto.
 wp; call (_: ={fv,gv,workspace,glob ROF} ==> ={res,glob ROF}); first by sim.
 auto.
qed.

lemma stopped_rom_proposal_bridge :
 equiv[StoppedKeygen(UniformSeedRNG,ExpandROM).run ~
       StoppedKeygen(PairPorts(ROMProposal),PairPorts(ROMProposal)).run :
 ={qf,qg,workspace,glob ROE,glob ROF} /\ 0<=qf{1} /\ 0<=qg{1} /\
 ROMProposal.n{2}=0 /\ ROMProposal.q{2}=qf{1}+qg{1} ==>
 ={res,glob ROE,glob ROF}].
proof.
 transitivity ResultStoppedKeygen(UniformSeedRNG,ExpandROM).run
  (={qf,qg,workspace,glob ROE,glob ROF} ==> ={res,glob ROE,glob ROF})
  (={qf,qg,workspace,glob ROE,glob ROF} /\ 0<=qf{1} /\ 0<=qg{1} /\
   ROMProposal.n{2}=0 /\ ROMProposal.q{2}=qf{1}+qg{1} ==> ={res,glob ROE,glob ROF}) => //.
 + smt().
 + exact (stopped_result_equiv UniformSeedRNG ExpandROM).
 transitivity ResultStoppedKeygen(PairPorts(ROMProposal),PairPorts(ROMProposal)).run
  (={qf,qg,workspace,glob ROE,glob ROF} /\ 0<=qf{1} /\ 0<=qg{1} /\
   ROMProposal.n{2}=0 /\ ROMProposal.q{2}=qf{1}+qg{1} ==> ={res,glob ROE,glob ROF})
  (={qf,qg,workspace,glob ROMProposal,PairPorts.pending,glob ROF} ==>
   ={res,glob ROMProposal,PairPorts.pending,glob ROF}) => //.
 + smt().
 + exact result_stopped_rom_bridge.
 symmetry; conseq (stopped_paired_result_equiv ROMProposal); smt().
qed.
lemma stopped_fresh_proposal_bridge :
 equiv[StoppedKeygen(UniformSeedRNG,FreshExpand).run ~
       StoppedKeygen(PairPorts(FreshProposal),PairPorts(FreshProposal)).run :
 ={qf,qg,workspace,glob ROF} /\ 0<=qf{1} /\ 0<=qg{1} /\
 FreshProposal.n{2}=0 /\ FreshProposal.q{2}=qf{1}+qg{1} ==>
 ={res,glob ROF}].
proof.
 transitivity ResultStoppedKeygen(UniformSeedRNG,FreshExpand).run
  (={qf,qg,workspace,glob ROF} ==> ={res,glob ROF})
  (={qf,qg,workspace,glob ROF} /\ 0<=qf{1} /\ 0<=qg{1} /\
   FreshProposal.n{2}=0 /\ FreshProposal.q{2}=qf{1}+qg{1} ==> ={res,glob ROF}) => //.
 + smt().
 + exact (stopped_result_equiv UniformSeedRNG FreshExpand).
 transitivity ResultStoppedKeygen(PairPorts(FreshProposal),PairPorts(FreshProposal)).run
  (={qf,qg,workspace,glob ROF} /\ 0<=qf{1} /\ 0<=qg{1} /\
   FreshProposal.n{2}=0 /\ FreshProposal.q{2}=qf{1}+qg{1} ==> ={res,glob ROF})
  (={qf,qg,workspace,glob FreshProposal,PairPorts.pending,glob ROF} ==>
   ={res,glob FreshProposal,PairPorts.pending,glob ROF}) => //.
 + smt().
 + exact result_stopped_fresh_bridge.
 symmetry; conseq (stopped_paired_result_equiv FreshProposal); smt().
qed.
