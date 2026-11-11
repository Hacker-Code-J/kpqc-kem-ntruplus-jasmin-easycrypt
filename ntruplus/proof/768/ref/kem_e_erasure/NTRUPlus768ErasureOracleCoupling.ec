require import AllCore List Distr FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152.
require import NTRUPlus768ROMDomains NTRUPlus768ROMDistributions NTRUPlus768ROMOracles.
require import NTRUPlus768CCAQueryCodec NTRUPlus768CCAOraclePorts.
require import NTRUPlus768RawXOFSampling NTRUPlus768RawXOFStreams NTRUPlus768RawXOF.
require import NTRUPlus768ErasureModel NTRUPlus768ErasureBudget.

lemma erasure_tables_set s m1 m2 x y : erasure_tables_agree s m1 m2 =>
 erasure_tables_agree s m1.[x<-y] m2.[x<-y].
proof.
 move=>h z hz; rewrite !get_setE; case(z=x)=>he //.
 exact(h z hz).
qed.


lemma erasure_tables_mem s m1 m2 x : erasure_tables_agree s m1 m2 =>
 !(List.mem s x) => (x \in m1)=(x \in m2).
proof. move=>h hx; by rewrite !domE (h x hx). qed.

lemma erasure_roe_agree s :
 equiv[ROE.get ~ ROE.get:
 ={input} /\ !(List.mem s input{1}) /\ erasure_tables_agree s ROE.m{1} ROE.m{2} ==>
 ={res} /\ erasure_tables_agree s ROE.m{1} ROE.m{2}].
proof.
 proc; if.
 + auto=> /> &1 &2 hx hm; have he:=erasure_tables_mem s _ _ _ hm hx; smt().
 + auto=> /> &1 &2 hx hm hmiss y hy.
   split; first by rewrite !get_set_sameE.
   exact(erasure_tables_set s _ _ _ _ hm).
 auto=> /> &1 &2 hx hm hhit.
 by rewrite (hm input{2} hx).
qed.

lemma erasure_shared_e_agree s :
 equiv[SharedCCAOracles.e ~ SharedCCAOracles.e:
 ={input} /\ !(List.mem s input{1}) /\ erasure_tables_agree s ROE.m{1} ROE.m{2} ==>
 ={res} /\ erasure_tables_agree s ROE.m{1} ROE.m{2}].
proof. proc; call(erasure_roe_agree s); auto. qed.

lemma erasure_raw_e_agree s :
 equiv[RawXOFStreams.e ~ RawXOFStreams.e:
 ={input,RawXOFStreams.es} /\ !(List.mem s input{1}) /\
 erasure_tables_agree s ROE.m{1} ROE.m{2} ==>
 ={res,RawXOFStreams.es} /\ erasure_tables_agree s ROE.m{1} ROE.m{2}].
proof.
 proc.
 seq 1 1:(={input,prefix,RawXOFStreams.es} /\ erasure_tables_agree s ROE.m{1} ROE.m{2}).
 + call(erasure_shared_e_agree s); auto.
 if; auto.
qed.

op erasure_full_safe (s:erasure_seed list) (input:W8.t list) =
 forall seed,decode_typed input=Some(E seed)=>!(List.mem s seed).
op erasure_get_safe (s:erasure_seed list) (input:W8.t list) outlen =
 forall seed,erasure_raw_seed input outlen=Some seed=>!(List.mem s seed).

lemma erasure_get_safe_full s input outlen :
 0<=outlen<=raw_xof_max_output =>erasure_get_safe s input outlen=>erasure_full_safe s input.
proof.
 move=>hn hs seed hd.
 have he:=decode_typed_sound input (E seed) hd.
 have hseed:erasure_raw_seed input outlen=Some seed.
 + rewrite -he; exact(erasure_raw_seed_e seed outlen hn).
 exact(hs seed hseed).
qed.

(* The suffix fields are listed separately. Taking glob RawXOFStreams
   here could accidentally demand equality of its transitive E state. *)
lemma erasure_raw_full_agree s :
 equiv[RawXOF.full ~ RawXOF.full:
 ={input,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other} /\
 erasure_full_safe s input{1} /\ erasure_tables_agree s ROE.m{1} ROE.m{2} ==>
 ={res,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other} /\
 erasure_tables_agree s ROE.m{1} ROE.m{2}].
proof.
 proc; match; 1,2:by auto; smt().
 + inline RawXOFStreams.untyped; sp; if; auto=> />; smt().
 move=>q1 q2; match; 1..4:by auto; smt().
 + move=>seed1 seed2; call(erasure_raw_e_agree s); auto=> />; rewrite /erasure_full_safe; smt().
 + move=>pk1 pk2; call (_: ={input,ROF.m,RawXOFStreams.fs} ==> ={res,ROF.m,RawXOFStreams.fs}).
   - by sim.
   auto=> />; smt().
 + move=>g1 g2; call (_: ={input,ROG.m,RawXOFStreams.gs} ==> ={res,ROG.m,RawXOFStreams.gs}).
   - by sim.
   auto=> />; smt().
 move=>h1 h2; call (_: ={input,ROH.m} ==> ={res,ROH.m}).
 + by sim.
 auto=> />; smt().
qed.

lemma erasure_raw_get_agree s :
 equiv[RawXOF.get ~ RawXOF.get:
 ={input,outlen,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other} /\
 erasure_get_safe s input{1} outlen{1} /\ erasure_tables_agree s ROE.m{1} ROE.m{2} ==>
 ={res,ROF.m,ROG.m,ROH.m,RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other} /\
 erasure_tables_agree s ROE.m{1} ROE.m{2}].
proof.
 proc; sp; if; 1,3:by auto.
 wp; call(erasure_raw_full_agree s); auto=> />.
 move=> &1 &2 hs hm h0 h224.
 have hn:0<=outlen{2}<=raw_xof_max_output by smt().
 exact(erasure_get_safe_full s _ _ hn hs).
qed.

lemma erasure_cap_e_upto s :
 equiv[CapEPort(SharedCCAExtendedOracles).e ~ CapEPort(SharedCCAExtendedOracles).e:
 ={input,glob EBudgetState} /\
 ErasureSeedLog.used{1}=s /\ ErasureSeedLog.used{2}=s /\
 !ErasureHit.bad{1} /\ !ErasureHit.bad{2} /\
 erasure_tables_agree s ROE.m{1} ROE.m{2} ==>
 ={ErasureHit.bad} /\ (!ErasureHit.bad{2} =>
 ={res,glob EBudgetState} /\ erasure_tables_agree s ROE.m{1} ROE.m{2})].
proof.
 proc; inline ErasureBudgetMonitor.request; sp; if; 1,3:by auto; smt().
 inline ErasureBudgetMonitor.forward ErasureHit.mark; sp.
 case(ErasureHit.bad{2}).
 + call{1} cca_extended_e_ll; call{2} cca_extended_e_ll; auto=> />; smt().
 call(erasure_shared_e_agree s); auto=> />; smt().
qed.

lemma erasure_cap_raw_upto s :
 equiv[CapEPort(SharedCCAExtendedOracles).raw ~ CapEPort(SharedCCAExtendedOracles).raw:
 ={input,outlen,glob EBudgetState,ROF.m,ROG.m,ROH.m,
 RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other} /\
 ErasureSeedLog.used{1}=s /\ ErasureSeedLog.used{2}=s /\
 !ErasureHit.bad{1} /\ !ErasureHit.bad{2} /\
 erasure_tables_agree s ROE.m{1} ROE.m{2} ==>
 ={ErasureHit.bad} /\ (!ErasureHit.bad{2} =>
 ={res,glob EBudgetState,ROF.m,ROG.m,ROH.m,
 RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other} /\
 erasure_tables_agree s ROE.m{1} ROE.m{2})].
proof.
 proc.
 seq 4 4:(={input,outlen,seed,allowed,result,glob EBudgetState,ROF.m,ROG.m,ROH.m,
 RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other} /\
 seed{1}=erasure_raw_seed input{1} outlen{1} /\
 ErasureSeedLog.used{1}=s /\ ErasureSeedLog.used{2}=s /\
 !ErasureHit.bad{1} /\ !ErasureHit.bad{2} /\
 erasure_tables_agree s ROE.m{1} ROE.m{2}).
 + inline ErasureBudgetMonitor.request; auto=> />; smt().
 if; 1,3:by auto; smt().
 seq 1 1:(={input,outlen,glob EBudgetState,ErasureHit.bad,ROF.m,ROG.m,ROH.m,
 RawXOFStreams.es,RawXOFStreams.fs,RawXOFStreams.gs,RawXOFStreams.other} /\
 (!ErasureHit.bad{2} => erasure_get_safe s input{1} outlen{1} /\
 erasure_tables_agree s ROE.m{1} ROE.m{2})).
 + inline ErasureBudgetMonitor.forward ErasureHit.mark; auto=> />;
   rewrite /erasure_get_safe; smt().
 case(ErasureHit.bad{2}).
 + call{1} cca_extended_raw_ll; call{2} cca_extended_raw_ll; auto=> />; smt().
 call(erasure_raw_get_agree s); auto=> />; smt().
qed.

lemma erasure_cap_e_bad :
 phoare[CapEPort(SharedCCAExtendedOracles).e:ErasureHit.bad ==>ErasureHit.bad]=1%r.
proof.
 conseq cap_shared_e_ll (_:ErasureHit.bad ==>ErasureHit.bad)=>//.
 proc; inline ErasureBudgetMonitor.request; sp; if; last by auto.
 call(_:true ==>true); first by trivial.
 inline ErasureBudgetMonitor.forward ErasureHit.mark; auto=> />; smt().
qed.
lemma erasure_cap_raw_bad :
 phoare[CapEPort(SharedCCAExtendedOracles).raw:ErasureHit.bad ==>ErasureHit.bad]=1%r.
proof.
 conseq cap_shared_raw_ll (_:ErasureHit.bad ==>ErasureHit.bad)=>//.
 proc; seq 4:ErasureHit.bad.
 + inline ErasureBudgetMonitor.request; auto.
 if; last by auto.
 call(_:true ==>true); first by trivial.
 inline ErasureBudgetMonitor.forward ErasureHit.mark; auto=> />; smt().
qed.
