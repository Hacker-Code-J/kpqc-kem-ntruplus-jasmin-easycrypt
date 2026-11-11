require import AllCore Distr FMap SDist.
from Jasmin require import JWord.
require import Array14466.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768ROMOracles.
require import NTRUPlus768CCASetupState.

clone SDist.GenDist as CCASetupDist with
 type in_t <- W8.t Array14466.t,
 type out_t <- cca_setup_state
 proof *.
clone SDist.Dist as CCASetupObserverDist with
 type a <- cca_setup_state
 proof *.

lemma cca_setup_source_sample (S<:CCASetupDist.Distinguisher) &m :
 equiv[S.guess ~ CCASetupDist.S.sample :
  x{1}=witness /\ (glob S){1}=(glob S){m} /\
  d{2}=mk(fun z=>Pr[S.guess(witness) @ &m:res=z]) ==> ={res}].
proof.
 bypr(res{1})(res{2}) => // &1 &2 z [hx [hg hd]].
 rewrite hx hd CCASetupDist.sampleE -(CCASetupDist.adv_mu1 S &m z witness).
 byequiv (_: ={x,glob S} ==> ={res}) => //.
 proc true; auto.
qed.

lemma cca_setup_source_mu (E<:KeygenExpand) &m (event:cca_setup_state->bool) :
 Pr[JointSetupSource(E).guess(witness) @ &m:event res]=
 mu (mk(fun z=>Pr[JointSetupSource(E).guess(witness) @ &m:res=z])) event.
proof.
 have hs:Pr[CCASetupDist.S.sample(mk(fun z=>Pr[JointSetupSource(E).guess(witness) @ &m:res=z]))
  @ &m:event res]=mu (mk(fun z=>Pr[JointSetupSource(E).guess(witness) @ &m:res=z])) event.
 + byphoare (_: d=mk(fun z=>Pr[JointSetupSource(E).guess(witness) @ &m:res=z]) ==> _) => //.
   proc; rnd; auto.
 rewrite -hs.
 by byequiv(cca_setup_source_sample (JointSetupSource(E)) &m) => //.
qed.

lemma cca_setup_source_law_ll (E<:KeygenExpand) &m :
 islossless JointSetupSource(E).guess =>
 is_lossless(mk(fun z=>Pr[JointSetupSource(E).guess(witness) @ &m:res=z])).
proof.
 move=>hll; rewrite /is_lossless.
 rewrite -(cca_setup_source_mu E &m predT).
 by byphoare hll.
qed.

lemma cca_setup_event_sdist (E1<:KeygenExpand) (E2<:KeygenExpand) &m eps :
 (forall (event:cca_setup_state->bool),
  `|Pr[JointSetupSource(E1).guess(witness) @ &m:event res]-
    Pr[JointSetupSource(E2).guess(witness) @ &m:event res]|<=eps) =>
 sdist (mk(fun z=>Pr[JointSetupSource(E1).guess(witness) @ &m:res=z]))
       (mk(fun z=>Pr[JointSetupSource(E2).guess(witness) @ &m:res=z])) <= eps.
proof.
 move=>h; apply sdist_le_ub=>event.
 rewrite -(cca_setup_source_mu E1 &m event) -(cca_setup_source_mu E2 &m event).
 exact(h event).
qed.
