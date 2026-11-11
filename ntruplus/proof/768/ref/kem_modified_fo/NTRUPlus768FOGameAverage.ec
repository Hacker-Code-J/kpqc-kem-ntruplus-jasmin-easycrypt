require import AllCore Distr RealSeries StdOrder.
require import NTRUPlus768ACWC2WorstCase.
require import NTRUPlus768FOSetupDistribution NTRUPlus768FOSetupExpectation.
import RealOrder RField.

(* Every kernel may be a subdistribution. These identities preserve its
   returning event mass; no normalization by termination is performed. *)
lemma fo_kernel_event_expectation ['a 'b] (d:'a distr) (K:'a->'b distr) event :
 mu(dlet d K)event=E d(fun x=>mu(K x)event).
proof. rewrite dletE /E; apply eq_sum=>x /=; ring. qed.
lemma fo_kernel_event_hasE ['a 'b] (d:'a distr) (K:'a->'b distr) event :
 hasE d(fun x=>mu(K x)event).
proof.
 apply(acwc2_bounded_hasE d _ 1%r)=> // x; exact(mu_bounded (K x)event).
qed.
lemma fo_event_difference_range ['a] (d0 d1:'a distr) event :
 0%r<=`|mu d0 event-mu d1 event|<=1%r.
proof.
 have h0:=mu_bounded d0 event.
 have h1:=mu_bounded d1 event.
 have hn:=normr_ge0 (mu d0 event-mu d1 event).
 have hu:`|mu d0 event-mu d1 event|<=1%r by rewrite ler_norml; smt().
 smt().
qed.

lemma fo_kernel_distance_average ['a 'b] (d:'a distr) (K0 K1:'a->'b distr)
 event (bound:'a->real) :
 hasE d bound =>
 (forall x,x \in d=>`|mu(K0 x)event-mu(K1 x)event|<=bound x) =>
 `|mu(dlet d K0)event-mu(dlet d K1)event|<=E d bound.
proof.
 move=>hb hpoint.
 have h0:=fo_kernel_event_hasE d K0 event.
 have h1:=fo_kernel_event_hasE d K1 event.
 have hd:hasE d(fun x=>mu(K0 x)event-mu(K1 x)event).
 + apply(hasE_le d _ (fun _=>1%r) (hasEC d 1%r))=>x.
   rewrite normr1; have h:=fo_event_difference_range (K0 x)(K1 x)event; smt().
 have ha:hasE d(fun x=>`|mu(K0 x)event-mu(K1 x)event|).
 + apply(acwc2_bounded_hasE d _ 1%r)=> // x.
   exact(fo_event_difference_range (K0 x)(K1 x)event).
 rewrite !fo_kernel_event_expectation -(expB d _ _ h0 h1).
 have hn:=exp_norm d _ hd.
 have he:=in_ler_exp d _ _ ha hb hpoint.
 exact(ler_trans _ _ _ hn he).
qed.

(* The actual setup law retains the key/F-cache pair and the independent
   pads. The pointwise premise is required only on that law's support. *)
lemma fo_setup_kernel_event_distance ['a] &m
 (K0 K1:fo_setup_observation->'a distr) event (Q:real) :
 0%r<=Q =>
 (forall s,s \in mk(fun z=>Pr[FOSetupSource.guess(witness) @ &m:res=z]) =>
   `|mu(K0 s)event-mu(K1 s)event|<=Q*fo_setup_error s) =>
 `|mu(dlet(mk(fun z=>Pr[FOSetupSource.guess(witness) @ &m:res=z]))K0)event-
   mu(dlet(mk(fun z=>Pr[FOSetupSource.guess(witness) @ &m:res=z]))K1)event|
 <=Q/(2%r^353).
proof.
 move=>hQ hpoint.
 have hh:hasE(mk(fun z=>Pr[FOSetupSource.guess(witness) @ &m:res=z]))
   (fun s=>Q*fo_setup_error s).
 + apply hasEZ; exact(fo_setup_error_hasE _).
 have ha:=fo_kernel_distance_average _ K0 K1 event (fun s=>Q*fo_setup_error s) hh hpoint.
 rewrite expZ in ha.
 have hn:=fo_setup_error_expectation &m.
 have hm:=ler_wpmul2l Q hQ _ _ (ltrW _ _ hn).
 have he:Q*(1%r/(2%r^353))=Q/(2%r^353) by ring.
 move:hm; rewrite he=>hm.
 exact(ler_trans _ _ _ ha hm).
qed.

lemma fo_setup_kernel_win_distance &m
 (K0 K1:fo_setup_observation->bool distr) (q:int) :
 0<=q =>
 (forall s,s \in mk(fun z=>Pr[FOSetupSource.guess(witness) @ &m:res=z]) =>
   `|mu1(K0 s)true-mu1(K1 s)true|<=q%r*fo_setup_error s) =>
 `|mu1(dlet(mk(fun z=>Pr[FOSetupSource.guess(witness) @ &m:res=z]))K0)true-
   mu1(dlet(mk(fun z=>Pr[FOSetupSource.guess(witness) @ &m:res=z]))K1)true|
 <=q%r/(2%r^353).
proof.
 move=>hq hpoint; apply(fo_setup_kernel_event_distance &m K0 K1 (pred1 true) q%r).
 + smt().
 exact hpoint.
qed.
