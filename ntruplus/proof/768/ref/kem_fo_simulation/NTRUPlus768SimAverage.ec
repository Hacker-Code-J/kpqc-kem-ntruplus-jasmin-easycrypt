require import AllCore Distr RealSeries StdOrder.
require import NTRUPlus768ACWC2WorstCase.
require import NTRUPlus768FOSetupDistribution NTRUPlus768FOSetupExpectation NTRUPlus768FOGameAverage.
import RealOrder RField.

lemma sim_affine_range (C Q x:real) :
 0%r<=C=>0%r<=Q=>0%r<=x<=1%r=>0%r<=C+Q*x<=C+Q.
proof. smt(). qed.
lemma sim_add_le (C x y:real) : x<=y=>C+x<=C+y.
proof. smt(). qed.

(* Generic averaging only. Its pointwise premise is discharged by the
   concrete adaptive comparison, after which the actual setup law gives
   the numerical bound. No weak-spread average is used pointwise. *)
lemma sim_setup_distance_average ['a] &m
 (K0 K1:fo_setup_observation->'a distr) event (C Q:real) :
 0%r<=C=>0%r<=Q=>
 (forall s,s \in mk(fun z=>Pr[FOSetupSource.guess(witness) @ &m:res=z])=>
  `|mu(K0 s)event-mu(K1 s)event|<=C+Q*fo_setup_error s)=>
 `|mu(dlet(mk(fun z=>Pr[FOSetupSource.guess(witness) @ &m:res=z]))K0)event-
   mu(dlet(mk(fun z=>Pr[FOSetupSource.guess(witness) @ &m:res=z]))K1)event|
 <=C+Q/(2%r^353).
proof.
 move=>hC hQ hp.
 pose d:=mk(fun z=>Pr[FOSetupSource.guess(witness) @ &m:res=z]).
 have h0:hasE d(fun _=>C) by apply hasEC.
 have h1:hasE d(fun s=>Q*fo_setup_error s) by apply hasEZ;exact(fo_setup_error_hasE d).
 have hs:hasE d(fun s=>C+Q*fo_setup_error s).
 + apply(acwc2_bounded_hasE d _ (C+Q));first by smt().
   move=>s.
   exact(sim_affine_range C Q (fo_setup_error s) hC hQ (fo_setup_error_range s)).
 have ha:=fo_kernel_distance_average d K0 K1 event _ hs hp.
 have hll:is_lossless d by exact(fo_setup_law_lossless &m witness).
 move:ha;rewrite(expD d _ _ h0 h1) expC hll /= expZ=>ha.
 have he:=fo_setup_error_expectation &m.
 have hm:=ler_wpmul2l Q hQ _ _ (ltrW _ _ he).
 have hn:E d fo_setup_error=E(mk(fun z=>Pr[FOSetupSource.guess(witness) @ &m:res=z]))fo_setup_error by done.
 move:ha;rewrite hn=>ha.
 have har:Q*(1%r/(2%r^353))=Q/(2%r^353) by ring.
 move:hm;rewrite har=>hm.
 exact(ler_trans _ _ _ ha (sim_add_le C _ _ hm)).
qed.

lemma sim_setup_win_distance &m (K0 K1:fo_setup_observation->bool distr) qD qH :
 0<=qD=>0<=qH=>
 (forall s,s \in mk(fun z=>Pr[FOSetupSource.guess(witness) @ &m:res=z])=>
  `|mu1(K0 s)true-mu1(K1 s)true|<=qD%r/(2%r^768)+(qH+qD)%r*fo_setup_error s)=>
 `|mu1(dlet(mk(fun z=>Pr[FOSetupSource.guess(witness) @ &m:res=z]))K0)true-
   mu1(dlet(mk(fun z=>Pr[FOSetupSource.guess(witness) @ &m:res=z]))K1)true|
 <=qD%r/(2%r^768)+(qH+qD)%r/(2%r^353).
proof.
 move=>hd hh hp;apply(sim_setup_distance_average &m K0 K1 (pred1 true) (qD%r/(2%r^768)) (qH+qD)%r)=> //.
 + clear hp;have hpos:0%r<2%r^768 by smt(expr_gt0).
   apply divr_ge0;smt().
 smt().
qed.
