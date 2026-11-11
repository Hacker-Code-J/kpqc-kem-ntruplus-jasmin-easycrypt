require import AllCore Distr DBool TotalProb StdOrder.
require import NTRUPlus768FOSetupDistribution.
import RealOrder RField.

(* A private fair-bit comparison converts a difference of returning event
   probabilities into a PH interval. It is used only in this proof transport. *)
clone TotalProb.TotalBool as SimSequentialTotalBool with type input <- fo_setup_observation proof *.
module type SimSequentialPhases = { proc phase(i:fo_setup_observation,b:bool):bool }.
module type SimSequentialSystem = {
 proc setup(i:fo_setup_observation):unit
 proc phase(i:fo_setup_observation,b:bool):bool
}.
module SimSequentialDifference(P:SimSequentialPhases) = {
 proc main(i:fo_setup_observation,x:bool):bool = {var r;r<@P.phase(i,x);return r=x;}
}.
module SimSequentialCoin(P:SimSequentialPhases) = {
 proc run(i:fo_setup_observation):bool = {var x,r;x<$dbool;r<@P.phase(i,x);return r=x;}
}.
module SimSequentialKernel(S:SimSequentialSystem) : SimSequentialPhases = {
 proc phase(i:fo_setup_observation,b:bool):bool = {var r;S.setup(i);r<@S.phase(i,b);return r;}
}.
module SimSequentialAfterSetup(S:SimSequentialSystem) = {
 proc run(i:fo_setup_observation):bool = {var r;S.setup(i);r<@SimSequentialCoin(S).run(i);return r;}
}.
lemma sim_sequential_difference_true (P<:SimSequentialPhases) i0 &m :
 Pr[SimSequentialDifference(P).main(i0,true)@&m:res]=Pr[P.phase(i0,true)@&m:res].
proof.
 byequiv(_: i{1}=i{2} /\ x{1}=b{2} /\ b{2}=true /\ ={glob P} ==> ={res})=> //.
 proc*;inline{1} SimSequentialDifference(P).main;wp.
 call(_: ={arg,glob P} ==> ={res,glob P});first by proc true.
 auto;smt().
qed.
lemma sim_sequential_difference_false (P<:SimSequentialPhases) i0 &m :
 Pr[SimSequentialDifference(P).main(i0,false)@&m:res]=Pr[P.phase(i0,false)@&m:!res].
proof.
 byequiv(_: i{1}=i{2} /\ x{1}=b{2} /\ b{2}=false /\ ={glob P} ==> res{1}=!res{2})=> //.
 proc*;inline{1} SimSequentialDifference(P).main;wp.
 call(_: ={arg,glob P} ==> ={res,glob P});first by proc true.
 auto;smt().
qed.
lemma sim_sequential_coin_formula (P<:SimSequentialPhases) i0 &m : islossless P.phase=>
 Pr[SimSequentialCoin(P).run(i0)@&m:res]=
 (1%r+Pr[P.phase(i0,true)@&m:res]-Pr[P.phase(i0,false)@&m:res])/2%r.
proof.
 move=>hll.
 have he:Pr[SimSequentialCoin(P).run(i0)@&m:res]=Pr[SimSequentialTotalBool.Rand(SimSequentialDifference(P)).f(dbool,i0)@&m:res].
 + byequiv(_: i{1}=i{2} /\ dt{2}=dbool /\ ={glob P} ==> ={res})=> //.
   proc;inline{2} SimSequentialDifference(P).main;wp.
   call(_: ={arg,glob P} ==> ={res,glob P});first by proc true.
   auto;smt().

 rewrite he (SimSequentialTotalBool.total_prob_bool (SimSequentialDifference(P)) i0 &m) (sim_sequential_difference_true P i0 &m) (sim_sequential_difference_false P i0 &m).
 have hl:Pr[P.phase(i0,false)@&m:true]=1%r by byphoare hll.
 rewrite Pr[mu_not] hl;ring.
qed.
lemma sim_sequential_commute_setup (S<:SimSequentialSystem) i0 &m :
 Pr[SimSequentialCoin(SimSequentialKernel(S)).run(i0)@&m:res]=Pr[SimSequentialAfterSetup(S).run(i0)@&m:res].
proof.
 byequiv(_: ={i,glob S} ==> ={res})=> //.
 proc;inline{1} SimSequentialKernel(S).phase;inline{2} SimSequentialCoin(S).run.
 swap{1} 2 -1.
 swap{1} 4 -2.
 wp;call(_: ={arg,glob S} ==> ={res,glob S});first by proc true.
 wp;rnd;wp;call(_: ={arg,glob S} ==> ={glob S});first by proc true.
 auto.

qed.
lemma sim_sequential_kernel_ll (S<:SimSequentialSystem) : islossless S.setup=>islossless S.phase=>islossless SimSequentialKernel(S).phase.
proof. move=>hs hp;proc;call hp;call hs;auto. qed.
(* The initializer may randomize and modify the full shared module state.
   Its PH1 postcondition supplies the phase precondition at every reached
   memory. Only initializer/phase termination is required; there is no
   assertion here about ROM KeyGen, and no kernel-distance premise. *)
lemma sim_sequential_distance (S<:SimSequentialSystem) (I:glob S->bool) i0 gamma &m :
 phoare[S.setup:arg=i0 ==>I(glob S)]=1%r=>
 islossless S.setup=>islossless S.phase=>
 (forall &n,I(glob S){n}=>
  `|Pr[S.phase(i0,true)@&n:res]-Pr[S.phase(i0,false)@&n:res]|<=gamma)=>
 `|Pr[SimSequentialKernel(S).phase(i0,true)@&m:res]-Pr[SimSequentialKernel(S).phase(i0,false)@&m:res]|<=gamma.
proof.
 move=>hsetup hs hp hb.
 have hsh:hoare[S.setup:arg=i0 ==>I(glob S)].
 + hoare;bypr=> &n hn.
   have ht:Pr[S.setup(i0)@&n:true]=1%r by byphoare hs.
   have hg:Pr[S.setup(i0)@&n:I(glob S)]=1%r by byphoare hsetup=> //.
   rewrite hn Pr[mu_not] ht hg;ring.
 have hu:phoare[SimSequentialCoin(S).run:arg=i0 /\ I(glob S) ==>res]<=((1%r+gamma)/2%r).
 + bypr=> &n [hi hI];rewrite hi (sim_sequential_coin_formula S i0 &n hp).
   have h:=hb &n hI;rewrite ler_norml in h;smt().
 have hl:phoare[SimSequentialCoin(S).run:arg=i0 /\ I(glob S) ==>res]>=((1%r-gamma)/2%r).
 + bypr=> &n [hi hI];rewrite hi (sim_sequential_coin_formula S i0 &n hp).
   have h:=hb &n hI;rewrite ler_norml in h;smt().
 have hku:Pr[SimSequentialAfterSetup(S).run(i0)@&m:res]<=(1%r+gamma)/2%r.
 + byphoare(_:arg=i0 ==>res)=> //.
   proc;call hu.
   call hsh;auto.
 have hkl:Pr[SimSequentialAfterSetup(S).run(i0)@&m:res]>=(1%r-gamma)/2%r.
 + byphoare(_:arg=i0 ==>res)=> //.
   proc;call hl.
   call hsetup;auto.
 have hf:=sim_sequential_coin_formula (SimSequentialKernel(S)) i0 &m (sim_sequential_kernel_ll S hs hp).
 rewrite (sim_sequential_commute_setup S i0 &m) in hf.
 rewrite ler_norml;smt().
qed.

(* Useful when two guarded phases agree outside the ready-state predicate. *)
lemma sim_sequential_unconditional (S<:SimSequentialSystem) i0 gamma &m :
 islossless S.setup=>islossless S.phase=>
 (forall &n,`|Pr[S.phase(i0,true)@&n:res]-Pr[S.phase(i0,false)@&n:res]|<=gamma)=>
 `|Pr[SimSequentialKernel(S).phase(i0,true)@&m:res]-Pr[SimSequentialKernel(S).phase(i0,false)@&m:res]|<=gamma.
proof.
 move=>hs hp hb.
 apply(sim_sequential_distance S (fun (_:glob S)=>true) i0 gamma &m _ hs hp _).
 + conseq hs;auto.
 move=> &n _;exact(hb &n).
qed.
