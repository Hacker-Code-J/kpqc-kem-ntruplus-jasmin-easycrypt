require import AllCore List Ring StdBigop StdOrder.
require import Array768.
import IntOrder Ring.IntID.

(* These are norms of signed integer coefficient differences, not norms
   of finite-field asint representatives. The pair uses the ordinary
   concatenated Euclidean convention: both squared norms are added. *)
op inj_sqnorm(v:int Array768.t) : int =
 Bigint.BIA.bigi predT (fun i=>v.[i]*v.[i]) 0 768.
op inj_pair_sqnorm(z:int Array768.t * int Array768.t) : int = inj_sqnorm z.`1+inj_sqnorm z.`2.
op inj_maximum(xs:int list) : int = foldr max 0 xs.
op inj_infnorm(v:int Array768.t) : int =
 inj_maximum(map(fun i=>`|v.[i]|)(range 0 768)).
op inj_pair_infnorm(z:int Array768.t * int Array768.t) : int = max (inj_infnorm z.`1) (inj_infnorm z.`2).

lemma inj_square_nonnegative(x:int) : 0<=x*x.
proof. have h:=IntOrder.ge0_sqr x;by move:h;rewrite expr2. qed.
lemma inj_square_bound(x:int) : -2<=x<=2=>x*x<=4.
proof. smt(). qed.
lemma inj_maximum_nonnegative xs : 0<=inj_maximum xs.
proof.
 elim:xs=>[|x xs ih];first by rewrite /inj_maximum /=.
 rewrite /inj_maximum /= -/inj_maximum;have h:=IntOrder.maxrr x (inj_maximum xs);smt().
qed.
lemma inj_maximum_upper xs bound : 0<=bound=>(forall x,x \in xs=>x<=bound)=>inj_maximum xs<=bound.
proof.
 move=>hb;elim:xs=>[|x xs ih] /=;first by rewrite /inj_maximum /=.
 move=>h;have hx:=h x _;first by smt().
 have ht:=ih _;first by move=>y hy;apply h;smt().
 rewrite /inj_maximum /= -/inj_maximum IntOrder.ler_maxrP;by split.
qed.
lemma inj_sqnorm_nonnegative v : 0<=inj_sqnorm v.
proof.
 rewrite /inj_sqnorm;apply Bigint.sumr_ge0=>i _;exact(inj_square_nonnegative v.[i]).
qed.
lemma inj_sqnorm_coefficient v i : 0<=i<768=>v.[i]*v.[i]<=inj_sqnorm v.
proof.
 move=>hi.
 have h:0<=Bigint.BIA.big (predC1 i) (fun j=>v.[j]*v.[j])(range 0 768).
 + apply Bigint.sumr_ge0=>j _;exact(inj_square_nonnegative v.[j]).
 rewrite /inj_sqnorm (Bigint.BIA.bigD1 _ _ i) ?(mem_range,range_uniq) //=.
 smt().
qed.
require import NTRUPlus768INJCollision.

lemma inj_sqnorm_zero : inj_sqnorm inj_zero=0.
proof.
 rewrite /inj_sqnorm;apply Bigint.BIA.big1_seq=>i.
 rewrite mem_range /= =>hi.
 by rewrite /inj_zero Array768.initiE.
qed.
lemma inj_sqnorm_zero_iff v : inj_sqnorm v=0 <=> v=inj_zero.
proof.
 split;last by move=>->;exact inj_sqnorm_zero.
 move=>hz;apply Array768.tP=>i hi.
 have h:=inj_sqnorm_coefficient v i hi.
 rewrite /inj_zero Array768.initiE //;smt().
qed.
lemma inj_sqnorm_positive v : v<>inj_zero=>0<inj_sqnorm v.
proof. have h:=inj_sqnorm_nonnegative v;have hz:=inj_sqnorm_zero_iff v;smt(). qed.
lemma inj_pair_sqnorm_positive v w : inj_pair_nonzero v w=>0<inj_pair_sqnorm(v,w).
proof.
 rewrite /inj_pair_nonzero /inj_pair_sqnorm /=;have hv:=inj_sqnorm_nonnegative v;have hw:=inj_sqnorm_nonnegative w.
 move=>[hn|hn];[have h:=inj_sqnorm_positive v hn|have h:=inj_sqnorm_positive w hn];smt().
qed.
lemma inj_short_sqnorm v : inj_short v=>inj_sqnorm v<=3072.
proof.
 move=>hv;have h:inj_sqnorm v<=Bigint.BIA.bigi predT (fun _=>4) 0 768.
 + rewrite /inj_sqnorm;apply Bigint.ler_sum_seq=>i /mem_range hi _.
   exact(inj_square_bound v.[i] (hv i hi)).
 by move:h;rewrite Bigint.bigi_constz.
qed.
lemma inj_infnorm_nonnegative v : 0<=inj_infnorm v.
proof. rewrite /inj_infnorm;exact(inj_maximum_nonnegative _). qed.
lemma inj_short_infnorm v : inj_short v=>inj_infnorm v<=2.
proof.
 move=>hv;rewrite /inj_infnorm;apply inj_maximum_upper=> // x /mapP[i [/mem_range hi ->]].
 rewrite IntOrder.ler_norml;exact(hv i hi).
qed.
lemma inj_short_pair_sqnorm v w : inj_short v=>inj_short w=>inj_pair_sqnorm(v,w)<=6144.
proof.
 move=>hv hw;rewrite /inj_pair_sqnorm /=;have h1:=inj_short_sqnorm v hv;have h2:=inj_short_sqnorm w hw;smt().
qed.
lemma inj_short_pair_infnorm v w : inj_short v=>inj_short w=>inj_pair_infnorm(v,w)<=2.
proof.
 move=>hv hw;rewrite /inj_pair_infnorm /= IntOrder.ler_maxrP.
 split;[exact(inj_short_infnorm v hv)|exact(inj_short_infnorm w hw)].
qed.
lemma inj_short_nonzero_pair_bounds v w : inj_short v=>inj_short w=>inj_pair_nonzero v w=>
 0<inj_pair_sqnorm(v,w)<=6144 /\ inj_pair_infnorm(v,w)<=2 /\
 inj_sqnorm v<=3072 /\ inj_sqnorm w<=3072.
proof.
 move=>hv hw hn;have hp:=inj_pair_sqnorm_positive v w hn;
 have hb:=inj_short_pair_sqnorm v w hv hw;have hi:=inj_short_pair_infnorm v w hv hw;
 have h1:=inj_short_sqnorm v hv;have h2:=inj_short_sqnorm w hw.
 split;first by split.
 split;first exact hi.
 by split.
qed.
