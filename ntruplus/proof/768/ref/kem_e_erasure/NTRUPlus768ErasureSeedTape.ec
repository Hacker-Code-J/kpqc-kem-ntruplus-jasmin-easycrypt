require import AllCore List Distr DList.
from Jasmin require import JWord.
require import Array32 Array14466.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768StoppedKeygenModel.
require import NTRUPlus768ErasureModel NTRUPlus768ROMDistributions.

clone DList.ParametricProgram as ErasureSeedLists with type t <- erasure_seed.

(* Unread tape entries can be resampled. The prefix before cursor is
   retained, including all rejected-attempt seeds. *)
module ErasureTape = {
 var q:int
 proc refresh_raw() = {
  var suffix:erasure_seed list;
  suffix <$ dlist uniform32 (q-ErasureSeedPool.cursor);
  ErasureSeedPool.seeds <- take ErasureSeedPool.cursor ErasureSeedPool.seeds ++ suffix;
 }
 proc normalize() = {
  if (!(0<=ErasureSeedPool.cursor /\ size ErasureSeedPool.seeds=q)) {
   q <- max 0 q;
   ErasureSeedPool.cursor <- max 0 ErasureSeedPool.cursor;
   ErasureSeedPool.seeds <- take q (ErasureSeedPool.seeds ++ nseq q witness);
  }
 }
 proc refresh() = { normalize(); refresh_raw(); }
}.
module ErasureOnlinePool = {
 proc sample_raw() : erasure_seed = {
  var i:int; var x:erasure_seed;
  i <- ErasureSeedPool.cursor;
  ErasureSeedPool.cursor <- i+1;
  x <- witness;
  if(i<ErasureTape.q){
   x <$ uniform32;
   ErasureSeedPool.seeds <- put ErasureSeedPool.seeds i x;
  }
  return x;
 }
 proc sample() : erasure_seed = {
  var x:erasure_seed;
  ErasureTape.normalize();
  x <@ sample_raw();
  return x;
 }
}.

lemma erasure_tape_refresh_raw_ll : islossless ErasureTape.refresh_raw.
proof. proc; wp; rnd; auto=> /> &m; exact(dlist_ll uniform32 _ uniform32_ll). qed.
lemma erasure_tape_normalize_ll : islossless ErasureTape.normalize.
proof. proc; if; auto. qed.
lemma erasure_tape_refresh_ll : islossless ErasureTape.refresh.
proof. proc; call erasure_tape_refresh_raw_ll; call erasure_tape_normalize_ll; auto. qed.
lemma erasure_online_raw_ll : islossless ErasureOnlinePool.sample_raw.
proof. proc; sp; if; auto=> />; smt(uniform32_ll). qed.
lemma erasure_online_pool_ll : islossless ErasureOnlinePool.sample.
proof. proc; call erasure_online_raw_ll; call erasure_tape_normalize_ll; auto. qed.

lemma erasure_take_put (xs:erasure_seed list) i x : 0<=i<size xs =>
 take(i+1)(put xs i x)=rcons(take i xs)x.
proof.
 move=>hi; rewrite put_in // take_cat size_takel 1:/#.
 rewrite (_:i+1<i=false) 1:/# /=.
 smt(take0 cats1).
qed.

(* Totalization only serves the generic eager rule. It is the identity on
   every valid tape state used by the actual stopped setup. *)
lemma erasure_tape_normalize_valid :
 hoare[ErasureTape.normalize : true ==> 0<=ErasureSeedPool.cursor /\
   size ErasureSeedPool.seeds=ErasureTape.q].
proof.
 proc; if.
 + auto=> /> &m _; split; first smt(lez_maxl lez_maxr).
   apply size_takel; rewrite size_cat size_nseq; smt(size_ge0 lez_maxl lez_maxr).
 auto.
qed.
lemma erasure_tape_normalize_identity xs0 c0 q0 :
 0<=c0 => size xs0=q0 =>
 hoare[ErasureTape.normalize : ErasureSeedPool.seeds=xs0 /\
   ErasureSeedPool.cursor=c0 /\ ErasureTape.q=q0 ==>
   ErasureSeedPool.seeds=xs0 /\ ErasureSeedPool.cursor=c0 /\ ErasureTape.q=q0].
proof. move=>hc hs; proc; rcondf 1; auto. qed.
lemma erasure_tape_normalize_self :
 equiv[ErasureTape.normalize ~ ErasureTape.normalize :
   ={ErasureSeedPool.seeds,ErasureSeedPool.cursor,ErasureTape.q} ==>
   ={ErasureSeedPool.seeds,ErasureSeedPool.cursor,ErasureTape.q} /\
   0<=ErasureSeedPool.cursor{1} /\ size ErasureSeedPool.seeds{1}=ErasureTape.q{1}].
proof.
 conseq (_: ={ErasureSeedPool.seeds,ErasureSeedPool.cursor,ErasureTape.q} ==>
   ={ErasureSeedPool.seeds,ErasureSeedPool.cursor,ErasureTape.q})
   erasure_tape_normalize_valid _ => //.
 proc; sim.
qed.
lemma erasure_online_raw_valid :
 hoare[ErasureOnlinePool.sample_raw : 0<=ErasureSeedPool.cursor /\
   size ErasureSeedPool.seeds=ErasureTape.q ==>
   0<=ErasureSeedPool.cursor /\ size ErasureSeedPool.seeds=ErasureTape.q].
proof. proc; sp; if; auto=> />; smt(size_put). qed.
lemma erasure_online_normalized_equiv :
 equiv[ErasureOnlinePool.sample ~ ErasureOnlinePool.sample_raw :
   ={ErasureSeedPool.seeds,ErasureSeedPool.cursor,ErasureTape.q} /\
   0<=ErasureSeedPool.cursor{1} /\ size ErasureSeedPool.seeds{1}=ErasureTape.q{1} ==>
   ={res,ErasureSeedPool.seeds,ErasureSeedPool.cursor,ErasureTape.q}].
proof.
 proc; inline ErasureTape.normalize; rcondf{1} 1; first by auto.
 inline ErasureOnlinePool.sample_raw; wp; sp; sim; auto.
qed.
lemma erasure_refresh_normalized_equiv :
 equiv[ErasureTape.refresh ~ ErasureTape.refresh_raw :
   ={ErasureSeedPool.seeds,ErasureSeedPool.cursor,ErasureTape.q} /\
   0<=ErasureSeedPool.cursor{1} /\ size ErasureSeedPool.seeds{1}=ErasureTape.q{1} ==>
   ={ErasureSeedPool.seeds,ErasureSeedPool.cursor,ErasureTape.q}].
proof.
 proc; inline ErasureTape.normalize; rcondf{1} 1; first by auto.
 inline ErasureTape.refresh_raw; sim; auto.
qed.

lemma erasure_tape_step_valid :
 eager[ErasureTape.refresh_raw();, ErasureSeedPool.sample ~ ErasureOnlinePool.sample_raw,
       ErasureTape.refresh_raw(); :
 ={ErasureSeedPool.seeds,ErasureSeedPool.cursor,ErasureTape.q} /\
 0<=ErasureSeedPool.cursor{1} /\ size ErasureSeedPool.seeds{1}=ErasureTape.q{1} ==>
 ={res,ErasureSeedPool.seeds,ErasureSeedPool.cursor,ErasureTape.q} /\
 0<=ErasureSeedPool.cursor{1} /\ size ErasureSeedPool.seeds{1}=ErasureTape.q{1}].
proof.
 eager proc; inline ErasureTape.refresh_raw.
 case ((ErasureSeedPool.cursor<ErasureTape.q){1}).
 + rcondt{2} 4; first by auto.
   swap{2} 7 -3.
   outline{1} 1 ~ ErasureSeedLists.Sample.sample.
   rewrite equiv[{1} 1 ErasureSeedLists.Sample_SampleCons_eq]; first by auto=> />; smt().
   inline ErasureSeedLists.SampleCons.sample.
   sp; wp.
   do 2!rnd; skip=> />.
   move=> &2 hi hlt.
   rewrite (_:size ErasureSeedPool.seeds{2}-(i{2}+1)=size ErasureSeedPool.seeds{2}-i{2}-1) 1:/#.
   split; first by done.
   move=> _ rs hrs; split; first exact hrs.
   move=> _ r _.
   have hs:size rs=size ErasureSeedPool.seeds{2}-i{2}-1.
   + apply(supp_dlist_size uniform32 _ rs _ hrs); smt().
   have ht:size(take i{2} ErasureSeedPool.seeds{2})=i{2} by apply size_takel; smt().
   rewrite erasure_take_put 1:/# cat_rcons nth_cat ht.
   rewrite (_:i{2}<i{2}=false) 1:/# (_:i{2}-i{2}=0) 1:/# /=.
   rewrite size_cat ht /= hs; smt().
 + rcondf{2} 4; first by auto.
   auto=> /> &2 hc hnot.
   rewrite (dlist0 uniform32 (size ErasureSeedPool.seeds{2}-(ErasureSeedPool.cursor{2}+1)) _) 1:/#.
   rewrite (dlist0 uniform32 (size ErasureSeedPool.seeds{2}-ErasureSeedPool.cursor{2}) _) 1:/#.
   split; first by done.
   move=> _ xs /supp_dunit ->; rewrite supp_dunit /= !cats0.
   rewrite (take_oversize ErasureSeedPool.cursor{2} ErasureSeedPool.seeds{2} _) 1:/#.
   rewrite (take_oversize (ErasureSeedPool.cursor{2}+1) ErasureSeedPool.seeds{2} _) 1:/#.
   rewrite nth_out 1:/#; smt().
qed.

lemma erasure_tape_step :
 eager[ErasureTape.refresh();, ErasureSeedPool.sample ~ ErasureOnlinePool.sample,
       ErasureTape.refresh(); :
 ={ErasureSeedPool.seeds,ErasureSeedPool.cursor,ErasureTape.q} ==>
 ={res,ErasureSeedPool.seeds,ErasureSeedPool.cursor,ErasureTape.q}].
proof.
 eager proc; inline ErasureTape.refresh.
 seq 1 1:(={ErasureSeedPool.seeds,ErasureSeedPool.cursor,ErasureTape.q} /\
   0<=ErasureSeedPool.cursor{1} /\ size ErasureSeedPool.seeds{1}=ErasureTape.q{1}).
 + call erasure_tape_normalize_self; auto.
 inline{2} ErasureTape.normalize.
 rcondf{2} 3.
 + move=> &m; wp; call erasure_online_raw_valid; auto.
 outline{1} [2 .. 3] ~ ErasureSeedPool.sample.
 swap{2} 2 1; wp.
 eager call erasure_tape_step_valid; auto.
qed.

module type ErasureTapeContext(R:KeygenSeedRNG) = {
 proc run(qf:int,qg:int,workspace:W8.t Array14466.t) : stopped_output {R.sample}
}.

lemma erasure_tape_context (A<:ErasureTapeContext {-ErasureSeedPool,-ErasureTape}) :
 eager[ErasureTape.refresh();, A(ErasureSeedPool).run ~ A(ErasureOnlinePool).run,
       ErasureTape.refresh(); :
 ={arg,glob A,ErasureSeedPool.seeds,ErasureSeedPool.cursor,ErasureTape.q} ==>
 ={res,glob A,ErasureSeedPool.seeds,ErasureSeedPool.cursor,ErasureTape.q}].
proof.
 eager proc (={ErasureSeedPool.seeds,ErasureSeedPool.cursor,ErasureTape.q})=> //;
   try by sim.
 exact erasure_tape_step.
qed.
